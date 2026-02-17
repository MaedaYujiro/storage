// LogEncoder: Log encoding for CSP to SAT conversion using Dadda tree
// Uses binary representation for integer variables

use std::collections::HashMap;
use std::cell::{Cell, RefCell};
use crate::{Var, Literal, Constraint, Assignment};
use crate::domain::Domain;
use crate::csp::CSP;
use crate::expr::Sum;
use super::{
    Encoder, SatSolverBackend, EncoderState,
    TRUE_LIT, FALSE_LIT,
    Simplifier,
};

/// LogEncoder: encodes CSP to SAT using log encoding with Dadda compression
pub struct LogEncoder<'a, B: SatSolverBackend> {
    csp: &'a CSP,
    /// Backend wrapped in RefCell for interior mutability (needed for encode_literal)
    backend: RefCell<B>,
    state: EncoderState,
    /// Maps (var, bit_index) to SAT variable
    bit_vars: HashMap<(Var, usize), i32>,
    /// Number of bits for each variable
    num_bits: HashMap<Var, usize>,
    /// Offset (lb) for each variable
    var_offset: HashMap<Var, i32>,
    /// Auxiliary variable counter (interior mutability for encode_literal)
    aux_var_counter: Cell<i32>,
}

impl<'a, B: SatSolverBackend> LogEncoder<'a, B> {
    pub fn new(csp: &'a CSP, backend: B) -> Self {
        Self {
            csp,
            backend: RefCell::new(backend),
            state: EncoderState::new(),
            bit_vars: HashMap::new(),
            num_bits: HashMap::new(),
            var_offset: HashMap::new(),
            aux_var_counter: Cell::new(0),
        }
    }

    /// Get the number of bits needed to represent values in [0, max_val]
    fn bits_needed(max_val: i32) -> usize {
        if max_val <= 0 {
            return 1;
        }
        (32 - max_val.leading_zeros()) as usize
    }

    /// Get the SAT literal for bit i of variable x
    /// Returns the SAT variable (positive literal) for the i-th bit
    pub fn bit(&self, x: &Var, i: usize) -> i32 {
        if let Some(&lit) = self.bit_vars.get(&(x.clone(), i)) {
            lit
        } else {
            // Bit index out of range
            FALSE_LIT
        }
    }

    /// Get the offset (lower bound) for variable x
    fn offset(&self, x: &Var) -> i32 {
        *self.var_offset.get(x).unwrap_or(&0)
    }

    /// Create a new auxiliary variable (uses interior mutability)
    fn new_aux_var(&self) -> i32 {
        let count = self.aux_var_counter.get() + 1;
        self.aux_var_counter.set(count);
        self.state.sat_variable_count + count
    }

    /// Sync auxiliary variable counter to state (call after encode operations)
    fn sync_aux_vars(&mut self) {
        self.state.sat_variable_count += self.aux_var_counter.get();
        self.aux_var_counter.set(0);
    }

    /// Encode a half adder: sum = a XOR b, carry = a AND b
    /// Returns (sum_var, carry_var) - uses interior mutability
    fn half_adder(&self, a: i32, b: i32) -> (i32, i32) {
        // Handle constants
        if a == FALSE_LIT {
            return (b, FALSE_LIT);
        }
        if b == FALSE_LIT {
            return (a, FALSE_LIT);
        }
        if a == TRUE_LIT {
            let sum = self.new_aux_var();
            // sum = NOT b
            self.backend.borrow_mut().add_clause(&[-sum, -b]);
            self.backend.borrow_mut().add_clause(&[sum, b]);
            return (sum, b);
        }
        if b == TRUE_LIT {
            let sum = self.new_aux_var();
            // sum = NOT a
            self.backend.borrow_mut().add_clause(&[-sum, -a]);
            self.backend.borrow_mut().add_clause(&[sum, a]);
            return (sum, a);
        }

        let sum = self.new_aux_var();
        let carry = self.new_aux_var();

        // sum = a XOR b
        // sum <=> (a AND NOT b) OR (NOT a AND b)
        self.backend.borrow_mut().add_clause(&[-a, -b, -sum]);  // a AND b => NOT sum
        self.backend.borrow_mut().add_clause(&[a, b, -sum]);    // NOT a AND NOT b => NOT sum
        self.backend.borrow_mut().add_clause(&[-a, b, sum]);    // NOT a AND b => sum
        self.backend.borrow_mut().add_clause(&[a, -b, sum]);    // a AND NOT b => sum

        // carry = a AND b
        self.backend.borrow_mut().add_clause(&[-a, -b, carry]); // a AND b => carry
        self.backend.borrow_mut().add_clause(&[a, -carry]);     // carry => a
        self.backend.borrow_mut().add_clause(&[b, -carry]);     // carry => b

        (sum, carry)
    }

    /// Encode a full adder: sum = a XOR b XOR c, carry = majority(a, b, c)
    /// Returns (sum_var, carry_var) - uses interior mutability
    fn full_adder(&self, a: i32, b: i32, c: i32) -> (i32, i32) {
        // Handle constants - reduce to half adder if possible
        if a == FALSE_LIT {
            return self.half_adder(b, c);
        }
        if b == FALSE_LIT {
            return self.half_adder(a, c);
        }
        if c == FALSE_LIT {
            return self.half_adder(a, b);
        }

        let sum = self.new_aux_var();
        let carry = self.new_aux_var();

        // sum = a XOR b XOR c (odd parity)
        // sum is true iff odd number of inputs are true
        self.backend.borrow_mut().add_clause(&[a, b, c, -sum]);      // 0 true => sum=0
        self.backend.borrow_mut().add_clause(&[-a, -b, c, -sum]);    // 2 true (a,b) => sum=0
        self.backend.borrow_mut().add_clause(&[-a, b, -c, -sum]);    // 2 true (a,c) => sum=0
        self.backend.borrow_mut().add_clause(&[a, -b, -c, -sum]);    // 2 true (b,c) => sum=0
        self.backend.borrow_mut().add_clause(&[-a, b, c, sum]);      // 1 true (a) => sum=1
        self.backend.borrow_mut().add_clause(&[a, -b, c, sum]);      // 1 true (b) => sum=1
        self.backend.borrow_mut().add_clause(&[a, b, -c, sum]);      // 1 true (c) => sum=1
        self.backend.borrow_mut().add_clause(&[-a, -b, -c, sum]);    // 3 true => sum=1

        // carry = majority(a, b, c)
        // carry is true iff at least 2 inputs are true
        self.backend.borrow_mut().add_clause(&[a, b, -carry]);      // need at least 2
        self.backend.borrow_mut().add_clause(&[a, c, -carry]);
        self.backend.borrow_mut().add_clause(&[b, c, -carry]);
        self.backend.borrow_mut().add_clause(&[-a, -b, carry]);     // 2 true => carry
        self.backend.borrow_mut().add_clause(&[-a, -c, carry]);
        self.backend.borrow_mut().add_clause(&[-b, -c, carry]);

        (sum, carry)
    }

    /// Dadda reduction: reduce columns of bits to at most 2 bits per column
    /// Input: columns[i] = list of bits with weight 2^i
    /// Output: two numbers (as bit vectors) whose sum equals the original
    fn dadda_reduce(&self, mut columns: Vec<Vec<i32>>) -> (Vec<i32>, Vec<i32>) {
        // Dadda sequence: 2, 3, 4, 6, 9, 13, 19, 28, ...
        // d(n+1) = floor(1.5 * d(n))
        fn dadda_sequence(max_height: usize) -> Vec<usize> {
            let mut seq = vec![2];
            while *seq.last().unwrap() < max_height {
                let next = (seq.last().unwrap() * 3) / 2;
                seq.push(next);
            }
            seq.reverse();
            seq
        }

        // Find maximum column height
        let max_height = columns.iter().map(|c| c.len()).max().unwrap_or(0);
        if max_height <= 2 {
            // Already reduced
            let row0: Vec<i32> = columns.iter().map(|c| c.first().copied().unwrap_or(FALSE_LIT)).collect();
            let row1: Vec<i32> = columns.iter().map(|c| c.get(1).copied().unwrap_or(FALSE_LIT)).collect();
            return (row0, row1);
        }

        let targets = dadda_sequence(max_height);

        for &target in &targets {
            if target >= max_height {
                continue;
            }

            // Reduce each column to at most 'target' bits
            for i in 0..columns.len() {
                while columns[i].len() > target {
                    if columns[i].len() >= 3 && columns[i].len() > target {
                        // Use full adder
                        let a = columns[i].pop().unwrap();
                        let b = columns[i].pop().unwrap();
                        let c = columns[i].pop().unwrap();
                        let (sum, carry) = self.full_adder(a, b, c);
                        columns[i].push(sum);
                        // Add carry to next column
                        if i + 1 >= columns.len() {
                            columns.push(Vec::new());
                        }
                        columns[i + 1].push(carry);
                    } else if columns[i].len() == 2 && columns[i].len() > target {
                        // This shouldn't happen with target >= 2, but handle it
                        break;
                    } else {
                        break;
                    }
                }
            }
        }

        // Final pass: ensure at most 2 bits per column
        for i in 0..columns.len() {
            while columns[i].len() > 2 {
                let a = columns[i].pop().unwrap();
                let b = columns[i].pop().unwrap();
                let c = columns[i].pop().unwrap_or(FALSE_LIT);
                let (sum, carry) = if c == FALSE_LIT {
                    self.half_adder(a, b)
                } else {
                    self.full_adder(a, b, c)
                };
                columns[i].push(sum);
                if i + 1 >= columns.len() {
                    columns.push(Vec::new());
                }
                columns[i + 1].push(carry);
            }
        }

        // Extract two rows
        let row0: Vec<i32> = columns.iter().map(|c| c.first().copied().unwrap_or(FALSE_LIT)).collect();
        let row1: Vec<i32> = columns.iter().map(|c| c.get(1).copied().unwrap_or(FALSE_LIT)).collect();

        (row0, row1)
    }

    /// Encode comparison: a + b <= constant using ripple-carry
    /// a and b are bit vectors (LSB first), constant is the bound
    fn encode_sum_le_constant(&self, a: &[i32], b: &[i32], constant: i64) {
        if constant < 0 {
            // Always false
            self.backend.borrow_mut().add_clause(&[]);
            return;
        }

        let max_bits = a.len().max(b.len());

        // Compute a + b and compare with constant
        // We use a different approach: enumerate forbidden patterns
        // For each bit position, if setting certain bits would exceed constant, forbid it

        // Actually, let's use a simpler approach:
        // Create the sum bits and then use a comparator

        // First, add a and b using ripple-carry adder
        let mut sum_bits = Vec::new();
        let mut carry = FALSE_LIT;

        for i in 0..max_bits {
            let ai = if i < a.len() { a[i] } else { FALSE_LIT };
            let bi = if i < b.len() { b[i] } else { FALSE_LIT };

            let (s, c) = self.full_adder(ai, bi, carry);
            sum_bits.push(s);
            carry = c;
        }
        sum_bits.push(carry);

        // Now encode sum_bits <= constant
        self.encode_bits_le_constant(&sum_bits, constant);
    }

    /// Encode: bit vector <= constant
    fn encode_bits_le_constant(&self, bits: &[i32], constant: i64) {
        if constant < 0 {
            self.backend.borrow_mut().add_clause(&[]);
            return;
        }

        // Check if constant is large enough to always satisfy
        let max_val = (1i64 << bits.len()) - 1;
        if constant >= max_val {
            return; // Always true
        }

        // Encode using bit-by-bit comparison
        // bits <= constant iff there exists a bit position i where:
        // - all higher bits match constant's bits
        // - bit i is 0 when constant's bit i is 0
        // OR all bits match constant

        // Simpler approach: forbid values > constant
        // For each value v > constant, add clause forbidding it
        // This is exponential, so only use for small ranges

        if bits.len() <= 10 {
            // Small enough for explicit enumeration
            for v in (constant + 1)..=(max_val.min(constant + (1 << bits.len()))) {
                let mut clause = Vec::new();
                for (i, &bit) in bits.iter().enumerate() {
                    if (v >> i) & 1 == 1 {
                        if bit != TRUE_LIT && bit != FALSE_LIT {
                            clause.push(-bit);
                        } else if bit == TRUE_LIT {
                            // This bit is always 1, can't change
                        } else {
                            // bit == FALSE_LIT, this value is impossible anyway
                            clause.clear();
                            break;
                        }
                    } else {
                        if bit == TRUE_LIT {
                            // This bit is always 1 but should be 0 for this value
                            // This value is impossible
                            clause.clear();
                            break;
                        }
                    }
                }
                if !clause.is_empty() {
                    self.backend.borrow_mut().add_clause(&clause);
                }
            }
        } else {
            // For larger ranges, use a more sophisticated encoding
            // Encode using lexicographic comparison
            self.encode_lex_le(bits, constant);
        }
    }

    /// Encode lexicographic comparison: bits <= constant
    fn encode_lex_le(&self, bits: &[i32], constant: i64) {
        // Process from MSB to LSB
        // At each position, either:
        // - All higher bits match and this bit < constant's bit (then we're done, it's less)
        // - All higher bits match and this bit = constant's bit (continue comparing)
        // - All higher bits match and this bit > constant's bit (forbidden)

        let n = bits.len();

        // aux[i] = true iff bits[n-1..i+1] == constant[n-1..i+1] (all higher bits match)
        let mut aux_vars = Vec::new();

        for i in (0..n).rev() {
            let const_bit = ((constant >> i) & 1) == 1;
            let bit = if i < bits.len() { bits[i] } else { FALSE_LIT };

            if i == n - 1 {
                // MSB
                if const_bit {
                    // constant's MSB is 1, so bit can be 0 or 1
                    // If bit is 0, we're definitely <=
                    // If bit is 1, continue comparing
                    let eq = self.new_aux_var();
                    // eq <=> (bit = 1)
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-eq, bit]);
                        self.backend.borrow_mut().add_clause(&[eq, -bit]);
                    } else if bit == TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[eq]);
                    } else {
                        self.backend.borrow_mut().add_clause(&[-eq]);
                    }
                    aux_vars.push(eq);
                } else {
                    // constant's MSB is 0, so bit must be 0
                    if bit != FALSE_LIT && bit != TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-bit]);
                    } else if bit == TRUE_LIT {
                        // Contradiction
                        self.backend.borrow_mut().add_clause(&[]);
                        return;
                    }
                    let eq = self.new_aux_var();
                    self.backend.borrow_mut().add_clause(&[eq]); // Always equal at this position
                    aux_vars.push(eq);
                }
            } else {
                let prev_eq = *aux_vars.last().unwrap();

                if const_bit {
                    // If prev_eq and bit = 1, continue (new_eq = true)
                    // If prev_eq and bit = 0, we're definitely less (new_eq irrelevant, but set false)
                    // If !prev_eq, we're already less, so new_eq = false
                    let new_eq = self.new_aux_var();

                    // new_eq => prev_eq AND bit
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-new_eq, prev_eq]);
                        self.backend.borrow_mut().add_clause(&[-new_eq, bit]);
                    } else if bit == TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-new_eq, prev_eq]);
                    } else {
                        self.backend.borrow_mut().add_clause(&[-new_eq]);
                    }

                    // prev_eq AND bit => new_eq
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq, -bit, new_eq]);
                    } else if bit == TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq, new_eq]);
                    }

                    aux_vars.push(new_eq);
                } else {
                    // If prev_eq and bit = 1, this is FORBIDDEN
                    // If prev_eq and bit = 0, continue (new_eq = true)
                    // If !prev_eq, we're already less

                    // Forbid: prev_eq AND bit
                    if bit != FALSE_LIT && bit != TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq, -bit]);
                    } else if bit == TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq]);
                    }

                    let new_eq = self.new_aux_var();
                    // new_eq <=> prev_eq (since bit must be 0 if prev_eq)
                    self.backend.borrow_mut().add_clause(&[-new_eq, prev_eq]);
                    self.backend.borrow_mut().add_clause(&[new_eq, -prev_eq]);

                    aux_vars.push(new_eq);
                }
            }
        }
    }

    /// Check if all coefficients are positive
    fn all_positive_coefficients(&self, sum: &Sum) -> bool {
        sum.terms().iter().all(|(a, _)| *a > 0)
    }

    /// Encode LeZero constraint: sum <= 0 (uses interior mutability)
    /// Only handles positive coefficients - negative coefficients should use encode_ge_zero
    fn encode_le_zero(&self, sum: &Sum, clause0: &[i32]) -> Vec<Vec<i32>> {
        let terms: Vec<_> = sum.terms().iter().map(|(a, v)| (*a, v.clone())).collect();
        let bound = -sum.b() as i64;  // sum of terms <= bound

        if terms.is_empty() {
            if bound >= 0 {
                return vec![];
            } else {
                return vec![clause0.to_vec()];
            }
        }

        // Check for negative coefficients - handle via encode_ge_zero
        if !self.all_positive_coefficients(sum) {
            // For mixed or negative coefficients, convert to GeZero problem
            // sum <= 0 <=> -sum >= 0
            return self.encode_ge_zero(&(-sum.clone()), clause0);
        }

        // Build columns for Dadda reduction (only positive coefficients)
        let mut columns: Vec<Vec<i32>> = Vec::new();
        let mut total_offset: i64 = 0;

        for (a, x) in &terms {
            let offset = self.offset(x);
            let n_bits = *self.num_bits.get(x).unwrap_or(&0);

            // a * x = a * (offset + sum(2^i * bit_i))
            total_offset += (*a as i64) * (offset as i64);

            for i in 0..n_bits {
                let weight = (*a as i64) * (1i64 << i);
                let bit = self.bit(x, i);

                let mut remaining_weight = weight;
                let mut col = 0;
                while remaining_weight > 0 {
                    if remaining_weight & 1 == 1 {
                        while columns.len() <= col {
                            columns.push(Vec::new());
                        }
                        columns[col].push(bit);
                    }
                    remaining_weight >>= 1;
                    col += 1;
                }
            }
        }

        let adjusted_bound = bound - total_offset;

        if columns.is_empty() {
            if adjusted_bound >= 0 {
                return vec![];
            } else {
                return vec![clause0.to_vec()];
            }
        }

        // Apply Dadda reduction
        let (row0, row1) = self.dadda_reduce(columns);

        // Encode: row0 + row1 <= adjusted_bound
        self.encode_sum_le_constant(&row0, &row1, adjusted_bound);

        vec![]
    }

    /// Encode GeZero constraint: sum >= 0 (uses interior mutability)
    /// Only handles positive coefficients - negative coefficients should use encode_le_zero
    fn encode_ge_zero(&self, sum: &Sum, clause0: &[i32]) -> Vec<Vec<i32>> {
        let terms: Vec<_> = sum.terms().iter().map(|(a, v)| (*a, v.clone())).collect();
        let bound = sum.b() as i64;  // sum of terms >= -bound, i.e., sum >= bound (when b is added to RHS)
        // Actually: sum >= 0 means sum_terms + b >= 0, i.e., sum_terms >= -b

        if terms.is_empty() {
            if bound <= 0 {
                return vec![];  // 0 >= -bound is always true when bound <= 0
            } else {
                return vec![clause0.to_vec()];  // 0 >= bound is false when bound > 0
            }
        }

        // Check for negative coefficients
        if !self.all_positive_coefficients(sum) {
            // For mixed or negative coefficients, convert to LeZero problem
            return self.encode_le_zero(&(-sum.clone()), clause0);
        }

        // Build columns for Dadda reduction (only positive coefficients)
        let mut columns: Vec<Vec<i32>> = Vec::new();
        let mut total_offset: i64 = 0;

        for (a, x) in &terms {
            let offset = self.offset(x);
            let n_bits = *self.num_bits.get(x).unwrap_or(&0);

            total_offset += (*a as i64) * (offset as i64);

            for i in 0..n_bits {
                let weight = (*a as i64) * (1i64 << i);
                let bit = self.bit(x, i);

                let mut remaining_weight = weight;
                let mut col = 0;
                while remaining_weight > 0 {
                    if remaining_weight & 1 == 1 {
                        while columns.len() <= col {
                            columns.push(Vec::new());
                        }
                        columns[col].push(bit);
                    }
                    remaining_weight >>= 1;
                    col += 1;
                }
            }
        }

        // We need: sum_terms >= -b
        // With offset: sum_bits + total_offset >= -b
        // sum_bits >= -b - total_offset
        let lower_bound = -bound - total_offset;

        if columns.is_empty() {
            if lower_bound <= 0 {
                return vec![];
            } else {
                return vec![clause0.to_vec()];
            }
        }

        // Apply Dadda reduction
        let (row0, row1) = self.dadda_reduce(columns);

        // Encode: row0 + row1 >= lower_bound
        self.encode_sum_ge_constant(&row0, &row1, lower_bound);

        vec![]
    }

    /// Encode comparison: a + b >= constant using ripple-carry
    fn encode_sum_ge_constant(&self, a: &[i32], b: &[i32], constant: i64) {
        if constant <= 0 {
            // Always true (sum of non-negative values >= 0)
            return;
        }

        let max_bits = a.len().max(b.len());

        // First, add a and b using ripple-carry adder
        let mut sum_bits = Vec::new();
        let mut carry = FALSE_LIT;

        for i in 0..max_bits {
            let ai = if i < a.len() { a[i] } else { FALSE_LIT };
            let bi = if i < b.len() { b[i] } else { FALSE_LIT };

            let (s, c) = self.full_adder(ai, bi, carry);
            sum_bits.push(s);
            carry = c;
        }
        sum_bits.push(carry);

        // Now encode sum_bits >= constant
        self.encode_bits_ge_constant(&sum_bits, constant);
    }

    /// Encode: bit vector >= constant
    fn encode_bits_ge_constant(&self, bits: &[i32], constant: i64) {
        if constant <= 0 {
            return; // Always true
        }

        let max_val = (1i64 << bits.len()) - 1;
        if constant > max_val {
            // Never satisfiable
            self.backend.borrow_mut().add_clause(&[]);
            return;
        }

        // bits >= constant iff NOT(bits < constant) iff NOT(bits <= constant - 1)
        // We encode by forbidding values < constant

        if bits.len() <= 10 && constant <= 1024 {
            // Small enough for explicit enumeration - forbid values 0..constant-1
            for v in 0..constant {
                let mut clause = Vec::new();
                for (i, &bit) in bits.iter().enumerate() {
                    // Forbid this specific value v
                    // At least one bit must differ from v's pattern
                    if (v >> i) & 1 == 1 {
                        // v has 1 at position i, so bit can be 0
                        if bit != TRUE_LIT && bit != FALSE_LIT {
                            clause.push(-bit);
                        } else if bit == FALSE_LIT {
                            // Already different, this value is automatically excluded
                            clause.clear();
                            break;
                        }
                    } else {
                        // v has 0 at position i, so bit can be 1
                        if bit != TRUE_LIT && bit != FALSE_LIT {
                            clause.push(bit);
                        } else if bit == TRUE_LIT {
                            // Already different
                            clause.clear();
                            break;
                        }
                    }
                }
                if !clause.is_empty() {
                    self.backend.borrow_mut().add_clause(&clause);
                }
            }
        } else {
            // Use lexicographic encoding for larger ranges
            self.encode_lex_ge(bits, constant);
        }
    }

    /// Encode lexicographic comparison: bits >= constant
    fn encode_lex_ge(&self, bits: &[i32], constant: i64) {
        // bits >= constant is equivalent to NOT(bits < constant)
        // bits < constant means bits <= constant - 1
        // So we need to ensure that bits is NOT <= constant - 1

        // An alternative: encode "bits >= constant" directly
        // For each bit position from MSB to LSB:
        // - If we've established bits > constant already, we're done
        // - If bits match so far and current bit > constant's bit, we're done (>)
        // - If bits match so far and current bit = constant's bit, continue
        // - If bits match so far and current bit < constant's bit, forbidden

        let n = bits.len();
        let mut aux_vars = Vec::new();

        for i in (0..n).rev() {
            let const_bit = ((constant >> i) & 1) == 1;
            let bit = if i < bits.len() { bits[i] } else { FALSE_LIT };

            if i == n - 1 {
                // MSB
                if const_bit {
                    // constant's MSB is 1, so bit must be 1 to have any chance of >=
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[bit]);
                    } else if bit == FALSE_LIT {
                        // Contradiction - value is always < constant
                        self.backend.borrow_mut().add_clause(&[]);
                        return;
                    }
                    let eq = self.new_aux_var();
                    self.backend.borrow_mut().add_clause(&[eq]); // bits = constant at this position
                    aux_vars.push(eq);
                } else {
                    // constant's MSB is 0
                    // If bit is 1, we're definitely >
                    // If bit is 0, continue comparing
                    let eq = self.new_aux_var();
                    // eq <=> (bit = 0)
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-eq, -bit]);
                        self.backend.borrow_mut().add_clause(&[eq, bit]);
                    } else if bit == TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-eq]);
                    } else {
                        self.backend.borrow_mut().add_clause(&[eq]);
                    }
                    aux_vars.push(eq);
                }
            } else {
                let prev_eq = *aux_vars.last().unwrap();

                if const_bit {
                    // constant has 1 at this position
                    // If prev_eq (all higher bits match) and bit = 0, this is FORBIDDEN (bits < constant)
                    // If prev_eq and bit = 1, continue (new_eq = true)
                    // If !prev_eq, we're already > (new_eq irrelevant)

                    // Forbid: prev_eq AND NOT bit
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq, bit]);
                    } else if bit == FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq]);
                    }

                    let new_eq = self.new_aux_var();
                    // new_eq <=> prev_eq (since bit must be 1 if prev_eq)
                    self.backend.borrow_mut().add_clause(&[-new_eq, prev_eq]);
                    self.backend.borrow_mut().add_clause(&[new_eq, -prev_eq]);

                    aux_vars.push(new_eq);
                } else {
                    // constant has 0 at this position
                    // If prev_eq and bit = 1, we're > (done, new_eq = false)
                    // If prev_eq and bit = 0, continue (new_eq = true)
                    // If !prev_eq, we're already >
                    let new_eq = self.new_aux_var();

                    // new_eq => prev_eq AND NOT bit
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-new_eq, prev_eq]);
                        self.backend.borrow_mut().add_clause(&[-new_eq, -bit]);
                    } else if bit == TRUE_LIT {
                        self.backend.borrow_mut().add_clause(&[-new_eq]);
                    } else {
                        self.backend.borrow_mut().add_clause(&[-new_eq, prev_eq]);
                    }

                    // prev_eq AND NOT bit => new_eq
                    if bit != TRUE_LIT && bit != FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq, bit, new_eq]);
                    } else if bit == FALSE_LIT {
                        self.backend.borrow_mut().add_clause(&[-prev_eq, new_eq]);
                    }

                    aux_vars.push(new_eq);
                }
            }
        }
    }

    /// Add clause to backend
    fn add_clause_internal(&mut self, clause: &[i32]) {
        let clause: Vec<_> = clause.iter()
            .filter(|&&l| l != FALSE_LIT)
            .copied()
            .collect();

        if clause.contains(&TRUE_LIT) {
            return;
        }

        if clause.is_empty() {
            self.backend.borrow_mut().add_clause(&[1]);
            self.backend.borrow_mut().add_clause(&[-1]);
            self.state.sat_clause_count += 2;
        } else {
            self.backend.borrow_mut().add_clause(&clause);
            self.state.sat_clause_count += 1;
        }
    }

    /// Encode the entire CSP
    pub fn encode_csp(&mut self) {
        // 1. Assign bit variables to integer variables
        for (var, domain) in self.csp.int_vars() {
            let lb = domain.lb();
            let range = domain.ub() - lb;
            let n_bits = Self::bits_needed(range);

            self.var_offset.insert(var.clone(), lb);
            self.num_bits.insert(var.clone(), n_bits);

            // Create SAT variables for bits
            let base_code = self.state.sat_variable_count + 1;
            for i in 0..n_bits {
                self.bit_vars.insert((var.clone(), i), base_code + i as i32);
            }
            self.state.sat_variable_count += n_bits as i32;
            self.state.var_code_map.insert(var.clone(), base_code);
        }

        // 2. Assign codes to boolean variables
        for b in self.csp.bool_vars() {
            self.state.bool_code_map.insert(b.clone(), self.state.sat_variable_count + 1);
            self.state.sat_variable_count += 1;
        }

        // 3. Reserve variables in backend
        self.backend.borrow_mut().reserve_vars(self.state.sat_variable_count);

        // 4. Encode domain bounds for integer variables
        for (var, domain) in self.csp.int_vars() {
            let clauses = self.encode_var(var);
            for clause in clauses {
                self.add_clause_internal(&clause);
            }

            // Encode upper bound: binary value <= range
            let range = domain.ub() - domain.lb();
            let n_bits = *self.num_bits.get(var).unwrap();
            let bits: Vec<i32> = (0..n_bits).map(|i| self.bit(var, i)).collect();
            self.encode_bits_le_constant(&bits, range as i64);
        }

        // 5. Encode constraints
        let constraints: Vec<_> = self.csp.constraints().to_vec();
        for c in constraints {
            self.add_constraint(&c);
        }

        // Sync auxiliary variables allocated during encoding
        self.sync_aux_vars();
    }

    /// Decode the SAT solution to an Assignment
    pub fn decode(&mut self) -> Assignment {
        let mut assignment = Assignment::new();

        let int_vars: Vec<_> = self.csp.int_vars().iter().map(|(v, _)| v.clone()).collect();
        for var in int_vars {
            let value = self.decode_var(&var);
            assignment.set_int(var, value);
        }

        let bool_vars: Vec<_> = self.csp.bool_vars().to_vec();
        for b in bool_vars {
            if let Some(&code) = self.state.bool_code_map.get(&b) {
                let value = self.backend.borrow_mut().model_value(code);
                assignment.set_bool(b, value);
            }
        }

        assignment
    }

    /// Access the CSP
    pub fn csp(&self) -> &CSP {
        self.csp
    }
}

impl<'a, B: SatSolverBackend> Encoder for LogEncoder<'a, B> {
    type Backend = B;

    fn sat_variables_size(&self, _var: &Var, domain: &Domain) -> i32 {
        // Log encoding: ceil(log2(ub - lb + 1)) bits
        let range = domain.ub() - domain.lb();
        Self::bits_needed(range) as i32
    }

    fn encode_var(&self, _var: &Var) -> Vec<Vec<i32>> {
        // Domain bounds are encoded separately in encode_csp
        // No explicit variable encoding needed here
        vec![]
    }

    fn encode_literal(&self, lit: &Constraint, clause0: &[i32]) -> Vec<Vec<i32>> {
        match lit {
            Constraint::Lit(literal) => {
                let code = match literal {
                    Literal::Pos(b) => {
                        *self.state.bool_code_map.get(b).expect("bool not encoded")
                    }
                    Literal::Neg(b) => {
                        -*self.state.bool_code_map.get(b).expect("bool not encoded")
                    }
                };
                let mut clause = clause0.to_vec();
                clause.push(code);
                vec![clause]
            }
            Constraint::LeZero(sum) => {
                self.encode_le_zero(sum, clause0)
            }
            Constraint::GeZero(sum) => {
                // sum >= 0 <=> -sum <= 0
                self.encode_le_zero(&(-sum.clone()), clause0)
            }
            Constraint::EqZero(sum) => {
                // sum == 0 <=> sum <= 0 AND sum >= 0
                let mut clauses = self.encode_le_zero(sum, clause0);
                clauses.extend(self.encode_le_zero(&(-sum.clone()), clause0));
                clauses
            }
            Constraint::NeZero(sum) => {
                // sum != 0 <=> sum <= -1 OR sum >= 1
                // This is complex with log encoding, use direct approach for single var
                let terms: Vec<_> = sum.terms().iter().collect();
                if terms.len() == 1 {
                    let (a, x) = terms[0];
                    let target = -sum.b();
                    if target % a != 0 {
                        return vec![];  // Always true
                    }
                    let d = target / a;
                    // x != d
                    let offset = self.offset(x);
                    let n_bits = *self.num_bits.get(x).unwrap_or(&0);
                    let val = d - offset;

                    if val < 0 || val >= (1 << n_bits) {
                        return vec![];  // Always true (value out of range)
                    }

                    // At least one bit must differ
                    let mut clause = clause0.to_vec();
                    for i in 0..n_bits {
                        let bit = self.bit(x, i);
                        let expected = ((val >> i) & 1) == 1;
                        if expected {
                            clause.push(-bit);
                        } else {
                            clause.push(bit);
                        }
                    }
                    return vec![clause];
                }

                // For multiple variables, fall back to less efficient encoding
                // sum != 0 is hard to encode directly
                vec![]
            }
            _ => panic!("LogEncoder: unexpected constraint type {:?}", lit),
        }
    }

    fn add_constraint(&mut self, c: &Constraint) {
        // Convert to LeZero form where possible
        let converted = match c {
            Constraint::GeZero(sum) => Constraint::LeZero(-sum.clone()),
            Constraint::EqZero(sum) => {
                // Handle as two constraints
                self.add_constraint(&Constraint::LeZero(sum.clone()));
                Constraint::LeZero(-sum.clone())
            }
            _ => c.clone(),
        };

        // Simplify
        let mut simplifier = Simplifier::new(self);
        let simplified = simplifier.simplify(&converted);

        for lits in simplified {
            if lits.is_empty() {
                continue;
            }

            if lits.len() == 1 {
                let clauses = self.encode_literal(&lits[0], &[]);
                for clause in clauses {
                    self.add_clause_internal(&clause);
                }
            } else {
                // Multiple literals
                let mut all_simple_bool = true;
                let mut sat_lits = Vec::new();

                for lit in &lits {
                    if let Constraint::Lit(l) = lit {
                        let code = match l {
                            Literal::Pos(b) => *self.state.bool_code_map.get(b).unwrap_or(&0),
                            Literal::Neg(b) => -*self.state.bool_code_map.get(b).unwrap_or(&0),
                        };
                        if code != 0 {
                            sat_lits.push(code);
                        } else {
                            all_simple_bool = false;
                            break;
                        }
                    } else {
                        all_simple_bool = false;
                        break;
                    }
                }

                if all_simple_bool && !sat_lits.is_empty() {
                    self.add_clause_internal(&sat_lits);
                } else {
                    for lit in lits {
                        let clauses = self.encode_literal(&lit, &[]);
                        for clause in clauses {
                            self.add_clause_internal(&clause);
                        }
                    }
                }
            }
        }
    }

    fn decode_var(&mut self, var: &Var) -> i32 {
        let offset = self.offset(var);
        let n_bits = *self.num_bits.get(var).unwrap_or(&0);

        let mut value = 0;
        for i in 0..n_bits {
            let bit = self.bit(var, i);
            if bit != FALSE_LIT && (bit == TRUE_LIT || self.backend.borrow_mut().model_value(bit)) {
                value |= 1 << i;
            }
        }

        offset + value
    }

    fn state(&self) -> &EncoderState {
        &self.state
    }

    fn state_mut(&mut self) -> &mut EncoderState {
        &mut self.state
    }

    fn backend(&self) -> &Self::Backend {
        // Note: This panics if there's an active mutable borrow
        // Consider using backend_mut() instead when possible
        unsafe { &*self.backend.as_ptr() }
    }

    fn backend_mut(&mut self) -> &mut Self::Backend {
        self.backend.get_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CaDiCaLSolver;
    use crate::expr::Sum;
    use std::collections::HashSet;

    /// Helper: enumerate all solutions for a single integer variable
    fn enumerate_all_int_solutions(
        encoder: &mut LogEncoder<CaDiCaLSolver>,
        var: &Var,
    ) -> Vec<i32> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let val = assignment.get_int(var).unwrap();
            solutions.push(val);

            // Block current solution: at least one bit must differ
            let n_bits = *encoder.num_bits.get(var).unwrap();
            let offset = encoder.offset(var);
            let binary_val = val - offset;

            let mut block_clause = Vec::new();
            for i in 0..n_bits {
                let bit = encoder.bit(var, i);
                if bit != FALSE_LIT && bit != TRUE_LIT {
                    let bit_set = ((binary_val >> i) & 1) == 1;
                    block_clause.push(if bit_set { -bit } else { bit });
                }
            }
            if !block_clause.is_empty() {
                encoder.backend.borrow_mut().add_clause(&block_clause);
            } else {
                break; // No more solutions possible
            }
        }

        solutions.sort();
        solutions
    }

    /// Helper: enumerate all solutions for two integer variables
    fn enumerate_all_two_int_solutions(
        encoder: &mut LogEncoder<CaDiCaLSolver>,
        var1: &Var,
        var2: &Var,
    ) -> Vec<(i32, i32)> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let val1 = assignment.get_int(var1).unwrap();
            let val2 = assignment.get_int(var2).unwrap();
            solutions.push((val1, val2));

            // Block current solution
            let mut block_clause = Vec::new();

            for (var, val) in [(var1, val1), (var2, val2)] {
                let n_bits = *encoder.num_bits.get(var).unwrap();
                let offset = encoder.offset(var);
                let binary_val = val - offset;

                for i in 0..n_bits {
                    let bit = encoder.bit(var, i);
                    if bit != FALSE_LIT && bit != TRUE_LIT {
                        let bit_set = ((binary_val >> i) & 1) == 1;
                        block_clause.push(if bit_set { -bit } else { bit });
                    }
                }
            }

            if !block_clause.is_empty() {
                encoder.backend.borrow_mut().add_clause(&block_clause);
            } else {
                break;
            }
        }

        solutions.sort();
        solutions
    }

    #[test]
    fn test_bits_needed() {
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(0), 1);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(1), 1);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(2), 2);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(3), 2);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(4), 3);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(7), 3);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(8), 4);
        assert_eq!(LogEncoder::<CaDiCaLSolver>::bits_needed(15), 4);
    }

    #[test]
    fn test_log_encoder_new() {
        let csp = CSP::new();
        let solver = CaDiCaLSolver::new();
        let encoder = LogEncoder::new(&csp, solver);
        assert_eq!(encoder.state.sat_variable_count, 0);
    }

    #[test]
    fn test_sat_variables_size() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 7));
        let solver = CaDiCaLSolver::new();
        let encoder = LogEncoder::new(&csp, solver);

        let domain = csp.domain(&x).unwrap();
        // Log encoding: 3 bits for [0, 7]
        assert_eq!(encoder.sat_variables_size(&x, domain), 3);
    }

    #[test]
    fn test_simple_csp_x_le_3_all_solutions() {
        // x in [0,7], x <= 3 -> solutions: {0, 1, 2, 3}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 7));
        csp.add(Sum::from(x.clone()).le(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![0, 1, 2, 3]);
    }

    #[test]
    fn test_simple_csp_x_ge_3_all_solutions() {
        // x in [0,7], x >= 3 -> solutions: {3, 4, 5, 6, 7}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 7));
        csp.add(Sum::from(x.clone()).ge(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_simple_csp_x_eq_3_all_solutions() {
        // x in [0,7], x == 3 -> solutions: {3}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 7));
        csp.add(Sum::from(x.clone()).eq(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3]);
    }

    #[test]
    fn test_offset_domain_all_solutions() {
        // x in [5,10], x <= 7 -> solutions: {5, 6, 7}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(5, 10));
        csp.add(Sum::from(x.clone()).le(7));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![5, 6, 7]);
    }

    #[test]
    fn test_two_vars_sum_all_solutions() {
        // x in [0,3], y in [0,3], x + y <= 4
        // solutions: all (x,y) where x+y <= 4
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 3));
        let y = csp.int_var("y", Domain::range(0, 3));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.le(4));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);

        // Expected: all (x,y) with x in [0,3], y in [0,3], x+y <= 4
        let expected: HashSet<(i32, i32)> = (0..=3)
            .flat_map(|x| (0..=3).map(move |y| (x, y)))
            .filter(|(x, y)| x + y <= 4)
            .collect();

        let actual: HashSet<(i32, i32)> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_two_vars_sum_ge_all_solutions() {
        // x in [0,3], y in [0,3], x + y >= 4
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 3));
        let y = csp.int_var("y", Domain::range(0, 3));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.ge(4));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);

        // Expected: all (x,y) with x in [0,3], y in [0,3], x+y >= 4
        let expected: HashSet<(i32, i32)> = (0..=3)
            .flat_map(|x| (0..=3).map(move |y| (x, y)))
            .filter(|(x, y)| x + y >= 4)
            .collect();

        let actual: HashSet<(i32, i32)> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_unsat() {
        // x in [0,3], x >= 5 (UNSAT)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 3));
        csp.add(Sum::from(x.clone()).ge(5));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        assert!(!SatSolverBackend::solve(encoder.backend_mut()));
    }

    #[test]
    fn test_bool_constraint_all_solutions() {
        // p AND (NOT p OR q) -> p=true, q=true (unique solution)
        let mut csp = CSP::new();
        let p = csp.bool_var("p");
        let q = csp.bool_var("q");

        csp.add(Constraint::Lit(Literal::pos(p.clone())));
        csp.add(Constraint::or(vec![
            Constraint::Lit(Literal::neg(p.clone())),
            Constraint::Lit(Literal::pos(q.clone())),
        ]));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        // Enumerate all boolean solutions
        let mut solutions = Vec::new();
        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let p_val = assignment.get_bool(&p).unwrap();
            let q_val = assignment.get_bool(&q).unwrap();
            solutions.push((p_val, q_val));

            // Block current solution
            let p_code = *encoder.state.bool_code_map.get(&p).unwrap();
            let q_code = *encoder.state.bool_code_map.get(&q).unwrap();
            let block_clause = vec![
                if p_val { -p_code } else { p_code },
                if q_val { -q_code } else { q_code },
            ];
            encoder.backend.borrow_mut().add_clause(&block_clause);
        }

        // p=true is forced, so q can be true or false? No, p=true AND (NOT p OR q) forces q=true
        // So only solution is (true, true)
        assert_eq!(solutions, vec![(true, true)]);
    }

    #[test]
    fn test_ne_constraint_all_solutions() {
        // x in [0,7], x != 3 -> solutions: {0, 1, 2, 4, 5, 6, 7}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 7));
        csp.add(Sum::from(x.clone()).ne(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![0, 1, 2, 4, 5, 6, 7]);
    }

    #[test]
    fn test_domain_no_constraint_all_solutions() {
        // x in [0,7], no constraint -> all 8 values
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 7));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![0, 1, 2, 3, 4, 5, 6, 7]);
    }

    #[test]
    fn test_small_domain_all_solutions() {
        // x in [1,3], no constraint -> {1, 2, 3}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3]);
    }

    #[test]
    fn test_two_vars_eq_all_solutions() {
        // x in [0,2], y in [0,2], x + y == 2
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 2));
        let y = csp.int_var("y", Domain::range(0, 2));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.eq(2));

        let solver = CaDiCaLSolver::new();
        let mut encoder = LogEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);

        // Expected: (0,2), (1,1), (2,0)
        let expected: HashSet<(i32, i32)> = [(0, 2), (1, 1), (2, 0)].into_iter().collect();
        let actual: HashSet<(i32, i32)> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }
}
