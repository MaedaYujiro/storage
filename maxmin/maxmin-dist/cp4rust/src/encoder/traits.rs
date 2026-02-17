// Encoder traits and common types
// Corresponds to Scarab's abstract class Encoder

use std::collections::HashMap;
use crate::{Bool, Var, Constraint};
use crate::domain::Domain;

/// TRUE literal constant (always true)
/// Scarab: TrueLit = Integer.MAX_VALUE
pub const TRUE_LIT: i32 = i32::MAX;

/// FALSE literal constant (always false)
/// Scarab: FalseLit = -Integer.MAX_VALUE
pub const FALSE_LIT: i32 = i32::MIN + 1;  // Use MIN+1 to avoid overflow when negating

/// SAT solver backend trait
/// Provides low-level access to SAT solver operations
pub trait SatSolverBackend {
    /// Add a clause to the solver
    fn add_clause(&mut self, clause: &[i32]);

    /// Reserve space for variables
    fn reserve_vars(&mut self, count: i32);

    /// Get the next free variable ID
    fn next_var_id(&mut self) -> i32;

    /// Get the value of a variable in the model (after solving)
    fn model_value(&mut self, var: i32) -> bool;

    /// Reset the solver
    fn reset(&mut self);

    /// Solve and return true if satisfiable
    fn solve(&mut self) -> bool;
}

/// Encoder state: common fields shared by all encoders
/// Scarab: fields of abstract class Encoder
pub struct EncoderState {
    /// Total number of SAT variables
    /// Scarab: satVariableCount
    pub sat_variable_count: i32,

    /// Total number of SAT clauses
    /// Scarab: satClauseCount
    pub sat_clause_count: i32,

    /// Integer variable -> DIMACS code mapping
    /// Scarab: varCodeMap: Map[Var, Int]
    pub var_code_map: HashMap<Var, i32>,

    /// Boolean variable -> DIMACS code mapping
    /// Scarab: boolCodeMap: Map[Bool, Int]
    pub bool_code_map: HashMap<Bool, i32>,

    /// Auxiliary boolean variable counter
    aux_bool_count: usize,
}

impl EncoderState {
    pub fn new() -> Self {
        Self {
            sat_variable_count: 0,
            sat_clause_count: 0,
            var_code_map: HashMap::new(),
            bool_code_map: HashMap::new(),
            aux_bool_count: 0,
        }
    }

    /// Generate a new auxiliary boolean variable
    pub fn new_aux_bool(&mut self) -> Bool {
        let name = format!("_aux_{}", self.aux_bool_count);
        self.aux_bool_count += 1;
        Bool::new(&name)
    }
}

impl Default for EncoderState {
    fn default() -> Self {
        Self::new()
    }
}

/// Encoder trait: abstract encoder for CSP to SAT conversion
/// Corresponds to Scarab's abstract class Encoder
pub trait Encoder {
    /// Associated SAT solver backend type
    type Backend: SatSolverBackend;

    // === Abstract methods (must be implemented by concrete encoders) ===

    /// Number of SAT variables needed to encode a variable
    /// Scarab: satVariablesSize(x: Var): Int
    fn sat_variables_size(&self, var: &Var, domain: &Domain) -> i32;

    /// Encode an integer variable (generate axiom clauses)
    /// Scarab: encode(x: Var): Seq[Seq[Int]]
    fn encode_var(&self, var: &Var) -> Vec<Vec<i32>>;

    /// Encode a literal with accumulated clause literals
    /// Scarab: encode(lit: Literal, clause0: Seq[Int]): Seq[Seq[Int]]
    fn encode_literal(&self, lit: &Constraint, clause0: &[i32]) -> Vec<Vec<i32>>;

    /// Add and encode a constraint
    /// Scarab: add(c: Constraint): Unit
    fn add_constraint(&mut self, c: &Constraint);

    /// Decode an integer variable value from the SAT solution
    /// Scarab: decode(x: Var): Int
    fn decode_var(&mut self, var: &Var) -> i32;

    // === Methods with access to state ===

    /// Get the encoder state
    fn state(&self) -> &EncoderState;

    /// Get mutable encoder state
    fn state_mut(&mut self) -> &mut EncoderState;

    /// Get the SAT backend
    fn backend(&self) -> &Self::Backend;

    /// Get mutable SAT backend
    fn backend_mut(&mut self) -> &mut Self::Backend;

    // === Concrete methods (default implementations) ===

    /// Get the DIMACS code for an integer variable
    /// Scarab: code(x: Var): Int
    fn var_code(&self, var: &Var) -> Option<i32> {
        self.state().var_code_map.get(var).copied()
    }

    /// Get the DIMACS code for a boolean variable
    /// Scarab: code(p: Bool): Int
    fn bool_code(&self, b: &Bool) -> Option<i32> {
        self.state().bool_code_map.get(b).copied()
    }

    /// Get the total number of SAT variables
    fn sat_variable_count(&self) -> i32 {
        self.state().sat_variable_count
    }

    /// Get the total number of SAT clauses
    fn sat_clause_count(&self) -> i32 {
        self.state().sat_clause_count
    }
}

/// Floor division: floor(b / a)
/// Scarab: floorDiv(b: Int, a: Int): Int
pub fn floor_div(b: i32, a: i32) -> i32 {
    if a > 0 {
        if b >= 0 { b / a } else { (b - a + 1) / a }
    } else {
        if b >= 0 { (b - a - 1) / a } else { b / a }
    }
}

/// Ceiling division: ceil(b / a)
/// Scarab: ceilDiv(b: Int, a: Int): Int
pub fn ceil_div(b: i32, a: i32) -> i32 {
    if a > 0 {
        if b >= 0 { (b + a - 1) / a } else { b / a }
    } else {
        if b >= 0 { b / a } else { (b + a + 1) / a }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_encoder_state_new() {
        let state = EncoderState::new();
        assert_eq!(state.sat_variable_count, 0);
        assert_eq!(state.sat_clause_count, 0);
        assert!(state.var_code_map.is_empty());
        assert!(state.bool_code_map.is_empty());
    }

    #[test]
    fn test_encoder_state_new_aux_bool() {
        let mut state = EncoderState::new();
        let b1 = state.new_aux_bool();
        let b2 = state.new_aux_bool();
        let b3 = state.new_aux_bool();

        assert_eq!(b1.name(), "_aux_0");
        assert_eq!(b2.name(), "_aux_1");
        assert_eq!(b3.name(), "_aux_2");
    }

    #[test]
    fn test_floor_div_positive() {
        // Positive divisor
        assert_eq!(floor_div(7, 3), 2);   // 7 / 3 = 2.33... -> 2
        assert_eq!(floor_div(6, 3), 2);   // 6 / 3 = 2
        assert_eq!(floor_div(-7, 3), -3); // -7 / 3 = -2.33... -> -3
        assert_eq!(floor_div(-6, 3), -2); // -6 / 3 = -2
    }

    #[test]
    fn test_floor_div_negative() {
        // Negative divisor
        assert_eq!(floor_div(7, -3), -3);  // 7 / -3 = -2.33... -> -3
        assert_eq!(floor_div(-7, -3), 2);  // -7 / -3 = 2.33... -> 2
    }

    #[test]
    fn test_ceil_div_positive() {
        // Positive divisor
        assert_eq!(ceil_div(7, 3), 3);    // 7 / 3 = 2.33... -> 3
        assert_eq!(ceil_div(6, 3), 2);    // 6 / 3 = 2
        assert_eq!(ceil_div(-7, 3), -2);  // -7 / 3 = -2.33... -> -2
        assert_eq!(ceil_div(-6, 3), -2);  // -6 / 3 = -2
    }

    #[test]
    fn test_ceil_div_negative() {
        // Negative divisor
        assert_eq!(ceil_div(7, -3), -2);   // 7 / -3 = -2.33... -> -2
        assert_eq!(ceil_div(-7, -3), 3);   // -7 / -3 = 2.33... -> 3
    }

    #[test]
    fn test_constants() {
        assert_eq!(TRUE_LIT, i32::MAX);
        assert_eq!(FALSE_LIT, i32::MIN + 1);
        // Ensure FALSE_LIT can be negated without overflow
        assert_eq!(-FALSE_LIT, -(i32::MIN + 1));
    }
}
