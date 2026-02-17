// OrderEncoderLe: Order encoding (x <= d) for CSP to SAT conversion
// Corresponds to Scarab's OrderEncoder class

use crate::{Var, Literal, Constraint, Assignment};
use crate::domain::Domain;
use crate::csp::CSP;
use super::{
    Encoder, SatSolverBackend, EncoderState,
    TRUE_LIT, FALSE_LIT, floor_div, ceil_div,
    Simplifier,
};

/// OrderEncoderLe: encodes CSP to SAT using order encoding (x <= d)
/// Scarab: class OrderEncoder(csp: CSP, satSolver: SatSolver) extends Encoder
pub struct OrderEncoderLe<'a, B: SatSolverBackend> {
    csp: &'a CSP,
    backend: B,
    state: EncoderState,
}

impl<'a, B: SatSolverBackend> OrderEncoderLe<'a, B> {
    pub fn new(csp: &'a CSP, backend: B) -> Self {
        Self {
            csp,
            backend,
            state: EncoderState::new(),
        }
    }

    /// Get the SAT literal for (x <= b)
    /// Scarab: le(x: Var, b: Int): Int
    pub fn le(&self, x: &Var, b: i32) -> i32 {
        let domain = self.csp.domain(x).expect("variable not found");
        if b < domain.lb() {
            FALSE_LIT
        } else if b >= domain.ub() {
            TRUE_LIT
        } else {
            let code = self.state.var_code_map.get(x).expect("variable not encoded");
            let pos = domain.pos(b).expect("value not in domain");
            code + pos as i32
        }
    }

    /// Get the SAT literal for (a * x <= b)
    /// Scarab: le(a: Int, x: Var, b: Int): Int
    pub fn le_ax(&self, a: i32, x: &Var, b: i32) -> i32 {
        if a > 0 {
            self.le(x, floor_div(b, a))
        } else if a < 0 {
            -self.le(x, ceil_div(b, a) - 1)
        } else {
            // a == 0: 0 <= b
            if b >= 0 { TRUE_LIT } else { FALSE_LIT }
        }
    }

    /// Lower bound of variable x
    fn lb(&self, x: &Var) -> i32 {
        self.csp.domain(x).map(|d| d.lb()).unwrap_or(0)
    }

    /// Upper bound of variable x
    fn ub(&self, x: &Var) -> i32 {
        self.csp.domain(x).map(|d| d.ub()).unwrap_or(0)
    }

    /// Lower bound of a*x
    fn lb_ax(&self, a: i32, x: &Var) -> i32 {
        if a > 0 { a * self.lb(x) } else { a * self.ub(x) }
    }

    /// Upper bound of a*x
    fn ub_ax(&self, a: i32, x: &Var) -> i32 {
        if a > 0 { a * self.ub(x) } else { a * self.lb(x) }
    }

    /// Lower bound of sum of terms
    fn lb_sum(&self, axs: &[(i32, Var)]) -> i32 {
        axs.iter().map(|(a, x)| self.lb_ax(*a, x)).sum()
    }

    /// Get domain values in range [lb, ub]
    fn range_values(&self, domain: &Domain, lb: i32, ub: i32) -> Vec<i32> {
        if domain.is_contiguous() {
            (lb.max(domain.lb())..=ub.min(domain.ub())).collect()
        } else {
            domain.values().iter()
                .filter(|&&v| v >= lb && v <= ub)
                .copied()
                .collect()
        }
    }

    /// Encode linear constraint: sum(ai * xi) <= c
    /// Scarab: encodeLe(axs: Seq[(Int, Var)], c: Int, clause0: Seq[Int]): Seq[Seq[Int]]
    pub fn encode_le(&self, axs: &[(i32, Var)], c: i32, clause0: &[i32]) -> Vec<Vec<i32>> {
        match axs {
            [] => {
                if c >= 0 {
                    vec![]  // Always true
                } else {
                    vec![clause0.to_vec()]  // Output clause
                }
            }
            [(a, x)] => {
                let lit = self.le_ax(*a, x, c);
                if lit == TRUE_LIT {
                    vec![]
                } else if lit == FALSE_LIT {
                    vec![clause0.to_vec()]
                } else {
                    let mut clause = clause0.to_vec();
                    clause.push(lit);
                    vec![clause]
                }
            }
            [(a, x), rest @ ..] => {
                if *a > 0 {
                    let ub0 = floor_div(c - self.lb_sum(rest), *a);
                    let lb_x = self.lb(x);
                    let ub_x = self.ub(x).min(ub0);

                    if lb_x > ub_x {
                        return vec![clause0.to_vec()];
                    }

                    let domain = self.csp.domain(x).unwrap();
                    let mut clauses = Vec::new();

                    for b in self.range_values(domain, lb_x, ub_x) {
                        let lit = self.le(x, b - 1);
                        if lit != TRUE_LIT {
                            let mut new_clause0 = clause0.to_vec();
                            new_clause0.push(lit);
                            clauses.extend(self.encode_le(rest, c - a * b, &new_clause0));
                        }
                    }

                    if self.ub(x) > ub0 {
                        let mut clause = clause0.to_vec();
                        clause.push(self.le(x, ub0));
                        clauses.push(clause);
                    }

                    clauses
                } else {
                    // a < 0
                    let lb0 = floor_div(c - self.lb_sum(rest), *a);
                    let lb_x = self.lb(x).max(lb0);
                    let ub_x = self.ub(x);

                    if lb_x > ub_x {
                        return vec![clause0.to_vec()];
                    }

                    let domain = self.csp.domain(x).unwrap();
                    let mut clauses = Vec::new();

                    for b in self.range_values(domain, lb_x, ub_x) {
                        let lit = -self.le(x, b);
                        if lit != TRUE_LIT {
                            let mut new_clause0 = clause0.to_vec();
                            new_clause0.push(lit);
                            clauses.extend(self.encode_le(rest, c - a * b, &new_clause0));
                        }
                    }

                    if self.lb(x) < lb0 {
                        let mut clause = clause0.to_vec();
                        clause.push(-self.le(x, lb0 - 1));
                        clauses.push(clause);
                    }

                    clauses
                }
            }
        }
    }

    /// Convert constraint to LeZero form
    /// Scarab: toLeZero(c: Constraint): Constraint
    pub fn to_le_zero(&self, c: &Constraint) -> Constraint {
        match c {
            Constraint::EqZero(sum) => {
                // x == 0 <=> x <= 0 && -x <= 0
                Constraint::and(vec![
                    Constraint::LeZero(sum.clone()),
                    Constraint::LeZero(-sum.clone()),
                ])
            }
            Constraint::NeZero(sum) => {
                // x != 0 <=> x <= -1 || -x <= -1
                Constraint::or(vec![
                    Constraint::LeZero(sum.clone() + (-1)),
                    Constraint::LeZero(-sum.clone() + (-1)),
                ])
            }
            Constraint::GeZero(sum) => {
                // x >= 0 <=> -x <= 0
                Constraint::LeZero(-sum.clone())
            }
            Constraint::And(cs) => {
                Constraint::and(cs.iter().map(|ci| self.to_le_zero(ci)).collect())
            }
            Constraint::Or(cs) => {
                Constraint::or(cs.iter().map(|ci| self.to_le_zero(ci)).collect())
            }
            _ => c.clone(),  // Lit, LeZero remain unchanged
        }
    }

    /// Add clause to backend, handling TRUE_LIT and FALSE_LIT
    fn add_clause_internal(&mut self, clause: &[i32]) {
        // Filter out FALSE_LIT
        let clause: Vec<_> = clause.iter()
            .filter(|&&l| l != FALSE_LIT)
            .copied()
            .collect();

        // If TRUE_LIT is present, clause is always true
        if clause.contains(&TRUE_LIT) {
            return;
        }

        // Empty clause means contradiction
        if clause.is_empty() {
            self.backend.add_clause(&[1]);
            self.backend.add_clause(&[-1]);
            self.state.sat_clause_count += 2;
        } else {
            self.backend.add_clause(&clause);
            self.state.sat_clause_count += 1;
        }
    }

    /// Encode a clause of literals
    fn encode_clause(&self, lits: &[Constraint]) -> Vec<Vec<i32>> {
        if lits.len() == 1 {
            self.encode_literal(&lits[0], &[])
        } else {
            // Multiple literals in clause
            // For now, encode each literal and combine
            // TODO: optimize for simple clauses
            let mut result = Vec::new();
            for lit in lits {
                result.extend(self.encode_literal(lit, &[]));
            }
            result
        }
    }

    /// Encode the entire CSP
    /// Scarab: encodeCSP(): Unit
    pub fn encode_csp(&mut self) {
        // 1. Assign codes to integer variables
        for (var, domain) in self.csp.int_vars() {
            self.state.var_code_map.insert(var.clone(), self.state.sat_variable_count + 1);
            self.state.sat_variable_count += self.sat_variables_size(var, domain);
        }

        // 2. Assign codes to boolean variables
        for b in self.csp.bool_vars() {
            self.state.bool_code_map.insert(b.clone(), self.state.sat_variable_count + 1);
            self.state.sat_variable_count += 1;
        }

        // 3. Reserve variables in backend
        self.backend.reserve_vars(self.state.sat_variable_count);

        // 4. Encode axiom clauses for integer variables
        for (var, _) in self.csp.int_vars() {
            let axiom_clauses = self.encode_var(var);
            for clause in axiom_clauses {
                self.add_clause_internal(&clause);
            }
        }

        // 5. Encode constraints
        let constraints: Vec<_> = self.csp.constraints().to_vec();
        for c in constraints {
            self.add_constraint(&c);
        }
    }

    /// Decode the SAT solution to an Assignment
    pub fn decode(&mut self) -> Assignment {
        let mut assignment = Assignment::new();

        // Decode integer variables
        let int_vars: Vec<_> = self.csp.int_vars().iter().map(|(v, _)| v.clone()).collect();
        for var in int_vars {
            let value = self.decode_var(&var);
            assignment.set_int(var, value);
        }

        // Decode boolean variables
        let bool_vars: Vec<_> = self.csp.bool_vars().to_vec();
        for b in bool_vars {
            if let Some(&code) = self.state.bool_code_map.get(&b) {
                let value = self.backend.model_value(code);
                assignment.set_bool(b, value);
            }
        }

        assignment
    }

    /// Solve the encoded CSP
    /// DEPRECATED: Use CspSolver::find() instead
    #[deprecated(since = "0.2.0", note = "Use CspSolver::find() instead")]
    pub fn solve(&mut self) -> bool {
        self.backend.solve()
    }

    /// Access the CSP
    pub fn csp(&self) -> &CSP {
        self.csp
    }
}

impl<'a, B: SatSolverBackend> Encoder for OrderEncoderLe<'a, B> {
    type Backend = B;

    fn sat_variables_size(&self, _var: &Var, domain: &Domain) -> i32 {
        // Order encoding: need (ub - lb) SAT variables for (x <= lb), ..., (x <= ub-1)
        if domain.is_contiguous() {
            domain.ub() - domain.lb()
        } else {
            (domain.size() - 1) as i32
        }
    }

    fn encode_var(&self, var: &Var) -> Vec<Vec<i32>> {
        let domain = self.csp.domain(var).expect("variable not found");

        if domain.is_contiguous() {
            // Axiom clauses: (x <= b-1) => (x <= b), i.e., !(x <= b-1) | (x <= b)
            (self.lb(var) + 1..=self.ub(var) - 1)
                .map(|b| vec![-self.le(var, b - 1), self.le(var, b)])
                .collect()
        } else {
            // Non-contiguous domain
            let values: Vec<_> = domain.values().to_vec();
            (1..=values.len() - 2)
                .map(|i| vec![-self.le(var, values[i - 1]), self.le(var, values[i])])
                .collect()
        }
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
                // Sort variables by domain size (ascending), then by coefficient absolute value (descending)
                let mut axs: Vec<_> = sum.terms().iter()
                    .map(|(a, v)| (*a, v.clone()))
                    .collect();
                axs.sort_by(|(a1, v1), (a2, v2)| {
                    let d1 = self.csp.domain(v1).map(|d| d.size()).unwrap_or(0);
                    let d2 = self.csp.domain(v2).map(|d| d.size()).unwrap_or(0);
                    if d1 == d2 {
                        a2.abs().cmp(&a1.abs())
                    } else {
                        d1.cmp(&d2)
                    }
                });
                self.encode_le(&axs, -sum.b(), clause0)
            }
            _ => panic!("OrderEncoderLe: unexpected constraint type {:?}", lit),
        }
    }

    fn add_constraint(&mut self, c: &Constraint) {
        let c = self.to_le_zero(c);
        let mut simplifier = Simplifier::new(self);
        let simplified = simplifier.simplify(&c);

        for lits in simplified {
            if lits.is_empty() {
                continue;
            }

            // Encode each literal
            if lits.len() == 1 {
                let clauses = self.encode_literal(&lits[0], &[]);
                for clause in clauses {
                    self.add_clause_internal(&clause);
                }
            } else {
                // Multiple literals in a clause - need to handle as disjunction
                // For simple bool literals, combine into one clause
                let mut all_simple_bool = true;
                let mut sat_lits = Vec::new();

                for lit in &lits {
                    if let Constraint::Lit(l) = lit {
                        let code = match l {
                            Literal::Pos(b) => {
                                *self.state.bool_code_map.get(b).unwrap_or(&0)
                            }
                            Literal::Neg(b) => {
                                -*self.state.bool_code_map.get(b).unwrap_or(&0)
                            }
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
                    // Complex clause - encode separately
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
        let domain = self.csp.domain(var).expect("variable not found").clone();

        if domain.is_contiguous() {
            for b in domain.lb()..domain.ub() {
                let lit = self.le(var, b);
                if lit != FALSE_LIT && lit != TRUE_LIT && self.backend.model_value(lit) {
                    return b;
                }
            }
            domain.ub()
        } else {
            let values: Vec<_> = domain.values().to_vec();
            for &v in values.iter().take(values.len() - 1) {
                let lit = self.le(var, v);
                if lit != FALSE_LIT && lit != TRUE_LIT && self.backend.model_value(lit) {
                    return v;
                }
            }
            *values.last().unwrap()
        }
    }

    fn state(&self) -> &EncoderState {
        &self.state
    }

    fn state_mut(&mut self) -> &mut EncoderState {
        &mut self.state
    }

    fn backend(&self) -> &Self::Backend {
        &self.backend
    }

    fn backend_mut(&mut self) -> &mut Self::Backend {
        &mut self.backend
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CaDiCaLSolver;

    #[test]
    fn test_order_encoder_new() {
        let csp = CSP::new();
        let solver = CaDiCaLSolver::new();
        let encoder = OrderEncoderLe::new(&csp, solver);
        assert_eq!(encoder.state.sat_variable_count, 0);
    }

    #[test]
    fn test_sat_variables_size_contiguous() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));  // {1,2,3,4,5}
        let solver = CaDiCaLSolver::new();
        let encoder = OrderEncoderLe::new(&csp, solver);

        let domain = csp.domain(&x).unwrap();
        // Order encoding: need 4 SAT vars for (x<=1), (x<=2), (x<=3), (x<=4)
        assert_eq!(encoder.sat_variables_size(&x, domain), 4);
    }

    #[test]
    fn test_sat_variables_size_non_contiguous() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::from(vec![1, 3, 5, 7]));
        let solver = CaDiCaLSolver::new();
        let encoder = OrderEncoderLe::new(&csp, solver);

        let domain = csp.domain(&x).unwrap();
        // 4 values -> 3 SAT variables
        assert_eq!(encoder.sat_variables_size(&x, domain), 3);
    }

    #[test]
    fn test_le_boundary() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);

        // Assign code to x
        encoder.state.var_code_map.insert(x.clone(), 1);

        // x <= 0 should be FALSE (below lb)
        assert_eq!(encoder.le(&x, 0), FALSE_LIT);

        // x <= 5 should be TRUE (at or above ub)
        assert_eq!(encoder.le(&x, 5), TRUE_LIT);
        assert_eq!(encoder.le(&x, 10), TRUE_LIT);

        // x <= 1, x <= 2, x <= 3, x <= 4 should return valid codes
        assert_eq!(encoder.le(&x, 1), 1);  // code + pos(1) = 1 + 0 = 1
        assert_eq!(encoder.le(&x, 2), 2);  // code + pos(2) = 1 + 1 = 2
        assert_eq!(encoder.le(&x, 3), 3);
        assert_eq!(encoder.le(&x, 4), 4);
    }

    #[test]
    fn test_encode_var_contiguous() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 4));  // {1,2,3,4}
        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);

        // Assign code to x (starting at 1)
        encoder.state.var_code_map.insert(x.clone(), 1);

        let clauses = encoder.encode_var(&x);
        // Should have axiom clauses: !(x<=1) | (x<=2), !(x<=2) | (x<=3)
        // i.e., [-1, 2], [-2, 3]
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0], vec![-1, 2]);
        assert_eq!(clauses[1], vec![-2, 3]);
    }

    #[test]
    fn test_to_le_zero() {
        let csp = CSP::new();
        let solver = CaDiCaLSolver::new();
        let encoder = OrderEncoderLe::new(&csp, solver);

        use crate::expr::Sum;

        let x = Var::new("x");
        let s = Sum::from(x);

        // GeZero -> LeZero
        let ge = s.clone().ge(0);
        let converted = encoder.to_le_zero(&ge);
        assert!(matches!(converted, Constraint::LeZero(_)));

        // EqZero -> And(LeZero, LeZero)
        let eq = s.clone().eq(0);
        let converted = encoder.to_le_zero(&eq);
        assert!(matches!(converted, Constraint::And(_)));

        // NeZero -> Or(LeZero, LeZero)
        let ne = s.ne(0);
        let converted = encoder.to_le_zero(&ne);
        assert!(matches!(converted, Constraint::Or(_)));
    }

    #[test]
    fn test_floor_div() {
        assert_eq!(floor_div(7, 3), 2);
        assert_eq!(floor_div(-7, 3), -3);
        assert_eq!(floor_div(6, 3), 2);
        assert_eq!(floor_div(-6, 3), -2);
    }

    #[test]
    fn test_ceil_div() {
        assert_eq!(ceil_div(7, 3), 3);
        assert_eq!(ceil_div(-7, 3), -2);
        assert_eq!(ceil_div(6, 3), 2);
    }

    // Integration tests with full solution enumeration

    use std::collections::HashSet;

    /// Helper: enumerate all solutions for a single integer variable
    fn enumerate_all_int_solutions(
        encoder: &mut OrderEncoderLe<CaDiCaLSolver>,
        var: &Var,
    ) -> Vec<i32> {
        let mut solutions = Vec::new();
        let domain = encoder.csp().domain(var).unwrap().clone();
        let values: Vec<i32> = domain.values().to_vec();

        while encoder.solve() {
            let assignment = encoder.decode();
            let val = assignment.get_int(var).unwrap();
            solutions.push(val);

            // Block current solution using order encoding
            // For non-contiguous domains, we need to use actual domain values
            // Find the position of val in the domain, then use prev/current values
            let pos = values.iter().position(|&v| v == val).unwrap();
            let mut block_clause = Vec::new();

            // x < val: use le(prev_val) where prev_val is the domain value before val
            if pos > 0 {
                let prev_val = values[pos - 1];
                let lit_le = encoder.le(var, prev_val);
                if lit_le != TRUE_LIT && lit_le != FALSE_LIT {
                    block_clause.push(lit_le);
                }
            }

            // x > val: use !le(val)
            let lit_gt = -encoder.le(var, val);
            if lit_gt != TRUE_LIT && lit_gt != FALSE_LIT {
                block_clause.push(lit_gt);
            }

            if !block_clause.is_empty() {
                encoder.backend_mut().add_clause(&block_clause);
            } else {
                break;
            }
        }

        solutions.sort();
        solutions
    }

    /// Helper: add blocking literals for a variable to a clause
    fn add_blocking_lits(
        encoder: &OrderEncoderLe<CaDiCaLSolver>,
        var: &Var,
        val: i32,
        block_clause: &mut Vec<i32>,
    ) {
        let domain = encoder.csp().domain(var).unwrap();
        let values: Vec<i32> = domain.values().to_vec();
        let pos = values.iter().position(|&v| v == val).unwrap();

        // x < val: use le(prev_val)
        if pos > 0 {
            let prev_val = values[pos - 1];
            let lit_le = encoder.le(var, prev_val);
            if lit_le != TRUE_LIT && lit_le != FALSE_LIT {
                block_clause.push(lit_le);
            }
        }

        // x > val: use !le(val)
        let lit_gt = -encoder.le(var, val);
        if lit_gt != TRUE_LIT && lit_gt != FALSE_LIT {
            block_clause.push(lit_gt);
        }
    }

    /// Helper: enumerate all solutions for two integer variables
    fn enumerate_all_two_int_solutions(
        encoder: &mut OrderEncoderLe<CaDiCaLSolver>,
        var1: &Var,
        var2: &Var,
    ) -> Vec<(i32, i32)> {
        let mut solutions = Vec::new();

        while encoder.solve() {
            let assignment = encoder.decode();
            let val1 = assignment.get_int(var1).unwrap();
            let val2 = assignment.get_int(var2).unwrap();
            solutions.push((val1, val2));

            // Block current solution
            let mut block_clause = Vec::new();
            add_blocking_lits(encoder, var1, val1, &mut block_clause);
            add_blocking_lits(encoder, var2, val2, &mut block_clause);

            if !block_clause.is_empty() {
                encoder.backend_mut().add_clause(&block_clause);
            } else {
                break;
            }
        }

        solutions.sort();
        solutions
    }

    /// Helper: enumerate all solutions for three integer variables
    fn enumerate_all_three_int_solutions(
        encoder: &mut OrderEncoderLe<CaDiCaLSolver>,
        var1: &Var,
        var2: &Var,
        var3: &Var,
    ) -> Vec<(i32, i32, i32)> {
        let mut solutions = Vec::new();

        while encoder.solve() {
            let assignment = encoder.decode();
            let val1 = assignment.get_int(var1).unwrap();
            let val2 = assignment.get_int(var2).unwrap();
            let val3 = assignment.get_int(var3).unwrap();
            solutions.push((val1, val2, val3));

            // Block current solution
            let mut block_clause = Vec::new();
            add_blocking_lits(encoder, var1, val1, &mut block_clause);
            add_blocking_lits(encoder, var2, val2, &mut block_clause);
            add_blocking_lits(encoder, var3, val3, &mut block_clause);

            if !block_clause.is_empty() {
                encoder.backend_mut().add_clause(&block_clause);
            } else {
                break;
            }
        }

        solutions.sort();
        solutions
    }

    #[test]
    fn test_simple_csp_x_le_5_all_solutions() {
        // x in [1,10], x <= 5 -> solutions: {1, 2, 3, 4, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));

        use crate::expr::Sum;
        csp.add(Sum::from(x.clone()).le(5));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_simple_csp_x_ge_3_all_solutions() {
        // x in [1,5], x >= 3 -> solutions: {3, 4, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));

        use crate::expr::Sum;
        csp.add(Sum::from(x.clone()).ge(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 4, 5]);
    }

    #[test]
    fn test_simple_csp_x_eq_3_all_solutions() {
        // x in [1,5], x == 3 -> solutions: {3}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));

        use crate::expr::Sum;
        csp.add(Sum::from(x.clone()).eq(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3]);
    }

    #[test]
    fn test_two_vars_sum_eq_all_solutions() {
        // x in [1,5], y in [1,5], x + y == 6
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        let y = csp.int_var("y", Domain::range(1, 5));

        use crate::expr::Sum;
        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.eq(6));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);

        // Expected: (1,5), (2,4), (3,3), (4,2), (5,1)
        let expected: HashSet<(i32, i32)> = [(1, 5), (2, 4), (3, 3), (4, 2), (5, 1)]
            .into_iter()
            .collect();
        let actual: HashSet<(i32, i32)> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_two_vars_sum_le_all_solutions() {
        // x in [0,2], y in [0,2], x + y <= 2
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 2));
        let y = csp.int_var("y", Domain::range(0, 2));

        use crate::expr::Sum;
        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.le(2));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);

        let expected: HashSet<(i32, i32)> = (0..=2)
            .flat_map(|x| (0..=2).map(move |y| (x, y)))
            .filter(|(x, y)| x + y <= 2)
            .collect();
        let actual: HashSet<(i32, i32)> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_unsat_csp() {
        // CSP: x in [1,3], x >= 5 (UNSAT)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));

        use crate::expr::Sum;
        csp.add(Sum::from(x.clone()).ge(5));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        assert!(!encoder.solve());
    }

    #[test]
    fn test_bool_only_constraint_all_solutions() {
        // p AND (!p OR q) -> p=true, q=true (unique solution)
        let mut csp = CSP::new();
        let p = csp.bool_var("p");
        let q = csp.bool_var("q");

        csp.add(Constraint::Lit(Literal::pos(p.clone())));
        csp.add(Constraint::or(vec![
            Constraint::Lit(Literal::neg(p.clone())),
            Constraint::Lit(Literal::pos(q.clone())),
        ]));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let mut solutions = Vec::new();
        while encoder.solve() {
            let assignment = encoder.decode();
            let p_val = assignment.get_bool(&p).unwrap();
            let q_val = assignment.get_bool(&q).unwrap();
            solutions.push((p_val, q_val));

            // Block
            let p_code = *encoder.state().bool_code_map.get(&p).unwrap();
            let q_code = *encoder.state().bool_code_map.get(&q).unwrap();
            encoder.backend_mut().add_clause(&[
                if p_val { -p_code } else { p_code },
                if q_val { -q_code } else { q_code },
            ]);
        }

        assert_eq!(solutions, vec![(true, true)]);
    }

    #[test]
    fn test_bool_and_int_all_solutions() {
        // p=true, x in [1,3], x <= 2 -> x in {1, 2}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        let p = csp.bool_var("p");

        use crate::expr::Sum;
        csp.add(Constraint::Lit(Literal::pos(p.clone())));
        csp.add(Sum::from(x.clone()).le(2));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2]);
    }

    #[test]
    fn test_non_contiguous_domain_all_solutions() {
        // x in {1, 3, 5}, x >= 2 -> solutions: {3, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::from(vec![1, 3, 5]));

        use crate::expr::Sum;
        csp.add(Sum::from(x.clone()).ge(2));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 5]);
    }

    #[test]
    fn test_negative_coefficient_all_solutions() {
        // x in [1,5], -x <= -3 (i.e., x >= 3) -> solutions: {3, 4, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));

        use crate::expr::Sum;
        let neg_x = -Sum::from(x.clone());
        csp.add(neg_x.le(-3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 4, 5]);
    }

    #[test]
    fn test_three_vars_constraint_all_solutions() {
        // x, y, z in [0,3], x + y + z == 6
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 3));
        let y = csp.int_var("y", Domain::range(0, 3));
        let z = csp.int_var("z", Domain::range(0, 3));

        use crate::expr::Sum;
        let sum = Sum::from(x.clone()) + Sum::from(y.clone()) + Sum::from(z.clone());
        csp.add(sum.eq(6));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_three_int_solutions(&mut encoder, &x, &y, &z);

        // Expected: all (x,y,z) in [0,3]^3 where x+y+z=6
        let expected: HashSet<(i32, i32, i32)> = (0..=3)
            .flat_map(|x| (0..=3).flat_map(move |y| (0..=3).map(move |z| (x, y, z))))
            .filter(|(x, y, z)| x + y + z == 6)
            .collect();
        let actual: HashSet<(i32, i32, i32)> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_domain_no_constraint_all_solutions() {
        // x in [1,4], no constraint -> all 4 values
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 4));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3, 4]);
    }
}
