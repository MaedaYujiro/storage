// DirectEncoder: Direct encoding for CSP to SAT conversion
// Uses x = d variables instead of order encoding

use crate::{Var, Literal, Constraint, Assignment};
use crate::domain::Domain;
use crate::csp::CSP;
use crate::expr::Sum;
use super::{
    Encoder, SatSolverBackend, EncoderState,
    TRUE_LIT, FALSE_LIT,
    Simplifier,
};

/// DirectEncoder: encodes CSP to SAT using direct encoding (x = d)
pub struct DirectEncoder<'a, B: SatSolverBackend> {
    csp: &'a CSP,
    backend: B,
    state: EncoderState,
}

impl<'a, B: SatSolverBackend> DirectEncoder<'a, B> {
    pub fn new(csp: &'a CSP, backend: B) -> Self {
        Self {
            csp,
            backend,
            state: EncoderState::new(),
        }
    }

    /// Get the SAT literal for (x = d)
    /// Returns TRUE_LIT if domain has only one value equal to d
    /// Returns FALSE_LIT if d is not in domain
    pub fn eq_val(&self, x: &Var, d: i32) -> i32 {
        let domain = self.csp.domain(x).expect("variable not found");

        if !domain.contains(d) {
            return FALSE_LIT;
        }

        if domain.size() == 1 {
            return TRUE_LIT;
        }

        let code = self.state.var_code_map.get(x).expect("variable not encoded");
        let pos = domain.pos(d).expect("value not in domain");
        code + pos as i32
    }

    /// Get the SAT literal for (x != d)
    pub fn ne_val(&self, x: &Var, d: i32) -> i32 {
        let lit = self.eq_val(x, d);
        if lit == TRUE_LIT {
            FALSE_LIT
        } else if lit == FALSE_LIT {
            TRUE_LIT
        } else {
            -lit
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

    /// Encode EqZero constraint: sum == 0
    /// For single variable: x + b == 0 => x == -b
    /// For multiple variables: enumerate valid combinations
    fn encode_eq_zero(&self, sum: &Sum, clause0: &[i32]) -> Vec<Vec<i32>> {
        let terms: Vec<_> = sum.terms().iter().map(|(a, v)| (*a, v.clone())).collect();
        let target = -sum.b();  // sum of terms == target

        if terms.is_empty() {
            // No variables: check if b == 0
            if target == 0 {
                return vec![];  // Always true
            } else {
                return vec![clause0.to_vec()];  // Always false
            }
        }

        if terms.len() == 1 {
            // Single variable: a*x == target => x == target/a (if divisible)
            let (a, x) = &terms[0];
            if target % a != 0 {
                return vec![clause0.to_vec()];  // No solution
            }
            let d = target / a;
            let lit = self.eq_val(x, d);
            if lit == TRUE_LIT {
                return vec![];
            } else if lit == FALSE_LIT {
                return vec![clause0.to_vec()];
            } else {
                let mut clause = clause0.to_vec();
                clause.push(lit);
                return vec![clause];
            }
        }

        // Multiple variables: enumerate all valid combinations
        self.encode_sum_eq(&terms, target, clause0)
    }

    /// Encode NeZero constraint: sum != 0
    /// For single variable: x + b != 0 => x != -b
    fn encode_ne_zero(&self, sum: &Sum, clause0: &[i32]) -> Vec<Vec<i32>> {
        let terms: Vec<_> = sum.terms().iter().map(|(a, v)| (*a, v.clone())).collect();
        let target = -sum.b();  // sum of terms != target

        if terms.is_empty() {
            if target != 0 {
                return vec![];  // Always true (0 != target where target != 0)
            } else {
                return vec![clause0.to_vec()];  // Always false (0 != 0)
            }
        }

        if terms.len() == 1 {
            // Single variable: a*x != target => x != target/a (if divisible)
            let (a, x) = &terms[0];
            if target % a != 0 {
                return vec![];  // Always true (no value makes it equal)
            }
            let d = target / a;
            let lit = self.ne_val(x, d);
            if lit == TRUE_LIT {
                return vec![];
            } else if lit == FALSE_LIT {
                return vec![clause0.to_vec()];
            } else {
                let mut clause = clause0.to_vec();
                clause.push(lit);
                return vec![clause];
            }
        }

        // Multiple variables: at least one combination must differ
        // sum != target means NOT(sum == target)
        // Collect all valid combinations and create a clause excluding them
        self.encode_sum_ne(&terms, target, clause0)
    }

    /// Encode sum of terms == target using direct encoding
    /// Creates clauses that enforce exactly one valid combination
    fn encode_sum_eq(&self, terms: &[(i32, Var)], target: i32, clause0: &[i32]) -> Vec<Vec<i32>> {
        // Generate all valid combinations
        let combinations = self.find_combinations(terms, target);

        if combinations.is_empty() {
            return vec![clause0.to_vec()];  // No valid combination
        }

        // At least one valid combination must be true
        // OR of (AND of x_i = d_i for each combination)
        // This requires auxiliary variables for CNF conversion

        // Simple approach: create a clause for each invalid combination
        // But this can be exponential. Instead, use implication chains.

        // For now, use a simpler approach:
        // Create auxiliary variable for each valid combination
        let mut clauses = Vec::new();
        let mut combo_vars = Vec::new();

        for combo in &combinations {
            // Create auxiliary variable for this combination
            let aux = self.state.sat_variable_count + combo_vars.len() as i32 + 1;
            combo_vars.push(aux);

            // aux => (x1 = d1 AND x2 = d2 AND ...)
            // Equivalent to: !aux OR (x1 = d1 AND x2 = d2 AND ...)
            // CNF: (!aux OR x1 = d1) AND (!aux OR x2 = d2) AND ...
            for (i, &d) in combo.iter().enumerate() {
                let lit = self.eq_val(&terms[i].1, d);
                if lit != TRUE_LIT {
                    let mut clause = clause0.to_vec();
                    clause.push(-aux);
                    if lit != FALSE_LIT {
                        clause.push(lit);
                    }
                    clauses.push(clause);
                }
            }

            // (x1 = d1 AND x2 = d2 AND ...) => aux
            // Equivalent to: !x1=d1 OR !x2=d2 OR ... OR aux
            let mut impl_clause = clause0.to_vec();
            for (i, &d) in combo.iter().enumerate() {
                let lit = self.eq_val(&terms[i].1, d);
                if lit == FALSE_LIT {
                    // This combination is impossible, skip the implication
                    impl_clause.clear();
                    break;
                }
                if lit != TRUE_LIT {
                    impl_clause.push(-lit);
                }
            }
            if !impl_clause.is_empty() || combo.iter().enumerate().all(|(i, &d)| {
                self.eq_val(&terms[i].1, d) == TRUE_LIT
            }) {
                impl_clause.push(aux);
                clauses.push(impl_clause);
            }
        }

        // At least one combination must be true: OR of all aux vars
        if !combo_vars.is_empty() {
            let mut alo_clause = clause0.to_vec();
            alo_clause.extend(combo_vars);
            clauses.push(alo_clause);
        }

        clauses
    }

    /// Encode sum of terms != target
    fn encode_sum_ne(&self, terms: &[(i32, Var)], target: i32, clause0: &[i32]) -> Vec<Vec<i32>> {
        // Find all combinations that make sum == target
        let combinations = self.find_combinations(terms, target);

        if combinations.is_empty() {
            return vec![];  // Always true (no combination equals target)
        }

        // For each invalid combination, at least one variable must differ
        // (x1 != d1) OR (x2 != d2) OR ...
        let mut clauses = Vec::new();

        for combo in combinations {
            let mut clause = clause0.to_vec();
            let mut all_true = true;

            for (i, d) in combo.iter().enumerate() {
                let lit = self.ne_val(&terms[i].1, *d);
                if lit == TRUE_LIT {
                    // Clause is satisfied
                    all_true = false;
                    break;
                }
                if lit != FALSE_LIT {
                    clause.push(lit);
                    all_true = false;
                }
            }

            if all_true && clause.len() == clause0.len() {
                // All ne_val returned FALSE_LIT, meaning all eq_val are TRUE_LIT
                // This combination is forced, so constraint is UNSAT
                clauses.push(clause0.to_vec());
                return clauses;
            }

            if clause.len() > clause0.len() {
                clauses.push(clause);
            }
        }

        clauses
    }

    /// Find all value combinations that make sum == target
    fn find_combinations(&self, terms: &[(i32, Var)], target: i32) -> Vec<Vec<i32>> {
        let mut results = Vec::new();
        let mut current = Vec::new();
        self.find_combinations_rec(terms, 0, target, &mut current, &mut results);
        results
    }

    fn find_combinations_rec(
        &self,
        terms: &[(i32, Var)],
        idx: usize,
        remaining: i32,
        current: &mut Vec<i32>,
        results: &mut Vec<Vec<i32>>,
    ) {
        if idx == terms.len() {
            if remaining == 0 {
                results.push(current.clone());
            }
            return;
        }

        let (a, x) = &terms[idx];
        let domain = self.csp.domain(x).unwrap();

        for &d in domain.values() {
            current.push(d);
            self.find_combinations_rec(terms, idx + 1, remaining - a * d, current, results);
            current.pop();
        }
    }

    /// Encode LeZero constraint using direct encoding
    /// sum <= 0: enumerate all valid combinations
    fn encode_le_zero(&self, sum: &Sum, clause0: &[i32]) -> Vec<Vec<i32>> {
        let terms: Vec<_> = sum.terms().iter().map(|(a, v)| (*a, v.clone())).collect();
        let bound = -sum.b();  // sum of terms <= bound

        if terms.is_empty() {
            if bound >= 0 {
                return vec![];
            } else {
                return vec![clause0.to_vec()];
            }
        }

        if terms.len() == 1 {
            // Single variable: a*x <= bound
            let (a, x) = &terms[0];
            let domain = self.csp.domain(x).unwrap();

            // For each invalid value, add clause excluding it
            let mut clauses = Vec::new();
            for &d in domain.values() {
                if a * d > bound {
                    let lit = self.ne_val(x, d);
                    if lit == FALSE_LIT {
                        // This value is forced but violates constraint
                        return vec![clause0.to_vec()];
                    }
                    if lit != TRUE_LIT {
                        let mut c = clause0.to_vec();
                        c.push(lit);
                        clauses.push(c);
                    }
                }
            }
            return clauses;
        }

        // Multiple variables: exclude invalid combinations
        self.encode_sum_le(&terms, bound, clause0)
    }

    /// Encode sum <= bound by excluding invalid combinations
    fn encode_sum_le(&self, terms: &[(i32, Var)], bound: i32, clause0: &[i32]) -> Vec<Vec<i32>> {
        // Find all combinations that violate sum <= bound
        let invalid_combos = self.find_combinations_gt(terms, bound);

        // For each invalid combination, at least one variable must differ
        let mut clauses = Vec::new();

        for combo in invalid_combos {
            let mut clause = clause0.to_vec();
            let mut satisfied = false;

            for (i, d) in combo.iter().enumerate() {
                let lit = self.ne_val(&terms[i].1, *d);
                if lit == TRUE_LIT {
                    satisfied = true;
                    break;
                }
                if lit != FALSE_LIT {
                    clause.push(lit);
                }
            }

            if !satisfied && clause.len() > clause0.len() {
                clauses.push(clause);
            } else if !satisfied && clause.len() == clause0.len() {
                // All values are forced and violate constraint
                return vec![clause0.to_vec()];
            }
        }

        clauses
    }

    /// Find combinations where sum > bound
    fn find_combinations_gt(&self, terms: &[(i32, Var)], bound: i32) -> Vec<Vec<i32>> {
        let mut results = Vec::new();
        let mut current = Vec::new();
        self.find_combinations_gt_rec(terms, 0, 0, bound, &mut current, &mut results);
        results
    }

    fn find_combinations_gt_rec(
        &self,
        terms: &[(i32, Var)],
        idx: usize,
        current_sum: i32,
        bound: i32,
        current: &mut Vec<i32>,
        results: &mut Vec<Vec<i32>>,
    ) {
        if idx == terms.len() {
            if current_sum > bound {
                results.push(current.clone());
            }
            return;
        }

        let (a, x) = &terms[idx];
        let domain = self.csp.domain(x).unwrap();

        for &d in domain.values() {
            current.push(d);
            self.find_combinations_gt_rec(terms, idx + 1, current_sum + a * d, bound, current, results);
            current.pop();
        }
    }

    /// Encode GeZero using LeZero: sum >= 0 <=> -sum <= 0
    fn encode_ge_zero(&self, sum: &Sum, clause0: &[i32]) -> Vec<Vec<i32>> {
        self.encode_le_zero(&(-sum.clone()), clause0)
    }

    /// Add clause to backend, handling TRUE_LIT and FALSE_LIT
    fn add_clause_internal(&mut self, clause: &[i32]) {
        let clause: Vec<_> = clause.iter()
            .filter(|&&l| l != FALSE_LIT)
            .copied()
            .collect();

        if clause.contains(&TRUE_LIT) {
            return;
        }

        if clause.is_empty() {
            self.backend.add_clause(&[1]);
            self.backend.add_clause(&[-1]);
            self.state.sat_clause_count += 2;
        } else {
            self.backend.add_clause(&clause);
            self.state.sat_clause_count += 1;
        }
    }

    /// Encode the entire CSP
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

        // 4. Encode axiom clauses for integer variables (ALO and AMO)
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

        let int_vars: Vec<_> = self.csp.int_vars().iter().map(|(v, _)| v.clone()).collect();
        for var in int_vars {
            let value = self.decode_var(&var);
            assignment.set_int(var, value);
        }

        let bool_vars: Vec<_> = self.csp.bool_vars().to_vec();
        for b in bool_vars {
            if let Some(&code) = self.state.bool_code_map.get(&b) {
                let value = self.backend.model_value(code);
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

impl<'a, B: SatSolverBackend> Encoder for DirectEncoder<'a, B> {
    type Backend = B;

    fn sat_variables_size(&self, _var: &Var, domain: &Domain) -> i32 {
        // Direct encoding: one SAT variable per domain value
        domain.size() as i32
    }

    fn encode_var(&self, var: &Var) -> Vec<Vec<i32>> {
        let domain = self.csp.domain(var).expect("variable not found");
        let values: Vec<_> = domain.values().to_vec();
        let mut clauses = Vec::new();

        if values.len() <= 1 {
            return clauses;  // No constraints needed for singleton domain
        }

        // ALO (At Least One): at least one value must be true
        // (x = d1) OR (x = d2) OR ... OR (x = dn)
        let mut alo_clause = Vec::new();
        for &d in &values {
            alo_clause.push(self.eq_val(var, d));
        }
        clauses.push(alo_clause);

        // AMO (At Most One): at most one value can be true
        // For each pair (di, dj), NOT(x = di AND x = dj)
        // Equivalent to: (x != di) OR (x != dj)
        for i in 0..values.len() {
            for j in (i + 1)..values.len() {
                clauses.push(vec![
                    self.ne_val(var, values[i]),
                    self.ne_val(var, values[j]),
                ]);
            }
        }

        clauses
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
            Constraint::EqZero(sum) => {
                self.encode_eq_zero(sum, clause0)
            }
            Constraint::NeZero(sum) => {
                self.encode_ne_zero(sum, clause0)
            }
            Constraint::LeZero(sum) => {
                self.encode_le_zero(sum, clause0)
            }
            Constraint::GeZero(sum) => {
                self.encode_ge_zero(sum, clause0)
            }
            _ => panic!("DirectEncoder: unexpected constraint type {:?}", lit),
        }
    }

    fn add_constraint(&mut self, c: &Constraint) {
        // Simplify the constraint
        let mut simplifier = Simplifier::new(self);
        let simplified = simplifier.simplify(c);

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
                // Multiple literals in a clause
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

        for &d in domain.values() {
            let lit = self.eq_val(var, d);
            if lit == TRUE_LIT || (lit != FALSE_LIT && self.backend.model_value(lit)) {
                return d;
            }
        }

        // Fallback: return first value
        domain.lb()
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
    use crate::expr::Sum;
    use std::collections::HashSet;

    /// Helper function to enumerate all solutions for a single integer variable
    fn enumerate_all_int_solutions(encoder: &mut DirectEncoder<CaDiCaLSolver>, var: &Var) -> Vec<i32> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let val = assignment.get_int(var).unwrap();
            solutions.push(val);

            // Add blocking clause: x != val
            let domain = encoder.csp().domain(var).unwrap();
            let mut blocking_clause = Vec::new();
            for &d in domain.values() {
                if d != val {
                    let lit = encoder.eq_val(var, d);
                    if lit != FALSE_LIT && lit != TRUE_LIT {
                        blocking_clause.push(lit);
                    }
                }
            }
            if blocking_clause.is_empty() {
                break;
            }
            encoder.backend_mut().add_clause(&blocking_clause);
        }

        solutions.sort();
        solutions
    }

    /// Helper function to enumerate all solutions for two integer variables
    fn enumerate_all_two_int_solutions(
        encoder: &mut DirectEncoder<CaDiCaLSolver>,
        var1: &Var,
        var2: &Var,
    ) -> Vec<(i32, i32)> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let val1 = assignment.get_int(var1).unwrap();
            let val2 = assignment.get_int(var2).unwrap();
            solutions.push((val1, val2));

            // Add blocking clause
            let domain1 = encoder.csp().domain(var1).unwrap().clone();
            let domain2 = encoder.csp().domain(var2).unwrap().clone();
            let mut blocking_clause = Vec::new();

            for &d in domain1.values() {
                if d != val1 {
                    let lit = encoder.eq_val(var1, d);
                    if lit != FALSE_LIT && lit != TRUE_LIT {
                        blocking_clause.push(lit);
                    }
                }
            }
            for &d in domain2.values() {
                if d != val2 {
                    let lit = encoder.eq_val(var2, d);
                    if lit != FALSE_LIT && lit != TRUE_LIT {
                        blocking_clause.push(lit);
                    }
                }
            }

            if blocking_clause.is_empty() {
                break;
            }
            encoder.backend_mut().add_clause(&blocking_clause);
        }

        solutions.sort();
        solutions
    }

    /// Helper function to enumerate all boolean solutions
    fn enumerate_all_bool_solutions(
        encoder: &mut DirectEncoder<CaDiCaLSolver>,
        vars: &[crate::Bool],
    ) -> Vec<Vec<bool>> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let mut sol = Vec::new();
            for v in vars {
                sol.push(assignment.get_bool(v).unwrap_or(false));
            }
            solutions.push(sol.clone());

            // Add blocking clause
            let mut blocking_clause = Vec::new();
            for (i, v) in vars.iter().enumerate() {
                if let Some(&code) = encoder.state().bool_code_map.get(v) {
                    if sol[i] {
                        blocking_clause.push(-code);
                    } else {
                        blocking_clause.push(code);
                    }
                }
            }
            if blocking_clause.is_empty() {
                break;
            }
            encoder.backend_mut().add_clause(&blocking_clause);
        }

        solutions.sort();
        solutions
    }

    #[test]
    fn test_direct_encoder_new() {
        let csp = CSP::new();
        let solver = CaDiCaLSolver::new();
        let encoder = DirectEncoder::new(&csp, solver);
        assert_eq!(encoder.state.sat_variable_count, 0);
    }

    #[test]
    fn test_sat_variables_size() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        let solver = CaDiCaLSolver::new();
        let encoder = DirectEncoder::new(&csp, solver);

        let domain = csp.domain(&x).unwrap();
        // Direct encoding: 5 SAT vars for x=1, x=2, x=3, x=4, x=5
        assert_eq!(encoder.sat_variables_size(&x, domain), 5);
    }

    #[test]
    fn test_eq_val_boundary() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);

        encoder.state.var_code_map.insert(x.clone(), 1);

        // x = 0 should be FALSE (not in domain)
        assert_eq!(encoder.eq_val(&x, 0), FALSE_LIT);
        // x = 6 should be FALSE (not in domain)
        assert_eq!(encoder.eq_val(&x, 6), FALSE_LIT);

        // x = 1, 2, 3, 4, 5 should return valid codes
        assert_eq!(encoder.eq_val(&x, 1), 1);
        assert_eq!(encoder.eq_val(&x, 2), 2);
        assert_eq!(encoder.eq_val(&x, 3), 3);
        assert_eq!(encoder.eq_val(&x, 4), 4);
        assert_eq!(encoder.eq_val(&x, 5), 5);
    }

    #[test]
    fn test_singleton_domain() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::from(vec![3]));
        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);

        encoder.state.var_code_map.insert(x.clone(), 1);

        // Singleton domain: x = 3 is always true
        assert_eq!(encoder.eq_val(&x, 3), TRUE_LIT);
        assert_eq!(encoder.eq_val(&x, 2), FALSE_LIT);
    }

    #[test]
    fn test_encode_var_alo_amo() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);

        encoder.state.var_code_map.insert(x.clone(), 1);

        let clauses = encoder.encode_var(&x);

        // ALO: [1, 2, 3] (at least one of x=1, x=2, x=3)
        // AMO: [-1, -2], [-1, -3], [-2, -3]
        assert_eq!(clauses.len(), 4);
        assert_eq!(clauses[0], vec![1, 2, 3]);  // ALO
    }

    #[test]
    fn test_simple_csp_x_eq_3_all_solutions() {
        // x in [1,5], x == 3 => only solution x=3
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add(Sum::from(x.clone()).eq(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3]);
    }

    #[test]
    fn test_simple_csp_x_ne_3_all_solutions() {
        // x in [1,5], x != 3 => solutions x=1,2,4,5
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add(Sum::from(x.clone()).ne(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 4, 5]);
    }

    #[test]
    fn test_simple_csp_x_le_3_all_solutions() {
        // x in [1,5], x <= 3 => solutions x=1,2,3
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add(Sum::from(x.clone()).le(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3]);
    }

    #[test]
    fn test_simple_csp_x_ge_3_all_solutions() {
        // x in [1,5], x >= 3 => solutions x=3,4,5
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add(Sum::from(x.clone()).ge(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 4, 5]);
    }

    #[test]
    fn test_two_vars_eq_all_solutions() {
        // x in [1,3], y in [1,3], x + y == 4 => (1,3), (2,2), (3,1)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        let y = csp.int_var("y", Domain::range(1, 3));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.eq(4));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);
        assert_eq!(solutions, vec![(1, 3), (2, 2), (3, 1)]);
    }

    #[test]
    fn test_two_vars_ne_all_solutions() {
        // x in [1,2], y in [1,2], x + y != 3 => (1,1), (2,2)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 2));
        let y = csp.int_var("y", Domain::range(1, 2));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.ne(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);
        assert_eq!(solutions, vec![(1, 1), (2, 2)]);
    }

    #[test]
    fn test_unsat_eq() {
        // x in [1,3], x == 5 (UNSAT)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        csp.add(Sum::from(x.clone()).eq(5));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        assert!(!SatSolverBackend::solve(encoder.backend_mut()));
    }

    #[test]
    fn test_bool_constraint_all_solutions() {
        // p AND (NOT p OR q) => only (p=true, q=true)
        let mut csp = CSP::new();
        let p = csp.bool_var("p");
        let q = csp.bool_var("q");

        csp.add(Constraint::Lit(Literal::pos(p.clone())));
        csp.add(Constraint::or(vec![
            Constraint::Lit(Literal::neg(p.clone())),
            Constraint::Lit(Literal::pos(q.clone())),
        ]));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_bool_solutions(&mut encoder, &[p.clone(), q.clone()]);
        assert_eq!(solutions, vec![vec![true, true]]);
    }

    #[test]
    fn test_non_contiguous_domain_all_solutions() {
        // x in {1, 3, 5}, x == 3 => only x=3
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::from(vec![1, 3, 5]));
        csp.add(Sum::from(x.clone()).eq(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3]);
    }

    #[test]
    fn test_coefficient_all_solutions() {
        // x in [1,5], 2*x == 6 => x == 3
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add((Sum::from(x.clone()) * 2).eq(6));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3]);
    }

    #[test]
    fn test_domain_no_constraint_all_solutions() {
        // x in [1,3], no constraints => all values are solutions
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3]);
    }

    #[test]
    fn test_two_vars_le_all_solutions() {
        // x in [1,3], y in [1,3], x + y <= 4
        // Expected: (1,1), (1,2), (1,3), (2,1), (2,2), (3,1)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        let y = csp.int_var("y", Domain::range(1, 3));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.le(4));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);
        let expected: HashSet<_> = vec![(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (3, 1)].into_iter().collect();
        let actual: HashSet<_> = solutions.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_non_contiguous_domain_no_constraint_all_solutions() {
        // x in {1, 3, 5}, no constraints => all values
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::from(vec![1, 3, 5]));

        let solver = CaDiCaLSolver::new();
        let mut encoder = DirectEncoder::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 3, 5]);
    }
}
