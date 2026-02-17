// OrderEncoderGe: Order encoding using x >= d (instead of x <= d)
// Based on OrderEncoder but uses greater-than-or-equal encoding

use crate::{Var, Literal, Constraint, Assignment};
use crate::domain::Domain;
use crate::csp::CSP;
use super::{
    Encoder, SatSolverBackend, EncoderState,
    TRUE_LIT, FALSE_LIT, floor_div, ceil_div,
    Simplifier,
};

/// OrderEncoderGe: encodes CSP to SAT using order encoding with x >= d
pub struct OrderEncoderGe<'a, B: SatSolverBackend> {
    csp: &'a CSP,
    backend: B,
    state: EncoderState,
}

impl<'a, B: SatSolverBackend> OrderEncoderGe<'a, B> {
    pub fn new(csp: &'a CSP, backend: B) -> Self {
        Self {
            csp,
            backend,
            state: EncoderState::new(),
        }
    }

    /// Get the SAT literal for (x >= b)
    /// Returns TRUE_LIT if b <= lb, FALSE_LIT if b > ub
    pub fn ge(&self, x: &Var, b: i32) -> i32 {
        let domain = self.csp.domain(x).expect("variable not found");
        if b <= domain.lb() {
            TRUE_LIT
        } else if b > domain.ub() {
            FALSE_LIT
        } else {
            let code = self.state.var_code_map.get(x).expect("variable not encoded");
            if domain.is_contiguous() {
                // SAT variables represent: (x >= lb+1), (x >= lb+2), ..., (x >= ub)
                // (x >= b) corresponds to code + (b - lb - 1)
                code + (b - domain.lb() - 1)
            } else {
                // Non-contiguous domain: SAT vars are (x >= values[1]), ..., (x >= values[n-1])
                // (x >= values[i]) corresponds to code + (i - 1) for i >= 1
                let values = domain.values();
                match values.binary_search(&b) {
                    Ok(pos) => {
                        // b is in the domain: ge(x, values[pos]) = code + (pos - 1)
                        code + (pos as i32 - 1)
                    }
                    Err(insert_pos) => {
                        // b is not in the domain: find smallest value >= b
                        // values[insert_pos] is the smallest value > b (if exists)
                        // x >= b is equivalent to x >= values[insert_pos]
                        if insert_pos >= values.len() {
                            FALSE_LIT
                        } else {
                            code + (insert_pos as i32 - 1)
                        }
                    }
                }
            }
        }
    }

    /// Get the SAT literal for (a * x >= b)
    pub fn ge_ax(&self, a: i32, x: &Var, b: i32) -> i32 {
        if a > 0 {
            // a*x >= b <=> x >= ceil(b/a)
            self.ge(x, ceil_div(b, a))
        } else if a < 0 {
            // a*x >= b <=> x <= floor(b/a) <=> !(x >= floor(b/a) + 1)
            -self.ge(x, floor_div(b, a) + 1)
        } else {
            // a == 0: 0 >= b
            if b <= 0 { TRUE_LIT } else { FALSE_LIT }
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

    /// Upper bound of sum of terms
    fn ub_sum(&self, axs: &[(i32, Var)]) -> i32 {
        axs.iter().map(|(a, x)| self.ub_ax(*a, x)).sum()
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

    /// Encode linear constraint: sum(ai * xi) >= c
    pub fn encode_ge(&self, axs: &[(i32, Var)], c: i32, clause0: &[i32]) -> Vec<Vec<i32>> {
        match axs {
            [] => {
                if c <= 0 {
                    vec![]  // Always true (0 >= c where c <= 0)
                } else {
                    vec![clause0.to_vec()]  // False (0 >= c where c > 0)
                }
            }
            [(a, x)] => {
                let lit = self.ge_ax(*a, x, c);
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
                    // For a > 0: need x >= lb0 where lb0 = ceil((c - ub_sum(rest)) / a)
                    let lb0 = ceil_div(c - self.ub_sum(rest), *a);
                    let lb_x = self.lb(x).max(lb0);
                    let ub_x = self.ub(x);

                    if lb_x > ub_x {
                        return vec![clause0.to_vec()];
                    }

                    let domain = self.csp.domain(x).unwrap();
                    let mut clauses = Vec::new();

                    for b in self.range_values(domain, lb_x, ub_x) {
                        // x = b implies rest >= c - a*b
                        // clause: (x > b) | (rest >= c - a*b)
                        // (x > b) = (x >= b+1)
                        let lit = self.ge(x, b + 1);
                        if lit != TRUE_LIT {
                            let mut new_clause0 = clause0.to_vec();
                            new_clause0.push(lit);
                            clauses.extend(self.encode_ge(rest, c - a * b, &new_clause0));
                        }
                    }

                    if self.lb(x) < lb0 {
                        let mut clause = clause0.to_vec();
                        clause.push(self.ge(x, lb0));
                        clauses.push(clause);
                    }

                    clauses
                } else {
                    // a < 0: for negative coefficient
                    // a*x >= c - sum(rest) where a < 0
                    // x <= (c - sum(rest)) / a = floor((c - ub_sum(rest)) / a)
                    let ub0 = floor_div(c - self.ub_sum(rest), *a);
                    let lb_x = self.lb(x);
                    let ub_x = self.ub(x).min(ub0);

                    if lb_x > ub_x {
                        return vec![clause0.to_vec()];
                    }

                    let domain = self.csp.domain(x).unwrap();
                    let mut clauses = Vec::new();

                    for b in self.range_values(domain, lb_x, ub_x) {
                        // x = b implies rest >= c - a*b
                        // clause: (x < b) | (rest >= c - a*b)
                        // (x < b) = !(x >= b)
                        let lit = -self.ge(x, b);
                        if lit != TRUE_LIT {
                            let mut new_clause0 = clause0.to_vec();
                            new_clause0.push(lit);
                            clauses.extend(self.encode_ge(rest, c - a * b, &new_clause0));
                        }
                    }

                    if self.ub(x) > ub0 {
                        let mut clause = clause0.to_vec();
                        clause.push(-self.ge(x, ub0 + 1));  // x <= ub0 = !(x >= ub0+1)
                        clauses.push(clause);
                    }

                    clauses
                }
            }
        }
    }

    /// Convert constraint to GeZero form
    pub fn to_ge_zero(&self, c: &Constraint) -> Constraint {
        match c {
            Constraint::EqZero(sum) => {
                // x == 0 <=> x >= 0 && -x >= 0
                Constraint::and(vec![
                    Constraint::GeZero(sum.clone()),
                    Constraint::GeZero(-sum.clone()),
                ])
            }
            Constraint::NeZero(sum) => {
                // x != 0 <=> x >= 1 || -x >= 1
                Constraint::or(vec![
                    Constraint::GeZero(sum.clone() + (-1)),
                    Constraint::GeZero(-sum.clone() + (-1)),
                ])
            }
            Constraint::LeZero(sum) => {
                // x <= 0 <=> -x >= 0
                Constraint::GeZero(-sum.clone())
            }
            Constraint::And(cs) => {
                Constraint::and(cs.iter().map(|ci| self.to_ge_zero(ci)).collect())
            }
            Constraint::Or(cs) => {
                Constraint::or(cs.iter().map(|ci| self.to_ge_zero(ci)).collect())
            }
            _ => c.clone(),  // Lit, GeZero remain unchanged
        }
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

impl<'a, B: SatSolverBackend> Encoder for OrderEncoderGe<'a, B> {
    type Backend = B;

    fn sat_variables_size(&self, _var: &Var, domain: &Domain) -> i32 {
        // Order encoding: need (ub - lb) SAT variables for (x >= lb+1), ..., (x >= ub)
        if domain.is_contiguous() {
            domain.ub() - domain.lb()
        } else {
            (domain.size() - 1) as i32
        }
    }

    fn encode_var(&self, var: &Var) -> Vec<Vec<i32>> {
        let domain = self.csp.domain(var).expect("variable not found");

        if domain.is_contiguous() {
            // Axiom clauses: (x >= b+1) => (x >= b), i.e., !(x >= b+1) | (x >= b)
            (self.lb(var) + 1..=self.ub(var) - 1)
                .map(|b| vec![-self.ge(var, b + 1), self.ge(var, b)])
                .collect()
        } else {
            // Non-contiguous domain
            let values: Vec<_> = domain.values().to_vec();
            (1..=values.len() - 2)
                .map(|i| vec![-self.ge(var, values[i + 1]), self.ge(var, values[i])])
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
            Constraint::GeZero(sum) => {
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
                // sum >= 0 <=> sum of terms >= -b
                self.encode_ge(&axs, -sum.b(), clause0)
            }
            _ => panic!("OrderEncoderGe: unexpected constraint type {:?}", lit),
        }
    }

    fn add_constraint(&mut self, c: &Constraint) {
        let c = self.to_ge_zero(c);
        let mut simplifier = Simplifier::new(self);
        let simplified = simplifier.simplify(&c);

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

        if domain.is_contiguous() {
            // Find the largest b such that (x >= b) is true
            for b in (domain.lb() + 1..=domain.ub()).rev() {
                let lit = self.ge(var, b);
                if lit != FALSE_LIT && lit != TRUE_LIT && self.backend.model_value(lit) {
                    return b;
                }
            }
            domain.lb()
        } else {
            let values: Vec<_> = domain.values().to_vec();
            for &v in values.iter().skip(1).rev() {
                let lit = self.ge(var, v);
                if lit != FALSE_LIT && lit != TRUE_LIT && self.backend.model_value(lit) {
                    return v;
                }
            }
            *values.first().unwrap()
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
    use crate::expr::Sum;
    use crate::encoder::SatSolverBackend;

    #[test]
    fn test_order_encoder_ge_new() {
        let csp = CSP::new();
        let solver = CaDiCaLSolver::new();
        let encoder = OrderEncoderGe::new(&csp, solver);
        assert_eq!(encoder.state.sat_variable_count, 0);
    }

    #[test]
    fn test_sat_variables_size_contiguous() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        let solver = CaDiCaLSolver::new();
        let encoder = OrderEncoderGe::new(&csp, solver);

        let domain = csp.domain(&x).unwrap();
        // 4 SAT vars for (x>=2), (x>=3), (x>=4), (x>=5)
        assert_eq!(encoder.sat_variables_size(&x, domain), 4);
    }

    #[test]
    fn test_ge_boundary() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);

        encoder.state.var_code_map.insert(x.clone(), 1);

        // x >= 1 should be TRUE (at or below lb)
        assert_eq!(encoder.ge(&x, 1), TRUE_LIT);
        assert_eq!(encoder.ge(&x, 0), TRUE_LIT);

        // x >= 6 should be FALSE (above ub)
        assert_eq!(encoder.ge(&x, 6), FALSE_LIT);

        // x >= 2, x >= 3, x >= 4, x >= 5 should return valid codes
        assert_eq!(encoder.ge(&x, 2), 1);  // code + pos(1) = 1 + 0 = 1
        assert_eq!(encoder.ge(&x, 3), 2);
        assert_eq!(encoder.ge(&x, 4), 3);
        assert_eq!(encoder.ge(&x, 5), 4);
    }

    #[test]
    fn test_encode_var_contiguous() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 4));
        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);

        encoder.state.var_code_map.insert(x.clone(), 1);

        let clauses = encoder.encode_var(&x);
        // Should have axiom clauses: !(x>=3) | (x>=2), !(x>=4) | (x>=3)
        // i.e., [-2, 1], [-3, 2]
        assert_eq!(clauses.len(), 2);
        assert_eq!(clauses[0], vec![-2, 1]);
        assert_eq!(clauses[1], vec![-3, 2]);
    }

    // Integration tests with full solution enumeration

    use std::collections::HashSet;

    /// Helper: enumerate all solutions for a single integer variable
    fn enumerate_all_int_solutions(
        encoder: &mut OrderEncoderGe<CaDiCaLSolver>,
        var: &Var,
    ) -> Vec<i32> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let val = assignment.get_int(var).unwrap();
            solutions.push(val);

            // Block current solution using ge encoding
            // x != val <=> (x >= val+1) OR (x < val) <=> ge(val+1) OR !ge(val)
            let lit_ge = encoder.ge(var, val + 1);
            let lit_lt = -encoder.ge(var, val);

            let mut block_clause = Vec::new();
            if lit_ge != TRUE_LIT && lit_ge != FALSE_LIT {
                block_clause.push(lit_ge);
            }
            if lit_lt != TRUE_LIT && lit_lt != FALSE_LIT {
                block_clause.push(lit_lt);
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

    /// Helper: enumerate all solutions for two integer variables
    fn enumerate_all_two_int_solutions(
        encoder: &mut OrderEncoderGe<CaDiCaLSolver>,
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
                let lit_ge = encoder.ge(var, val + 1);
                let lit_lt = -encoder.ge(var, val);
                if lit_ge != TRUE_LIT && lit_ge != FALSE_LIT {
                    block_clause.push(lit_ge);
                }
                if lit_lt != TRUE_LIT && lit_lt != FALSE_LIT {
                    block_clause.push(lit_lt);
                }
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

    /// Helper: enumerate all solutions for three integer variables
    fn enumerate_all_three_int_solutions(
        encoder: &mut OrderEncoderGe<CaDiCaLSolver>,
        var1: &Var,
        var2: &Var,
        var3: &Var,
    ) -> Vec<(i32, i32, i32)> {
        let mut solutions = Vec::new();

        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let val1 = assignment.get_int(var1).unwrap();
            let val2 = assignment.get_int(var2).unwrap();
            let val3 = assignment.get_int(var3).unwrap();
            solutions.push((val1, val2, val3));

            // Block current solution
            let mut block_clause = Vec::new();
            for (var, val) in [(var1, val1), (var2, val2), (var3, val3)] {
                let lit_ge = encoder.ge(var, val + 1);
                let lit_lt = -encoder.ge(var, val);
                if lit_ge != TRUE_LIT && lit_ge != FALSE_LIT {
                    block_clause.push(lit_ge);
                }
                if lit_lt != TRUE_LIT && lit_lt != FALSE_LIT {
                    block_clause.push(lit_lt);
                }
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

    #[test]
    fn test_simple_csp_x_le_5_all_solutions() {
        // x in [1,10], x <= 5 -> solutions: {1, 2, 3, 4, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        csp.add(Sum::from(x.clone()).le(5));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_simple_csp_x_ge_3_all_solutions() {
        // x in [1,5], x >= 3 -> solutions: {3, 4, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add(Sum::from(x.clone()).ge(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 4, 5]);
    }

    #[test]
    fn test_simple_csp_x_eq_3_all_solutions() {
        // x in [1,5], x == 3 -> solutions: {3}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));
        csp.add(Sum::from(x.clone()).eq(3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
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

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.eq(6));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_two_int_solutions(&mut encoder, &x, &y);

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

        let sum = Sum::from(x.clone()) + Sum::from(y.clone());
        csp.add(sum.le(2));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
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
        // x in [1,3], x >= 5 (UNSAT)
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        csp.add(Sum::from(x.clone()).ge(5));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        assert!(!SatSolverBackend::solve(encoder.backend_mut()));
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
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let mut solutions = Vec::new();
        while SatSolverBackend::solve(encoder.backend_mut()) {
            let assignment = encoder.decode();
            let p_val = assignment.get_bool(&p).unwrap();
            let q_val = assignment.get_bool(&q).unwrap();
            solutions.push((p_val, q_val));

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
    fn test_non_contiguous_domain_all_solutions() {
        // x in {1, 3, 5}, x >= 2 -> solutions: {3, 5}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::from(vec![1, 3, 5]));
        csp.add(Sum::from(x.clone()).ge(2));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![3, 5]);
    }

    #[test]
    fn test_negative_coefficient_all_solutions() {
        // x in [1,5], -x >= -3 (i.e., x <= 3) -> solutions: {1, 2, 3}
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 5));

        let neg_x = -Sum::from(x.clone());
        csp.add(neg_x.ge(-3));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3]);
    }

    #[test]
    fn test_three_vars_constraint_all_solutions() {
        // x, y, z in [0,3], x + y + z == 6
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(0, 3));
        let y = csp.int_var("y", Domain::range(0, 3));
        let z = csp.int_var("z", Domain::range(0, 3));

        let sum = Sum::from(x.clone()) + Sum::from(y.clone()) + Sum::from(z.clone());
        csp.add(sum.eq(6));

        let solver = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_three_int_solutions(&mut encoder, &x, &y, &z);

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
        let mut encoder = OrderEncoderGe::new(&csp, solver);
        encoder.encode_csp();

        let solutions = enumerate_all_int_solutions(&mut encoder, &x);
        assert_eq!(solutions, vec![1, 2, 3, 4]);
    }
}
