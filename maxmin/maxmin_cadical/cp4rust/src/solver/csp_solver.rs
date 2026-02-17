// CspSolver: High-level constraint solving interface
// Corresponds to Scarab's Solver.scala

use crate::{CSP, Assignment};
use crate::encoder::{OrderEncoderLe, SatSolverBackend, TRUE_LIT, FALSE_LIT, Encoder};

/// CspSolver: orchestrates CSP encoding and solving
/// Scarab: class Solver(val csp: CSP, val satSolver: SatSolver, val encoder: Encoder)
pub struct CspSolver<'a, B: SatSolverBackend> {
    encoder: OrderEncoderLe<'a, B>,
    /// Cached solution (equivalent to Scarab's _solutionOpt)
    solution_cache: Option<Assignment>,
    /// Whether CSP has been encoded
    encoded: bool,
}

impl<'a, B: SatSolverBackend> CspSolver<'a, B> {
    /// Create a new CspSolver
    /// Scarab: new Solver(csp, satSolver, encoder)
    pub fn new(csp: &'a CSP, backend: B) -> Self {
        Self {
            encoder: OrderEncoderLe::new(csp, backend),
            solution_cache: None,
            encoded: false,
        }
    }

    /// Encode and find first solution
    /// Scarab: def find: Boolean
    pub fn find(&mut self) -> bool {
        if !self.encoded {
            self.encoder.encode_csp();
            self.encoded = true;
        }

        if self.encoder.backend_mut().solve() {
            self.solution_cache = Some(self.encoder.decode());
            true
        } else {
            self.solution_cache = None;
            false
        }
    }

    /// Find next solution (blocks current solution)
    /// Scarab: def findNext: Boolean
    pub fn find_next(&mut self) -> bool {
        if self.solution_cache.is_none() {
            return false;
        }

        self.add_block_constraint();

        if self.encoder.backend_mut().solve() {
            self.solution_cache = Some(self.encoder.decode());
            true
        } else {
            self.solution_cache = None;
            false
        }
    }

    /// Get the current solution (panics if none)
    /// Scarab: def solution: Assignment
    pub fn solution(&self) -> &Assignment {
        self.solution_cache.as_ref().expect("No solution available")
    }

    /// Get the current solution (Option)
    /// Scarab: def solutionOpt: Option[Assignment]
    pub fn solution_opt(&self) -> Option<&Assignment> {
        self.solution_cache.as_ref()
    }

    /// Check satisfiability without decoding
    /// Scarab: def isSatisfiable: Boolean
    pub fn is_satisfiable(&mut self) -> bool {
        if !self.encoded {
            self.encoder.encode_csp();
            self.encoded = true;
        }
        self.encoder.backend_mut().solve()
    }

    /// Reset solver state
    /// Scarab: def reset(): Unit
    pub fn reset(&mut self) {
        self.encoder.backend_mut().reset();
        self.solution_cache = None;
        self.encoded = false;
    }

    /// Encode CSP to SAT (idempotent)
    /// Returns true if encoding was performed, false if already encoded
    pub fn encode(&mut self) -> bool {
        if self.encoded {
            return false;
        }
        self.encoder.encode_csp();
        self.encoded = true;
        true
    }

    /// Check if CSP has been encoded
    pub fn is_encoded(&self) -> bool {
        self.encoded
    }

    /// Solve the encoded SAT problem
    /// Returns true if satisfiable, false if unsatisfiable
    /// Panics if not yet encoded
    pub fn solve(&mut self) -> bool {
        assert!(self.encoded, "CSP must be encoded before solving");
        self.encoder.backend_mut().solve()
    }

    /// Decode the SAT solution to CSP assignment
    /// Returns the assignment and caches it
    /// Panics if not yet encoded or last solve was UNSAT
    pub fn decode(&mut self) -> &Assignment {
        assert!(self.encoded, "CSP must be encoded before decoding");
        self.solution_cache = Some(self.encoder.decode());
        self.solution_cache.as_ref().unwrap()
    }

    /// Access the encoder
    pub fn encoder(&self) -> &OrderEncoderLe<'a, B> {
        &self.encoder
    }

    /// Access the encoder mutably
    pub fn encoder_mut(&mut self) -> &mut OrderEncoderLe<'a, B> {
        &mut self.encoder
    }

    /// Add constraint blocking current solution
    /// Scarab: private def addBlockConstraint(): Unit
    fn add_block_constraint(&mut self) {
        let Some(assignment) = &self.solution_cache else { return };
        let mut clause = Vec::new();

        // Block integer variables: x != value
        for (var, _) in self.encoder.csp().int_vars() {
            if let Some(value) = assignment.get_int(var) {
                // x != value <=> (x <= value-1) OR (x > value)
                // Order encoding: le(x, value-1) OR !le(x, value)
                let lit_le = self.encoder.le(var, value - 1);
                let lit_gt = -self.encoder.le(var, value);

                if lit_le != TRUE_LIT && lit_le != FALSE_LIT {
                    clause.push(lit_le);
                }
                if lit_gt != TRUE_LIT && lit_gt != FALSE_LIT {
                    clause.push(lit_gt);
                }
            }
        }

        // Block boolean variables: !current_value
        for b in self.encoder.csp().bool_vars() {
            if let Some(value) = assignment.get_bool(b) {
                if let Some(&code) = self.encoder.state().bool_code_map.get(b) {
                    clause.push(if value { -code } else { code });
                }
            }
        }

        if !clause.is_empty() {
            self.encoder.backend_mut().add_clause(&clause);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Domain, CaDiCaLSolver};
    use crate::expr::Sum;

    #[test]
    fn test_find_single_solution() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        csp.add(Sum::from(x.clone()).le(5));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        assert!(solver.find());
        let sol = solver.solution();
        let x_val = sol.get_int(&x).unwrap();
        assert!(x_val >= 1 && x_val <= 5);
    }

    #[test]
    fn test_find_unsat() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        csp.add(Sum::from(x.clone()).ge(10));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        assert!(!solver.find());
        assert!(solver.solution_opt().is_none());
    }

    #[test]
    fn test_find_next_enumerate() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        let mut solutions = Vec::new();

        // Find first solution
        assert!(solver.find());
        solutions.push(solver.solution().get_int(&x).unwrap());

        // Find remaining solutions
        while solver.find_next() {
            solutions.push(solver.solution().get_int(&x).unwrap());
        }

        // Should have 3 solutions: x=1, x=2, x=3
        solutions.sort();
        assert_eq!(solutions, vec![1, 2, 3]);
    }

    #[test]
    fn test_find_next_two_vars() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 2));
        let y = csp.int_var("y", Domain::range(1, 2));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        let mut solutions = Vec::new();

        assert!(solver.find());
        solutions.push((
            solver.solution().get_int(&x).unwrap(),
            solver.solution().get_int(&y).unwrap()
        ));

        while solver.find_next() {
            solutions.push((
                solver.solution().get_int(&x).unwrap(),
                solver.solution().get_int(&y).unwrap()
            ));
        }

        // Should have 4 solutions: (1,1), (1,2), (2,1), (2,2)
        solutions.sort();
        assert_eq!(solutions.len(), 4);
        assert_eq!(solutions, vec![(1, 1), (1, 2), (2, 1), (2, 2)]);
    }

    #[test]
    fn test_solution_access() {
        let mut csp = CSP::new();
        let _x = csp.int_var("x", Domain::range(1, 5));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        // Before find, no solution
        assert!(solver.solution_opt().is_none());

        // After find, solution available
        solver.find();
        assert!(solver.solution_opt().is_some());
        let _ = solver.solution(); // Should not panic
    }

    #[test]
    fn test_is_satisfiable() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        csp.add(Sum::from(x.clone()).le(5));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        assert!(solver.is_satisfiable());
        // Note: is_satisfiable doesn't decode, so solution may not be cached
    }

    #[test]
    fn test_reset() {
        let mut csp = CSP::new();
        let _x = csp.int_var("x", Domain::range(1, 5));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        solver.find();
        assert!(solver.solution_opt().is_some());

        solver.reset();
        assert!(solver.solution_opt().is_none());

        // Can solve again after reset
        assert!(solver.find());
    }

    #[test]
    fn test_encode_solve_decode_separate() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        csp.add(Sum::from(x.clone()).le(5));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        // Initially not encoded
        assert!(!solver.is_encoded());

        // Encode
        assert!(solver.encode()); // Returns true (encoding performed)
        assert!(solver.is_encoded());
        assert!(!solver.encode()); // Returns false (already encoded)

        // Solve
        assert!(solver.solve()); // SAT

        // Decode
        let sol = solver.decode();
        let x_val = sol.get_int(&x).unwrap();
        assert!(x_val >= 1 && x_val <= 5);
    }

    #[test]
    fn test_encode_solve_decode_unsat() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 3));
        csp.add(Sum::from(x.clone()).ge(10));

        let backend = CaDiCaLSolver::new();
        let mut solver = CspSolver::new(&csp, backend);

        solver.encode();
        assert!(!solver.solve()); // UNSAT
    }
}
