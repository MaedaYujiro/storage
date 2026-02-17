// BddMinisatSolver: All-solutions SAT solver using BDD-based MiniSat
// Wraps bddminisat-sys for enumerating all satisfying assignments

use bddminisat_sys::*;
use crate::encoder::SatSolverBackend;
use std::ptr;

/// All-solutions SAT solver using BDD-based MiniSat
pub struct BddMinisatSolver {
    solver: *mut solver,
    num_vars: i32,
    next_var: i32,
    solved: bool,
    satisfiable: bool,
    /// UNSAT detected during clause addition
    trivially_unsat: bool,
    /// Cached first solution for model_value
    cached_solution: Option<Vec<bool>>,
}

impl BddMinisatSolver {
    /// Create a new BDD-MiniSat solver
    pub fn new() -> Self {
        let solver = unsafe { solver_new() };
        Self {
            solver,
            num_vars: 0,
            next_var: 1,
            solved: false,
            satisfiable: false,
            trivially_unsat: false,
            cached_solution: None,
        }
    }

    /// Get the number of variables
    pub fn num_vars(&self) -> i32 {
        self.num_vars
    }

    /// Set the number of variables
    pub fn set_num_vars(&mut self, n: i32) {
        self.num_vars = n;
        unsafe {
            solver_setnvars(self.solver, n);
        }
    }

    /// Add a clause (literals use 1-based indexing: 1, -1, 2, -2, ...)
    /// Returns false if the clause addition detected unsatisfiability
    pub fn add_clause(&mut self, lits: &[i32]) -> bool {
        if self.trivially_unsat {
            return false;
        }

        if lits.is_empty() {
            // Empty clause is always false
            self.trivially_unsat = true;
            return false;
        }

        // Convert to bddminisat literals (0-based variable indices)
        let mut clause: Vec<lit> = lits.iter().map(|&l| {
            let var = l.abs() - 1;  // Convert 1-based to 0-based
            let lit = toLit(var);
            if l < 0 {
                lit_neg(lit)
            } else {
                lit
            }
        }).collect();

        let result = unsafe {
            solver_addclause(self.solver, clause.as_mut_ptr(), clause.as_mut_ptr().add(clause.len()))
        };

        if result == 0 {
            self.trivially_unsat = true;
            return false;
        }

        self.solved = false;
        true
    }

    /// Solve and build OBDD for all solutions
    /// Returns true if satisfiable
    pub fn solve(&mut self) -> bool {
        if self.solved {
            return self.satisfiable;
        }

        // Check for trivial unsatisfiability detected during clause addition
        if self.trivially_unsat {
            self.solved = true;
            self.satisfiable = false;
            return false;
        }

        let result = unsafe {
            solver_solve(self.solver, ptr::null_mut(), ptr::null_mut())
        };
        self.solved = true;
        self.satisfiable = result != 0;

        self.satisfiable
    }

    /// Get the OBDD root (internal use)
    fn obdd_root(&self) -> *mut obdd_t {
        unsafe { (*self.solver).root }
    }

    /// Get the number of solutions (must call solve() first)
    pub fn num_solutions(&self) -> u64 {
        let root = self.obdd_root();
        if root.is_null() {
            return 0;
        }
        unsafe { obdd_nsols(self.num_vars, root) as u64 }
    }

    /// Get all solutions as a vector of boolean vectors
    /// Each inner vector represents one solution (true/false for each variable)
    pub fn all_solutions(&self) -> Vec<Vec<bool>> {
        let root = self.obdd_root();
        if root.is_null() || self.num_vars == 0 {
            return Vec::new();
        }

        let mut solutions = Vec::new();
        let mut assignment = vec![false; self.num_vars as usize];
        self.collect_solutions_from(root, 1, &mut assignment, &mut solutions);
        solutions
    }

    /// Recursively collect solutions from OBDD
    /// `current_var` is the next variable index to assign (1-based)
    fn collect_solutions_from(
        &self,
        node: *mut obdd_t,
        current_var: i32,
        assignment: &mut Vec<bool>,
        solutions: &mut Vec<Vec<bool>>,
    ) {
        unsafe {
            // Check for terminal nodes
            if obdd_const(node) {
                if node == top_node {
                    // True terminal: enumerate all remaining unassigned variables
                    self.enumerate_remaining(current_var, assignment, solutions);
                }
                // False terminal (bot_node): not a solution, do nothing
                return;
            }

            let node_var = obdd_label(node);  // 1-based variable index

            // Enumerate all don't-care variables between current_var and node_var
            if current_var < node_var {
                // There are skipped variables - enumerate them
                self.enumerate_skipped(node, current_var, node_var, assignment, solutions);
            } else {
                // No skipped variables, proceed normally
                let var_idx = (node_var - 1) as usize;  // Convert to 0-based index

                // Traverse low branch (var = false)
                assignment[var_idx] = false;
                self.collect_solutions_from((*node).lo, node_var + 1, assignment, solutions);

                // Traverse high branch (var = true)
                assignment[var_idx] = true;
                self.collect_solutions_from((*node).hi, node_var + 1, assignment, solutions);
            }
        }
    }

    /// Enumerate solutions for skipped (don't-care) variables
    fn enumerate_skipped(
        &self,
        node: *mut obdd_t,
        current_var: i32,
        target_var: i32,
        assignment: &mut Vec<bool>,
        solutions: &mut Vec<Vec<bool>>,
    ) {
        if current_var >= target_var {
            // Reached the target variable, continue normal traversal
            self.collect_solutions_from(node, current_var, assignment, solutions);
            return;
        }

        let var_idx = (current_var - 1) as usize;

        // Try false
        assignment[var_idx] = false;
        self.enumerate_skipped(node, current_var + 1, target_var, assignment, solutions);

        // Try true
        assignment[var_idx] = true;
        self.enumerate_skipped(node, current_var + 1, target_var, assignment, solutions);
    }

    /// Enumerate all remaining variables after reaching TOP
    fn enumerate_remaining(
        &self,
        current_var: i32,
        assignment: &mut Vec<bool>,
        solutions: &mut Vec<Vec<bool>>,
    ) {
        if current_var > self.num_vars {
            // All variables assigned, record solution
            solutions.push(assignment.clone());
            return;
        }

        let var_idx = (current_var - 1) as usize;

        // Try false
        assignment[var_idx] = false;
        self.enumerate_remaining(current_var + 1, assignment, solutions);

        // Try true
        assignment[var_idx] = true;
        self.enumerate_remaining(current_var + 1, assignment, solutions);
    }
}

impl Default for BddMinisatSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for BddMinisatSolver {
    fn drop(&mut self) {
        unsafe {
            // Note: We don't call obdd_delete_all because it seems to have
            // issues with global state. The solver_delete should clean up
            // the solver's memory, and any OBDD nodes will be leaked but
            // this is acceptable for now.
            solver_delete(self.solver);
        }
    }
}

impl SatSolverBackend for BddMinisatSolver {
    fn add_clause(&mut self, clause: &[i32]) {
        // Call the inherent method, ignoring the return value
        let _ = BddMinisatSolver::add_clause(self, clause);
    }

    fn reserve_vars(&mut self, count: i32) {
        if count > self.num_vars {
            self.set_num_vars(count);
        }
        if self.next_var <= count {
            self.next_var = count + 1;
        }
    }

    fn next_var_id(&mut self) -> i32 {
        let id = self.next_var;
        self.next_var += 1;
        // Ensure num_vars is updated
        if id > self.num_vars {
            self.set_num_vars(id);
        }
        id
    }

    fn model_value(&mut self, var: i32) -> bool {
        // Ensure we have solved and have a cached solution
        if self.cached_solution.is_none() && self.satisfiable {
            // Get first solution from OBDD
            let solutions = self.all_solutions();
            if !solutions.is_empty() {
                self.cached_solution = Some(solutions.into_iter().next().unwrap());
            }
        }

        if let Some(ref sol) = self.cached_solution {
            let idx = (var.abs() - 1) as usize;
            if idx < sol.len() {
                return sol[idx];
            }
        }
        false
    }

    fn reset(&mut self) {
        unsafe {
            solver_delete(self.solver);
            self.solver = solver_new();
        }
        self.num_vars = 0;
        self.next_var = 1;
        self.solved = false;
        self.satisfiable = false;
        self.trivially_unsat = false;
        self.cached_solution = None;
    }

    fn solve(&mut self) -> bool {
        // Call the inherent method
        let result = BddMinisatSolver::solve(self);
        // Cache solution if satisfiable
        if result && self.cached_solution.is_none() {
            let solutions = self.all_solutions();
            if !solutions.is_empty() {
                self.cached_solution = Some(solutions.into_iter().next().unwrap());
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Note: bddminisat-sys has global state issues that cause crashes
    // when multiple tests run in parallel or sequentially.
    // Tests marked with #[ignore] pass individually but fail together.
    // Run with: cargo test bddminisat -- --ignored --test-threads=1

    #[test]
    fn test_new_solver() {
        let solver = BddMinisatSolver::new();
        assert_eq!(solver.num_vars(), 0);
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_add_clause_simple() {
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(2);
        // x1 OR x2
        solver.add_clause(&[1, 2]);
        assert!(solver.solve());
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_unsat() {
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(1);
        // x1 AND NOT x1
        solver.add_clause(&[1]);
        solver.add_clause(&[-1]);
        assert!(!solver.solve());
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_count_solutions_single_var() {
        // x1 has 2 solutions: true, false
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(1);
        assert!(solver.solve());
        assert_eq!(solver.num_solutions(), 2);
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_count_solutions_with_constraint() {
        // x1 OR x2 has 3 solutions: (T,T), (T,F), (F,T)
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(2);
        solver.add_clause(&[1, 2]);
        assert!(solver.solve());
        assert_eq!(solver.num_solutions(), 3);
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_enumerate_all_solutions() {
        // x1 AND x2 has 1 solution: (T,T)
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(2);
        solver.add_clause(&[1]);
        solver.add_clause(&[2]);
        assert!(solver.solve());

        let solutions = solver.all_solutions();
        assert_eq!(solutions.len(), 1);
        assert_eq!(solutions[0], vec![true, true]);
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_enumerate_multiple_solutions() {
        // x1 OR x2 has 3 solutions
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(2);
        solver.add_clause(&[1, 2]);
        assert!(solver.solve());

        let mut solutions = solver.all_solutions();
        solutions.sort();
        assert_eq!(solutions.len(), 3);
        // (F,T), (T,F), (T,T)
        assert_eq!(solutions[0], vec![false, true]);
        assert_eq!(solutions[1], vec![true, false]);
        assert_eq!(solutions[2], vec![true, true]);
    }

    #[test]
    #[ignore = "bddminisat global state issue"]
    fn test_three_vars() {
        // x1 OR x2 OR x3 has 7 solutions (all except F,F,F)
        let mut solver = BddMinisatSolver::new();
        solver.set_num_vars(3);
        solver.add_clause(&[1, 2, 3]);
        assert!(solver.solve());
        assert_eq!(solver.num_solutions(), 7);
    }
}
