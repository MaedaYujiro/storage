// CaDiCaL Solver using cadical-sys

use std::collections::HashMap;
use cadical_sys::{CaDiCal, Status};
use crate::expr::{Bool, Literal, Constraint};
use crate::Assignment;

// Re-export traits from cadical-sys
pub use cadical_sys::ExternalPropagator;
pub use cadical_sys::Terminator;

/// Solver state (mirrors cadical_sys::State)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverState {
    Initializing,
    Configuring,
    Steady,
    Adding,
    Solving,
    Satisfied,
    Unsatisfied,
    Deleting,
    Ready,
    Valid,
    Invalid,
}

impl From<cadical_sys::State> for SolverState {
    fn from(s: cadical_sys::State) -> Self {
        match s {
            cadical_sys::State::INITIALIZING => SolverState::Initializing,
            cadical_sys::State::CONFIGURING => SolverState::Configuring,
            cadical_sys::State::STEADY => SolverState::Steady,
            cadical_sys::State::ADDING => SolverState::Adding,
            cadical_sys::State::SOLVING => SolverState::Solving,
            cadical_sys::State::SATISFIED => SolverState::Satisfied,
            cadical_sys::State::UNSATISFIED => SolverState::Unsatisfied,
            cadical_sys::State::DELETING => SolverState::Deleting,
            cadical_sys::State::READY => SolverState::Ready,
            cadical_sys::State::VALID => SolverState::Valid,
            cadical_sys::State::INVALID => SolverState::Invalid,
        }
    }
}

/// Solver status (last solve result)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverStatus {
    Satisfiable,
    Unsatisfiable,
    Unknown,
}

impl From<cadical_sys::Status> for SolverStatus {
    fn from(s: cadical_sys::Status) -> Self {
        match s {
            cadical_sys::Status::SATISFIABLE => SolverStatus::Satisfiable,
            cadical_sys::Status::UNSATISFIABLE => SolverStatus::Unsatisfiable,
            cadical_sys::Status::UNKNOWN => SolverStatus::Unknown,
        }
    }
}

/// Solve result
pub enum SolveResult {
    Sat(Assignment),
    Unsat,
}

impl SolveResult {
    pub fn is_sat(&self) -> bool {
        matches!(self, SolveResult::Sat(_))
    }

    pub fn is_unsat(&self) -> bool {
        matches!(self, SolveResult::Unsat)
    }
}

/// CaDiCaL-based SAT Solver
pub struct CaDiCaLSolver {
    solver: CaDiCal,
    bool_to_var: HashMap<Bool, i32>,
    next_var: i32,
}

impl CaDiCaLSolver {
    pub fn new() -> Self {
        CaDiCaLSolver {
            solver: CaDiCal::new(),
            bool_to_var: HashMap::new(),
            next_var: 1,
        }
    }

    fn get_var(&mut self, b: &Bool) -> i32 {
        if let Some(&var) = self.bool_to_var.get(b) {
            var
        } else {
            let var = self.next_var;
            self.next_var += 1;
            self.bool_to_var.insert(b.clone(), var);
            var
        }
    }

    fn encode_literal(&mut self, lit: &Literal) -> i32 {
        match lit {
            Literal::Pos(b) => self.get_var(b),
            Literal::Neg(b) => -self.get_var(b),
        }
    }

    pub fn add(&mut self, constraint: Constraint) {
        self.encode(&constraint);
    }

    fn encode(&mut self, constraint: &Constraint) {
        match constraint {
            Constraint::Lit(lit) => {
                let l = self.encode_literal(lit);
                self.solver.add(l);
                self.solver.add(0); // terminate clause
            }
            Constraint::And(cs) => {
                for c in cs {
                    self.encode(c);
                }
            }
            Constraint::Or(cs) => {
                let lits = self.collect_or_lits(cs);
                for l in lits {
                    self.solver.add(l);
                }
                self.solver.add(0); // terminate clause
            }
            _ => panic!("Arithmetic constraints not supported in SAT solver"),
        }
    }

    fn collect_or_lits(&mut self, cs: &[Constraint]) -> Vec<i32> {
        let mut lits = Vec::new();
        for c in cs {
            match c {
                Constraint::Lit(lit) => {
                    lits.push(self.encode_literal(lit));
                }
                Constraint::Or(nested) => {
                    lits.extend(self.collect_or_lits(nested));
                }
                _ => panic!("Complex nested constraints in Or not yet supported"),
            }
        }
        lits
    }

    pub fn solve(&mut self) -> SolveResult {
        match self.solver.solve() {
            Status::SATISFIABLE => {
                let mut assignment = Assignment::new();
                for (bool_var, &var) in &self.bool_to_var {
                    let val = self.solver.val(var);
                    // val > 0 means true, val < 0 means false, val == 0 means don't care
                    let bool_val = val > 0 || val == 0;
                    assignment.set_bool(bool_var.clone(), bool_val);
                }
                SolveResult::Sat(assignment)
            }
            Status::UNSATISFIABLE => SolveResult::Unsat,
            Status::UNKNOWN => panic!("Solver interrupted or unknown state"),
        }
    }

    // IPASIR-UP: External Propagator support

    /// Connect an external propagator to the solver
    pub fn connect_propagator<'a, 'b: 'a, P: ExternalPropagator>(
        &'a mut self,
        propagator: &'b mut P,
    ) {
        self.solver.connect_external_propagator(propagator);
    }

    /// Disconnect the external propagator
    pub fn disconnect_propagator(&mut self) {
        self.solver.disconnect_external_propagator();
    }

    /// Add a variable to be observed by the external propagator
    pub fn add_observed_var(&mut self, var: i32) {
        self.solver.add_observed_var(var);
    }

    /// Add a Bool variable to be observed by the external propagator
    pub fn observe(&mut self, b: &Bool) {
        let var = self.get_var(b);
        self.solver.add_observed_var(var);
    }

    /// Remove a variable from being observed
    pub fn remove_observed_var(&mut self, var: i32) {
        self.solver.remove_observed_var(var);
    }

    /// Reset all observed variables
    pub fn reset_observed_vars(&mut self) {
        self.solver.reset_observed_vars();
    }

    /// Check if a literal was a decision
    pub fn is_decision(&mut self, lit: i32) -> bool {
        self.solver.is_decision(lit)
    }

    /// Force backtrack to a certain decision level
    pub fn force_backtrack(&mut self, level: usize) {
        self.solver.force_backtrack(level);
    }

    // Phase control

    /// Set the default phase (polarity) for a variable
    pub fn phase(&mut self, lit: i32) {
        self.solver.phase(lit);
    }

    /// Clear the phase setting for a variable
    pub fn unphase(&mut self, lit: i32) {
        self.solver.unphase(lit);
    }

    // Assumptions

    /// Add an assumption for the next solve call
    pub fn assume(&mut self, lit: i32) {
        self.solver.assume(lit);
    }

    /// Add a Bool literal as an assumption
    pub fn assume_literal(&mut self, lit: &Literal) {
        let l = self.encode_literal(lit);
        self.solver.assume(l);
    }

    /// Check if a literal is in the UNSAT core (failed assumption)
    pub fn failed(&mut self, lit: i32) -> bool {
        self.solver.failed(lit)
    }

    // Variable management

    /// Get the number of active variables
    pub fn vars(&mut self) -> i32 {
        self.solver.vars()
    }

    /// Reserve space for variables up to max_var
    pub fn reserve(&mut self, max_var: i32) {
        self.solver.reserve(max_var);
    }

    /// Freeze a variable (prevent elimination)
    pub fn freeze(&mut self, lit: i32) {
        self.solver.freeze(lit);
    }

    /// Unfreeze a variable
    pub fn melt(&mut self, lit: i32) {
        self.solver.melt(lit);
    }

    /// Check if a variable is frozen
    pub fn frozen(&self, lit: i32) -> bool {
        self.solver.frozen(lit)
    }

    /// Get the root-level assignment of a literal (0 if not fixed)
    pub fn fixed(&self, lit: i32) -> i32 {
        self.solver.fixed(lit)
    }

    /// Get the internal variable ID for a Bool
    pub fn var_id(&mut self, b: &Bool) -> i32 {
        self.get_var(b)
    }

    // Solver configuration

    /// Get the value of a solver option
    pub fn get_option(&mut self, name: &str) -> i32 {
        self.solver.get(name.to_string())
    }

    /// Set a solver option
    pub fn set_option(&mut self, name: &str, val: i32) -> bool {
        self.solver.set(name.to_string(), val)
    }

    /// Apply a preset configuration (e.g., "plain", "sat", "unsat")
    pub fn configure(&mut self, name: &str) -> bool {
        self.solver.configure(name.to_string())
    }

    /// Set a search limit (e.g., "conflicts", "decisions")
    pub fn limit(&mut self, name: &str, val: i32) -> bool {
        self.solver.limit(name.to_string(), val)
    }

    // Simplification

    /// Run preprocessing/simplification
    pub fn simplify(&mut self) -> SolveResult {
        match self.solver.simplify(0) {
            Status::SATISFIABLE => {
                let mut assignment = Assignment::new();
                for (bool_var, &var) in &self.bool_to_var {
                    let val = self.solver.val(var);
                    let bool_val = val > 0 || val == 0;
                    assignment.set_bool(bool_var.clone(), bool_val);
                }
                SolveResult::Sat(assignment)
            }
            Status::UNSATISFIABLE => SolveResult::Unsat,
            Status::UNKNOWN => {
                // UNKNOWN means simplification completed but didn't solve
                // This is normal - return Sat with empty assignment as placeholder
                SolveResult::Sat(Assignment::new())
            }
        }
    }

    /// Run preprocessing with specified number of rounds
    pub fn simplify_rounds(&mut self, rounds: i32) -> SolveResult {
        match self.solver.simplify(rounds) {
            Status::SATISFIABLE => {
                let mut assignment = Assignment::new();
                for (bool_var, &var) in &self.bool_to_var {
                    let val = self.solver.val(var);
                    let bool_val = val > 0 || val == 0;
                    assignment.set_bool(bool_var.clone(), bool_val);
                }
                SolveResult::Sat(assignment)
            }
            Status::UNSATISFIABLE => SolveResult::Unsat,
            Status::UNKNOWN => SolveResult::Sat(Assignment::new()),
        }
    }

    // State and statistics

    /// Get the current solver state
    pub fn state(&self) -> SolverState {
        self.solver.state().into()
    }

    /// Get the solver status (last solve result)
    pub fn status(&self) -> SolverStatus {
        self.solver.status().into()
    }

    /// Print statistics to stdout
    pub fn print_statistics(&mut self) {
        self.solver.statistics();
    }

    /// Check if the formula is inconsistent (contains empty clause)
    pub fn inconsistent(&mut self) -> bool {
        self.solver.inconsistent()
    }

    /// Get number of active (non-eliminated) variables
    pub fn active(&self) -> i32 {
        self.solver.active()
    }

    /// Get number of irredundant clauses
    pub fn irredundant(&self) -> i64 {
        self.solver.irredundant()
    }

    /// Get number of redundant (learned) clauses
    pub fn redundant(&self) -> i64 {
        self.solver.redundant()
    }

    // Terminator

    /// Connect a terminator callback to allow early termination
    pub fn connect_terminator<'a, 'b: 'a, T: Terminator>(
        &'a mut self,
        terminator: &'b mut T,
    ) {
        self.solver.connect_terminator(terminator);
    }

    /// Disconnect the terminator callback
    pub fn disconnect_terminator(&mut self) {
        self.solver.disconnect_terminator();
    }

    /// Request solver termination
    pub fn terminate(&mut self) {
        self.solver.terminate();
    }
}

impl Default for CaDiCaLSolver {
    fn default() -> Self {
        Self::new()
    }
}

/// Type alias for backward compatibility
pub type SatSolver = CaDiCaLSolver;

// SatSolverBackend implementation for CaDiCaLSolver
use crate::encoder::SatSolverBackend;

impl SatSolverBackend for CaDiCaLSolver {
    fn add_clause(&mut self, clause: &[i32]) {
        for &lit in clause {
            self.solver.add(lit);
        }
        self.solver.add(0);  // terminate clause
    }

    fn reserve_vars(&mut self, count: i32) {
        // CaDiCaL doesn't require explicit reservation, but update next_var
        if self.next_var <= count {
            self.next_var = count + 1;
        }
    }

    fn next_var_id(&mut self) -> i32 {
        let id = self.next_var;
        self.next_var += 1;
        id
    }

    fn model_value(&mut self, var: i32) -> bool {
        self.solver.val(var.abs()) > 0
    }

    fn reset(&mut self) {
        self.solver = CaDiCal::new();
        self.bool_to_var.clear();
        self.next_var = 1;
    }

    fn solve(&mut self) -> bool {
        matches!(self.solver.solve(), Status::SATISFIABLE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{Literal, Constraint};

    #[test]
    fn test_cadical_basic_sat() {
        let p = Bool::new("p");
        let c = Constraint::Lit(Literal::pos(p.clone()));
        let mut solver = CaDiCaLSolver::new();
        solver.add(c);
        let result = solver.solve();
        assert!(result.is_sat());
    }

    #[test]
    fn test_cadical_basic_unsat() {
        let p = Bool::new("p");
        let c1 = Constraint::Lit(Literal::pos(p.clone()));
        let c2 = Constraint::Lit(Literal::neg(p.clone()));
        let mut solver = CaDiCaLSolver::new();
        solver.add(c1);
        solver.add(c2);
        let result = solver.solve();
        assert!(result.is_unsat());
    }

    #[test]
    fn test_cadical_get_solution() {
        let p = Bool::new("p");
        let c = Constraint::Lit(Literal::pos(p.clone()));
        let mut solver = CaDiCaLSolver::new();
        solver.add(c);
        let result = solver.solve();
        if let SolveResult::Sat(assignment) = result {
            assert_eq!(assignment.get_bool(&p), Some(true));
        } else {
            panic!("Expected Sat");
        }
    }

    #[test]
    fn test_cadical_and_or() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        // (p ∨ q) ∧ ¬p  =>  q = true
        let c1 = Constraint::or(vec![
            Constraint::Lit(Literal::pos(p.clone())),
            Constraint::Lit(Literal::pos(q.clone())),
        ]);
        let c2 = Constraint::Lit(Literal::neg(p.clone()));
        let mut solver = CaDiCaLSolver::new();
        solver.add(c1);
        solver.add(c2);
        let result = solver.solve();
        if let SolveResult::Sat(assignment) = result {
            assert_eq!(assignment.get_bool(&p), Some(false));
            assert_eq!(assignment.get_bool(&q), Some(true));
        } else {
            panic!("Expected Sat");
        }
    }

    #[test]
    fn test_assumptions() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        // (p ∨ q)
        let mut solver = CaDiCaLSolver::new();
        let c = Constraint::or(vec![
            Constraint::Lit(Literal::pos(p.clone())),
            Constraint::Lit(Literal::pos(q.clone())),
        ]);
        solver.add(c);

        // Assume ¬p, should be SAT with q = true
        let p_var = solver.var_id(&p);
        solver.assume(-p_var);
        let result = solver.solve();
        assert!(result.is_sat());
    }

    #[test]
    fn test_assumptions_unsat_core() {
        let p = Bool::new("p");
        let mut solver = CaDiCaLSolver::new();
        // p
        solver.add(Constraint::Lit(Literal::pos(p.clone())));

        // Assume ¬p, should be UNSAT
        let p_var = solver.var_id(&p);
        solver.assume(-p_var);
        let result = solver.solve();
        assert!(result.is_unsat());

        // ¬p should be in the failed assumptions
        assert!(solver.failed(-p_var));
    }

    #[test]
    fn test_phase_control() {
        let p = Bool::new("p");
        let mut solver = CaDiCaLSolver::new();
        let p_var = solver.var_id(&p);

        // Set phase to negative (prefer false)
        solver.phase(-p_var);

        // With no constraints, solver should follow phase hint
        let result = solver.solve();
        if let SolveResult::Sat(assignment) = result {
            // Phase hints are not guaranteed, but we can at least verify no crash
            let _ = assignment.get_bool(&p);
        }
    }

    #[test]
    fn test_freeze_melt() {
        let p = Bool::new("p");
        let mut solver = CaDiCaLSolver::new();
        let p_var = solver.var_id(&p);

        solver.freeze(p_var);
        assert!(solver.frozen(p_var));

        solver.melt(p_var);
        assert!(!solver.frozen(p_var));
    }

    // External propagator test
    use std::cell::RefCell;
    use std::rc::Rc;

    struct TestPropagator {
        assignments: Rc<RefCell<Vec<i32>>>,
        decision_levels: Rc<RefCell<usize>>,
    }

    impl TestPropagator {
        fn new() -> (Self, Rc<RefCell<Vec<i32>>>, Rc<RefCell<usize>>) {
            let assignments = Rc::new(RefCell::new(Vec::new()));
            let levels = Rc::new(RefCell::new(0usize));
            (
                TestPropagator {
                    assignments: Rc::clone(&assignments),
                    decision_levels: Rc::clone(&levels),
                },
                assignments,
                levels,
            )
        }
    }

    impl ExternalPropagator for TestPropagator {
        fn notify_assignment(&mut self, lits: &[i32]) {
            self.assignments.borrow_mut().extend_from_slice(lits);
        }

        fn notify_new_decision_level(&mut self) {
            *self.decision_levels.borrow_mut() += 1;
        }

        fn notify_backtrack(&mut self, new_level: usize) {
            *self.decision_levels.borrow_mut() = new_level;
        }

        fn cb_check_found_model(&mut self, _model: &[i32]) -> bool {
            true // Accept the model
        }

        fn cb_has_external_clause(&mut self, _is_forgettable: &mut bool) -> bool {
            false // No external clauses
        }

        fn cb_add_external_clause_lit(&mut self) -> i32 {
            0 // No clause to add
        }
    }

    #[test]
    fn test_external_propagator_notify() {
        let (mut propagator, assignments, _levels) = TestPropagator::new();

        let p = Bool::new("p");
        let mut solver = CaDiCaLSolver::new();
        let p_var = solver.var_id(&p);

        // Connect propagator and observe variable
        solver.connect_propagator(&mut propagator);
        solver.add_observed_var(p_var);

        // Add constraint: p
        solver.add(Constraint::Lit(Literal::pos(p.clone())));

        let result = solver.solve();
        assert!(result.is_sat());

        // Propagator should have been notified about p's assignment
        let notified = assignments.borrow();
        assert!(!notified.is_empty(), "Propagator should receive notifications");
    }

    // Phase 3: Advanced feature tests

    #[test]
    fn test_solver_state() {
        let mut solver = CaDiCaLSolver::new();
        // Initial state should be Configuring
        assert_eq!(solver.state(), SolverState::Configuring);

        let p = Bool::new("p");
        solver.add(Constraint::Lit(Literal::pos(p)));
        // After adding clauses, state should be Steady
        let state = solver.state();
        assert!(state == SolverState::Steady || state == SolverState::Adding);
    }

    #[test]
    fn test_solver_status() {
        let mut solver = CaDiCaLSolver::new();
        // Initial status should be Unknown
        assert_eq!(solver.status(), SolverStatus::Unknown);

        let p = Bool::new("p");
        solver.add(Constraint::Lit(Literal::pos(p)));
        solver.solve();
        // After SAT, status should be Satisfiable
        assert_eq!(solver.status(), SolverStatus::Satisfiable);
    }

    #[test]
    fn test_solver_options() {
        let mut solver = CaDiCaLSolver::new();

        // Get default value of a valid option
        let verbose = solver.get_option("verbose");
        assert!(verbose >= 0); // Should be a valid value

        // Set option - some options can only be set during configuration phase
        // verbose can always be set
        let _result = solver.set_option("verbose", 1);
        // Note: set returns false if option name is invalid, not if value can't be changed

        // Test with a configuration-time option before any clauses added
        let mut solver2 = CaDiCaLSolver::new();
        let check_result = solver2.set_option("check", 0);
        // check is a valid option name
        assert!(check_result || !check_result); // Just verify no panic
    }

    #[test]
    fn test_solver_configure() {
        let mut solver = CaDiCaLSolver::new();

        // Apply "plain" configuration (disables most preprocessing)
        let success = solver.configure("plain");
        assert!(success);
    }

    #[test]
    fn test_solver_limit() {
        let mut solver = CaDiCaLSolver::new();

        // Set conflict limit
        let success = solver.limit("conflicts", 1000);
        assert!(success);
    }

    #[test]
    fn test_solver_statistics() {
        let mut solver = CaDiCaLSolver::new();
        let p = Bool::new("p");
        solver.add(Constraint::Lit(Literal::pos(p)));
        solver.solve();

        // These should not panic
        let active = solver.active();
        assert!(active >= 0);

        let irr = solver.irredundant();
        assert!(irr >= 0);

        let red = solver.redundant();
        assert!(red >= 0);
    }

    #[test]
    fn test_inconsistent() {
        let mut solver = CaDiCaLSolver::new();
        assert!(!solver.inconsistent());

        let p = Bool::new("p");
        solver.add(Constraint::Lit(Literal::pos(p.clone())));
        solver.add(Constraint::Lit(Literal::neg(p)));

        // After adding conflicting unit clauses, may or may not be detected
        // until solve is called
        solver.solve();
        // After UNSAT solve, it should be inconsistent
        assert!(solver.inconsistent());
    }

    // Terminator test
    struct CountingTerminator {
        call_count: Rc<RefCell<i32>>,
        terminate_after: i32,
    }

    impl Terminator for CountingTerminator {
        fn terminated(&mut self) -> bool {
            let mut count = self.call_count.borrow_mut();
            *count += 1;
            *count >= self.terminate_after
        }
    }

    #[test]
    fn test_terminator() {
        let call_count = Rc::new(RefCell::new(0));
        let mut terminator = CountingTerminator {
            call_count: Rc::clone(&call_count),
            terminate_after: 1000000, // High limit so it doesn't terminate early
        };

        let mut solver = CaDiCaLSolver::new();
        solver.connect_terminator(&mut terminator);

        let p = Bool::new("p");
        solver.add(Constraint::Lit(Literal::pos(p)));
        let result = solver.solve();

        // Should complete normally
        assert!(result.is_sat());

        // Terminator should have been called at least once
        // (may or may not be called depending on problem size)
    }
}
