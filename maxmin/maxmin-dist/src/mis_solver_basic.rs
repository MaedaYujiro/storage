use cadical_sys::{CaDiCal, Status};
use crate::graph::Graph;
use std::sync::atomic::{AtomicUsize, Ordering};

static MIS_BASIC_SOLVE_COUNT: AtomicUsize = AtomicUsize::new(0);

pub struct MisSolverBasic {
    graph: Graph,
}

impl MisSolverBasic {
    pub fn new(graph: Graph) -> Self {
        MisSolverBasic { graph }
    }

    fn var(&self, v: usize) -> i32 {
        (v + 1) as i32
    }

    fn create_solver_with_is_constraints(&self) -> CaDiCal {
        let mut solver = CaDiCal::new();
        // For each edge (u, v), add clause: ¬x_u ∨ ¬x_v
        for u in 0..self.graph.num_vertices {
            for &v in self.graph.neighbors(u) {
                if u < v {
                    let lit_u = self.var(u);
                    let lit_v = self.var(v);
                    solver.clause2(-lit_u, -lit_v);
                }
            }
        }
        solver
    }

    /// Compute a single maximal independent set starting from the current solver state.
    /// Returns None if no maximal independent set exists with current constraints.
    fn compute_single_maximal(&self, solver: &mut CaDiCal) -> Option<Vec<usize>> {
        let mut last_solution: Option<Vec<usize>> = None;
        loop {
            MIS_BASIC_SOLVE_COUNT.fetch_add(1, Ordering::SeqCst);
            let status = solver.solve();
            if status != Status::SATISFIABLE {
                return last_solution;
            }

            // Extract L+ and L- from current model
            let positive_lits: Vec<usize> = (0..self.graph.num_vertices)
                .filter(|&v| solver.val(self.var(v)) > 0)
                .collect();
            let negative_lits: Vec<usize> = (0..self.graph.num_vertices)
                .filter(|&v| solver.val(self.var(v)) < 0)
                .collect();
            last_solution = Some(positive_lits.clone());

            // If L- is empty, current model is maximal
            if negative_lits.is_empty() {
                return Some(positive_lits);
            }

            // Add blocking clauses to extend toward maximality
            // L+ as unit clauses (must include all of them)
            for &v in &positive_lits {
                solver.clause1(self.var(v));
            }

            // L- as one clause (must include at least one)
            for &v in &negative_lits {
                solver.add(self.var(v));
            }
            solver.add(0);
        }
    }

    pub fn get_cnf_stats(&self) -> (i32, i32) {
        // Return (num_vars, num_clauses)
        // Each vertex has one variable
        let num_vars = self.graph.num_vertices as i32;
        
        // For each edge (u, v): ¬x_u ∨ ¬x_v (one clause per edge)
        let num_clauses = self.graph.num_edges as i32;
        
        (num_vars, num_clauses)
    }

    pub fn get_solve_count() -> usize {
        MIS_BASIC_SOLVE_COUNT.load(Ordering::SeqCst)
    }

    pub fn reset_solve_count() {
        MIS_BASIC_SOLVE_COUNT.store(0, Ordering::SeqCst);
    }

    pub fn enumerate_maximal(&self) -> Vec<Vec<usize>> {
        let mut results: Vec<Vec<usize>> = Vec::new();

        loop {
            let mut solver = self.create_solver_with_is_constraints();

            // Add blocking clauses for already found maximal sets
            for found_set in &results {
                // Block: must include at least one vertex not in found_set
                for v in 0..self.graph.num_vertices {
                    if !found_set.contains(&v) {
                        solver.add(self.var(v));
                    }
                }
                solver.add(0);
            }

            match self.compute_single_maximal(&mut solver) {
                Some(mut maximal_set) => {
                    maximal_set.sort();
                    if !results.contains(&maximal_set) {
                        results.push(maximal_set);
                    } else {
                        break;
                    }
                }
                None => break,
            }
        }

        results
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn is_independent_set(graph: &Graph, set: &[usize]) -> bool {
        for (i, &u) in set.iter().enumerate() {
            for &v in &set[i + 1..] {
                if graph.neighbors(u).contains(&v) {
                    return false;
                }
            }
        }
        true
    }

    fn is_maximal(graph: &Graph, set: &[usize]) -> bool {
        if !is_independent_set(graph, set) {
            return false;
        }
        // Check that no vertex can be added
        for v in 0..graph.num_vertices {
            if set.contains(&v) {
                continue;
            }
            let can_add = set.iter().all(|&u| !graph.neighbors(u).contains(&v));
            if can_add {
                return false;
            }
        }
        true
    }

    #[test]
    fn test_single_vertex_graph() {
        let g = Graph::new(1);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![0]);
        assert!(is_maximal(&g, &results[0]));
    }

    #[test]
    fn test_two_isolated_vertices() {
        let g = Graph::new(2);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        // Only one maximal IS: {0, 1}
        assert_eq!(results.len(), 1);
        assert!(results[0].contains(&0));
        assert!(results[0].contains(&1));
        assert!(is_maximal(&g, &results[0]));
    }

    #[test]
    fn test_single_edge() {
        let mut g = Graph::new(2);
        g.add_edge(0, 1);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        // Two maximal IS: {0} and {1}
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_maximal(&g, r));
        }
    }

    #[test]
    fn test_triangle() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(0, 2);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        // Three maximal IS: {0}, {1}, {2}
        assert_eq!(results.len(), 3);
        for r in &results {
            assert_eq!(r.len(), 1);
            assert!(is_maximal(&g, r));
        }
    }

    #[test]
    fn test_path_3() {
        // Path: 0 - 1 - 2
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        // Two maximal IS: {0, 2} and {1}
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_maximal(&g, r));
        }
        // Check {0, 2} is in results
        let has_02 = results.iter().any(|r| r.len() == 2 && r.contains(&0) && r.contains(&2));
        assert!(has_02);
        // Check {1} is in results
        let has_1 = results.iter().any(|r| r == &vec![1]);
        assert!(has_1);
    }

    #[test]
    fn test_square() {
        // Square: 0 - 1 - 2 - 3 - 0
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 0);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        // Two maximal IS: {0, 2} and {1, 3}
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_maximal(&g, r));
            assert_eq!(r.len(), 2);
        }
    }

    #[test]
    fn test_all_results_are_independent() {
        let mut g = Graph::new(5);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 4);
        g.add_edge(4, 0);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        for r in &results {
            assert!(is_independent_set(&g, r), "Not an independent set: {:?}", r);
            assert!(is_maximal(&g, r), "Not maximal: {:?}", r);
        }
    }

    #[test]
    fn test_complete_graph_4() {
        // K4: all vertices connected to each other
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(0, 2);
        g.add_edge(0, 3);
        g.add_edge(1, 2);
        g.add_edge(1, 3);
        g.add_edge(2, 3);
        let solver = MisSolverBasic::new(g.clone());
        let results = solver.enumerate_maximal();

        // Four maximal IS: {0}, {1}, {2}, {3}
        assert_eq!(results.len(), 4);
        for r in &results {
            assert_eq!(r.len(), 1);
            assert!(is_maximal(&g, r));
        }
    }
}
