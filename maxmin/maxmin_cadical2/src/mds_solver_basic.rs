use crate::graph::Graph;
use cadical_sys::{CaDiCal, Status};
use std::sync::atomic::{AtomicUsize, Ordering};

static MDS_BASIC_SOLVE_COUNT: AtomicUsize = AtomicUsize::new(0);

pub struct MdsSolverBasic {
    graph: Graph,
}

impl MdsSolverBasic {
    pub fn new(graph: Graph) -> Self {
        MdsSolverBasic { graph }
    }

    fn var(&self, v: usize) -> i32 {
        (v + 1) as i32
    }

    fn create_solver_with_ds_constraints(&self) -> CaDiCal {
        let mut solver = CaDiCal::new();
        // For each vertex v, it must be dominated:
        // x_v ∨ (∨_{u ∈ N(v)} x_u)
        for v in 0..self.graph.num_vertices {
            solver.add(self.var(v));
            for &u in self.graph.neighbors(v) {
                solver.add(self.var(u));
            }
            solver.add(0);
        }
        solver
    }

    /// Compute a single minimal dominating set starting from the current solver state.
    /// Returns None if no dominating set exists with current constraints.
    fn compute_single_minimal(&self, solver: &mut CaDiCal) -> Option<Vec<usize>> {
        let mut last_solution: Option<Vec<usize>> = None;
        loop {
            MDS_BASIC_SOLVE_COUNT.fetch_add(1, Ordering::SeqCst);
            let status = solver.solve();
            if status != Status::SATISFIABLE {
                return last_solution;
            }

            // Extract L+ (in dominating set) and L- (not in dominating set)
            let positive_lits: Vec<usize> = (0..self.graph.num_vertices)
                .filter(|&v| solver.val(self.var(v)) > 0)
                .collect();
            let negative_lits: Vec<usize> = (0..self.graph.num_vertices)
                .filter(|&v| solver.val(self.var(v)) < 0)
                .collect();
            last_solution = Some(positive_lits.clone());

            // If L+ is empty, we're done (empty set, only for empty graph)
            if positive_lits.is_empty() {
                return Some(positive_lits);
            }

            // Add blocking clauses to shrink toward minimality
            // L- as unit clauses (must exclude all of them)
            for &v in &negative_lits {
                solver.clause1(-self.var(v));
            }

            // L+ as one clause (must exclude at least one)
            for &v in &positive_lits {
                solver.add(-self.var(v));
            }
            solver.add(0);
        }
    }

    pub fn get_cnf_stats(&self) -> (i32, i32) {
        // Return (num_vars, num_clauses)
        // Each vertex has one variable
        let num_vars = self.graph.num_vertices as i32;

        // Domination constraint for each vertex: x_v ∨ (∨_{u ∈ N(v)} x_u)
        // This becomes one clause per vertex
        let num_clauses = self.graph.num_vertices as i32;

        (num_vars, num_clauses)
    }

    pub fn get_solve_count() -> usize {
        MDS_BASIC_SOLVE_COUNT.load(Ordering::SeqCst)
    }

    pub fn reset_solve_count() {
        MDS_BASIC_SOLVE_COUNT.store(0, Ordering::SeqCst);
    }

    pub fn enumerate_minimal(&self) -> Vec<Vec<usize>> {
        let mut results: Vec<Vec<usize>> = Vec::new();

        loop {
            let mut solver = self.create_solver_with_ds_constraints();

            // Add blocking clauses for already found minimal sets
            for found_set in &results {
                // Block: must exclude at least one vertex from found_set
                // (ensures next solution is not a superset of found_set)
                for &v in found_set {
                    solver.add(-self.var(v));
                }
                solver.add(0);
            }

            match self.compute_single_minimal(&mut solver) {
                Some(mut minimal_set) => {
                    minimal_set.sort();
                    if !results.contains(&minimal_set) {
                        results.push(minimal_set);
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

    fn is_dominating_set(graph: &Graph, set: &[usize]) -> bool {
        for v in 0..graph.num_vertices {
            if set.contains(&v) {
                continue;
            }
            // v must have at least one neighbor in set
            let has_neighbor_in_set = graph.neighbors(v).iter().any(|&u| set.contains(&u));
            if !has_neighbor_in_set {
                return false;
            }
        }
        true
    }

    fn is_minimal(graph: &Graph, set: &[usize]) -> bool {
        if !is_dominating_set(graph, set) {
            return false;
        }
        // Check that removing any vertex breaks domination
        for &v in set {
            let subset: Vec<usize> = set.iter().filter(|&&u| u != v).copied().collect();
            if is_dominating_set(graph, &subset) {
                return false;
            }
        }
        true
    }

    #[test]
    fn test_single_vertex_graph() {
        let g = Graph::new(1);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![0]);
        assert!(is_minimal(&g, &results[0]));
    }

    #[test]
    fn test_two_isolated_vertices() {
        let g = Graph::new(2);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // Only one minimal DS: {0, 1} (each must dominate itself)
        assert_eq!(results.len(), 1);
        assert!(results[0].contains(&0));
        assert!(results[0].contains(&1));
        assert!(is_minimal(&g, &results[0]));
    }

    #[test]
    fn test_single_edge() {
        let mut g = Graph::new(2);
        g.add_edge(0, 1);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // Two minimal DS: {0} and {1}
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_minimal(&g, r));
            assert_eq!(r.len(), 1);
        }
    }

    #[test]
    fn test_triangle() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(0, 2);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // Three minimal DS: {0}, {1}, {2}
        assert_eq!(results.len(), 3);
        for r in &results {
            assert_eq!(r.len(), 1);
            assert!(is_minimal(&g, r));
        }
    }

    #[test]
    fn test_path_3() {
        // Path: 0 - 1 - 2
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // Two minimal DS: {1} and {0, 2}
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_minimal(&g, r));
        }
        let has_1 = results.iter().any(|r| r == &vec![1]);
        assert!(has_1);
        let has_02 = results
            .iter()
            .any(|r| r.len() == 2 && r.contains(&0) && r.contains(&2));
        assert!(has_02);
    }

    #[test]
    fn test_path_4() {
        // Path: 0 - 1 - 2 - 3
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // Minimal DS: {0, 2}, {0, 3}, {1, 2}, {1, 3}
        for r in &results {
            assert!(is_minimal(&g, r), "Not minimal: {:?}", r);
        }
        assert_eq!(results.len(), 4);
    }

    #[test]
    fn test_square() {
        // Square: 0 - 1 - 2 - 3 - 0
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 0);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // All pairs are minimal DS: {0,1}, {1,2}, {2,3}, {0,3}, {0,2}, {1,3}
        assert_eq!(results.len(), 6);
        for r in &results {
            assert!(is_minimal(&g, r));
            assert_eq!(r.len(), 2);
        }
    }

    #[test]
    fn test_star_4() {
        // Star: 0 connected to 1, 2, 3
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(0, 2);
        g.add_edge(0, 3);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        // Minimal DS: {0} (center dominates all) and {1, 2, 3} (leaves dominate center)
        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_minimal(&g, r));
        }
        let has_center = results.iter().any(|r| r == &vec![0]);
        assert!(has_center);
        let has_leaves = results.iter().any(|r| r.len() == 3);
        assert!(has_leaves);
    }

    #[test]
    fn test_all_results_are_dominating() {
        let mut g = Graph::new(5);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 4);
        g.add_edge(4, 0);
        let solver = MdsSolverBasic::new(g.clone());
        let results = solver.enumerate_minimal();

        for r in &results {
            assert!(is_dominating_set(&g, r), "Not a dominating set: {:?}", r);
            assert!(is_minimal(&g, r), "Not minimal: {:?}", r);
        }
    }
}
