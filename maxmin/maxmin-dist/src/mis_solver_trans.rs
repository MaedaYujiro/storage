use cp4rust::{CSP, Bool, Constraint, BddMinisatSolver, Encoder};
use cp4rust::encoder::OrderEncoderLe;
use crate::graph::Graph;
use std::sync::atomic::{AtomicUsize, Ordering};

static MIS_TRANS_SOLVE_COUNT: AtomicUsize = AtomicUsize::new(0);

pub struct MisSolverTrans {
    graph: Graph,
}

impl MisSolverTrans {
    pub fn new(graph: Graph) -> Self {
        MisSolverTrans { graph }
    }

    pub fn get_solve_count() -> usize {
        MIS_TRANS_SOLVE_COUNT.load(Ordering::SeqCst)
    }

    pub fn reset_solve_count() {
        MIS_TRANS_SOLVE_COUNT.store(0, Ordering::SeqCst);
    }

    pub fn enumerate_maximal(&self) -> (Vec<Vec<usize>>, (i32, i32), (i32, i32)) {
        // Return (results, (orig_vars, orig_clauses), (encoded_vars, encoded_clauses))
        let mut csp = CSP::new();

        // Create Bool variables for each vertex
        let x: Vec<Bool> = (0..self.graph.num_vertices)
            .map(|v| csp.bool_var(&format!("x{}", v)))
            .collect();

        // Constraint 1: Independent set constraints
        // For each edge (u, v): ¬x_u ∨ ¬x_v
        for u in 0..self.graph.num_vertices {
            for &v in self.graph.neighbors(u) {
                if u < v {
                    let not_x_u = !Constraint::from(&x[u]);
                    let not_x_v = !Constraint::from(&x[v]);
                    csp.add(Constraint::or(vec![not_x_u, not_x_v]));
                }
            }
        }

        // Constraint 2: Maximality constraints
        // For each vertex v: CC(¬x_v) → x_v
        // CC(¬x_v) = clauses containing ¬x_v with ¬x_v removed
        // ¬x_v appears in IS clauses for edges incident to v
        // From edge (u, v): ¬x_u ∨ ¬x_v, removing ¬x_v gives ¬x_u
        // So CC(¬x_v) = {¬x_u : u ∈ N(v)}
        // The constraint is: (∧_{u ∈ N(v)} ¬x_u) → x_v
        for v in 0..self.graph.num_vertices {
            let neighbors: Vec<&usize> = self.graph.neighbors(v).iter().collect();

            if neighbors.is_empty() {
                // Isolated vertex must be in any maximal IS
                csp.add(Constraint::from(&x[v]));
                continue;
            }

            // CC(¬x_v): conjunction of ¬x_u for all neighbors u
            let cc_clauses: Vec<Constraint> = neighbors
                .iter()
                .map(|&&u| !Constraint::from(&x[u]))
                .collect();

            // Maximality constraint: (∧ CC(¬x_v)) → x_v
            let cc_and = Constraint::and(cc_clauses);
            let x_v = Constraint::from(&x[v]);
            csp.add(cc_and.implies(x_v));
        }

        // Original CSP statistics
        let orig_vars = self.graph.num_vertices as i32;
        let orig_clauses = self.graph.num_edges as i32;

        // Encode and solve using BddMinisatSolver
        let backend = BddMinisatSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, backend);
        encoder.encode_csp();

        let encoded_vars = encoder.state().sat_variable_count as i32;
        let encoded_clauses = encoder.state().sat_clause_count as i32;

        // Get the bool code map before moving solver
        let bool_codes: Vec<i32> = x.iter()
            .map(|b| *encoder.state().bool_code_map.get(b).unwrap())
            .collect();

        // Ensure num_vars is set correctly (encoder may have added Tseitin auxiliary vars)
        let total_vars = encoder.state().sat_variable_count;
        let solver = encoder.backend_mut();
        solver.set_num_vars(total_vars);

        MIS_TRANS_SOLVE_COUNT.fetch_add(1, Ordering::SeqCst);
        if !solver.solve() {
            return (Vec::new(), (orig_vars, orig_clauses), (encoded_vars, encoded_clauses));
        }

        // Get all solutions
        let all_sols = solver.all_solutions();

        // Convert solutions to vertex sets, projecting to original Bool variables
        // and deduplicating (since Tseitin auxiliary variables create multiple solutions)
        let mut results: Vec<Vec<usize>> = Vec::new();
        for sol in all_sols {
            let mut set: Vec<usize> = Vec::new();
            for v in 0..self.graph.num_vertices {
                // Get the SAT variable index (1-based code, convert to 0-based index)
                let sat_idx = (bool_codes[v] - 1) as usize;
                if sat_idx < sol.len() && sol[sat_idx] {
                    set.push(v);
                }
            }
            // Deduplicate: only add if not already present
            if !results.contains(&set) {
                results.push(set);
            }
        }

        (results, (orig_vars, orig_clauses), (encoded_vars, encoded_clauses))
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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![0]);
        assert!(is_maximal(&g, &results[0]));
    }

    #[test]
    fn test_two_isolated_vertices() {
        let g = Graph::new(2);
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

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
        let solver = MisSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_maximal();

        // Four maximal IS: {0}, {1}, {2}, {3}
        assert_eq!(results.len(), 4);
        for r in &results {
            assert_eq!(r.len(), 1);
            assert!(is_maximal(&g, r));
        }
    }
}
