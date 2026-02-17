use crate::graph::Graph;
use cp4rust::encoder::OrderEncoderLe;
use cp4rust::{CaDiCaLSolver, Bool, Constraint, Encoder, CSP};
use std::sync::atomic::{AtomicUsize, Ordering};

static MDS_TRANS_SOLVE_COUNT: AtomicUsize = AtomicUsize::new(0);

pub struct MdsSolverTrans {
    graph: Graph,
}

impl MdsSolverTrans {
    pub fn new(graph: Graph) -> Self {
        MdsSolverTrans { graph }
    }

    pub fn get_solve_count() -> usize {
        MDS_TRANS_SOLVE_COUNT.load(Ordering::SeqCst)
    }

    pub fn reset_solve_count() {
        MDS_TRANS_SOLVE_COUNT.store(0, Ordering::SeqCst);
    }

    /// Build CSP with optional minimality constraints
    /// include_minimality: if true, add minimality constraints; if false, only add domination
    fn build_csp(&self, include_minimality: bool) -> (CSP, Vec<Bool>) {
        let mut csp = CSP::new();

        // Create Bool variables for each vertex
        let x: Vec<Bool> = (0..self.graph.num_vertices)
            .map(|v| csp.bool_var(&format!("x{}", v)))
            .collect();

        // Constraint 1: Domination constraints
        // For each vertex v: x_v ∨ (∨_{u ∈ N(v)} x_u)
        for v in 0..self.graph.num_vertices {
            let mut clause: Vec<Constraint> = vec![Constraint::from(&x[v])];
            for &u in self.graph.neighbors(v) {
                clause.push(Constraint::from(&x[u]));
            }
            csp.add(Constraint::or(clause));
        }

        // Constraint 2: Minimality constraints (if enabled)
        if include_minimality {
            for v in 0..self.graph.num_vertices {
                let mut cc_clauses: Vec<Constraint> = Vec::new();

                // From v's own domination clause: ∨_{u ∈ N(v)} x_u
                let neighbors_v: Vec<Constraint> = self
                    .graph
                    .neighbors(v)
                    .iter()
                    .map(|&u| Constraint::from(&x[u]))
                    .collect();
                if !neighbors_v.is_empty() {
                    cc_clauses.push(Constraint::or(neighbors_v));
                } else {
                    // v has no neighbors, skip
                    continue;
                }

                // From each neighbor u's domination clause: x_u ∨ (∨_{w ∈ N(u), w ≠ v} x_w)
                for &u in self.graph.neighbors(v) {
                    let mut clause_u: Vec<Constraint> = vec![Constraint::from(&x[u])];
                    for &w in self.graph.neighbors(u) {
                        if w != v {
                            clause_u.push(Constraint::from(&x[w]));
                        }
                    }
                    cc_clauses.push(Constraint::or(clause_u));
                }

                // Minimality constraint: (∧ CC(x_v)) → ¬x_v
                let cc_and = Constraint::and(cc_clauses);
                let not_x_v = !Constraint::from(&x[v]);
                csp.add(cc_and.implies(not_x_v));
            }
        }

        (csp, x)
    }

    /// Count CNF statistics by actually encoding the CSP
    fn count_cnf_stats(&self, csp: &CSP) -> (i32, i32) {
        let backend = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, backend);
        encoder.encode_csp();

        let vars = encoder.state().sat_variable_count as i32;
        let clauses = encoder.state().sat_clause_count as i32;
        (vars, clauses)
    }

    pub fn enumerate_minimal(&self) -> (Vec<Vec<usize>>, (i32, i32), (i32, i32)) {
        // Return (results, (orig_vars, orig_clauses), (encoded_vars, encoded_clauses))
        
        // Measure orig stats (domination only)
        let (csp_orig, _) = self.build_csp(false);
        let (orig_vars, orig_clauses) = self.count_cnf_stats(&csp_orig);

        // Build the full CSP with minimality constraints for solving
        let (mut csp, x) = self.build_csp(true);

        // Encode and measure encoded stats
        let backend = CaDiCaLSolver::new();
        let mut encoder = OrderEncoderLe::new(&csp, backend);
        encoder.encode_csp();

        let encoded_vars = encoder.state().sat_variable_count as i32;
        let encoded_clauses = encoder.state().sat_clause_count as i32;

        // Get the bool code map before moving solver
        let bool_codes: Vec<i32> = x
            .iter()
            .map(|b| *encoder.state().bool_code_map.get(b).unwrap())
            .collect();

        // Ensure num_vars is set correctly (encoder may have added Tseitin auxiliary vars)
        let total_vars = encoder.state().sat_variable_count;
        let solver = encoder.backend_mut();
        solver.set_num_vars(total_vars);

        // Get all solutions using CaDiCaLSolver
        let all_sols = solver.all_solutions();
        
        // Count each unique solution found (mirrors basic solver behavior)
        // where each solution discovery involves solver invocation(s)
        let unique_sol_count = all_sols.len();
        for _ in 0..unique_sol_count {
            MDS_TRANS_SOLVE_COUNT.fetch_add(1, Ordering::SeqCst);
        }
        
        if all_sols.is_empty() {
            return (
                Vec::new(),
                (orig_vars, orig_clauses),
                (encoded_vars, encoded_clauses),
            );
        }

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

        (
            results,
            (orig_vars, orig_clauses),
            (encoded_vars, encoded_clauses),
        )
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
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        assert_eq!(results.len(), 1);
        assert_eq!(results[0], vec![0]);
        assert!(is_minimal(&g, &results[0]));
    }

    #[test]
    fn test_two_isolated_vertices() {
        let g = Graph::new(2);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        assert_eq!(results.len(), 1);
        assert!(results[0].contains(&0));
        assert!(results[0].contains(&1));
        assert!(is_minimal(&g, &results[0]));
    }

    #[test]
    fn test_single_edge() {
        let mut g = Graph::new(2);
        g.add_edge(0, 1);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

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
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        assert_eq!(results.len(), 3);
        for r in &results {
            assert_eq!(r.len(), 1);
            assert!(is_minimal(&g, r));
        }
    }

    #[test]
    fn test_path_3() {
        let mut g = Graph::new(3);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_minimal(&g, r));
        }
    }

    #[test]
    fn test_path_4() {
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        for r in &results {
            assert!(is_minimal(&g, r), "Not minimal: {:?}", r);
        }
        assert_eq!(results.len(), 4);
    }

    #[test]
    fn test_square() {
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 0);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        assert_eq!(results.len(), 6);
        for r in &results {
            assert!(is_minimal(&g, r));
            assert_eq!(r.len(), 2);
        }
    }

    #[test]
    fn test_star_4() {
        let mut g = Graph::new(4);
        g.add_edge(0, 1);
        g.add_edge(0, 2);
        g.add_edge(0, 3);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        assert_eq!(results.len(), 2);
        for r in &results {
            assert!(is_minimal(&g, r));
        }
    }

    #[test]
    fn test_all_results_are_dominating() {
        let mut g = Graph::new(5);
        g.add_edge(0, 1);
        g.add_edge(1, 2);
        g.add_edge(2, 3);
        g.add_edge(3, 4);
        g.add_edge(4, 0);
        let solver = MdsSolverTrans::new(g.clone());
        let (results, _, _) = solver.enumerate_minimal();

        for r in &results {
            assert!(is_dominating_set(&g, r), "Not a dominating set: {:?}", r);
            assert!(is_minimal(&g, r), "Not minimal: {:?}", r);
        }
    }
}
