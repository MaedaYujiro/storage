mod graph;
mod mds_solver_basic;
mod mds_solver_trans;
mod mis_solver_basic;
mod mis_solver_trans;

use graph::Graph;
use mds_solver_basic::MdsSolverBasic;
use mds_solver_trans::MdsSolverTrans;
use mis_solver_basic::MisSolverBasic;
use mis_solver_trans::MisSolverTrans;

fn print_usage(program: &str) {
    eprintln!("Usage: {} <solver> <filename>", program);
    eprintln!();
    eprintln!("Solvers:");
    eprintln!("  mds-basic  Enumerate minimal dominating sets (basic algorithm)");
    eprintln!("  mds-trans  Enumerate minimal dominating sets (trans encoding)");
    eprintln!("  mis-basic  Enumerate maximal independent sets (basic algorithm)");
    eprintln!("  mis-trans  Enumerate maximal independent sets (trans encoding)");
    eprintln!();
    eprintln!("Example:");
    eprintln!("  {} mds-basic graph.col", program);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() < 3 {
        print_usage(&args[0]);
        std::process::exit(1);
    }

    let solver_type = &args[1];
    let filename = &args[2];

    let graph = match Graph::from_dimacs(filename) {
        Ok(g) => g,
        Err(e) => {
            eprintln!("Error loading graph: {}", e);
            std::process::exit(1);
        }
    };

    println!("Graph: {} vertices, {} edges", graph.num_vertices, graph.num_edges);

    let results: Vec<Vec<usize>> = match solver_type.as_str() {
        "mds-basic" => {
            println!("Enumerating minimal dominating sets (basic)...");
            let solver = MdsSolverBasic::new(graph);
            let (vars, clauses) = solver.get_cnf_stats();
            println!("CNF: {} variables, {} clauses", vars, clauses);
            let results = solver.enumerate_minimal();
            println!("Solver invocations: {}", MdsSolverBasic::get_solve_count());
            results
        }
        "mds-trans" => {
            println!("Enumerating minimal dominating sets (trans)...");
            let solver = MdsSolverTrans::new(graph);
            let (results, (orig_vars, orig_clauses), (enc_vars, enc_clauses)) = solver.enumerate_minimal();
            println!("CSP: {} variables, {} clauses", orig_vars, orig_clauses);
            println!("CNF: {} variables, {} clauses", enc_vars, enc_clauses);
            println!("CaDiCal solver invocations: {}", MdsSolverTrans::get_solve_count());
            results
        }
        "mis-basic" => {
            println!("Enumerating maximal independent sets (basic)...");
            let solver = MisSolverBasic::new(graph);
            let (vars, clauses) = solver.get_cnf_stats();
            println!("CNF: {} variables, {} clauses", vars, clauses);
            let results = solver.enumerate_maximal();
            println!("Solver invocations: {}", MisSolverBasic::get_solve_count());
            results
        }
        "mis-trans" => {
            println!("Enumerating maximal independent sets (trans)...");
            let solver = MisSolverTrans::new(graph);
            let (results, (orig_vars, orig_clauses), (enc_vars, enc_clauses)) = solver.enumerate_maximal();
            println!("CSP: {} variables, {} clauses", orig_vars, orig_clauses);
            println!("CNF: {} variables, {} clauses", enc_vars, enc_clauses);
            println!("CaDiCal solver invocations: {}", MisSolverTrans::get_solve_count());
            results
        }
        _ => {
            eprintln!("Unknown solver: {}", solver_type);
            print_usage(&args[0]);
            std::process::exit(1);
        }
    };

    println!();
    println!("Found {} solutions:", results.len());
    for (i, sol) in results.iter().enumerate() {
        println!("  {}: {:?}", i + 1, sol);
    }
}
