use cadical_sys::CaDiCal;

fn main() {
    let mut solver = CaDiCal::new();
    
    // Try to add a simple clause
    solver.add(1);
    solver.add(2);
    solver.add(0);
    
    // Check what methods are available
    // Print the solver's state (we need to check what's available)
    println!("Solver created");
    
    // Let's see what we can call
    // Check if there's a num_vars or num_clauses method
}
