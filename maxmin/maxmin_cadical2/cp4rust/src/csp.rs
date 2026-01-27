// CSP (Constraint Satisfaction Problem) container

use crate::expr::{Bool, Var, Constraint};
use crate::domain::Domain;

/// CSP container: holds variables, domains, and constraints
#[derive(Debug, Clone)]
pub struct CSP {
    int_vars: Vec<(Var, Domain)>,
    bool_vars: Vec<Bool>,
    constraints: Vec<Constraint>,
}

impl CSP {
    pub fn new() -> Self {
        CSP {
            int_vars: vec![],
            bool_vars: vec![],
            constraints: vec![],
        }
    }

    pub fn int_var(&mut self, name: &str, domain: Domain) -> Var {
        let v = Var::new(name);
        self.int_vars.push((v.clone(), domain));
        v
    }

    pub fn bool_var(&mut self, name: &str) -> Bool {
        let b = Bool::new(name);
        self.bool_vars.push(b.clone());
        b
    }

    pub fn add(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    pub fn num_int_vars(&self) -> usize {
        self.int_vars.len()
    }

    pub fn num_bool_vars(&self) -> usize {
        self.bool_vars.len()
    }

    pub fn num_constraints(&self) -> usize {
        self.constraints.len()
    }

    /// Get all integer variables with their domains
    pub fn int_vars(&self) -> &[(Var, Domain)] {
        &self.int_vars
    }

    /// Get all boolean variables
    pub fn bool_vars(&self) -> &[Bool] {
        &self.bool_vars
    }

    /// Get all constraints
    pub fn constraints(&self) -> &[Constraint] {
        &self.constraints
    }

    /// Get domain of an integer variable
    pub fn domain(&self, var: &Var) -> Option<&Domain> {
        self.int_vars.iter()
            .find(|(v, _)| v == var)
            .map(|(_, d)| d)
    }
}

impl Default for CSP {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Sum;

    #[test]
    fn test_csp_new() {
        let csp = CSP::new();
        assert_eq!(csp.num_int_vars(), 0);
        assert_eq!(csp.num_bool_vars(), 0);
        assert_eq!(csp.num_constraints(), 0);
    }

    #[test]
    fn test_csp_add_int_var() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        assert_eq!(csp.num_int_vars(), 1);
        assert_eq!(x.name(), "x");
    }

    #[test]
    fn test_csp_add_bool_var() {
        let mut csp = CSP::new();
        let p = csp.bool_var("p");
        assert_eq!(csp.num_bool_vars(), 1);
        assert_eq!(p.name(), "p");
    }

    #[test]
    fn test_csp_add_constraint() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        let c = Sum::from(x).le(5);
        csp.add(c);
        assert_eq!(csp.num_constraints(), 1);
    }

    #[test]
    fn test_csp_int_vars() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));
        let y = csp.int_var("y", Domain::range(0, 5));

        let vars = csp.int_vars();
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0].0, x);
        assert_eq!(vars[1].0, y);
    }

    #[test]
    fn test_csp_bool_vars() {
        let mut csp = CSP::new();
        let p = csp.bool_var("p");
        let q = csp.bool_var("q");

        let vars = csp.bool_vars();
        assert_eq!(vars.len(), 2);
        assert_eq!(vars[0], p);
        assert_eq!(vars[1], q);
    }

    #[test]
    fn test_csp_domain() {
        let mut csp = CSP::new();
        let x = csp.int_var("x", Domain::range(1, 10));

        let dom = csp.domain(&x);
        assert!(dom.is_some());
        assert_eq!(dom.unwrap().lb(), 1);
        assert_eq!(dom.unwrap().ub(), 10);

        let unknown = Var::new("unknown");
        assert!(csp.domain(&unknown).is_none());
    }
}
