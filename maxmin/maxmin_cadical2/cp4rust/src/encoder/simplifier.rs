// Simplifier: Convert constraints to CNF using Tseitin transformation
// Corresponds to Scarab's Simplifier class

use crate::{Literal, Constraint};
use super::Encoder;

/// Simplifier: transforms constraints into CNF form
/// Scarab: class Simplifier(val encoder: Encoder)
pub struct Simplifier<'a, E: Encoder + ?Sized> {
    encoder: &'a mut E,
}

impl<'a, E: Encoder + ?Sized> Simplifier<'a, E> {
    pub fn new(encoder: &'a mut E) -> Self {
        Self { encoder }
    }

    /// Flatten nested Or constraints
    /// Scarab: flattenOr(c: Constraint): Seq[Constraint]
    pub fn flatten_or(&self, c: &Constraint) -> Vec<Constraint> {
        match c {
            Constraint::Or(cs) => {
                cs.iter().flat_map(|ci| self.flatten_or(ci)).collect()
            }
            _ => vec![c.clone()],
        }
    }

    /// Check if a literal is "simple" (single variable coefficient)
    /// Scarab: isSimpleLiteral(lit: Literal): Boolean
    pub fn is_simple_literal(&self, lit: &Constraint) -> bool {
        match lit {
            Constraint::Lit(_) => true,
            Constraint::LeZero(sum) | Constraint::GeZero(sum) |
            Constraint::EqZero(sum) | Constraint::NeZero(sum) => {
                sum.terms().len() <= 1
            }
            _ => false,
        }
    }

    /// Check if a clause is "simple" (at most one complex literal)
    /// Scarab: isSimpleClause(lits: Seq[Literal]): Boolean
    pub fn is_simple_clause(&self, lits: &[Constraint]) -> bool {
        lits.iter().filter(|lit| !self.is_simple_literal(lit)).count() <= 1
    }

    /// Tseitin transformation: introduce auxiliary variable for complex constraint
    /// Scarab: tseitin(c: Constraint): (Literal, Seq[Or])
    /// Returns (auxiliary literal, additional clauses)
    pub fn tseitin(&mut self, c: &Constraint) -> (Constraint, Vec<Constraint>) {
        match c {
            c if c.is_literal() => (c.clone(), vec![]),
            Constraint::And(cs) => {
                let p = self.encoder.state_mut().new_aux_bool();
                // Register the auxiliary variable
                let code = self.encoder.state().sat_variable_count + 1;
                self.encoder.state_mut().bool_code_map.insert(p.clone(), code);
                self.encoder.state_mut().sat_variable_count += 1;

                let p_lit = Constraint::Lit(Literal::pos(p.clone()));
                let not_p = Constraint::Lit(Literal::neg(p));
                // p -> (c1 & c2 & ...) means (!p | c1) & (!p | c2) & ...
                let clauses = cs.iter()
                    .map(|ci| Constraint::or(vec![not_p.clone(), ci.clone()]))
                    .collect();
                (p_lit, clauses)
            }
            Constraint::Or(cs) => {
                let p = self.encoder.state_mut().new_aux_bool();
                // Register the auxiliary variable
                let code = self.encoder.state().sat_variable_count + 1;
                self.encoder.state_mut().bool_code_map.insert(p.clone(), code);
                self.encoder.state_mut().sat_variable_count += 1;

                let p_lit = Constraint::Lit(Literal::pos(p.clone()));
                let not_p = Constraint::Lit(Literal::neg(p));
                // p -> (c1 | c2 | ...) means (!p | c1 | c2 | ...)
                let mut clause_lits = vec![not_p];
                clause_lits.extend(cs.iter().cloned());
                let clause = Constraint::or(clause_lits);
                (p_lit, vec![clause])
            }
            _ => unreachable!("tseitin should only be called on And/Or/Literal"),
        }
    }

    /// Convert constraint to CNF (list of clauses, each clause is list of literals)
    /// Scarab: toCNF(c: Constraint): Seq[Seq[Literal]]
    pub fn to_cnf(&mut self, c: &Constraint) -> Vec<Vec<Constraint>> {
        match c {
            c if c.is_literal() => vec![vec![c.clone()]],
            Constraint::And(cs) => {
                cs.iter().flat_map(|ci| self.to_cnf(ci)).collect()
            }
            Constraint::Or(_) => {
                let flattened = self.flatten_or(c);
                let ts: Vec<_> = flattened.iter()
                    .map(|ci| self.tseitin(ci))
                    .collect();
                // Main clause: (p1 | p2 | ... | pn)
                let main_clause: Vec<_> = ts.iter().map(|(lit, _)| lit.clone()).collect();
                let mut result = vec![main_clause];
                // Add extra clauses from Tseitin transformation
                for (_, extra_clauses) in ts {
                    for extra in extra_clauses {
                        result.extend(self.to_cnf(&extra));
                    }
                }
                result
            }
            _ => unreachable!("to_cnf called on non-constraint"),
        }
    }

    /// Simplify constraint to CNF
    /// Scarab: simplify(c: Constraint): Seq[Seq[Literal]]
    pub fn simplify(&mut self, c: &Constraint) -> Vec<Vec<Constraint>> {
        self.to_cnf(c).into_iter().flat_map(|lits| {
            if self.is_simple_clause(&lits) {
                vec![lits]
            } else {
                // Complex clause: introduce auxiliary variables for complex literals
                let mut result_clause = Vec::new();
                let mut extra_clauses = Vec::new();

                for lit in lits {
                    if self.is_simple_literal(&lit) {
                        result_clause.push(lit);
                    } else {
                        // Create auxiliary variable for complex literal
                        let p = self.encoder.state_mut().new_aux_bool();
                        let code = self.encoder.state().sat_variable_count + 1;
                        self.encoder.state_mut().bool_code_map.insert(p.clone(), code);
                        self.encoder.state_mut().sat_variable_count += 1;

                        let p_lit = Constraint::Lit(Literal::pos(p.clone()));
                        let not_p = Constraint::Lit(Literal::neg(p));
                        result_clause.push(p_lit);
                        // (!p | lit) clause
                        extra_clauses.push(vec![not_p, lit]);
                    }
                }

                let mut result = vec![result_clause];
                result.extend(extra_clauses);
                result
            }
        }).collect()
    }
}

#[cfg(test)]
mod tests {
    #[allow(unused_imports)]
    use super::*;
    use crate::{Bool, Literal, Constraint};
    use crate::expr::Var;
    use crate::expr::Sum;

    // We need a mock encoder for testing Simplifier
    // For now, we'll test the methods that don't require encoder state

    #[test]
    fn test_flatten_or_simple() {
        // Test with a simple Or (no nesting)
        let p = Bool::new("p");
        let q = Bool::new("q");
        let c = Constraint::or(vec![
            Constraint::Lit(Literal::pos(p)),
            Constraint::Lit(Literal::pos(q)),
        ]);

        // Create a minimal test - flatten_or doesn't need encoder state
        // We'll test this properly in integration tests
    }

    #[test]
    fn test_is_simple_literal() {
        let p = Bool::new("p");
        let x = Var::new("x");

        // Bool literal is simple
        let lit = Constraint::Lit(Literal::pos(p));
        assert!(lit.is_literal());

        // Single variable sum is simple
        let s = Sum::from(x.clone());
        let c = s.le(5);
        assert!(c.is_literal());

        // Two variable sum has terms().len() == 2, so not simple
        let y = Var::new("y");
        let s2 = Sum::from(x) + Sum::from(y);
        let c2 = s2.le(10);
        assert!(c2.is_literal());
        // This would be checked by is_simple_literal, but we can't test without encoder
    }
}
