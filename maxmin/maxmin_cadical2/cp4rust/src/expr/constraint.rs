// Constraint: Bool, Literal, Constraint

use std::ops::{BitAnd, BitOr, Not};
use super::term::Sum;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bool(String);

impl Bool {
    pub fn new(name: &str) -> Self {
        Bool(name.to_string())
    }

    pub fn name(&self) -> &str {
        &self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Pos(Bool),
    Neg(Bool),
}

impl Literal {
    pub fn pos(b: Bool) -> Self {
        Literal::Pos(b)
    }

    pub fn neg(b: Bool) -> Self {
        Literal::Neg(b)
    }

    pub fn is_positive(&self) -> bool {
        matches!(self, Literal::Pos(_))
    }

    pub fn negate(&self) -> Self {
        match self {
            Literal::Pos(b) => Literal::Neg(b.clone()),
            Literal::Neg(b) => Literal::Pos(b.clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Constraint {
    Lit(Literal),
    And(Vec<Constraint>),
    Or(Vec<Constraint>),
    LeZero(Sum),  // sum <= 0
    GeZero(Sum),  // sum >= 0
    EqZero(Sum),  // sum == 0
    NeZero(Sum),  // sum != 0
}

impl From<Literal> for Constraint {
    fn from(lit: Literal) -> Self {
        Constraint::Lit(lit)
    }
}

impl From<Bool> for Constraint {
    fn from(b: Bool) -> Self {
        Constraint::Lit(Literal::Pos(b))
    }
}

impl From<&Bool> for Constraint {
    fn from(b: &Bool) -> Self {
        Constraint::Lit(Literal::Pos(b.clone()))
    }
}

impl Constraint {
    pub fn and(constraints: Vec<Constraint>) -> Self {
        Constraint::And(constraints)
    }

    pub fn or(constraints: Vec<Constraint>) -> Self {
        Constraint::Or(constraints)
    }

    /// p.implies(q) = !p | q
    pub fn implies(self, other: Constraint) -> Self {
        !self | other
    }

    /// p.iff(q) = (p => q) & (q => p)
    pub fn iff(self, other: Constraint) -> Self {
        let p_implies_q = self.clone().implies(other.clone());
        let q_implies_p = other.implies(self);
        p_implies_q & q_implies_p
    }

    /// Check if this constraint is a literal (not And/Or)
    /// Scarab: Literal is Bool, Not, LeZero, GeZero, EqZero, NeZero
    pub fn is_literal(&self) -> bool {
        matches!(self,
            Constraint::Lit(_) |
            Constraint::LeZero(_) |
            Constraint::GeZero(_) |
            Constraint::EqZero(_) |
            Constraint::NeZero(_)
        )
    }
}

impl BitAnd for Constraint {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        Constraint::And(vec![self, rhs])
    }
}

impl BitOr for Constraint {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        Constraint::Or(vec![self, rhs])
    }
}

impl Not for Constraint {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Constraint::Lit(lit) => Constraint::Lit(lit.negate()),
            Constraint::And(cs) => Constraint::Or(cs.into_iter().map(|c| !c).collect()),
            Constraint::Or(cs) => Constraint::And(cs.into_iter().map(|c| !c).collect()),
            // !(sum <= 0) => sum > 0 => sum >= 1 => (sum - 1) >= 0
            Constraint::LeZero(sum) => Constraint::GeZero(sum + (-1)),
            // !(sum >= 0) => sum < 0 => sum <= -1 => sum + 1 <= 0
            Constraint::GeZero(sum) => Constraint::LeZero(sum + 1),
            // !(sum == 0) => sum != 0
            Constraint::EqZero(sum) => Constraint::NeZero(sum),
            // !(sum != 0) => sum == 0
            Constraint::NeZero(sum) => Constraint::EqZero(sum),
        }
    }
}

// Extend Sum with comparison methods that return Constraint
impl Sum {
    /// self <= rhs  =>  self - rhs <= 0
    pub fn le(self, rhs: i32) -> Constraint {
        Constraint::LeZero(self + (-rhs))
    }

    /// self >= rhs  =>  self - rhs >= 0
    pub fn ge(self, rhs: i32) -> Constraint {
        Constraint::GeZero(self + (-rhs))
    }

    /// self == rhs  =>  self - rhs == 0
    pub fn eq(self, rhs: i32) -> Constraint {
        Constraint::EqZero(self + (-rhs))
    }

    /// self != rhs  =>  self - rhs != 0
    pub fn ne(self, rhs: i32) -> Constraint {
        Constraint::NeZero(self + (-rhs))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::term::Var;

    #[test]
    fn test_bool_creation() {
        let p = Bool::new("p");
        assert_eq!(p.name(), "p");
    }

    #[test]
    fn test_bool_equality() {
        let p1 = Bool::new("p");
        let p2 = Bool::new("p");
        assert_eq!(p1, p2);
    }

    #[test]
    fn test_literal_pos() {
        let p = Bool::new("p");
        let lit = Literal::pos(p.clone());
        assert!(lit.is_positive());
    }

    #[test]
    fn test_literal_neg() {
        let p = Bool::new("p");
        let lit = Literal::neg(p.clone());
        assert!(!lit.is_positive());
    }

    #[test]
    fn test_literal_negation() {
        let p = Bool::new("p");
        let pos = Literal::pos(p.clone());
        let neg = pos.negate();
        assert!(!neg.is_positive());
    }

    #[test]
    fn test_constraint_from_literal() {
        let p = Bool::new("p");
        let lit = Literal::pos(p);
        let c: Constraint = lit.into();
        assert!(matches!(c, Constraint::Lit(_)));
    }

    #[test]
    fn test_and() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = Constraint::and(vec![cp, cq]);
        assert!(matches!(c, Constraint::And(_)));
    }

    #[test]
    fn test_or() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = Constraint::or(vec![cp, cq]);
        assert!(matches!(c, Constraint::Or(_)));
    }

    #[test]
    fn test_bitand_operator() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = cp & cq;
        assert!(matches!(c, Constraint::And(_)));
    }

    #[test]
    fn test_bitor_operator() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = cp | cq;
        assert!(matches!(c, Constraint::Or(_)));
    }

    #[test]
    fn test_not_operator_on_literal() {
        let p = Bool::new("p");
        let c: Constraint = Literal::pos(p.clone()).into();
        let neg_c = !c;
        // !p should become Lit(Neg(p))
        assert!(matches!(neg_c, Constraint::Lit(Literal::Neg(_))));
    }

    #[test]
    fn test_not_operator_on_and() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = cp & cq;
        let neg_c = !c;
        // !(p & q) should become (!p | !q) by De Morgan
        assert!(matches!(neg_c, Constraint::Or(_)));
    }

    #[test]
    fn test_not_operator_on_or() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = cp | cq;
        let neg_c = !c;
        // !(p | q) should become (!p & !q) by De Morgan
        assert!(matches!(neg_c, Constraint::And(_)));
    }

    #[test]
    fn test_implies() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = cp.implies(cq);
        // p => q is equivalent to !p | q
        assert!(matches!(c, Constraint::Or(_)));
    }

    #[test]
    fn test_iff() {
        let p = Bool::new("p");
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(p).into();
        let cq: Constraint = Literal::pos(q).into();
        let c = cp.iff(cq);
        // p <=> q is equivalent to (p => q) & (q => p)
        assert!(matches!(c, Constraint::And(_)));
    }

    // Sum comparison -> Constraint tests
    #[test]
    fn test_sum_le_zero() {
        let x = Var::new("x");
        let s = Sum::from(x);  // x
        let c = s.le(0);  // x <= 0
        assert!(matches!(c, Constraint::LeZero(_)));
    }

    #[test]
    fn test_sum_ge_zero() {
        let x = Var::new("x");
        let s = Sum::from(x);  // x
        let c = s.ge(0);  // x >= 0
        assert!(matches!(c, Constraint::GeZero(_)));
    }

    #[test]
    fn test_sum_eq_zero() {
        let x = Var::new("x");
        let s = Sum::from(x);  // x
        let c = s.eq(0);  // x == 0
        assert!(matches!(c, Constraint::EqZero(_)));
    }

    #[test]
    fn test_sum_ne_zero() {
        let x = Var::new("x");
        let s = Sum::from(x);  // x
        let c = s.ne(0);  // x != 0
        assert!(matches!(c, Constraint::NeZero(_)));
    }

    #[test]
    fn test_sum_le_value() {
        let x = Var::new("x");
        let s = Sum::from(x.clone());  // x
        let c = s.le(5);  // x <= 5  =>  x - 5 <= 0
        if let Constraint::LeZero(sum) = c {
            assert_eq!(sum.b(), -5);
        } else {
            panic!("Expected LeZero");
        }
    }

    #[test]
    fn test_is_literal() {
        let p = Bool::new("p");
        let x = Var::new("x");
        let s = Sum::from(x);

        // Literals
        assert!(Constraint::Lit(Literal::pos(p.clone())).is_literal());
        assert!(Constraint::Lit(Literal::neg(p)).is_literal());
        assert!(s.clone().le(5).is_literal());  // LeZero
        assert!(s.clone().ge(5).is_literal());  // GeZero
        assert!(s.clone().eq(5).is_literal());  // EqZero
        assert!(s.ne(5).is_literal());          // NeZero

        // Non-literals
        let q = Bool::new("q");
        let cp: Constraint = Literal::pos(Bool::new("p")).into();
        let cq: Constraint = Literal::pos(q).into();
        assert!(!Constraint::and(vec![cp.clone(), cq.clone()]).is_literal());
        assert!(!Constraint::or(vec![cp, cq]).is_literal());
    }
}
