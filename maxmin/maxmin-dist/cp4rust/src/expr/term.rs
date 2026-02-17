// Term: Var, Sum

use std::ops::{Add, Mul, Neg, Sub};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Var(String);

impl Var {
    pub fn new(name: &str) -> Self {
        Var(name.to_string())
    }

    pub fn name(&self) -> &str {
        &self.0
    }
}

/// Linear expression: b + a₁x₁ + a₂x₂ + ... + aₙxₙ
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sum {
    b: i32,
    terms: Vec<(i32, Var)>,
}

impl Sum {
    pub fn new(b: i32, terms: Vec<(i32, Var)>) -> Self {
        Sum { b, terms }
    }

    pub fn constant(b: i32) -> Self {
        Sum { b, terms: vec![] }
    }

    pub fn term(coef: i32, var: Var) -> Self {
        Sum { b: 0, terms: vec![(coef, var)] }
    }

    pub fn b(&self) -> i32 {
        self.b
    }

    pub fn terms(&self) -> &[(i32, Var)] {
        &self.terms
    }
}

impl From<Var> for Sum {
    fn from(var: Var) -> Self {
        Sum { b: 0, terms: vec![(1, var)] }
    }
}

impl From<i32> for Sum {
    fn from(b: i32) -> Self {
        Sum::constant(b)
    }
}

impl Add for Sum {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let mut terms = self.terms;
        terms.extend(rhs.terms);
        Sum { b: self.b + rhs.b, terms }
    }
}

impl Add<i32> for Sum {
    type Output = Self;

    fn add(self, rhs: i32) -> Self::Output {
        Sum { b: self.b + rhs, terms: self.terms }
    }
}

impl Sub for Sum {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Neg for Sum {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Sum {
            b: -self.b,
            terms: self.terms.into_iter().map(|(a, v)| (-a, v)).collect(),
        }
    }
}

impl Mul<i32> for Sum {
    type Output = Self;

    fn mul(self, rhs: i32) -> Self::Output {
        Sum {
            b: self.b * rhs,
            terms: self.terms.into_iter().map(|(a, v)| (a * rhs, v)).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_var_creation() {
        let x = Var::new("x");
        assert_eq!(x.name(), "x");
    }

    #[test]
    fn test_var_equality() {
        let x1 = Var::new("x");
        let x2 = Var::new("x");
        assert_eq!(x1, x2);
    }

    #[test]
    fn test_sum_from_constant() {
        let s = Sum::constant(5);
        assert_eq!(s.b(), 5);
        assert!(s.terms().is_empty());
    }

    #[test]
    fn test_sum_from_var() {
        let x = Var::new("x");
        let s = Sum::from(x.clone());
        assert_eq!(s.b(), 0);
        assert_eq!(s.terms().len(), 1);
        assert_eq!(s.terms()[0], (1, x));
    }

    #[test]
    fn test_sum_with_coefficient() {
        let x = Var::new("x");
        let s = Sum::term(3, x.clone());
        assert_eq!(s.b(), 0);
        assert_eq!(s.terms()[0], (3, x));
    }

    #[test]
    fn test_sum_add_sums() {
        let x = Var::new("x");
        let y = Var::new("y");
        let s1 = Sum::term(2, x.clone());
        let s2 = Sum::term(3, y.clone());
        let s = s1 + s2;
        assert_eq!(s.b(), 0);
        assert_eq!(s.terms().len(), 2);
    }

    #[test]
    fn test_sum_add_constant() {
        let x = Var::new("x");
        let s1 = Sum::term(2, x.clone());
        let s = s1 + 5;
        assert_eq!(s.b(), 5);
    }

    #[test]
    fn test_sum_sub() {
        let x = Var::new("x");
        let y = Var::new("y");
        let s1 = Sum::term(2, x.clone());
        let s2 = Sum::term(3, y.clone());
        let s = s1 - s2;
        assert_eq!(s.terms().len(), 2);
    }

    #[test]
    fn test_sum_neg() {
        let x = Var::new("x");
        let s1 = Sum::new(5, vec![(2, x.clone())]);
        let s = -s1;
        assert_eq!(s.b(), -5);
        assert_eq!(s.terms()[0].0, -2);
    }

    #[test]
    fn test_sum_mul_scalar() {
        let x = Var::new("x");
        let s1 = Sum::new(2, vec![(3, x.clone())]);
        let s = s1 * 4;
        assert_eq!(s.b(), 8);
        assert_eq!(s.terms()[0].0, 12);
    }
}
