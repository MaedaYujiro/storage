// Assignment: maps variables to values (a solution candidate)

use std::collections::HashMap;
use crate::expr::{Bool, Var, Sum};

/// Assignment: maps variables to values (a solution candidate)
#[derive(Debug, Clone, Default)]
pub struct Assignment {
    int_values: HashMap<Var, i32>,
    bool_values: HashMap<Bool, bool>,
}

impl Assignment {
    pub fn new() -> Self {
        Assignment {
            int_values: HashMap::new(),
            bool_values: HashMap::new(),
        }
    }

    pub fn set_int(&mut self, var: Var, value: i32) {
        self.int_values.insert(var, value);
    }

    pub fn get_int(&self, var: &Var) -> Option<i32> {
        self.int_values.get(var).copied()
    }

    pub fn set_bool(&mut self, var: Bool, value: bool) {
        self.bool_values.insert(var, value);
    }

    pub fn get_bool(&self, var: &Bool) -> Option<bool> {
        self.bool_values.get(var).copied()
    }

    pub fn int_values(&self) -> &HashMap<Var, i32> {
        &self.int_values
    }

    pub fn bool_values(&self) -> &HashMap<Bool, bool> {
        &self.bool_values
    }

    pub fn eval_sum(&self, sum: &Sum) -> Option<i32> {
        let mut result = sum.b();
        for (coef, var) in sum.terms() {
            let val = self.get_int(var)?;
            result += coef * val;
        }
        Some(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_assignment_new() {
        let a = Assignment::new();
        assert!(a.int_values().is_empty());
        assert!(a.bool_values().is_empty());
    }

    #[test]
    fn test_assignment_set_int() {
        let mut a = Assignment::new();
        let x = Var::new("x");
        a.set_int(x.clone(), 5);
        assert_eq!(a.get_int(&x), Some(5));
    }

    #[test]
    fn test_assignment_set_bool() {
        let mut a = Assignment::new();
        let p = Bool::new("p");
        a.set_bool(p.clone(), true);
        assert_eq!(a.get_bool(&p), Some(true));
    }

    #[test]
    fn test_assignment_eval_sum() {
        let mut a = Assignment::new();
        let x = Var::new("x");
        let y = Var::new("y");
        a.set_int(x.clone(), 3);
        a.set_int(y.clone(), 2);
        // 5 + 2x + 3y = 5 + 6 + 6 = 17
        let s = Sum::new(5, vec![(2, x), (3, y)]);
        assert_eq!(a.eval_sum(&s), Some(17));
    }
}
