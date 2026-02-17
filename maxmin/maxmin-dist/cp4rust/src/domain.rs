// Domain: set of possible values for a variable

/// Domain of a variable: set of possible values
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain {
    values: Vec<i32>,  // sorted, unique values
}

impl Domain {
    pub fn range(lb: i32, ub: i32) -> Self {
        Domain { values: (lb..=ub).collect() }
    }

    pub fn size(&self) -> usize {
        self.values.len()
    }

    pub fn lb(&self) -> i32 {
        self.values[0]
    }

    pub fn ub(&self) -> i32 {
        self.values[self.values.len() - 1]
    }

    pub fn contains(&self, v: i32) -> bool {
        self.values.binary_search(&v).is_ok()
    }

    pub fn values(&self) -> &[i32] {
        &self.values
    }

    /// Check if domain is contiguous (no gaps)
    /// Scarab: isContiguous
    pub fn is_contiguous(&self) -> bool {
        self.values.len() == (self.ub() - self.lb() + 1) as usize
    }

    /// Get the position (index) of a value in the domain
    /// For contiguous domains: value - lb
    /// For non-contiguous domains: binary search position
    /// Scarab: pos(value: Int): Int
    pub fn pos(&self, value: i32) -> Option<usize> {
        if self.is_contiguous() {
            if value >= self.lb() && value <= self.ub() {
                Some((value - self.lb()) as usize)
            } else {
                None
            }
        } else {
            self.values.binary_search(&value).ok()
        }
    }
}

impl From<Vec<i32>> for Domain {
    fn from(mut values: Vec<i32>) -> Self {
        values.sort();
        values.dedup();
        Domain { values }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_domain_from_range() {
        let d = Domain::range(1, 5);  // {1, 2, 3, 4, 5}
        assert_eq!(d.size(), 5);
        assert_eq!(d.lb(), 1);
        assert_eq!(d.ub(), 5);
    }

    #[test]
    fn test_domain_from_values() {
        let d = Domain::from(vec![1, 3, 5]);  // {1, 3, 5}
        assert_eq!(d.size(), 3);
        assert_eq!(d.lb(), 1);
        assert_eq!(d.ub(), 5);
    }

    #[test]
    fn test_domain_contains() {
        let d = Domain::range(1, 5);
        assert!(d.contains(3));
        assert!(!d.contains(6));
    }

    #[test]
    fn test_domain_is_contiguous() {
        let d1 = Domain::range(1, 5);  // {1, 2, 3, 4, 5}
        assert!(d1.is_contiguous());

        let d2 = Domain::from(vec![1, 3, 5]);  // {1, 3, 5}
        assert!(!d2.is_contiguous());

        let d3 = Domain::from(vec![1, 2, 3, 4, 5]);
        assert!(d3.is_contiguous());
    }

    #[test]
    fn test_domain_pos_contiguous() {
        let d = Domain::range(1, 5);  // {1, 2, 3, 4, 5}
        assert_eq!(d.pos(1), Some(0));
        assert_eq!(d.pos(3), Some(2));
        assert_eq!(d.pos(5), Some(4));
        assert_eq!(d.pos(0), None);
        assert_eq!(d.pos(6), None);
    }

    #[test]
    fn test_domain_pos_non_contiguous() {
        let d = Domain::from(vec![1, 3, 5, 7]);  // {1, 3, 5, 7}
        assert_eq!(d.pos(1), Some(0));
        assert_eq!(d.pos(3), Some(1));
        assert_eq!(d.pos(5), Some(2));
        assert_eq!(d.pos(7), Some(3));
        assert_eq!(d.pos(2), None);
        assert_eq!(d.pos(4), None);
    }
}
