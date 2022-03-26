// SPDX-License-Identifier: Apache-2.0

use super::*;
use core::{cmp::Ordering, ops::*};

/// Expresses a linear set by its starting and termination points
///
/// This type is fully isomorphic with `core::ops::Range` and `Span`. However,
/// unlike `core::ops::Range`, this type is not an iterator and therefore can
/// implement `Copy`. Points may have any number of dimensions.
#[repr(C)]
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct Line<T> {
    /// The start point
    pub start: T,

    /// The first point excluded by the set
    pub end: T,
}

impl<T> Line<T> {
    /// Create a new line
    ///
    /// # Example
    ///
    /// ```
    /// let line = lset::Line::new(5, 10);
    /// assert_eq!(line.start, 5);
    /// assert_eq!(line.end, 10);
    /// ```
    #[inline(always)]
    pub const fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    /// Indicates whether the line is empty
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(Line::from(2..2).is_empty());
    /// assert!(!Line::from(2..3).is_empty());
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool
    where
        T: PartialEq,
    {
        self.start == self.end
    }
}

impl<T: PartialOrd> Line<T> {
    /// Returns the intersection between the sets, if any.
    ///
    /// ```
    /// use lset::*;
    ///
    /// let a = Line::new(0, 5);
    /// let b = Line::new(2, 7);
    /// let c = Line::new(5, 10);
    ///
    /// assert_eq!(a.intersection(b), Some(Line::new(2, 5)));
    /// assert_eq!(b.intersection(c), Some(Line::new(5, 7)));
    /// assert_eq!(a.intersection(a), Some(a));
    /// assert_eq!(b.intersection(b), Some(b));
    /// assert_eq!(c.intersection(c), Some(c));
    /// assert_eq!(a.intersection(c), None);
    /// ```
    pub fn intersection(self, other: Self) -> Option<Self> {
        let start = if other.start >= self.start && other.start < self.end {
            Some(other.start)
        } else {
            None
        };

        let end = if other.end > self.start && other.end <= self.end {
            Some(other.end)
        } else {
            None
        };

        match (start, end) {
            (Some(start), Some(end)) => Some(Line::new(start, end)),
            (Some(start), None) => Some(Line::new(start, self.end)),
            (None, Some(end)) => Some(Line::new(self.start, end)),
            (None, None) => None,
        }
    }
}

impl<T: Add<T, Output = T>> Add<T> for Line<T> {
    type Output = Self;

    /// Grows the line by the size of the operand
    ///
    /// # Example
    ///
    /// ```
    /// let before = lset::Line::new(5, 10);
    /// let after = before + 5;
    /// assert_eq!(after.start, 5);
    /// assert_eq!(after.end, 15);
    /// ```
    #[inline(always)]
    fn add(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            end: self.end + rhs,
        }
    }
}

impl<T: AddAssign<T>> AddAssign<T> for Line<T> {
    /// Grows the line by the size of the operand
    ///
    /// # Example
    ///
    /// ```
    /// let mut line = lset::Line::new(5, 10);
    /// line += 5;
    /// assert_eq!(line.start, 5);
    /// assert_eq!(line.end, 15);
    /// ```
    #[inline(always)]
    fn add_assign(&mut self, rhs: T) {
        self.end += rhs;
    }
}

impl<T: Sub<T, Output = T>> Sub<T> for Line<T> {
    type Output = Self;

    /// Shrinks the line by the size of the operand
    ///
    /// # Example
    ///
    /// ```
    /// let before = lset::Line::new(5, 10);
    /// let after = before - 5;
    /// assert_eq!(after.start, 5);
    /// assert_eq!(after.end, 5);
    /// ```
    #[inline(always)]
    fn sub(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            end: self.end - rhs,
        }
    }
}

impl<T: SubAssign<T>> SubAssign<T> for Line<T> {
    /// Shrinks the line by the size of the operand
    ///
    /// # Example
    ///
    /// ```
    /// let mut line = lset::Line::new(5, 10);
    /// line -= 5;
    /// assert_eq!(line.start, 5);
    /// assert_eq!(line.end, 5);
    /// ```
    #[inline(always)]
    fn sub_assign(&mut self, rhs: T) {
        self.end -= rhs;
    }
}

impl<T: Copy + Sub<T, Output = T>> Shl<T> for Line<T> {
    type Output = Self;

    /// Shifts the line downwards without changing size
    ///
    /// # Example
    ///
    /// ```
    /// let before = lset::Line::new(5, 10);
    /// let after = before << 5;
    /// assert_eq!(after.start, 0);
    /// assert_eq!(after.end, 5);
    /// ```
    #[inline(always)]
    fn shl(self, rhs: T) -> Self::Output {
        Self {
            start: self.start - rhs,
            end: self.end - rhs,
        }
    }
}

impl<T: Copy + SubAssign<T>> ShlAssign<T> for Line<T> {
    /// Shifts the line downwards without changing size
    ///
    /// # Example
    ///
    /// ```
    /// let mut line = lset::Line::new(5, 10);
    /// line <<= 5;
    /// assert_eq!(line.start, 0);
    /// assert_eq!(line.end, 5);
    /// ```
    #[inline(always)]
    fn shl_assign(&mut self, rhs: T) {
        self.start -= rhs;
        self.end -= rhs;
    }
}

impl<T: Copy + Add<T, Output = T>> Shr<T> for Line<T> {
    type Output = Self;

    /// Shifts the line upwards without changing size
    ///
    /// # Example
    ///
    /// ```
    /// let before = lset::Line::new(5, 10);
    /// let after = before >> 5;
    /// assert_eq!(after.start, 10);
    /// assert_eq!(after.end, 15);
    /// ```
    #[inline(always)]
    fn shr(self, rhs: T) -> Self::Output {
        Self {
            start: self.start + rhs,
            end: self.end + rhs,
        }
    }
}

impl<T: Copy + AddAssign<T>> ShrAssign<T> for Line<T> {
    /// Shifts the line upwards without changing size
    ///
    /// # Example
    ///
    /// ```
    /// let mut line = lset::Line::new(5, 10);
    /// line >>= 5;
    /// assert_eq!(line.start, 10);
    /// assert_eq!(line.end, 15);
    /// ```
    #[inline(always)]
    fn shr_assign(&mut self, rhs: T) {
        self.start += rhs;
        self.end += rhs;
    }
}

impl<T: PartialOrd> PartialOrd for Line<T> {
    /// Compares two `Line` types.
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(Line::new(5, 10) <= Line::new(5, 10));
    /// assert!(Line::new(5, 10) >= Line::new(5, 10));
    /// assert!(Line::new(5, 10) < Line::new(10, 15));
    /// assert!(Line::new(10, 15) > Line::new(5, 10));
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            Some(Ordering::Equal)
        } else if self.start >= other.end {
            Some(Ordering::Greater)
        } else if self.end <= other.start {
            Some(Ordering::Less)
        } else {
            None
        }
    }
}

impl<T> From<Range<T>> for Line<T> {
    /// Converts a `Range` into a `Line`
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert_eq!(Line::new(5, 10), Line::from(5..10));
    /// assert_eq!(Line::new(5, 10), (5..10).into());
    /// ```
    #[inline(always)]
    fn from(value: Range<T>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl<T> From<Line<T>> for Range<T> {
    /// Converts a `Line` into a `Range`
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert_eq!(5..10, std::ops::Range::from(Line::new(5, 10)));
    /// assert_eq!(5..10, Line::new(5, 10).into());
    /// ```
    #[inline(always)]
    fn from(value: Line<T>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl<T: Clone + Add<U, Output = T>, U> From<Span<T, U>> for Line<T> {
    /// Converts a `Span` into a `Line`
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert_eq!(Line::new(5, 10), Line::from(Span::new(5, 5)));
    /// assert_eq!(Line::new(5, 10), Span::new(5, 5).into());
    /// ```
    #[inline(always)]
    fn from(value: Span<T, U>) -> Self {
        Self {
            start: value.start.clone(),
            end: value.start + value.count,
        }
    }
}

impl<T: PartialOrd> Contains<T> for Line<T> {
    /// Indicates whether the line contains a point
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(!Line::from(2..3).contains(&1));
    /// assert!(Line::from(2..3).contains(&2));
    /// assert!(!Line::from(2..3).contains(&3));

    /// assert!(!Line::from(3..2).contains(&1));
    /// assert!(!Line::from(3..2).contains(&2));
    /// assert!(!Line::from(3..2).contains(&3));
    /// ```
    #[inline(always)]
    fn contains(&self, value: &T) -> bool {
        if self.start <= self.end {
            &self.start <= value && value < &self.end
        } else {
            false
        }
    }
}

impl<T: PartialOrd> Contains<Self> for Line<T> {
    /// Indicates whether the line contains another line
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(Line::from(4..8).contains(&Line::from(5..7)));
    /// assert!(Line::from(4..8).contains(&Line::from(4..7)));
    /// assert!(Line::from(4..8).contains(&Line::from(5..8)));
    /// assert!(Line::from(4..8).contains(&Line::from(4..8)));
    /// assert!(!Line::from(4..8).contains(&Line::from(3..8)));
    /// assert!(!Line::from(4..8).contains(&Line::from(4..9)));
    /// assert!(!Line::from(4..8).contains(&Line::from(3..9)));
    /// assert!(!Line::from(4..8).contains(&Line::from(2..10)));
    /// assert!(!Line::from(4..8).contains(&Line::from(6..5)));
    /// assert!(!Line::from(7..3).contains(&Line::from(5..6)));
    /// ```
    #[inline(always)]
    fn contains(&self, value: &Self) -> bool {
        if self.start <= self.end && value.start <= value.end {
            self.start <= value.start && value.end <= self.end
        } else {
            false
        }
    }
}

impl<T: PartialOrd> Split<Self> for Line<T> {
    /// Splits a line by another line
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// let line = Line::from(2..5);
    /// assert_eq!(line.split(Line::from(1..4)), None);
    /// assert_eq!(line.split(Line::from(3..6)), None);
    /// assert_eq!(line.split(Line::from(2..2)), None);
    /// assert_eq!(line.split(Line::from(2..3)), Some((Line::from(2..2), Line::from(3..5))));
    /// assert_eq!(line.split(Line::from(3..3)), None);
    /// assert_eq!(line.split(Line::from(3..4)), Some((Line::from(2..3), Line::from(4..5))));
    /// assert_eq!(line.split(Line::from(4..4)), None);
    /// assert_eq!(line.split(Line::from(4..5)), Some((Line::from(2..4), Line::from(5..5))));
    /// assert_eq!(line.split(Line::from(5..5)), None);
    /// assert_eq!(line.split(line), Some((Line::from(2..2), Line::from(5..5))));
    /// ```
    #[inline(always)]
    fn split(self, at: Self) -> Option<(Self, Self)> {
        if at.start == at.end {
            return None;
        }

        if !self.contains(&at) {
            return None;
        }

        let l = Self {
            start: self.start,
            end: at.start,
        };

        let r = Self {
            start: at.end,
            end: self.end,
        };

        Some((l, r))
    }
}

impl<T: PartialOrd + Copy> Split<T> for Line<T> {
    /// Splits a line at a point
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// let line = Line::from(2..4);
    /// assert_eq!(line.split(1), None);
    /// assert_eq!(line.split(2), Some((Line::from(2..2), line)));
    /// assert_eq!(line.split(3), Some((Line::from(2..3), Line::from(3..4))));
    /// assert_eq!(line.split(4), Some((line, Line::from(4..4))));
    /// assert_eq!(line.split(5), None);
    /// ```
    #[inline(always)]
    fn split(self, at: T) -> Option<(Self, Self)> {
        if at < self.start || at > self.end {
            return None;
        }

        let l = Self {
            start: self.start,
            end: at,
        };

        let r = Self {
            start: at,
            end: self.end,
        };

        Some((l, r))
    }
}
