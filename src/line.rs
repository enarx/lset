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
}

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
impl<T: Add<T, Output = T>> Add<T> for Line<T> {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            end: self.end + rhs,
        }
    }
}

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
impl<T: AddAssign<T>> AddAssign<T> for Line<T> {
    #[inline(always)]
    fn add_assign(&mut self, rhs: T) {
        self.end += rhs;
    }
}

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
impl<T: Sub<T, Output = T>> Sub<T> for Line<T> {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            end: self.end - rhs,
        }
    }
}

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
impl<T: SubAssign<T>> SubAssign<T> for Line<T> {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: T) {
        self.end -= rhs;
    }
}

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
impl<T: Copy + Sub<T, Output = T>> Shl<T> for Line<T> {
    type Output = Self;

    #[inline(always)]
    fn shl(self, rhs: T) -> Self::Output {
        Self {
            start: self.start - rhs,
            end: self.end - rhs,
        }
    }
}

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
impl<T: Copy + SubAssign<T>> ShlAssign<T> for Line<T> {
    #[inline(always)]
    fn shl_assign(&mut self, rhs: T) {
        self.start -= rhs;
        self.end -= rhs;
    }
}

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
impl<T: Copy + Add<T, Output = T>> Shr<T> for Line<T> {
    type Output = Self;

    #[inline(always)]
    fn shr(self, rhs: T) -> Self::Output {
        Self {
            start: self.start + rhs,
            end: self.end + rhs,
        }
    }
}

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
impl<T: Copy + AddAssign<T>> ShrAssign<T> for Line<T> {
    #[inline(always)]
    fn shr_assign(&mut self, rhs: T) {
        self.start += rhs;
        self.end += rhs;
    }
}

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
impl<T: PartialOrd> PartialOrd for Line<T> {
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

/// Converts a `Range` into a `Line`
///
/// # Example
///
/// ```
/// use lset::*;
/// assert_eq!(Line::new(5, 10), Line::from(5..10));
/// assert_eq!(Line::new(5, 10), (5..10).into());
/// ```
impl<T> From<Range<T>> for Line<T> {
    #[inline(always)]
    fn from(value: Range<T>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

/// Converts a `Line` into a `Range`
///
/// # Example
///
/// ```
/// use lset::*;
/// assert_eq!(5..10, std::ops::Range::from(Line::new(5, 10)));
/// assert_eq!(5..10, Line::new(5, 10).into());
/// ```
impl<T> From<Line<T>> for Range<T> {
    #[inline(always)]
    fn from(value: Line<T>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

/// Converts a `Span` into a `Line`
///
/// # Example
///
/// ```
/// use lset::*;
/// assert_eq!(Line::new(5, 10), Line::from(Span::new(5, 5)));
/// assert_eq!(Line::new(5, 10), Span::new(5, 5).into());
/// ```
impl<T: Clone + Add<U, Output = T>, U> From<Span<T, U>> for Line<T> {
    #[inline(always)]
    fn from(value: Span<T, U>) -> Self {
        Self {
            start: value.start.clone(),
            end: value.start + value.count,
        }
    }
}

impl<T: PartialOrd> Contains<T> for Line<T> {
    #[inline(always)]
    fn contains(&self, value: &T) -> bool {
        if self.start < self.end {
            &self.start <= value && value < &self.end
        } else {
            &self.start >= value && value > &self.end
        }
    }
}

impl<T: PartialOrd> Contains<Self> for Line<T> {
    #[inline(always)]
    fn contains(&self, value: &Self) -> bool {
        self.contains(&value.start) && self.contains(&value.end)
    }
}

impl<T: PartialEq> Empty for Line<T> {
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

impl<T: PartialOrd> Split<Self> for Line<T> {
    #[inline(always)]
    fn split(self, at: Self) -> Option<(Self, Self)> {
        if !self.contains(&at.start) && at.start != self.end {
            return None;
        }

        if !self.contains(&at.end) && at.end != self.end {
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
    #[inline(always)]
    fn split(self, at: T) -> Option<(Self, Self)> {
        self.split(Self { start: at, end: at })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! x {
        ($range:expr) => {
            Line::from($range)
        };
    }

    #[test]
    fn convert() {
        let range = 2..3;
        let line = Line { start: 2, end: 3 };

        assert_eq!(range, line.into());
        assert_eq!(line, range.into());
    }

    #[test]
    #[allow(clippy::reversed_empty_ranges)]
    fn contains() {
        assert!(!x!(2..3).contains(&1));
        assert!(x!(2..3).contains(&2));
        assert!(!x!(2..3).contains(&3));

        assert!(!x!(3..2).contains(&1));
        assert!(!x!(3..2).contains(&2));
        assert!(x!(3..2).contains(&3));

        assert!(x!(0..9).contains(&x!(2..4)));
        assert!(x!(0..9).contains(&x!(0..0)));
        assert!(x!(0..9).contains(&x!(5..5)));
        assert!(!x!(0..9).contains(&x!(9..9)));
        assert!(!x!(0..9).contains(&x!(2..14)));
        assert!(!x!(0..9).contains(&x!(12..14)));

        assert!(x!(8..3).contains(&x!(5..7)));
        assert!(!x!(8..3).contains(&x!(5..17)));
        assert!(!x!(8..3).contains(&x!(15..17)));
    }

    #[test]
    fn is_empty() {
        assert!(x!(2..2).is_empty());
        assert!(!x!(2..3).is_empty());
    }

    #[test]
    fn split() {
        assert_eq!(x!(2..4).split(1), None);
        assert_eq!(x!(2..4).split(2), Some((x!(2..2), x!(2..4))));
        assert_eq!(x!(2..4).split(3), Some((x!(2..3), x!(3..4))));
        assert_eq!(x!(2..4).split(4), Some((x!(2..4), x!(4..4))));
        assert_eq!(x!(2..4).split(5), None);

        assert_eq!(x!(2..5).split(x!(1..4)), None);
        assert_eq!(x!(2..5).split(x!(3..6)), None);
        assert_eq!(x!(2..5).split(x!(2..2)), Some((x!(2..2), x!(2..5))));
        assert_eq!(x!(2..5).split(x!(2..3)), Some((x!(2..2), x!(3..5))));
        assert_eq!(x!(2..5).split(x!(3..3)), Some((x!(2..3), x!(3..5))));
        assert_eq!(x!(2..5).split(x!(3..4)), Some((x!(2..3), x!(4..5))));
        assert_eq!(x!(2..5).split(x!(4..5)), Some((x!(2..4), x!(5..5))));
        assert_eq!(x!(2..5).split(x!(5..5)), Some((x!(2..5), x!(5..5))));
    }
}
