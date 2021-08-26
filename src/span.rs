// SPDX-License-Identifier: Apache-2.0

use super::*;
use core::ops::*;

/// Expresses a linear set by its start element and number of elements.
///
/// This type is fully isomorphic with `core::ops::Range` and `Line`. However,
/// unlike `core::ops::Range`, this type is not an iterator and therefore can
/// implement `Copy`.
#[repr(C)]
#[derive(Copy, Clone, Default, Debug, PartialEq, Eq)]
pub struct Span<T, U = T> {
    /// The start element
    pub start: T,

    /// The number of elments
    pub count: U,
}

impl<T, U> Span<T, U> {
    /// Create a new span
    ///
    /// # Example
    ///
    /// ```
    /// let span = lset::Span::new(5, 10);
    /// assert_eq!(span.start, 5);
    /// assert_eq!(span.count, 10);
    /// ```
    #[inline(always)]
    pub const fn new(start: T, count: U) -> Self {
        Self { start, count }
    }
}

/// Grows the line by the size of the operand
///
/// # Example
///
/// ```
/// let before = lset::Span::new(5, 10);
/// let after = before + 5;
/// assert_eq!(after.start, 5);
/// assert_eq!(after.count, 15);
/// ```
impl<T: Add<T, Output = T>> Add<T> for Span<T> {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            count: self.count + rhs,
        }
    }
}

/// Grows the line by the size of the operand
///
/// # Example
///
/// ```
/// let mut span = lset::Span::new(5, 10);
/// span += 5;
/// assert_eq!(span.start, 5);
/// assert_eq!(span.count, 15);
/// ```
impl<T: AddAssign<T>> AddAssign<T> for Span<T> {
    #[inline(always)]
    fn add_assign(&mut self, rhs: T) {
        self.count += rhs;
    }
}

/// Shrinks the line by the size of the operand
///
/// # Example
///
/// ```
/// let before = lset::Span::new(5, 10);
/// let after = before - 5;
/// assert_eq!(after.start, 5);
/// assert_eq!(after.count, 5);
/// ```
impl<T: Sub<T, Output = T>> Sub<T> for Span<T> {
    type Output = Self;

    #[inline(always)]
    fn sub(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            count: self.count - rhs,
        }
    }
}

/// Shrinks the line by the size of the operand
///
/// # Example
///
/// ```
/// let mut span = lset::Span::new(5, 10);
/// span -= 5;
/// assert_eq!(span.start, 5);
/// assert_eq!(span.count, 5);
/// ```
impl<T: SubAssign<T>> SubAssign<T> for Span<T> {
    #[inline(always)]
    fn sub_assign(&mut self, rhs: T) {
        self.count -= rhs;
    }
}

/// Shifts the line downwards without changing size
///
/// # Example
///
/// ```
/// let before = lset::Span::new(5, 10);
/// let after = before << 5;
/// assert_eq!(after.start, 0);
/// assert_eq!(after.count, 10);
/// ```
impl<T: Copy + Sub<T, Output = T>> Shl<T> for Span<T> {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shl(self, rhs: T) -> Self::Output {
        Self {
            start: self.start - rhs,
            count: self.count,
        }
    }
}

/// Shifts the line downwards without changing size
///
/// # Example
///
/// ```
/// let mut span = lset::Span::new(5, 10);
/// span <<= 5;
/// assert_eq!(span.start, 0);
/// assert_eq!(span.count, 10);
/// ```
impl<T: Copy + SubAssign<T>> ShlAssign<T> for Span<T> {
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn shl_assign(&mut self, rhs: T) {
        self.start -= rhs;
    }
}

/// Shifts the line upwards without changing size
///
/// # Example
///
/// ```
/// let before = lset::Span::new(5, 10);
/// let after = before >> 5;
/// assert_eq!(after.start, 10);
/// assert_eq!(after.count, 10);
/// ```
impl<T: Copy + Add<T, Output = T>> Shr<T> for Span<T> {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, rhs: T) -> Self::Output {
        Self {
            start: self.start + rhs,
            count: self.count,
        }
    }
}

/// Shifts the line upwards without changing size
///
/// # Example
///
/// ```
/// let mut span = lset::Span::new(5, 10);
/// span >>= 5;
/// assert_eq!(span.start, 10);
/// assert_eq!(span.count, 10);
/// ```
impl<T: Copy + AddAssign<T>> ShrAssign<T> for Span<T> {
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn shr_assign(&mut self, rhs: T) {
        self.start += rhs;
    }
}

/// Converts a `Range` into a `Span`
///
/// # Example
///
/// ```
/// use lset::*;
/// assert_eq!(Span::new(5, 10), Span::from(5..15));
/// assert_eq!(Span::new(5, 10), (5..15).into());
/// ```
impl<T: Copy + Sub<T, Output = U>, U> From<Range<T>> for Span<T, U> {
    #[inline(always)]
    fn from(value: Range<T>) -> Self {
        Self {
            start: value.start,
            count: value.end - value.start,
        }
    }
}

/// Converts a `Span` into a `Range`
///
/// # Example
///
/// ```
/// use lset::*;
/// assert_eq!(5..15, std::ops::Range::from(Span::new(5, 10)));
/// assert_eq!(5..15, Span::new(5, 10).into());
/// ```
impl<T: Clone + Add<U, Output = T>, U> From<Span<T, U>> for Range<T> {
    #[inline(always)]
    fn from(value: Span<T, U>) -> Self {
        Self {
            start: value.start.clone(),
            end: value.start + value.count,
        }
    }
}

/// Converts a `Line` into a `Span`
///
/// # Example
///
/// ```
/// use lset::*;
/// assert_eq!(Span::new(5, 10), Span::from(Line::new(5, 15)));
/// assert_eq!(Span::new(5, 10), (Line::new(5, 15)).into());
/// ```
impl<T: Clone + Sub<T, Output = U>, U> From<Line<T>> for Span<T, U> {
    #[inline(always)]
    fn from(value: Line<T>) -> Self {
        Self {
            start: value.start.clone(),
            count: value.end - value.start,
        }
    }
}

impl<T, U> Contains<T> for Span<T, U>
where
    Self: Into<Line<T>> + Clone,
    Line<T>: Contains<T>,
{
    #[inline(always)]
    fn contains(&self, value: &T) -> bool {
        self.clone().into().contains(value)
    }
}

impl<T, U> Contains<Self> for Span<T, U>
where
    Self: Into<Line<T>> + Clone,
    T: PartialOrd,
{
    #[inline(always)]
    fn contains(&self, value: &Self) -> bool {
        self.clone().into().contains(&value.clone().into())
    }
}

impl<T, U, V> Empty for Span<T, U>
where
    T: PartialOrd<V> + Add<U, Output = V> + Clone,
    U: Clone,
{
    #[inline(always)]
    fn is_empty(&self) -> bool {
        self.start == self.start.clone() + self.count.clone()
    }
}

impl<T, U> Split<Self> for Span<T, U>
where
    Self: Into<Line<T>>,
    Line<T>: Into<Self>,
    Line<T>: Split<Line<T>>,
{
    #[inline(always)]
    fn split(self, at: Self) -> Option<(Self, Self)> {
        let (l, r) = self.into().split(at.into())?;
        Some((l.into(), r.into()))
    }
}

impl<T, U> Split<U> for Span<T, U>
where
    T: Add<U, Output = T> + Clone,
    Line<T>: Split<T> + Into<Self>,
    Self: Into<Line<T>>,
{
    #[inline(always)]
    fn split(self, at: U) -> Option<(Self, Self)> {
        let e = self.start.clone() + at;
        let (l, r) = self.into().split(e)?;
        Some((l.into(), r.into()))
    }
}

#[cfg(test)]
mod test {
    use super::*;

    macro_rules! x {
        ($range:expr) => {
            Span::from($range)
        };
    }

    #[test]
    fn convert() {
        let range = 2..3;
        let line = Line { start: 2, end: 3 };
        let span = Span { start: 2, count: 1 };

        assert_eq!(range, span.into());
        assert_eq!(span, range.into());

        assert_eq!(line, span.into());
        assert_eq!(span, line.into());
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
        assert_eq!(x!(2..4).split(0), Some((x!(2..2), x!(2..4))));
        assert_eq!(x!(2..4).split(1), Some((x!(2..3), x!(3..4))));
        assert_eq!(x!(2..4).split(2), Some((x!(2..4), x!(4..4))));
        assert_eq!(x!(2..4).split(3), None);

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
