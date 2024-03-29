// SPDX-License-Identifier: Apache-2.0

use super::*;
use core::{cmp::Ordering, ops::*};

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

    /// Indicates whether the span is empty
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(Span::from(2..2).is_empty());
    /// assert!(!Span::from(2..3).is_empty());
    /// ```
    #[inline(always)]
    pub fn is_empty(&self) -> bool
    where
        T: Copy + PartialEq + Add<U, Output = T>,
        U: Copy,
    {
        self.start + self.count == self.start
    }
}

impl<T, U> Span<T, U>
where
    Span<T, U>: Into<Line<T>> + From<Line<T>>,
    T: PartialOrd,
{
    /// Returns the intersection between the sets, if any.
    ///
    /// ```
    /// use lset::*;
    ///
    /// let a = Span::new(0, 5);
    /// let b = Span::new(2, 5);
    /// let c = Span::new(5, 5);
    ///
    /// assert_eq!(a.intersection(b), Some(Span::new(2, 3)));
    /// assert_eq!(b.intersection(c), Some(Span::new(5, 2)));
    /// assert_eq!(a.intersection(a), Some(a));
    /// assert_eq!(b.intersection(b), Some(b));
    /// assert_eq!(c.intersection(c), Some(c));
    /// assert_eq!(a.intersection(c), None);
    /// ```
    pub fn intersection(self, other: Self) -> Option<Self> {
        self.into().intersection(other.into()).map(|x| x.into())
    }
}

impl<T: Add<T, Output = T>> Add<T> for Span<T> {
    type Output = Self;

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
    #[inline(always)]
    fn add(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            count: self.count + rhs,
        }
    }
}

impl<T: AddAssign<T>> AddAssign<T> for Span<T> {
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
    #[inline(always)]
    fn add_assign(&mut self, rhs: T) {
        self.count += rhs;
    }
}

impl<T: Sub<T, Output = T>> Sub<T> for Span<T> {
    type Output = Self;

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
    #[inline(always)]
    fn sub(self, rhs: T) -> Self::Output {
        Self {
            start: self.start,
            count: self.count - rhs,
        }
    }
}

impl<T: SubAssign<T>> SubAssign<T> for Span<T> {
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
    #[inline(always)]
    fn sub_assign(&mut self, rhs: T) {
        self.count -= rhs;
    }
}

impl<T: Copy + Sub<T, Output = T>> Shl<T> for Span<T> {
    type Output = Self;

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
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shl(self, rhs: T) -> Self::Output {
        Self {
            start: self.start - rhs,
            count: self.count,
        }
    }
}

impl<T: Copy + SubAssign<T>> ShlAssign<T> for Span<T> {
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
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn shl_assign(&mut self, rhs: T) {
        self.start -= rhs;
    }
}

impl<T: Copy + Add<T, Output = T>> Shr<T> for Span<T> {
    type Output = Self;

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
    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, rhs: T) -> Self::Output {
        Self {
            start: self.start + rhs,
            count: self.count,
        }
    }
}

impl<T: Copy + AddAssign<T>> ShrAssign<T> for Span<T> {
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
    #[inline(always)]
    #[allow(clippy::suspicious_op_assign_impl)]
    fn shr_assign(&mut self, rhs: T) {
        self.start += rhs;
    }
}

impl<T: PartialEq, U: PartialEq> PartialOrd for Span<T, U>
where
    Span<T, U>: Copy + Into<Line<T>>,
    Line<T>: PartialOrd,
{
    /// Compares two `Span` types.
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(Span::new(5, 5) <= Span::new(5, 5));
    /// assert!(Span::new(5, 5) >= Span::new(5, 5));
    /// assert!(Span::new(5, 5) < Span::new(10, 5));
    /// assert!(Span::new(10, 5) > Span::new(5, 5));
    /// ```
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        (*self).into().partial_cmp(&(*other).into())
    }
}

impl<T: Copy + Sub<T, Output = U>, U> From<Range<T>> for Span<T, U> {
    /// Converts a `Range` into a `Span`
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert_eq!(Span::new(5, 10), Span::from(5..15));
    /// assert_eq!(Span::new(5, 10), (5..15).into());
    /// ```
    #[inline(always)]
    fn from(value: Range<T>) -> Self {
        Self {
            start: value.start,
            count: value.end - value.start,
        }
    }
}

impl<T: Clone + Add<U, Output = T>, U> From<Span<T, U>> for Range<T> {
    /// Converts a `Span` into a `Range`
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert_eq!(5..15, std::ops::Range::from(Span::new(5, 10)));
    /// assert_eq!(5..15, Span::new(5, 10).into());
    /// ```
    #[inline(always)]
    fn from(value: Span<T, U>) -> Self {
        Self {
            start: value.start.clone(),
            end: value.start + value.count,
        }
    }
}

impl<T: Clone + Sub<T, Output = U>, U> From<Line<T>> for Span<T, U> {
    /// Converts a `Line` into a `Span`
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert_eq!(Span::new(5, 10), Span::from(Line::new(5, 15)));
    /// assert_eq!(Span::new(5, 10), (Line::new(5, 15)).into());
    /// ```
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
    /// Indicates whether the span contains a point
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(!Span::from(2..3).contains(&1));
    /// assert!(Span::from(2..3).contains(&2));
    /// assert!(!Span::from(2..3).contains(&3));

    /// assert!(!Span::from(3..2).contains(&1));
    /// assert!(!Span::from(3..2).contains(&2));
    /// assert!(!Span::from(3..2).contains(&3));
    /// ```
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
    /// Indicates whether the span contains another span
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// assert!(Span::from(4..8).contains(&Span::from(5..7)));
    /// assert!(Span::from(4..8).contains(&Span::from(4..7)));
    /// assert!(Span::from(4..8).contains(&Span::from(5..8)));
    /// assert!(Span::from(4..8).contains(&Span::from(4..8)));
    /// assert!(!Span::from(4..8).contains(&Span::from(3..8)));
    /// assert!(!Span::from(4..8).contains(&Span::from(4..9)));
    /// assert!(!Span::from(4..8).contains(&Span::from(3..9)));
    /// assert!(!Span::from(4..8).contains(&Span::from(2..10)));
    /// assert!(!Span::from(4..8).contains(&Span::from(6..5)));
    /// assert!(!Span::from(7..3).contains(&Span::from(5..6)));
    /// ```
    #[inline(always)]
    fn contains(&self, value: &Self) -> bool {
        self.clone().into().contains(&value.clone().into())
    }
}

impl<T, U> Split<Self> for Span<T, U>
where
    Self: Into<Line<T>>,
    Line<T>: Into<Self>,
    Line<T>: Split<Line<T>>,
{
    /// Splits a span by another span
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// let span = Span::from(2..5);
    /// assert_eq!(span.split(Span::from(1..4)), None);
    /// assert_eq!(span.split(Span::from(3..6)), None);
    /// assert_eq!(span.split(Span::from(2..2)), None);
    /// assert_eq!(span.split(Span::from(2..3)), Some((Span::from(2..2), Span::from(3..5))));
    /// assert_eq!(span.split(Span::from(3..3)), None);
    /// assert_eq!(span.split(Span::from(3..4)), Some((Span::from(2..3), Span::from(4..5))));
    /// assert_eq!(span.split(Span::from(4..4)), None);
    /// assert_eq!(span.split(Span::from(4..5)), Some((Span::from(2..4), Span::from(5..5))));
    /// assert_eq!(span.split(Span::from(5..5)), None);
    /// assert_eq!(span.split(span), Some((Span::from(2..2), Span::from(5..5))));
    /// ```
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
    /// Splits a span at a offset
    ///
    /// # Example
    ///
    /// ```
    /// use lset::*;
    /// let span = Span::from(2..4);
    /// assert_eq!(span.split(0), Some((Span::from(2..2), span)));
    /// assert_eq!(span.split(1), Some((Span::from(2..3), Span::from(3..4))));
    /// assert_eq!(span.split(2), Some((span, Span::from(4..4))));
    /// assert_eq!(span.split(3), None);
    /// ```
    #[inline(always)]
    fn split(self, at: U) -> Option<(Self, Self)> {
        let e = self.start.clone() + at;
        let (l, r) = self.into().split(e)?;
        Some((l.into(), r.into()))
    }
}
