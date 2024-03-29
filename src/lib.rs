// SPDX-License-Identifier: Apache-2.0

//! This crate contains types for measuring linear sets by either the end
//! points (`Line`) or by a starting point and the number of elements (`Span`).
//!
//! In the interest of zero-cost abstractions, all methods are always inlined
//! for maximum compiler optimization. Thus, you only pay for the conversions
//! that are actually used.

#![no_std]
#![forbid(unsafe_code, clippy::expect_used, clippy::panic)]
#![deny(
    rust_2018_idioms,
    unused_lifetimes,
    unused_qualifications,
    clippy::all,
    missing_docs
)]

mod line;
mod span;

pub use crate::line::Line;
pub use crate::span::Span;

/// Determines whether a set contains an element
pub trait Contains<T> {
    /// Returns whether or not the set contains the element
    fn contains(&self, value: &T) -> bool;
}

/// Splits the set
pub trait Split<T>: Sized {
    /// Splits the set
    ///
    /// Returns `None` if `at` is not in the set.
    fn split(self, at: T) -> Option<(Self, Self)>;
}
