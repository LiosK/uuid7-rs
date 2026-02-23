//! Integration with `rand` (v0.10) crate.

#![cfg(feature = "rand010")]

use super::{RandSource, V7Generator};
use rand_core010::Rng;

/// An adapter that implements [`RandSource`] for [`Rng`] types.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Adapter<T>(/** The wrapped [`Rng`] type. */ pub T);

impl<T: Rng> RandSource for Adapter<T> {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
}

impl<T: Rng> V7Generator<Adapter<T>> {
    /// Creates a generator object with a specified random number generator that implements [`Rng`]
    /// from `rand` (v0.10) crate.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(all(feature = "std", feature = "rand010"))]
    /// # {
    /// use uuid7::V7Generator;
    ///
    /// let mut g = V7Generator::with_rand010(rand::rng());
    /// println!("{}", g.generate());
    /// # }
    /// ```
    pub const fn with_rand010(rng: T) -> Self {
        Self::new(Adapter(rng))
    }
}
