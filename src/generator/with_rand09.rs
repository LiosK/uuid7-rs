//! Integration with `rand` (v0.9) crate.

#![cfg(feature = "rand09")]

use super::{RandSource, V7Generator};
use rand_core09::RngCore;

/// An adapter that implements [`RandSource`] for [`RngCore`] types.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Adapter<T>(/** The wrapped [`RngCore`] type. */ pub T);

impl<T: RngCore> RandSource for Adapter<T> {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }
}

impl<T: RngCore> V7Generator<Adapter<T>> {
    /// Creates a generator object with a specified random number generator that implements
    /// [`RngCore`] from `rand` (v0.9) crate.
    ///
    /// # Examples
    ///
    /// ```ignore
    /// use uuid7::V7Generator;
    ///
    /// let mut g = V7Generator::with_rand09(rand::rng());
    /// println!("{}", g.generate());
    /// ```
    pub const fn with_rand09(rng: T) -> Self {
        Self::new(Adapter(rng))
    }
}
