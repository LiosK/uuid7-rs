//! Integration with `rand` (v0.8) crate.
//!
//!  Currently, this module is always enabled and cannot be turned off. This behavior is deprecated
//!  and for backward compatibility only. Enable `rand08` crate feature explicitly when needed.

#![cfg_attr(docsrs, doc(cfg(feature = "rand08")))]
#![deprecated(since = "1.5.0", note = "use a newer version of `rand` crate")]

use super::{RandSource, V7Generator};
use rand_core06::RngCore;

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
    /// [`RngCore`] from `rand` (v0.8) crate.
    pub const fn with_rand08(rng: T) -> Self {
        Self::new(Adapter(rng))
    }
}

/// This is a deprecated blanket impl retained for backward compatibility. Do not depend on this
/// impl; use [`V7Generator::with_rand08()`] instead.
impl<T: RngCore> RandSource for T {
    fn next_u32(&mut self) -> u32 {
        self.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.next_u64()
    }
}
