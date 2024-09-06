//!  Integration with `rand` (v0.8) crate.

use super::{Rng, V7Generator};
use rand::RngCore;

/// An adapter that implements this crate's [`Rng`] for [`RngCore`] types.
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Adapter<T>(/** The wrapped [`RngCore`] type. */ pub T);

impl<T: RngCore> Rng for Adapter<T> {
    fn next_u32(&mut self) -> u32 {
        self.0.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.0.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.0.fill_bytes(dest)
    }
}

impl<T: RngCore> V7Generator<Adapter<T>> {
    /// Creates a generator instance with a specified random number generator that implements
    /// [`RngCore`] from `rand` (v0.8) crate.
    pub const fn with_rand08(rng: T) -> Self {
        Self::new(Adapter(rng))
    }
}

/// This is a deprecated blanket impl retained for backward compatibility. Do not depend on this
/// impl; use [`V7Generator::with_rand08()`] instead.
impl<T: RngCore> Rng for T {
    fn next_u32(&mut self) -> u32 {
        self.next_u32()
    }

    fn next_u64(&mut self) -> u64 {
        self.next_u64()
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.fill_bytes(dest)
    }
}
