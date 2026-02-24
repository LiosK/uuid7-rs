//! UUIDv7 generator and related types.

#[cfg(not(feature = "std"))]
use core as std;
use std::{fmt, iter};

use crate::Uuid;

/// A trait that defines the minimum random number generator interface for [`V7Generator`].
pub trait RandSource {
    /// Returns the next random `u32`.
    fn next_u32(&mut self) -> u32;

    /// Returns the next random `u64`.
    fn next_u64(&mut self) -> u64;
}

#[deprecated(since = "1.5.0", note = "use `RandSource` instead")]
pub use RandSource as Rng;

pub mod with_rand010;
pub mod with_rand08;
pub mod with_rand09;

/// A trait that defines the minimum system clock interface for [`V7Generator`].
pub trait TimeSource {
    /// Returns the current Unix timestamp in milliseconds.
    fn unix_ts_ms(&mut self) -> u64;
}

/// Represents a UUIDv7 generator that encapsulates a counter and guarantees the monotonic order of
/// UUIDs generated within the same millisecond.
///
/// This type provides the interface to customize the random number generator, system clock, and
/// clock rollback handling of a UUIDv7 generator.
///
/// # Examples
///
/// This structure is typically instantiated with a random number generator from `rand` crate via
/// the adapters enabled by the corresponding cargo features.
///
/// ```rust
/// # #[cfg(all(feature = "std", feature = "rand010"))]
/// # {
/// use uuid7::V7Generator;
///
/// let mut g = V7Generator::with_rand010(rand::rng());
/// println!("{}", g.generate());
/// if let Some(value) = g.generate_or_abort() {
///     println!("{}", value);
/// }
/// # }
/// ```
///
/// # Generator functions
///
/// The generator comes with four different methods that generate a UUIDv7:
///
/// | Flavor                        | Timestamp | On big clock rewind |
/// | ----------------------------- | --------- | ------------------- |
/// | [`generate`]                  | Now       | Resets generator    |
/// | [`generate_or_abort`]         | Now       | Returns `None`      |
/// | [`generate_or_reset_with_ts`] | Argument  | Resets generator    |
/// | [`generate_or_abort_with_ts`] | Argument  | Returns `None`      |
///
/// All of the four return a monotonically increasing UUID by reusing the previous timestamp even
/// if the one provided is smaller than the immediately preceding UUID's. However, when such a
/// clock rollback is considered significant (by default, more than ten seconds):
///
/// 1.  `generate` (or_reset) methods reset the generator and return a new UUID based on the given
///     timestamp, breaking the increasing order of UUIDs.
/// 2.  `or_abort` variants abort and return `None` immediately.
///
/// The `with_ts` functions accepts the timestamp as an argument.
///
/// [`generate`]: V7Generator::generate
/// [`generate_or_abort`]: V7Generator::generate_or_abort
/// [`generate_or_reset_with_ts`]: V7Generator::generate_or_reset_with_ts
/// [`generate_or_abort_with_ts`]: V7Generator::generate_or_abort_with_ts
#[derive(Clone, Eq, PartialEq)]
pub struct V7Generator<R, T = StdSystemTime> {
    /// Biased by one to distinguish zero (uninitialized) and zero (UNIX epoch).
    timestamp_biased: u64,
    counter: u64,

    /// The random number generator used by the generator.
    rand_source: R,

    /// The system clock used by the generator.
    time_source: T,

    /// The amount of `unix_ts_ms` rollback that is considered significant (in milliseconds).
    rollback_allowance: u64,
}

impl<R> V7Generator<R> {
    /// Creates a generator object.
    ///
    /// Use [`V7Generator::with_rand010()`] to create a generator with the random number generators
    /// from `rand` crate. Although this constructor accepts `rand::RngCore` (v0.8) types for
    /// historical reasons, such behavior is deprecated and will be removed in the future.
    pub const fn new(rand_source: R) -> Self {
        Self::with_rand_and_time_sources(rand_source, StdSystemTime)
    }
}

impl<R, T> V7Generator<R, T> {
    /// Creates a generator object with specified random number generator and system clock.
    ///
    /// Use [`with_rand010::Adapter`] to pass a random number generator from `rand` crate. Although
    /// this constructor accepts `rand::RngCore` (v0.8) types for historical reasons, such behavior
    /// is deprecated and will be removed in the future.
    pub const fn with_rand_and_time_sources(rand_source: R, time_source: T) -> Self {
        Self {
            timestamp_biased: 0,
            counter: 0,
            rand_source,
            time_source,
            rollback_allowance: 10_000, // 10 seconds in milliseconds
        }
    }

    /// Sets the `rollback_allowance` parameter of the generator.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. The default value is `10_000` (milliseconds). See the
    /// [`V7Generator`] type documentation for the treatment of the significant rollback.
    pub fn set_rollback_allowance(&mut self, rollback_allowance: u64) {
        if rollback_allowance >= 1 << 48 {
            panic!("`rollback_allowance` out of reasonable range");
        }
        self.rollback_allowance = rollback_allowance;
    }

    /// Resets the internal state of the generator.
    pub(crate) fn reset_state(&mut self) {
        self.timestamp_biased = 0;
        self.counter = 0;
    }

    /// Replaces the random number generator with the argument, returning the old one.
    #[cfg(all(unix, feature = "global_gen"))]
    pub(crate) fn replace_rand_source(&mut self, rand_source: R) -> R {
        std::mem::replace(&mut self.rand_source, rand_source)
    }
}

impl<R: RandSource, T: TimeSource> V7Generator<R, T> {
    /// Generates a new UUIDv7 object from the current timestamp, or resets the generator upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    pub fn generate(&mut self) -> Uuid {
        let unix_ts_ms = self.time_source.unix_ts_ms();
        self.generate_or_reset_with_ts(unix_ts_ms)
    }

    /// Generates a new UUIDv7 object from the current timestamp, or returns `None` upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    pub fn generate_or_abort(&mut self) -> Option<Uuid> {
        let unix_ts_ms = self.time_source.unix_ts_ms();
        self.generate_or_abort_with_ts(unix_ts_ms)
    }
}

impl<R: RandSource, T> V7Generator<R, T> {
    /// Generates a new UUIDv7 object from the `unix_ts_ms` passed, or resets the generator upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a 48-bit unsigned integer.
    pub fn generate_or_reset_with_ts(&mut self, unix_ts_ms: u64) -> Uuid {
        if let Some(value) = self.generate_or_abort_with_ts(unix_ts_ms) {
            value
        } else {
            // reset state and resume
            self.reset_state();
            self.generate_or_abort_with_ts(unix_ts_ms).unwrap()
        }
    }

    /// Generates a new UUIDv7 object from the `unix_ts_ms` passed, or returns `None` upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a 48-bit unsigned integer.
    pub fn generate_or_abort_with_ts(&mut self, unix_ts_ms: u64) -> Option<Uuid> {
        if unix_ts_ms >= 1 << 48 {
            panic!("`unix_ts_ms` must be a 48-bit unsigned integer");
        }

        const MAX_COUNTER: u64 = (1 << 42) - 1;
        let unix_ts_ms = unix_ts_ms + 1;
        if unix_ts_ms > self.timestamp_biased {
            self.timestamp_biased = unix_ts_ms;
            self.counter = self.rand_source.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + self.rollback_allowance >= self.timestamp_biased {
            // go on with previous timestamp if new one is not much smaller
            self.counter += 1;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp_biased += 1;
                self.counter = self.rand_source.next_u64() & MAX_COUNTER;
            }
        } else {
            // abort if clock went backwards to unbearable extent
            return None;
        }

        Some(Uuid::from_fields_v7(
            self.timestamp_biased - 1,
            (self.counter >> 30) as u16,
            ((self.counter & 0x3fff_ffff) << 32) | self.rand_source.next_u32() as u64,
        ))
    }

    /// Generates a new UUIDv4 object utilizing the random number generator inside.
    #[cfg(feature = "global_gen")]
    pub(crate) fn generate_v4(&mut self) -> Uuid {
        let mut bytes = [0u8; 16];
        bytes[..8].copy_from_slice(&self.rand_source.next_u64().to_le_bytes());
        bytes[8..].copy_from_slice(&self.rand_source.next_u64().to_le_bytes());
        bytes[6] = 0x40 | (bytes[6] >> 4);
        bytes[8] = 0x80 | (bytes[8] >> 2);
        Uuid::from(bytes)
    }

    /// Generates a new UUIDv7 object from the `unix_ts_ms` passed, or resets the generator upon
    /// significant timestamp rollback.
    ///
    /// This method is a deprecated version of `generate_or_reset_with_ts()` that accepts the
    /// `rollback_allowance` parameter as an argument, rather than using [the generator-level
    /// parameter](Self::set_rollback_allowance).
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a 48-bit unsigned integer.
    #[deprecated(since = "1.5.0", note = "use `generate_or_reset_with_ts()` instead")]
    pub fn generate_or_reset_core(&mut self, unix_ts_ms: u64, rollback_allowance: u64) -> Uuid {
        #[allow(deprecated)]
        if let Some(value) = self.generate_or_abort_core(unix_ts_ms, rollback_allowance) {
            value
        } else {
            // reset state and resume
            self.reset_state();
            self.generate_or_abort_core(unix_ts_ms, rollback_allowance)
                .unwrap()
        }
    }

    /// Generates a new UUIDv7 object from the `unix_ts_ms` passed, or returns `None` upon
    /// significant timestamp rollback.
    ///
    /// This method is a deprecated version of `generate_or_abort_with_ts()` that accepts the
    /// `rollback_allowance` parameter as an argument, rather than using [the generator-level
    /// parameter](Self::set_rollback_allowance).
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a 48-bit unsigned integer.
    #[deprecated(since = "1.5.0", note = "use `generate_or_abort_with_ts()` instead")]
    pub fn generate_or_abort_core(
        &mut self,
        unix_ts_ms: u64,
        rollback_allowance: u64,
    ) -> Option<Uuid> {
        struct PanicGuard<'a, R, T> {
            orig_rollback_allowance: u64,
            inner: &'a mut V7Generator<R, T>,
        }
        impl<R, T> Drop for PanicGuard<'_, R, T> {
            fn drop(&mut self) {
                self.inner.rollback_allowance = self.orig_rollback_allowance;
            }
        }

        let guard = PanicGuard {
            orig_rollback_allowance: self.rollback_allowance,
            inner: self,
        };
        guard.inner.set_rollback_allowance(rollback_allowance);
        guard.inner.generate_or_abort_with_ts(unix_ts_ms)
    }
}

impl<R: Default, T: Default> Default for V7Generator<R, T> {
    fn default() -> Self {
        Self::with_rand_and_time_sources(R::default(), T::default())
    }
}

impl<R, T: fmt::Debug> fmt::Debug for V7Generator<R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("V7Generator")
            .field("time_source", &self.time_source)
            .field("rollback_allowance", &self.rollback_allowance)
            .finish()
    }
}

/// Supports operations as an infinite iterator that produces a new UUIDv7 object for each call of
/// `next()`.
///
/// # Examples
///
/// ```rust
/// # #[cfg(all(feature = "std", feature = "rand010"))]
/// # {
/// use uuid7::V7Generator;
///
/// V7Generator::with_rand010(rand::rng())
///     .enumerate()
///     .skip(4)
///     .take(4)
///     .for_each(|(i, e)| println!("[{}] {}", i, e));
/// # }
/// ```
impl<R: RandSource, T: TimeSource> Iterator for V7Generator<R, T> {
    type Item = Uuid;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.generate())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

impl<R: RandSource, T: TimeSource> iter::FusedIterator for V7Generator<R, T> {}

/// The default [`TimeSource`] that uses [`std::time::SystemTime`].
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct StdSystemTime;

#[cfg(feature = "std")]
impl TimeSource for StdSystemTime {
    fn unix_ts_ms(&mut self) -> u64 {
        use std::time;
        time::SystemTime::now()
            .duration_since(time::UNIX_EPOCH)
            .expect("clock may have gone backwards")
            .as_millis() as u64
    }
}

#[cfg(test)]
mod tests;

/// Obsolete test cases
#[cfg(test)]
#[allow(deprecated)]
mod tests_generate_or_reset {
    use super::V7Generator;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g = V7Generator::for_testing();
        let mut prev = g.generate_or_reset_core(ts, 10_000);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g.generate_or_reset_core(ts - i.min(4_000), 10_000);
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[..6] >= ts.to_be_bytes()[2..]);
    }

    /// Breaks increasing order of UUIDs if timestamp goes backwards a lot
    #[test]
    fn breaks_increasing_order_of_uuids_if_timestamp_goes_backwards_a_lot() {
        let ts = 0x0123_4567_89abu64;
        let mut g = V7Generator::for_testing();
        let mut prev = g.generate_or_reset_core(ts, 10_000);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);

        let mut curr = g.generate_or_reset_core(ts - 10_000, 10_000);
        assert!(prev < curr);

        prev = curr;
        curr = g.generate_or_reset_core(ts - 10_001, 10_000);
        assert!(prev > curr);
        assert_eq!(curr.as_bytes()[..6], (ts - 10_001).to_be_bytes()[2..]);

        prev = curr;
        curr = g.generate_or_reset_core(ts - 10_002, 10_000);
        assert!(prev < curr);
    }
}

/// Obsolete test cases
#[cfg(test)]
#[allow(deprecated)]
mod tests_generate_or_abort {
    use super::V7Generator;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g = V7Generator::for_testing();
        let mut prev = g.generate_or_abort_core(ts, 10_000).unwrap();
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g.generate_or_abort_core(ts - i.min(4_000), 10_000).unwrap();
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[..6] >= ts.to_be_bytes()[2..]);
    }

    /// Returns None if timestamp goes backwards a lot
    #[test]
    fn returns_none_if_timestamp_goes_backwards_a_lot() {
        let ts = 0x0123_4567_89abu64;
        let mut g = V7Generator::for_testing();
        let prev = g.generate_or_abort_core(ts, 10_000).unwrap();
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);

        let mut curr = g.generate_or_abort_core(ts - 10_000, 10_000);
        assert!(prev < curr.unwrap());

        curr = g.generate_or_abort_core(ts - 10_001, 10_000);
        assert!(curr.is_none());

        curr = g.generate_or_abort_core(ts - 10_002, 10_000);
        assert!(curr.is_none());
    }
}
