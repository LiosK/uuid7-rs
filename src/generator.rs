//! UUIDv7 generator and related types.

#[cfg(not(feature = "std"))]
use core as std;
use std::{fmt, iter};

use crate::Uuid;

pub mod with_rand08;
pub mod with_rand09;

/// A trait that defines the minimum random number generator interface for [`V7Generator`].
pub trait Rng {
    /// Returns the next random `u32`.
    fn next_u32(&mut self) -> u32;

    /// Returns the next random `u64`.
    fn next_u64(&mut self) -> u64;
}

/// A trait that defines the minimum system clock interface for [`V7Generator`].
pub trait TimeSource {
    /// Returns the current Unix timestamp in milliseconds.
    fn unix_ts_ms(&mut self) -> u64;
}

/// Represents a UUIDv7 generator that encapsulates a counter and guarantees the monotonic order of
/// UUIDs generated within the same millisecond.
///
/// This type provides the interface to customize the random number generator, system clock, and
/// clock rollback handling of a UUIDv7 generator. It also helps control the scope of guaranteed
/// order of the generated UUIDs. The following example guarantees the process-wide (cross-thread)
/// monotonicity using Rust's standard synchronization mechanism.
///
/// # Examples
///
/// ```rust
/// # #[cfg(feature = "rand09")]
/// # {
/// use rand::{rngs::StdRng, SeedableRng as _};
/// use std::{sync, thread};
/// use uuid7::V7Generator;
///
/// let rng = StdRng::from_os_rng();
/// let g = sync::Arc::new(sync::Mutex::new(V7Generator::with_rand09(rng)));
/// thread::scope(|s| {
///     for i in 0..4 {
///         let g = sync::Arc::clone(&g);
///         s.spawn(move || {
///             for _ in 0..8 {
///                 println!("{} by thread {}", g.lock().unwrap().generate(), i);
///                 thread::yield_now();
///             }
///         });
///     }
/// });
/// # }
/// ```
///
/// # Generator functions
///
/// The generator comes with four different methods that generate a UUIDv7:
///
/// | Flavor                     | Timestamp | On big clock rewind |
/// | -------------------------- | --------- | ------------------- |
/// | [`generate`]               | Now       | Resets generator    |
/// | [`generate_or_abort`]      | Now       | Returns `None`      |
/// | [`generate_or_reset_core`] | Argument  | Resets generator    |
/// | [`generate_or_abort_core`] | Argument  | Returns `None`      |
///
/// All of the four return a monotonically increasing UUID by reusing the previous timestamp even
/// if the one provided is smaller than the immediately preceding UUID's. However, when such a
/// clock rollback is considered significant (by default, more than ten seconds):
///
/// 1.  `generate` (or_reset) methods reset the generator and return a new UUID based on the given
///     timestamp, breaking the increasing order of UUIDs.
/// 2.  `or_abort` variants abort and return `None` immediately.
///
/// The `core` functions offer low-level primitives to customize the behavior.
///
/// [`generate`]: V7Generator::generate
/// [`generate_or_abort`]: V7Generator::generate_or_abort
/// [`generate_or_reset_core`]: V7Generator::generate_or_reset_core
/// [`generate_or_abort_core`]: V7Generator::generate_or_abort_core
#[derive(Clone, Eq, PartialEq, Default)]
pub struct V7Generator<R, T = StdSystemTime> {
    /// Biased by one to distinguish zero (uninitialized) and zero (UNIX epoch).
    timestamp_biased: u64,
    counter: u64,

    /// The random number generator used by the generator.
    rng: R,

    /// The system clock used by the generator.
    time_source: T,
}

impl<R> V7Generator<R> {
    /// Creates a generator instance.
    ///
    /// Use [`V7Generator::with_rand09()`] to create a generator with the random number generators
    /// from `rand` crate. Although this constructor accepts `rand::RngCore` (v0.8) types for
    /// historical reasons, such behavior is deprecated and will be removed in the future.
    pub const fn new(rng: R) -> Self {
        Self {
            timestamp_biased: 0,
            counter: 0,
            rng,
            time_source: StdSystemTime,
        }
    }
}

impl<R: Rng, T: TimeSource> V7Generator<R, T> {
    /// Generates a new UUIDv7 object from the current timestamp, or resets the generator upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    pub fn generate(&mut self) -> Uuid {
        let unix_ts_ms = self.time_source.unix_ts_ms();
        self.generate_or_reset_core(unix_ts_ms, 10_000)
    }

    /// Generates a new UUIDv7 object from the current timestamp, or returns `None` upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    pub fn generate_or_abort(&mut self) -> Option<Uuid> {
        let unix_ts_ms = self.time_source.unix_ts_ms();
        self.generate_or_abort_core(unix_ts_ms, 10_000)
    }
}

impl<R: Rng, T> V7Generator<R, T> {
    /// Generates a new UUIDv7 object from the `unix_ts_ms` passed, or resets the generator upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. A suggested value is `10_000` (milliseconds).
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a 48-bit unsigned integer.
    pub fn generate_or_reset_core(&mut self, unix_ts_ms: u64, rollback_allowance: u64) -> Uuid {
        if let Some(value) = self.generate_or_abort_core(unix_ts_ms, rollback_allowance) {
            value
        } else {
            // reset state and resume
            self.timestamp_biased = 0;
            self.generate_or_abort_core(unix_ts_ms, rollback_allowance)
                .unwrap()
        }
    }

    /// Generates a new UUIDv7 object from the `unix_ts_ms` passed, or returns `None` upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. A suggested value is `10_000` (milliseconds).
    ///
    /// # Panics
    ///
    /// Panics if `unix_ts_ms` is not a 48-bit unsigned integer.
    pub fn generate_or_abort_core(
        &mut self,
        unix_ts_ms: u64,
        rollback_allowance: u64,
    ) -> Option<Uuid> {
        const MAX_COUNTER: u64 = (1 << 42) - 1;

        assert!(
            unix_ts_ms < 1 << 48,
            "`unix_ts_ms` must be a 48-bit unsigned integer"
        );
        assert!(
            rollback_allowance < 1 << 48,
            "`rollback_allowance` out of reasonable range"
        );

        let unix_ts_ms = unix_ts_ms + 1;
        if unix_ts_ms > self.timestamp_biased {
            self.timestamp_biased = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + rollback_allowance >= self.timestamp_biased {
            // go on with previous timestamp if new one is not much smaller
            self.counter += 1;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp_biased += 1;
                self.counter = self.rng.next_u64() & MAX_COUNTER;
            }
        } else {
            // abort if clock went backwards to unbearable extent
            return None;
        }

        Some(Uuid::from_fields_v7(
            self.timestamp_biased - 1,
            (self.counter >> 30) as u16,
            ((self.counter & 0x3fff_ffff) << 32) | self.rng.next_u32() as u64,
        ))
    }

    /// Generates a new UUIDv4 object utilizing the random number generator inside.
    #[cfg(feature = "global_gen")]
    pub(crate) fn generate_v4(&mut self) -> Uuid {
        let mut bytes = [0u8; 16];
        bytes[..8].copy_from_slice(&self.rng.next_u64().to_le_bytes());
        bytes[8..].copy_from_slice(&self.rng.next_u64().to_le_bytes());
        bytes[6] = 0x40 | (bytes[6] >> 4);
        bytes[8] = 0x80 | (bytes[8] >> 2);
        Uuid::from(bytes)
    }
}

impl<R, T> fmt::Debug for V7Generator<R, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        f.debug_struct("V7Generator").finish()
    }
}

/// Supports operations as an infinite iterator that produces a new UUIDv7 object for each call of
/// `next()`.
///
/// # Examples
///
/// ```rust
/// # #[cfg(feature = "rand09")]
/// # {
/// use uuid7::V7Generator;
///
/// V7Generator::with_rand09(rand::rng())
///     .enumerate()
///     .skip(4)
///     .take(4)
///     .for_each(|(i, e)| println!("[{}] {}", i, e));
/// # }
/// ```
impl<R: Rng, T: TimeSource> Iterator for V7Generator<R, T> {
    type Item = Uuid;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.generate())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

impl<R: Rng, T: TimeSource> iter::FusedIterator for V7Generator<R, T> {}

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

/// A mock random number generator for testing.
#[cfg(all(test, feature = "std"))]
struct MockRng;

#[cfg(all(test, feature = "std"))]
impl Rng for MockRng {
    fn next_u32(&mut self) -> u32 {
        rand::random()
    }

    fn next_u64(&mut self) -> u64 {
        rand::random()
    }
}

#[cfg(all(test, feature = "std"))]
mod tests_generate_or_reset {
    use super::{MockRng, V7Generator};

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g = V7Generator::new(MockRng);
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
        let mut g = V7Generator::new(MockRng);
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

#[cfg(all(test, feature = "std"))]
mod tests_generate_or_abort {
    use super::{MockRng, V7Generator};

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g = V7Generator::new(MockRng);
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
        let mut g = V7Generator::new(MockRng);
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
