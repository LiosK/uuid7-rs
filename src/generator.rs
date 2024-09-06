//! UUIDv7 generator and related types.

use crate::Uuid;

pub mod with_rand08;

/// A trait that defines the minimum random number generator interface for [`V7Generator`].
pub trait Rng {
    /// Returns the next random `u32`.
    fn next_u32(&mut self) -> u32;

    /// Returns the next random `u64`.
    fn next_u64(&mut self) -> u64;

    /// Fills `dest` with random data.
    fn fill_bytes(&mut self, dest: &mut [u8]);
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
/// use rand::rngs::OsRng;
/// use std::{sync, thread};
/// use uuid7::V7Generator;
///
/// let g = sync::Arc::new(sync::Mutex::new(V7Generator::with_rand08(OsRng)));
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
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct V7Generator<R> {
    timestamp: u64,
    counter: u64,

    /// The random number generator used by the generator.
    rng: R,
}

impl<R: Rng> V7Generator<R> {
    /// Creates a generator instance.
    pub const fn new(rng: R) -> Self {
        Self {
            timestamp: 0,
            counter: 0,
            rng,
        }
    }

    /// Generates a new UUIDv7 object from the current timestamp, or resets the generator upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate(&mut self) -> Uuid {
        use std::time;
        self.generate_or_reset_core(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backwards")
                .as_millis() as u64,
            10_000,
        )
    }

    /// Generates a new UUIDv7 object from the current timestamp, or returns `None` upon
    /// significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate_or_abort(&mut self) -> Option<Uuid> {
        use std::time;
        self.generate_or_abort_core(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backwards")
                .as_millis() as u64,
            10_000,
        )
    }

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
    /// Panics if `unix_ts_ms` is not a 48-bit positive integer.
    pub fn generate_or_reset_core(&mut self, unix_ts_ms: u64, rollback_allowance: u64) -> Uuid {
        if let Some(value) = self.generate_or_abort_core(unix_ts_ms, rollback_allowance) {
            value
        } else {
            // reset state and resume
            self.timestamp = 0;
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
    /// Panics if `unix_ts_ms` is not a 48-bit positive integer.
    pub fn generate_or_abort_core(
        &mut self,
        unix_ts_ms: u64,
        rollback_allowance: u64,
    ) -> Option<Uuid> {
        const MAX_COUNTER: u64 = (1 << 42) - 1;

        assert!(
            0 < unix_ts_ms && unix_ts_ms < 1 << 48,
            "`unix_ts_ms` must be a 48-bit positive integer"
        );
        assert!(
            rollback_allowance < 1 << 48,
            "`rollback_allowance` out of reasonable range"
        );

        if unix_ts_ms > self.timestamp {
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + rollback_allowance >= self.timestamp {
            // go on with previous timestamp if new one is not much smaller
            self.counter += 1;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp += 1;
                self.counter = self.rng.next_u64() & MAX_COUNTER;
            }
        } else {
            // abort if clock went backwards to unbearable extent
            return None;
        }

        Some(Uuid::from_fields_v7(
            self.timestamp,
            (self.counter >> 30) as u16,
            ((self.counter & 0x3fff_ffff) << 32) | self.rng.next_u32() as u64,
        ))
    }

    /// Generates a new UUIDv4 object utilizing the random number generator inside.
    #[cfg(feature = "global_gen")]
    pub(crate) fn generate_v4(&mut self) -> Uuid {
        let mut bytes = [0u8; 16];
        self.rng.fill_bytes(&mut bytes);
        bytes[6] = 0x40 | (bytes[6] >> 4);
        bytes[8] = 0x80 | (bytes[8] >> 2);
        Uuid::from(bytes)
    }
}

/// Supports operations as an infinite iterator that produces a new UUIDv7 object for each call of
/// `next()`.
///
/// # Examples
///
/// ```rust
/// use uuid7::V7Generator;
///
/// V7Generator::with_rand08(rand::thread_rng())
///     .enumerate()
///     .skip(4)
///     .take(4)
///     .for_each(|(i, e)| println!("[{}] {}", i, e));
/// ```
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<R: Rng> Iterator for V7Generator<R> {
    type Item = Uuid;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.generate())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<R: Rng> std::iter::FusedIterator for V7Generator<R> {}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests_generate_or_reset {
    use super::{with_rand08, V7Generator};

    type ThreadGen = V7Generator<with_rand08::Adapter<rand::rngs::ThreadRng>>;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: ThreadGen = Default::default();
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
        let mut g: ThreadGen = Default::default();
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

#[cfg(feature = "std")]
#[cfg(test)]
mod tests_generate_or_abort {
    use super::{with_rand08, V7Generator};

    type ThreadGen = V7Generator<with_rand08::Adapter<rand::rngs::ThreadRng>>;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: ThreadGen = Default::default();
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
        let mut g: ThreadGen = Default::default();
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
