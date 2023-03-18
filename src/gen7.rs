//! UUIDv7 generator-related types

use crate::Uuid;

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
/// let g = sync::Arc::new(sync::Mutex::new(V7Generator::new(OsRng)));
/// let handle = {
///     let g = sync::Arc::clone(&g);
///     thread::spawn(move || {
///         for _ in 0..8 {
///             println!("{} by child", g.lock().unwrap().generate());
///             thread::yield_now();
///         }
///     })
/// };
///
/// for _ in 0..8 {
///     println!("{} by parent", g.lock().unwrap().generate());
///     thread::yield_now();
/// }
///
/// handle.join().unwrap();
/// ```
///
/// # Generator functions
///
/// The generator offers four different methods to generate a UUIDv7:
///
/// | Flavor                      | Timestamp | On big clock rewind |
/// | --------------------------- | --------- | ------------------- |
/// | [`generate`]                | Now       | Rewinds state       |
/// | [`generate_no_rewind`]      | Now       | Returns `None`      |
/// | [`generate_core`]           | Argument  | Rewinds state       |
/// | [`generate_core_no_rewind`] | Argument  | Returns `None`      |
///
/// Each method returns monotonically increasing UUIDs unless a timestamp provided is significantly
/// (by ten seconds or more by default) smaller than the one embedded in the immediately preceding
/// UUID. If such a significant clock rollback is detected, the standard `generate` rewinds the
/// generator state and returns a new UUID based on the current timestamp, whereas `no_rewind`
/// variants keep the state untouched and return `None`. `core` functions offer low-level
/// primitives.
///
/// [`generate`]: V7Generator::generate
/// [`generate_no_rewind`]: V7Generator::generate_no_rewind
/// [`generate_core`]: V7Generator::generate_core
/// [`generate_core_no_rewind`]: V7Generator::generate_core_no_rewind
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct V7Generator<R> {
    timestamp: u64,
    counter: u64,

    /// Random number generator used by the generator.
    rng: R,
}

impl<R: rand::RngCore> V7Generator<R> {
    /// Creates a generator instance.
    pub const fn new(rng: R) -> Self {
        Self {
            timestamp: 0,
            counter: 0,
            rng,
        }
    }

    /// Generates a new UUIDv7 object from the current timestamp.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate(&mut self) -> Uuid {
        use std::time;
        self.generate_core(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backward")
                .as_millis() as u64,
            10_000,
        )
    }

    /// Generates a new UUIDv7 object from the current timestamp, guaranteeing the monotonic order
    /// of generated IDs despite a significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate_no_rewind(&mut self) -> Option<Uuid> {
        use std::time;
        self.generate_core_no_rewind(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backward")
                .as_millis() as u64,
            10_000,
        )
    }

    /// Generates a new UUIDv7 object from a given `unix_ts_ms`.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. A suggested value is `10_000` (milliseconds).
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a 48-bit positive integer.
    pub fn generate_core(&mut self, unix_ts_ms: u64, rollback_allowance: u64) -> Uuid {
        if let Some(value) = self.generate_core_no_rewind(unix_ts_ms, rollback_allowance) {
            value
        } else {
            // reset state and resume
            self.timestamp = 0;
            self.generate_core_no_rewind(unix_ts_ms, rollback_allowance)
                .unwrap()
        }
    }

    /// Generates a new UUIDv7 object from a given `unix_ts_ms`, guaranteeing the monotonic order
    /// of generated IDs despite a significant timestamp rollback.
    ///
    /// See the [`V7Generator`] type documentation for the description.
    ///
    /// The `rollback_allowance` parameter specifies the amount of `unix_ts_ms` rollback that is
    /// considered significant. A suggested value is `10_000` (milliseconds).
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a 48-bit positive integer.
    pub fn generate_core_no_rewind(
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
            "too large `rollback_allowance`"
        );

        if unix_ts_ms > self.timestamp {
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + rollback_allowance > self.timestamp {
            // go on with previous timestamp if new one is not much smaller
            self.counter += 1;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp += 1;
                self.counter = self.rng.next_u64() & MAX_COUNTER;
            }
        } else {
            // abort if clock moves back to unbearable extent
            return None;
        }

        Some(Uuid::from_fields_v7(
            self.timestamp,
            (self.counter >> 30) as u16,
            ((self.counter & 0x3fff_ffff) << 32) | self.rng.next_u32() as u64,
        ))
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
/// V7Generator::new(rand::thread_rng())
///     .enumerate()
///     .skip(4)
///     .take(4)
///     .for_each(|(i, e)| println!("[{i}] {e}"));
/// ```
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<R: rand::RngCore> Iterator for V7Generator<R> {
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
impl<R: rand::RngCore> std::iter::FusedIterator for V7Generator<R> {}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests_generate_core {
    use super::V7Generator;
    use rand::rngs::ThreadRng;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: V7Generator<ThreadRng> = Default::default();
        let mut prev = g.generate_core(ts, 10_000);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g.generate_core(ts - i.min(4_000), 10_000);
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[..6] >= ts.to_be_bytes()[2..]);
    }

    /// Breaks increasing order of UUIDs if timestamp moves backward a lot
    #[test]
    fn breaks_increasing_order_of_uuids_if_timestamp_moves_backward_a_lot() {
        let ts = 0x0123_4567_89abu64;
        let mut g: V7Generator<ThreadRng> = Default::default();
        let prev = g.generate_core(ts, 10_000);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        let curr = g.generate_core(ts - 10_000, 10_000);
        assert!(prev > curr);
        assert_eq!(curr.as_bytes()[..6], (ts - 10_000).to_be_bytes()[2..]);
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests_generate_core_no_rewind {
    use super::V7Generator;
    use rand::rngs::ThreadRng;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: V7Generator<ThreadRng> = Default::default();
        let mut prev = g.generate_core_no_rewind(ts, 10_000).unwrap();
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g
                .generate_core_no_rewind(ts - i.min(4_000), 10_000)
                .unwrap();
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[..6] >= ts.to_be_bytes()[2..]);
    }

    /// Returns None if timestamp moves backward a lot
    #[test]
    fn returns_none_if_timestamp_moves_backward_a_lot() {
        let ts = 0x0123_4567_89abu64;
        let mut g: V7Generator<ThreadRng> = Default::default();
        let prev = g.generate_core_no_rewind(ts, 10_000).unwrap();
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        let curr = g.generate_core_no_rewind(ts - 10_000, 10_000);
        assert!(curr.is_none());
    }
}
