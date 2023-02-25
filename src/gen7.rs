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
    /// This method returns monotonically increasing UUIDs unless the up-to-date timestamp is
    /// significantly (by ten seconds or more) smaller than the one embedded in the immediately
    /// preceding UUID. If such a significant clock rollback is detected, this method resets the
    /// generator state and returns a new UUID based on the up-to-date timestamp.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate(&mut self) -> Uuid {
        use std::time;
        self.generate_from_ts(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backward")
                .as_millis() as u64,
        )
    }

    /// Generates a new UUIDv7 object from the current timestamp, guaranteeing that the returned
    /// UUID is greater than the immediately preceding one generated by the generator.
    ///
    /// This method returns monotonically increasing UUIDs unless the up-to-date timestamp is
    /// significantly (by ten seconds or more) smaller than the one embedded in the immediately
    /// preceding UUID. If such a significant clock rollback is detected, this method returns
    /// `None`.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate_monotonic(&mut self) -> Option<Uuid> {
        use std::time;
        self.generate_from_ts_monotonic(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backward")
                .as_millis() as u64,
        )
    }

    /// Generates a new UUIDv7 object from a given `unix_ts_ms`.
    ///
    /// This method returns monotonically increasing UUIDs unless a given `unix_ts_ms` is
    /// significantly (by ten seconds or more) smaller than the one embedded in the immediately
    /// preceding UUID. If such a significant clock rollback is detected, this method resets the
    /// generator state and returns a new UUID based on the given argument.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a 48-bit positive integer.
    pub fn generate_from_ts(&mut self, unix_ts_ms: u64) -> Uuid {
        if let Some(value) = self.generate_from_ts_monotonic(unix_ts_ms) {
            value
        } else {
            // reset state and resume
            self.timestamp = 0;
            self.generate_from_ts_monotonic(unix_ts_ms).unwrap()
        }
    }

    /// Generates a new UUIDv7 object from a given `unix_ts_ms`, guaranteeing that the returned
    /// UUID is greater than the immediately preceding one generated by the generator.
    ///
    /// This method returns monotonically increasing UUIDs unless a given `unix_ts_ms` is
    /// significantly (by ten seconds or more) smaller than the one embedded in the immediately
    /// preceding UUID. If such a significant clock rollback is detected, this method returns
    /// `None`.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a 48-bit positive integer.
    pub fn generate_from_ts_monotonic(&mut self, unix_ts_ms: u64) -> Option<Uuid> {
        const MAX_COUNTER: u64 = (1 << 42) - 1;
        const ROLLBACK_ALLOWANCE: u64 = 10_000; // 10 seconds

        if unix_ts_ms == 0 || unix_ts_ms >= 1 << 48 {
            panic!("`unix_ts_ms` must be a 48-bit positive integer");
        }

        if unix_ts_ms > self.timestamp {
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + ROLLBACK_ALLOWANCE > self.timestamp {
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
mod tests_generate_from_ts {
    use super::V7Generator;
    use rand::rngs::ThreadRng;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: V7Generator<ThreadRng> = Default::default();
        let mut prev = g.generate_from_ts(ts);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g.generate_from_ts(ts - i.min(4_000));
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
        let prev = g.generate_from_ts(ts);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        let curr = g.generate_from_ts(ts - 10_000);
        assert!(prev > curr);
        assert_eq!(curr.as_bytes()[..6], (ts - 10_000).to_be_bytes()[2..]);
    }
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests_generate_from_ts_monotonic {
    use super::V7Generator;
    use rand::rngs::ThreadRng;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: V7Generator<ThreadRng> = Default::default();
        let mut prev = g.generate_from_ts_monotonic(ts).unwrap();
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g.generate_from_ts_monotonic(ts - i.min(4_000)).unwrap();
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
        let prev = g.generate_from_ts_monotonic(ts).unwrap();
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        let curr = g.generate_from_ts_monotonic(ts - 10_000);
        assert!(curr.is_none());
    }
}
