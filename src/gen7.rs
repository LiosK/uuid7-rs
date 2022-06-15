//! UUIDv7 generator-related types

use crate::Uuid;
use rand::RngCore;

#[cfg(feature = "std")]
use std::time::{SystemTime, UNIX_EPOCH};

/// Represents a UUIDv7 generator that encapsulates a counter and guarantees the monotonic order of
/// UUIDs generated within the same millisecond.
///
/// This type provides the interface to customize the random number generator, system clock, and
/// counter overflow handling of a UUIDv7 generator. It also helps control the scope of guaranteed
/// order of the generated UUIDs. The following example guarantees the process-wide (cross-thread)
/// monotonicity using Rust's standard synchronization mechanism.
///
/// # Examples
///
/// ```rust
/// use std::sync::{Arc, Mutex};
/// use std::thread::{spawn, yield_now};
/// use uuid7::gen7::Generator;
///
/// let g = Arc::new(Mutex::new(Generator::new(rand::rngs::OsRng)));
/// let handle = {
///     let g = Arc::clone(&g);
///     spawn(move || {
///         for _ in 0..8 {
///             println!("{} by child", g.lock().unwrap().generate());
///             yield_now();
///         }
///     })
/// };
///
/// for _ in 0..8 {
///     println!("{} by parent", g.lock().unwrap().generate());
///     yield_now();
/// }
///
/// handle.join().unwrap();
/// ```
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Generator<R> {
    timestamp: u64,
    counter: u64,

    /// Random number generator used by the generator.
    rng: R,
}

impl<R: RngCore> Generator<R> {
    /// Creates a generator instance.
    pub const fn new(rng: R) -> Self {
        Self {
            timestamp: 0,
            counter: 0,
            rng,
        }
    }

    /// Generates a new UUIDv7 object.
    #[cfg(feature = "std")]
    #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
    pub fn generate(&mut self) -> Uuid {
        self.generate_core(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock may have gone backward")
                .as_millis() as u64,
        )
        .0
    }

    /// Generates a new UUIDv7 object from a given `unix_ts_ms`.
    ///
    /// This method returns a generated UUID and one of the [`Status`] codes that describe the
    /// internal state involved in the generation. A caller can usually ignore them unless the
    /// monotonic order of generated UUIDs is of critical importance to the application.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use uuid7::gen7::{Generator, Status};
    /// let mut g = Generator::new(rand::thread_rng());
    ///
    /// let ts = 0x017f_22e2_79b0u64;
    /// let (first, status) = g.generate_core(ts);
    /// assert_eq!(status, Status::NewTimestamp);
    /// assert_eq!(first.as_bytes()[0..6], ts.to_be_bytes()[2..]);
    ///
    /// let (second, status) = g.generate_core(ts);
    /// if status == Status::ClockRollback {
    ///     panic!("clock moved backward; monotonic order of UUIDs broken");
    /// } else {
    ///     assert!(second.as_bytes()[0..6] >= ts.to_be_bytes()[2..]);
    /// }
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a 48-bit positive integer.
    pub fn generate_core(&mut self, unix_ts_ms: u64) -> (Uuid, Status) {
        const MAX_COUNTER: u64 = (1 << 42) - 1;

        if unix_ts_ms == 0 || unix_ts_ms >= 1 << 48 {
            panic!("`unix_ts_ms` must be a 48-bit positive integer");
        }

        let mut status = Status::NewTimestamp;
        if unix_ts_ms > self.timestamp {
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + 10_000 > self.timestamp {
            self.counter += 1;
            status = Status::CounterInc;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp += 1;
                self.counter = self.rng.next_u64() & MAX_COUNTER;
                status = Status::TimestampInc;
            }
        } else {
            // reset state if clock moves back by ten seconds or more
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
            status = Status::ClockRollback;
        }

        (
            Uuid::from_fields_v7(
                self.timestamp,
                (self.counter >> 30) as u16,
                ((self.counter & 0x3fff_ffff) << 32) | self.rng.next_u32() as u64,
            ),
            status,
        )
    }
}

/// Status code returned by [`Generator::generate_core`] method.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum Status {
    /// Returned when `unix_ts_ms` was used because it was greater than the previous one.
    NewTimestamp,
    /// Returned when the counter was incremented because `unix_ts_ms` was no greater than the
    /// previous one.
    CounterInc,
    /// Returned when `unix_ts_ms` was incremented because the counter was incremented and reached
    /// its maximum value.
    TimestampInc,
    /// Returned when the monotonic order of UUIDs was broken because `unix_ts_ms` was less than
    /// the previous one by ten seconds or more.
    ClockRollback,
}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use super::{Generator, Status};
    use rand::rngs::ThreadRng;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: Generator<ThreadRng> = Default::default();
        let (mut prev, status) = g.generate_core(ts);
        assert_eq!(status, Status::NewTimestamp);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000 as u64 {
            let (curr, status) = g.generate_core(ts - i.min(4_000));
            assert!(status == Status::CounterInc || status == Status::TimestampInc);
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[..6] >= ts.to_be_bytes()[2..]);
    }
}
