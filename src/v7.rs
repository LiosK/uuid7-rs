//! UUIDv7-related functionality

use crate::Uuid;
use rand::{rngs::ThreadRng, RngCore};
use std::cell::RefCell;
use std::time::{SystemTime, UNIX_EPOCH};

thread_local! {
    static DEFAULT_GENERATOR: RefCell<Generator<ThreadRng>> = Default::default();
}

/// Generates a UUIDv7 object.
///
/// This function employs a thread-local generator and guarantees the per-thread monotonic order of
/// UUIDs generated within the same millisecond.
///
/// # Examples
///
/// ```rust
/// use uuid7::uuid7;
///
/// let uuid = uuid7();
/// println!("{}", uuid); // e.g. "01809424-3e59-7c05-9219-566f82fff672"
/// println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
/// ```
pub fn uuid7() -> Uuid {
    DEFAULT_GENERATOR.with(|g| g.borrow_mut().generate())
}

/// Represents a UUIDv7 generator that encapsulates a counter and guarantees the monotonic order of
/// UUIDs generated within the same millisecond.
///
/// # Examples
///
/// ```rust
/// use uuid7::v7::Generator;
///
/// let mut g = Generator::new(rand::rngs::OsRng);
/// println!("{}", g.generate());
/// ```
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Generator<R> {
    timestamp: u64,
    counter: u64,

    /// Random number generator used by the generator.
    rng: R,
}

const MAX_COUNTER: u64 = (1 << 42) - 1;

impl<R: RngCore> Generator<R> {
    /// Creates a generator.
    pub fn new(rng: R) -> Self {
        Self {
            timestamp: Default::default(),
            counter: Default::default(),
            rng,
        }
    }

    /// Generates a new UUIDv7 object.
    pub fn generate(&mut self) -> Uuid {
        self.generate_core(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock may have gone backwards")
                .as_millis() as u64,
        )
        .0
    }

    /// Generates a new UUIDv7 object from a `unix_ts_ms`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use uuid7::v7::{Generator, Status};
    /// let mut g = Generator::new(rand::thread_rng());
    ///
    /// let ts = 0x017f_22e2_79b0u64;
    /// let (first, status) = g.generate_core(ts);
    /// assert_eq!(status, Status::NewTimestamp);
    /// assert_eq!(first.as_bytes()[0..6], ts.to_be_bytes()[2..]);
    ///
    /// let (second, status) = g.generate_core(ts);
    /// if status == Status::ClockRollback {
    ///     panic!("clock moved backwards; monotonic order of UUIDs broken");
    /// } else {
    ///     assert!(second.as_bytes()[0..6] >= ts.to_be_bytes()[2..]);
    /// }
    /// ```
    ///
    /// # Returned values
    ///
    /// This method returns a generated UUID and one of the following status codes that describe
    /// the internal state involved in the generation. The status codes are not error codes; a
    /// caller can usually ignore them unless the monotonic order of generated UUIDs is of critical
    /// importance to the application.
    ///
    /// - `NewTimestamp`: the up-to-date `unix_ts_ms` was used as the clock moved forwards.
    /// - `CounterInc`: the counter was incremented because `unix_ts_ms` did not move forwards.
    /// - `TimestampInc`: `unix_ts_ms` was incremented because the counter reached its maximum
    ///   value.
    /// - `ClockRollback`: the monotonic order of UUIDs was broken because the clock moved back
    ///   more than ten seconds.
    pub fn generate_core(&mut self, unix_ts_ms: u64) -> (Uuid, Status) {
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
            // reset state if clock moves back more than ten seconds
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
    NewTimestamp,
    CounterInc,
    TimestampInc,
    ClockRollback,
}

#[cfg(test)]
mod tests {
    use super::{uuid7, Generator, Status};
    use rand::rngs::ThreadRng;

    const N_SAMPLES: usize = 200_000;
    thread_local!(static SAMPLES: Vec<String> = (0..N_SAMPLES).map(|_| uuid7().into()).collect());

    /// Generates canonical string
    #[test]
    fn generates_canonical_string() {
        let pattern = r"^[0-9a-f]{8}-[0-9a-f]{4}-7[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$";
        let re = regex::Regex::new(pattern).unwrap();
        SAMPLES.with(|samples| {
            for e in samples {
                assert!(re.is_match(e));
            }
        });
    }

    /// Generates 200k identifiers without collision
    #[test]
    fn generates_200k_identifiers_without_collision() {
        use std::collections::HashSet;
        SAMPLES.with(|samples| {
            let s: HashSet<&String> = samples.iter().collect();
            assert_eq!(s.len(), N_SAMPLES);
        });
    }

    /// Generates sortable string representation by creation time
    #[test]
    fn generates_sortable_string_representation_by_creation_time() {
        SAMPLES.with(|samples| {
            for i in 1..N_SAMPLES {
                assert!(samples[i - 1] < samples[i]);
            }
        });
    }

    /// Encodes up-to-date timestamp
    #[test]
    fn encodes_up_to_date_timestamp() {
        use std::time::{SystemTime, UNIX_EPOCH};
        for _ in 0..10_000 {
            let ts_now = (SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("clock may have gone backwards")
                .as_millis()) as i64;
            let mut timestamp = 0i64;
            for e in uuid7().as_bytes().iter().take(6) {
                timestamp = timestamp * 256 + *e as i64;
            }
            assert!((ts_now - timestamp).abs() < 16);
        }
    }

    /// Encodes unique sortable pair of timestamp and counter
    #[test]
    fn encodes_unique_sortable_pair_of_timestamp_and_counter() {
        SAMPLES.with(|samples| {
            let mut prev_timestamp = &samples[0][0..13];
            let mut prev_counter = &samples[0][15..28];
            for i in 1..N_SAMPLES {
                let curr_timestamp = &samples[i][0..13];
                let curr_counter = &samples[i][15..28];
                assert!(
                    prev_timestamp < curr_timestamp
                        || (prev_timestamp == curr_timestamp && prev_counter < curr_counter)
                );
                prev_timestamp = curr_timestamp;
                prev_counter = curr_counter;
            }
        });
    }

    /// Sets constant bits and random bits properly
    #[test]
    fn sets_constant_bits_and_random_bits_properly() {
        // count '1' of each bit
        let bins = SAMPLES.with(|samples| {
            let mut bins = [0u32; 128];
            for e in samples {
                let mut it = bins.iter_mut().rev();
                for c in e.chars().rev() {
                    if let Some(mut num) = c.to_digit(16) {
                        for _ in 0..4 {
                            *it.next().unwrap() += num & 1;
                            num >>= 1;
                        }
                    }
                }
            }
            bins
        });

        // test if constant bits are all set to 1 or 0
        let n = N_SAMPLES as u32;
        assert_eq!(bins[48], 0, "version bit 48");
        assert_eq!(bins[49], n, "version bit 49");
        assert_eq!(bins[50], n, "version bit 50");
        assert_eq!(bins[51], n, "version bit 51");
        assert_eq!(bins[64], n, "variant bit 64");
        assert_eq!(bins[65], 0, "variant bit 65");

        // test if random bits are set to 1 at ~50% probability
        // set margin based on binom dist 99.999% confidence interval
        let margin = 4.417173 * (0.5 * 0.5 / N_SAMPLES as f64).sqrt();
        for i in 96..128 {
            let p = bins[i] as f64 / N_SAMPLES as f64;
            assert!((p - 0.5).abs() < margin, "random bit {}: {}", i, p);
        }
    }

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: Generator<ThreadRng> = Default::default();
        let (mut prev, status) = g.generate_core(ts);
        assert_eq!(status, Status::NewTimestamp);
        assert_eq!(prev.as_bytes()[0..6], ts.to_be_bytes()[2..]);
        for i in 0..N_SAMPLES as u64 {
            let (curr, status) = g.generate_core(ts - i.min(4_000));
            assert!(status == Status::CounterInc || status == Status::TimestampInc);
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[0..6] >= ts.to_be_bytes()[2..]);
    }
}
