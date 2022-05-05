//! UUIDv7-related functionality

use crate::Uuid;
use rand::{rngs::ThreadRng, RngCore};
use std::cell::RefCell;
use std::time::{SystemTime, UNIX_EPOCH};

thread_local! {
    static DEFAULT_GENERATOR: RefCell<Generator<ThreadRng, StdSystemTime>> = Default::default();
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
/// use uuid7::v7::{Generator, StdSystemTime};
///
/// let mut g = Generator::new(rand::rngs::OsRng, StdSystemTime);
/// println!("{}", g.generate());
/// ```
#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct Generator<R, C> {
    timestamp: u64,
    counter: u64,

    /// Random number generator used by the generator.
    rng: R,

    /// Timestamp source used by the generator.
    clock: C,
}

const MAX_COUNTER: u64 = (1 << 42) - 1;

impl<R: RngCore, C: UnixTsMs> Generator<R, C> {
    /// Creates a generator.
    pub fn new(rng: R, clock: C) -> Self {
        Self {
            timestamp: Default::default(),
            counter: Default::default(),
            rng,
            clock,
        }
    }

    /// Generates a new UUIDv7 object.
    pub fn generate(&mut self) -> Uuid {
        let ts = self.clock.unix_ts_ms();
        if ts > self.timestamp {
            self.timestamp = ts;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if ts + 10_000 > self.timestamp {
            self.counter += 1;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp += 1;
                self.counter = self.rng.next_u64() & MAX_COUNTER;
            }
        } else {
            // reset state if clock moves back more than ten seconds
            self.timestamp = ts;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        }

        Uuid::from_fields_v7(
            self.timestamp,
            (self.counter >> 30) as u16,
            ((self.counter & 0x3fff_ffff) << 32) | self.rng.next_u32() as u64,
        )
    }
}

/// Interface representing timestamp sources that return the Unix timestamp in milliseconds.
pub trait UnixTsMs {
    /// Returns the Unix timestamp in milliseconds.
    fn unix_ts_ms(&mut self) -> u64;
}

/// Default [`UnixTsMs`] source that uses [`std::time::SystemTime`].
#[derive(Clone, Debug, Default)]
pub struct StdSystemTime;

impl UnixTsMs for StdSystemTime {
    fn unix_ts_ms(&mut self) -> u64 {
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock may have gone backwards")
            .as_millis() as u64
    }
}

#[cfg(test)]
mod tests {
    use super::uuid7;

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
}
