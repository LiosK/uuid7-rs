//! Default generator and entry point functions.

#![cfg(feature = "global_gen")]

use std::sync;

use crate::{Uuid, V7Generator};

/// Returns the lock handle of process-wide global generator, creating one if none exists.
fn lock_global_gen() -> sync::MutexGuard<'static, GlobalGenInner> {
    static G: sync::LazyLock<sync::Mutex<GlobalGenInner>> = sync::LazyLock::new(Default::default);
    G.lock().expect("uuid7: could not lock global generator")
}

/// Generates a UUIDv7 object.
///
/// This function employs a global generator and guarantees the process-wide monotonic order of
/// UUIDs generated within the same millisecond. On Unix, this function resets the generator when
/// the process ID changes (i.e., upon process forks) to prevent collisions across processes.
///
/// # Examples
///
/// ```rust
/// let uuid = uuid7::uuid7();
/// println!("{}", uuid); // e.g., "01809424-3e59-7c05-9219-566f82fff672"
/// println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
///
/// let uuid_string: String = uuid7::uuid7().to_string();
/// ```
pub fn uuid7() -> Uuid {
    lock_global_gen().get_mut().generate()
}

/// Generates a UUIDv4 object.
///
/// # Examples
///
/// ```rust
/// let uuid = uuid7::uuid4();
/// println!("{}", uuid); // e.g., "2ca4b2ce-6c13-40d4-bccf-37d222820f6f"
/// ```
pub fn uuid4() -> Uuid {
    lock_global_gen().get_mut().generate_v4()
}

use global_gen_rng::GlobalGenRng;

/// A thin wrapper to reset the state when the process ID changes (i.e., upon Unix forks).
#[derive(Debug)]
struct GlobalGenInner {
    #[cfg(unix)]
    pid: u32,
    generator: V7Generator<GlobalGenRng>,
}

impl Default for GlobalGenInner {
    fn default() -> Self {
        Self {
            #[cfg(unix)]
            pid: std::process::id(),
            generator: V7Generator::new(
                GlobalGenRng::try_new().expect("uuid7: could not initialize global generator"),
            ),
        }
    }
}

impl GlobalGenInner {
    /// Returns a mutable reference to the inner [`V7Generator`] instance, reseting the
    /// generator state on Unix if the process ID has changed.
    fn get_mut(&mut self) -> &mut V7Generator<GlobalGenRng> {
        #[cfg(unix)]
        if self.pid != std::process::id() {
            self.pid = std::process::id();
            self.generator.reset_state();
            if let Ok(rng) = GlobalGenRng::try_new() {
                self.generator.replace_rand_source(rng);
            }
        }
        &mut self.generator
    }
}

mod global_gen_rng {
    use rand::{Rng as _, SeedableRng as _, rngs::StdRng, rngs::SysRng};

    use crate::generator::RandSource;

    /// The new type for the random number generator of the global generator.
    ///
    /// The global generator currently employs [`StdRng`] and reseeds it after every 64KiB
    /// consumption, emulating the strategy used by `ThreadRng`.
    #[derive(Debug)]
    pub struct GlobalGenRng {
        counter: usize,
        inner: StdRng,
    }

    const RESEED_THRESHOLD: usize = 64 * 1024;

    impl RandSource for GlobalGenRng {
        fn next_u32(&mut self) -> u32 {
            if self.counter >= RESEED_THRESHOLD {
                self.try_to_reseed();
            }
            self.counter += 32 / 8;
            self.inner.next_u32()
        }

        fn next_u64(&mut self) -> u64 {
            if self.counter >= RESEED_THRESHOLD {
                self.try_to_reseed();
            }
            self.counter += 64 / 8;
            self.inner.next_u64()
        }
    }

    impl GlobalGenRng {
        pub fn try_new() -> Result<Self, impl std::error::Error> {
            StdRng::try_from_rng(&mut SysRng).map(|inner| Self { counter: 0, inner })
        }

        #[cold]
        fn try_to_reseed(&mut self) {
            if let Ok(rng) = Self::try_new() {
                *self = rng;
            }
        }
    }

    #[cfg(test)]
    #[test]
    fn reseeded_after_64kib() {
        let seed = rand::TryRng::try_next_u64(&mut SysRng).unwrap();
        let mut g1 = StdRng::seed_from_u64(seed);
        let mut g2 = GlobalGenRng {
            counter: 0,
            inner: StdRng::seed_from_u64(seed),
        };

        for _ in 0..(64 * 1024 / (32 / 8 + 32 / 8 + 64 / 8)) {
            assert_eq!(g1.next_u32(), g2.next_u32());
            assert_eq!(g1.next_u32(), g2.next_u32());
            assert_eq!(g1.next_u64(), g2.next_u64());
        }

        assert_ne!(g1.next_u32(), g2.next_u32());
        assert_ne!(g1.next_u64(), g2.next_u64());
    }
}

#[cfg(test)]
mod tests_v7 {
    use super::uuid7;
    use crate::Variant;

    use std::{collections, sync};

    const N_SAMPLES: usize = 100_000;
    static SAMPLES: sync::LazyLock<Vec<String>> =
        sync::LazyLock::new(|| (0..N_SAMPLES).map(|_| uuid7().into()).collect());

    /// Generates canonical string
    #[test]
    fn generates_canonical_string() {
        let pattern = r"^[0-9a-f]{8}-[0-9a-f]{4}-7[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$";
        let re = regex::Regex::new(pattern).unwrap();
        for e in &SAMPLES[..] {
            assert!(re.is_match(e));
        }
    }

    /// Generates 100k identifiers without collision
    #[test]
    fn generates_100k_identifiers_without_collision() {
        let s: collections::HashSet<&String> = SAMPLES.iter().collect();
        assert_eq!(s.len(), N_SAMPLES);
    }

    /// Generates sortable string representation by creation time
    #[test]
    fn generates_sortable_string_representation_by_creation_time() {
        for i in 1..N_SAMPLES {
            assert!(SAMPLES[i - 1] < SAMPLES[i]);
        }
    }

    /// Encodes up-to-date timestamp
    #[test]
    fn encodes_up_to_date_timestamp() {
        use std::time;
        for _ in 0..10_000 {
            let ts_now = (time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
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
        let mut prev_timestamp = &SAMPLES[0][0..13];
        let mut prev_counter = &SAMPLES[0][15..28];
        for e in &SAMPLES[1..] {
            let curr_timestamp = &e[0..13];
            let curr_counter = &e[15..28];
            assert!(
                prev_timestamp < curr_timestamp
                    || (prev_timestamp == curr_timestamp && prev_counter < curr_counter)
            );
            prev_timestamp = curr_timestamp;
            prev_counter = curr_counter;
        }
    }

    /// Sets constant bits and random bits properly
    #[test]
    fn sets_constant_bits_and_random_bits_properly() {
        // count '1' of each bit
        let mut bins = [0u32; 128];
        for e in &SAMPLES[..] {
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
        #[allow(clippy::needless_range_loop)]
        for i in 96..128 {
            let p = bins[i] as f64 / N_SAMPLES as f64;
            assert!((p - 0.5).abs() < margin, "random bit {}: {}", i, p);
        }
    }

    /// Sets correct variant and version bits
    #[test]
    fn sets_correct_variant_and_version_bits() {
        for _ in 0..1_000 {
            let e = uuid7();
            assert_eq!(e.variant(), Variant::Var10);
            assert_eq!(e.version(), Some(7));
        }
    }

    /// Generates no IDs sharing same timestamp and counters under multithreading
    #[test]
    fn generates_no_ids_sharing_same_timestamp_and_counters_under_multithreading()
    -> Result<(), Box<dyn std::error::Error>> {
        use std::{collections::HashSet, sync::mpsc, thread};

        let (tx, rx) = mpsc::channel();
        for _ in 0..4 {
            let tx = tx.clone();
            thread::Builder::new()
                .spawn(move || {
                    for _ in 0..10_000 {
                        tx.send(uuid7()).unwrap();
                    }
                })
                .map_err(|err| format!("failed to spawn thread: {:?}", err))?;
        }
        drop(tx);

        let mut s = HashSet::new();
        while let Ok(e) = rx.recv() {
            s.insert(<[u8; 12]>::try_from(&e.as_bytes()[..12]).unwrap());
        }

        assert_eq!(s.len(), 4 * 10_000);
        Ok(())
    }
}

#[cfg(test)]
mod tests_v4 {
    use super::uuid4;
    use crate::Variant;

    use std::{collections, sync};

    const N_SAMPLES: usize = 100_000;
    static SAMPLES: sync::LazyLock<Vec<String>> =
        sync::LazyLock::new(|| (0..N_SAMPLES).map(|_| uuid4().into()).collect());

    /// Generates canonical string
    #[test]
    fn generates_canonical_string() {
        let pattern = r"^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$";
        let re = regex::Regex::new(pattern).unwrap();
        for e in &SAMPLES[..] {
            assert!(re.is_match(e));
        }
    }

    /// Generates 100k identifiers without collision
    #[test]
    fn generates_100k_identifiers_without_collision() {
        let s: collections::HashSet<&String> = SAMPLES.iter().collect();
        assert_eq!(s.len(), N_SAMPLES);
    }

    /// Sets constant bits and random bits properly
    #[test]
    fn sets_constant_bits_and_random_bits_properly() {
        // count '1' of each bit
        let mut bins = [0u32; 128];
        for e in &SAMPLES[..] {
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

        // test if constant bits are all set to 1 or 0
        let n = N_SAMPLES as u32;
        assert_eq!(bins[48], 0, "version bit 48");
        assert_eq!(bins[49], n, "version bit 49");
        assert_eq!(bins[50], 0, "version bit 50");
        assert_eq!(bins[51], 0, "version bit 51");
        assert_eq!(bins[64], n, "variant bit 64");
        assert_eq!(bins[65], 0, "variant bit 65");

        // test if random bits are set to 1 at ~50% probability
        // set margin based on binom dist 99.999% confidence interval
        let margin = 4.417173 * (0.5 * 0.5 / N_SAMPLES as f64).sqrt();
        for i in (0..48).chain(52..64).chain(66..128) {
            let p = bins[i] as f64 / N_SAMPLES as f64;
            assert!((p - 0.5).abs() < margin, "random bit {}: {}", i, p);
        }
    }

    /// Sets correct variant and version bits
    #[test]
    fn sets_correct_variant_and_version_bits() {
        for _ in 0..1_000 {
            let e = uuid4();
            assert_eq!(e.variant(), Variant::Var10);
            assert_eq!(e.version(), Some(4));
        }
    }
}
