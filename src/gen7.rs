//! UUIDv7 generator-related types

use crate::Uuid;

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
/// use rand::rngs::OsRng;
/// use std::{sync, thread};
/// use uuid7::gen7::Generator;
///
/// let g = sync::Arc::new(sync::Mutex::new(Generator::new(OsRng)));
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
pub struct Generator<R> {
    timestamp: u64,
    counter: u64,

    /// Random number generator used by the generator.
    rng: R,
}

impl<R: rand::RngCore> Generator<R> {
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
        use std::time;
        self.generate_core(
            time::SystemTime::now()
                .duration_since(time::UNIX_EPOCH)
                .expect("clock may have gone backward")
                .as_millis() as u64,
        )
    }

    /// Generates a new UUIDv7 object from a given `unix_ts_ms`.
    ///
    /// # Panics
    ///
    /// Panics if the argument is not a 48-bit positive integer.
    pub fn generate_core(&mut self, unix_ts_ms: u64) -> Uuid {
        const MAX_COUNTER: u64 = (1 << 42) - 1;

        if unix_ts_ms == 0 || unix_ts_ms >= 1 << 48 {
            panic!("`unix_ts_ms` must be a 48-bit positive integer");
        }

        if unix_ts_ms > self.timestamp {
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        } else if unix_ts_ms + 10_000 > self.timestamp {
            self.counter += 1;
            if self.counter > MAX_COUNTER {
                // increment timestamp at counter overflow
                self.timestamp += 1;
                self.counter = self.rng.next_u64() & MAX_COUNTER;
            }
        } else {
            // reset state if clock moves back by ten seconds or more
            self.timestamp = unix_ts_ms;
            self.counter = self.rng.next_u64() & MAX_COUNTER;
        }

        Uuid::from_fields_v7(
            self.timestamp,
            (self.counter >> 30) as u16,
            ((self.counter & 0x3fff_ffff) << 32) | self.rng.next_u32() as u64,
        )
    }
}

/// Supports operations as an infinite iterator that produces a new UUIDv7 object for each call of
/// `next()`.
///
/// # Examples
///
/// ```rust
/// use uuid7::gen7::Generator;
///
/// Generator::new(rand::thread_rng())
///     .enumerate()
///     .skip(4)
///     .take(4)
///     .for_each(|(i, e)| println!("[{i}] {e}"));
/// ```
#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
impl<R: rand::RngCore> Iterator for Generator<R> {
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
impl<R: rand::RngCore> std::iter::FusedIterator for Generator<R> {}

#[cfg(feature = "std")]
#[cfg(test)]
mod tests {
    use super::Generator;
    use rand::rngs::ThreadRng;

    /// Generates increasing UUIDs even with decreasing or constant timestamp
    #[test]
    fn generates_increasing_uuids_even_with_decreasing_or_constant_timestamp() {
        let ts = 0x0123_4567_89abu64;
        let mut g: Generator<ThreadRng> = Default::default();
        let mut prev = g.generate_core(ts);
        assert_eq!(prev.as_bytes()[..6], ts.to_be_bytes()[2..]);
        for i in 0..100_000u64 {
            let curr = g.generate_core(ts - i.min(4_000));
            assert!(prev < curr);
            prev = curr;
        }
        assert!(prev.as_bytes()[..6] >= ts.to_be_bytes()[2..]);
    }
}
