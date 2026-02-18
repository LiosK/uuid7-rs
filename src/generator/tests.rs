use super::*;
use std::cell;

impl V7Generator<()> {
    pub(crate) fn for_testing() -> V7Generator<impl RandSource, impl TimeSource> {
        V7Generator::with_rand_and_time_sources(new_rand_source(), new_time_source())
    }
}

impl Uuid {
    fn timestamp(&self) -> u64 {
        assert_eq!(self.version(), Some(7));
        u64::from_be_bytes(self.as_bytes()[..8].try_into().unwrap()) >> 16
    }
}

fn new_rand_source() -> impl RandSource {
    struct MockRandSource;
    impl RandSource for MockRandSource {
        fn next_u32(&mut self) -> u32 {
            rand::random()
        }
        fn next_u64(&mut self) -> u64 {
            rand::random()
        }
    }
    MockRandSource
}

fn new_time_source() -> impl TimeSource {
    #[cfg(feature = "std")]
    return StdSystemTime;

    #[cfg(not(feature = "std"))]
    {
        struct MockTimeSource(u64);
        impl TimeSource for MockTimeSource {
            fn unix_ts_ms(&mut self) -> u64 {
                self.0 += 8;
                self.0
            }
        }
        MockTimeSource(0x0123_4567_89abu64)
    }
}

/// Reads timestamp from time source
#[test]
fn reads_timestamp_from_time_source() {
    struct PeekableTimeSource<'a, T>(&'a cell::Cell<u64>, T);
    impl<T: TimeSource> TimeSource for PeekableTimeSource<'_, T> {
        fn unix_ts_ms(&mut self) -> u64 {
            self.0.set(self.1.unix_ts_ms());
            self.0.get()
        }
    }

    let ts = cell::Cell::default();
    let time_source = PeekableTimeSource(&ts, new_time_source());
    let mut g = V7Generator::with_rand_and_time_sources(new_rand_source(), time_source);

    assert_eq!(g.generate().timestamp(), ts.get());
    assert_eq!(g.generate().timestamp(), ts.get());
    assert_eq!(g.generate_or_abort().unwrap().timestamp(), ts.get());
    assert_eq!(g.generate_or_abort().unwrap().timestamp(), ts.get());
    assert_eq!(g.generate().timestamp(), ts.get());
    assert_eq!(g.generate_or_abort().unwrap().timestamp(), ts.get());
    assert_eq!(g.generate().timestamp(), ts.get());
    assert_eq!(g.generate_or_abort().unwrap().timestamp(), ts.get());
}

/// Generator methods handle clock rollback according to their specifications
#[test]
fn handle_clock_rollback() {
    const DEFAULT_ROLLBACK_ALLOWANCE: u64 = 10_000;

    struct CellTimeSource<'a>(&'a cell::Cell<u64>);

    impl TimeSource for CellTimeSource<'_> {
        fn unix_ts_ms(&mut self) -> u64 {
            self.0.get()
        }
    }

    for rollback_allowance in [DEFAULT_ROLLBACK_ALLOWANCE, 5_000, 20_000] {
        let ts = cell::Cell::new(0);
        let [mut g0, mut g1, mut g2, mut g3] = [
            V7Generator::with_rand_and_time_sources(new_rand_source(), CellTimeSource(&ts)),
            V7Generator::with_rand_and_time_sources(new_rand_source(), CellTimeSource(&ts)),
            V7Generator::with_rand_and_time_sources(new_rand_source(), CellTimeSource(&ts)),
            V7Generator::with_rand_and_time_sources(new_rand_source(), CellTimeSource(&ts)),
        ];

        if rollback_allowance != DEFAULT_ROLLBACK_ALLOWANCE {
            g0.set_rollback_allowance(rollback_allowance);
            g1.set_rollback_allowance(rollback_allowance);
        }

        let methods: [(&mut dyn FnMut() -> Option<Uuid>, bool); 4] = [
            (&mut || Some(g0.generate()), true),
            (&mut || g1.generate_or_abort(), false),
            (
                &mut || Some(g2.generate_or_reset_core(ts.get(), rollback_allowance)),
                true,
            ),
            (
                &mut || g3.generate_or_abort_core(ts.get(), rollback_allowance),
                false,
            ),
        ];

        for (generate, is_reset) in methods {
            let mut ts_base = new_time_source().unix_ts_ms();

            ts.set(ts_base);
            let mut prev = generate().unwrap();
            assert_eq!(prev.timestamp(), ts_base);

            // generates increasing IDs with constant timestamp
            for _ in 0..50 {
                let curr = generate().unwrap();
                assert!(prev < curr);
                assert!(curr.timestamp() >= ts_base);
                prev = curr;
            }

            // generates increasing IDs with decreasing timestamp
            for i in 0..50_000u64 {
                ts.set(ts_base - i.min(rollback_allowance - 1));
                let curr = generate().unwrap();
                assert!(prev < curr);
                assert!(curr.timestamp() >= ts_base);
                prev = curr;
            }

            // reset generator state
            ts_base += rollback_allowance * 4;
            ts.set(ts_base);
            prev = generate().unwrap();
            assert_eq!(prev.timestamp(), ts_base);

            ts.set(ts_base - rollback_allowance);
            let mut curr = generate();
            assert!(prev < curr.unwrap());
            assert!(curr.unwrap().timestamp() >= ts_base);

            if is_reset {
                // breaks increasing order if timestamp goes backwards a lot
                prev = curr.unwrap();
                ts.set(ts_base - rollback_allowance - 1);
                curr = generate();
                assert!(prev > curr.unwrap());
                assert_eq!(curr.unwrap().timestamp(), ts_base - rollback_allowance - 1);

                prev = curr.unwrap();
                ts.set(ts_base - rollback_allowance - 2);
                curr = generate();
                assert!(prev < curr.unwrap());
                assert!(curr.unwrap().timestamp() >= ts_base - rollback_allowance - 1);
            } else {
                // returns None if timestamp goes backwards a lot
                ts.set(ts_base - rollback_allowance - 1);
                curr = generate();
                assert!(curr.is_none());

                ts.set(ts_base - rollback_allowance - 2);
                curr = generate();
                assert!(curr.is_none());
            }
        }
    }
}

/// Is iterable with for-in loop
#[test]
fn is_iterable_with_for_in_loop() {
    let mut i = 0;
    for e in V7Generator::for_testing() {
        assert!(e.timestamp() > 0);
        i += 1;
        if i > 100 {
            break;
        }
    }
    assert_eq!(i, 101);
}
