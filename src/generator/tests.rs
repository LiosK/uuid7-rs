use super::*;

impl V7Generator<()> {
    pub(crate) fn for_testing() -> V7Generator<impl RandSource, impl TimeSource> {
        V7Generator::with_rand_and_time_sources(new_rand_source(), new_time_source())
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
