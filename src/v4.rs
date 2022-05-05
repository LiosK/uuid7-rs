//! UUIDv4-related functionality

use crate::Uuid;
use rand::random;

/// Generates a UUIDv4 object.
///
/// # Examples
///
/// ```rust
/// use uuid7::uuid4;
///
/// let uuid = uuid4();
/// println!("{}", uuid); // e.g. "2ca4b2ce-6c13-40d4-bccf-37d222820f6f"
/// println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
/// ```
pub fn uuid4() -> Uuid {
    let mut bytes: [u8; 16] = random();
    bytes[6] = 0x40 | (bytes[6] >> 4);
    bytes[8] = 0x80 | (bytes[8] >> 2);
    Uuid::from(bytes)
}

#[cfg(test)]
mod tests {
    use super::uuid4;

    const N_SAMPLES: usize = 200_000;
    thread_local!(static SAMPLES: Vec<String> = (0..N_SAMPLES).map(|_| uuid4().into()).collect());

    /// Generates canonical string
    #[test]
    fn generates_canonical_string() {
        let pattern = r"^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$";
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
}
