#[cfg(not(feature = "std"))]
use core as std;

use std::{fmt, str::from_utf8_unchecked};

/// Represents a Universally Unique IDentifier.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct Uuid([u8; 16]);

impl Uuid {
    /// Nil UUID (00000000-0000-0000-0000-000000000000)
    pub const NIL: Self = Self([0x00; 16]);

    /// Max UUID (ffffffff-ffff-ffff-ffff-ffffffffffff)
    pub const MAX: Self = Self([0xff; 16]);

    /// Returns a reference to the underlying byte array.
    pub const fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Creates a UUID byte array from UUIDv7 field values.
    pub const fn from_fields_v7(unix_ts_ms: u64, rand_a: u16, rand_b: u64) -> Self {
        if unix_ts_ms >= 1 << 48 || rand_a >= 1 << 12 || rand_b >= 1 << 62 {
            panic!("invalid field value");
        }

        Self([
            (unix_ts_ms >> 40) as u8,
            (unix_ts_ms >> 32) as u8,
            (unix_ts_ms >> 24) as u8,
            (unix_ts_ms >> 16) as u8,
            (unix_ts_ms >> 8) as u8,
            unix_ts_ms as u8,
            0x70 | (rand_a >> 8) as u8,
            rand_a as u8,
            0x80 | (rand_b >> 56) as u8,
            (rand_b >> 48) as u8,
            (rand_b >> 40) as u8,
            (rand_b >> 32) as u8,
            (rand_b >> 24) as u8,
            (rand_b >> 16) as u8,
            (rand_b >> 8) as u8,
            rand_b as u8,
        ])
    }

    /// Writes the 8-4-4-4-12 hexadecimal string representation to `buf` as an ASCII byte array.
    ///
    /// # Panics
    ///
    /// This method panics if the length of `buf` is smaller than 36.
    pub fn write_utf8(&self, buf: &mut [u8]) {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";
        let mut buf_iter = buf[0..36].iter_mut();
        for i in 0..16 {
            let e = self.0[i] as usize;
            *buf_iter.next().unwrap() = DIGITS[e >> 4];
            *buf_iter.next().unwrap() = DIGITS[e & 15];
            if i == 3 || i == 5 || i == 7 || i == 9 {
                *buf_iter.next().unwrap() = b'-';
            }
        }
    }
}

impl fmt::Display for Uuid {
    /// Returns the 8-4-4-4-12 canonical hexadecimal string representation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut buffer = [0u8; 36];
        self.write_utf8(&mut buffer);
        f.write_str(unsafe { from_utf8_unchecked(&buffer) })
    }
}

impl From<Uuid> for [u8; 16] {
    fn from(src: Uuid) -> Self {
        src.0
    }
}

impl From<[u8; 16]> for Uuid {
    fn from(src: [u8; 16]) -> Self {
        Self(src)
    }
}

impl AsRef<[u8]> for Uuid {
    fn as_ref(&self) -> &[u8] {
        self.as_bytes()
    }
}

#[cfg(feature = "std")]
impl From<Uuid> for String {
    fn from(src: Uuid) -> Self {
        src.to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::Uuid;
    use core::str::from_utf8;

    /// Returns a collection of prepared cases
    fn prepare_cases() -> &'static [((u64, u16, u64), &'static str)] {
        const MAX_UINT48: u64 = (1 << 48) - 1;
        const MAX_UINT12: u16 = (1 << 12) - 1;
        const MAX_UINT62: u64 = (1 << 62) - 1;

        &[
            ((0, 0, 0), "00000000-0000-7000-8000-000000000000"),
            ((MAX_UINT48, 0, 0), "ffffffff-ffff-7000-8000-000000000000"),
            ((0, MAX_UINT12, 0), "00000000-0000-7fff-8000-000000000000"),
            ((0, 0, MAX_UINT62), "00000000-0000-7000-bfff-ffffffffffff"),
            (
                (MAX_UINT48, MAX_UINT12, MAX_UINT62),
                "ffffffff-ffff-7fff-bfff-ffffffffffff",
            ),
            (
                (0x17f22e279b0, 0xcc3, 0x18c4dc0c0c07398f),
                "017f22e2-79b0-7cc3-98c4-dc0c0c07398f",
            ),
        ]
    }

    /// Encodes prepared cases correctly
    #[test]
    fn encodes_prepared_cases_correctly() {
        let mut buf = [0u8; 36];

        for (fs, text) in prepare_cases() {
            let from_fields = Uuid::from_fields_v7(fs.0, fs.1, fs.2);
            from_fields.write_utf8(&mut buf);
            assert_eq!(&from_utf8(&buf).unwrap(), text);
            #[cfg(feature = "std")]
            assert_eq!(&from_fields.to_string(), text);
        }
    }

    /// Returns Nil and Max UUIDs
    #[test]
    fn returns_nil_and_max_uuids() {
        let mut buf = [0u8; 36];

        Uuid::NIL.write_utf8(&mut buf);
        assert_eq!(
            from_utf8(&buf).unwrap(),
            "00000000-0000-0000-0000-000000000000"
        );

        Uuid::MAX.write_utf8(&mut buf);
        assert_eq!(
            from_utf8(&buf).unwrap(),
            "ffffffff-ffff-ffff-ffff-ffffffffffff"
        );
    }
}
