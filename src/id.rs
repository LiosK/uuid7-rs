#[cfg(not(feature = "std"))]
use core as std;

use fstr::FStr;
use std::{fmt, str};

/// Represents a Universally Unique IDentifier.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
pub struct Uuid([u8; 16]);

impl Uuid {
    /// The Nil UUID value (00000000-0000-0000-0000-000000000000).
    pub const NIL: Self = Self([0x00; 16]);

    /// The Max UUID value (ffffffff-ffff-ffff-ffff-ffffffffffff).
    pub const MAX: Self = Self([0xff; 16]);

    /// Returns a reference to the underlying byte array.
    pub const fn as_bytes(&self) -> &[u8; 16] {
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

    /// Returns the 8-4-4-4-12 hexadecimal string representation stored in a stack-allocated
    /// string-like type that can be handled like [`String`] through common traits.
    ///
    /// This method is primarily for `no_std` environments where heap-allocated string types are
    /// not readily available. Use the [`fmt::Display`] trait usually to get the 8-4-4-4-12
    /// canonical hexadecimal string representation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use uuid7::Uuid;
    ///
    /// let x = "01809424-3e59-7c05-9219-566f82fff672".parse::<Uuid>()?;
    /// let y = x.encode();
    /// assert_eq!(y, "01809424-3e59-7c05-9219-566f82fff672");
    /// assert_eq!(format!("{y}"), "01809424-3e59-7c05-9219-566f82fff672");
    /// # Ok::<(), uuid7::ParseError>(())
    /// ```
    pub fn encode(&self) -> FStr<36> {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";

        let mut buffer = [0u8; 36];
        let mut buf_iter = buffer.iter_mut();
        for i in 0..16 {
            let e = self.0[i] as usize;
            *buf_iter.next().unwrap() = DIGITS[e >> 4];
            *buf_iter.next().unwrap() = DIGITS[e & 15];
            if i == 3 || i == 5 || i == 7 || i == 9 {
                *buf_iter.next().unwrap() = b'-';
            }
        }
        unsafe { FStr::from_inner_unchecked(buffer) }
    }

    /// Reports the variant field value of the UUID or, if appropriate, `Nil` or `Max`.
    ///
    /// For convenience, this function reports [`Variant::Nil`] or [`Variant::Max`] if `self`
    /// represents the Nil or Max UUID, although the Nil and Max UUIDs are technically subsumed
    /// under the variants `0b0` and `0b111`, respectively.
    pub fn variant(&self) -> Variant {
        match self.0[8] >> 4 {
            0b0000..=0b0111 => {
                if self == &Self::NIL {
                    Variant::Nil
                } else {
                    Variant::Var0
                }
            }
            0b1000..=0b1011 => Variant::Var10,
            0b1100..=0b1101 => Variant::Var110,
            0b1110..=0b1111 => {
                if self == &Self::MAX {
                    Variant::Max
                } else {
                    Variant::VarReserved
                }
            }
            _ => unreachable!(),
        }
    }

    /// Returns the version field value of the UUID or `None` if `self` does not have the variant
    /// field value of `0b10`.
    pub fn version(&self) -> Option<u8> {
        match self.variant() {
            Variant::Var10 => Some(self.0[6] >> 4),
            _ => None,
        }
    }
}

impl fmt::Display for Uuid {
    /// Returns the 8-4-4-4-12 canonical hexadecimal string representation.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.encode().as_str(), f)
    }
}

impl str::FromStr for Uuid {
    type Err = ParseError;

    /// Creates an object from the 8-4-4-4-12 hexadecimal string representation.
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        const ERR_LEN: ParseError = ParseError::length();
        const ERR_DIGIT: ParseError = ParseError::digit();
        let mut dst = [0u8; 16];
        let mut iter = src.chars();
        for (i, e) in dst.iter_mut().enumerate() {
            let hi = iter.next().ok_or(ERR_LEN)?.to_digit(16).ok_or(ERR_DIGIT)? as u8;
            let lo = iter.next().ok_or(ERR_LEN)?.to_digit(16).ok_or(ERR_DIGIT)? as u8;
            *e = (hi << 4) | lo;
            if (i == 3 || i == 5 || i == 7 || i == 9) && iter.next().ok_or(ERR_LEN)? != '-' {
                return Err(ParseError::format());
            }
        }
        if iter.next().is_none() {
            Ok(Self(dst))
        } else {
            Err(ERR_LEN)
        }
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

impl From<Uuid> for u128 {
    fn from(src: Uuid) -> Self {
        Self::from_be_bytes(src.0)
    }
}

impl From<u128> for Uuid {
    fn from(src: u128) -> Self {
        Self(src.to_be_bytes())
    }
}

/// An error parsing an invalid string representation of UUID.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseError {
    kind: ParseErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseErrorKind {
    Length,
    Digit,
    Format,
}

impl ParseError {
    const fn length() -> Self {
        Self {
            kind: ParseErrorKind::Length,
        }
    }

    const fn digit() -> Self {
        Self {
            kind: ParseErrorKind::Digit,
        }
    }

    const fn format() -> Self {
        Self {
            kind: ParseErrorKind::Format,
        }
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ParseErrorKind::*;
        write!(f, "could not parse string as UUID: ")?;
        match self.kind {
            Length => write!(f, "invalid length"),
            Digit => write!(f, "invalid digit"),
            Format => write!(f, "invalid format"),
        }
    }
}

/// The reserved UUID variants and the Nil and Max markers.
///
/// For convenience, this enum defines the independent Nil and Max variants, although they are
/// technically subsumed under the variants `0b0` and `0b111`, respectively.
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
#[non_exhaustive]
pub enum Variant {
    /// The variant `0b0` (NCS), excluding the Nil UUID.
    Var0,

    /// The variant `0b10` (RFC 4122).
    Var10,

    /// The variant `0b110` (Microsoft).
    Var110,

    /// The variant `0b111` reserved for future definitions, excluding the Max UUID.
    VarReserved,

    /// The Nil UUID, which is technically included in the variant `0b0`.
    Nil,

    /// The Max UUID, which is technically included in the variant `0b111`.
    Max,
}

#[cfg(feature = "std")]
#[cfg_attr(docsrs, doc(cfg(feature = "std")))]
mod std_ext {
    use super::{ParseError, Uuid};

    impl From<Uuid> for String {
        fn from(src: Uuid) -> Self {
            src.encode().into()
        }
    }

    impl TryFrom<String> for Uuid {
        type Error = ParseError;

        fn try_from(src: String) -> Result<Self, Self::Error> {
            src.parse()
        }
    }

    impl std::error::Error for ParseError {}
}

#[cfg(feature = "uuid")]
#[cfg_attr(docsrs, doc(cfg(feature = "uuid")))]
mod uuid_support {
    use super::Uuid;

    impl From<Uuid> for uuid::Uuid {
        fn from(src: Uuid) -> Self {
            uuid::Uuid::from_bytes(src.0)
        }
    }

    impl From<uuid::Uuid> for Uuid {
        fn from(src: uuid::Uuid) -> Self {
            Self(src.into_bytes())
        }
    }
}

#[cfg(feature = "serde")]
#[cfg_attr(docsrs, doc(cfg(feature = "serde")))]
mod serde_support {
    use super::{fmt, str, Uuid};
    use serde::{de, Deserializer, Serializer};

    impl serde::Serialize for Uuid {
        fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
            if serializer.is_human_readable() {
                serializer.serialize_str(&self.encode())
            } else {
                serializer.serialize_bytes(self.as_bytes())
            }
        }
    }

    impl<'de> serde::Deserialize<'de> for Uuid {
        fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
            if deserializer.is_human_readable() {
                deserializer.deserialize_str(VisitorImpl)
            } else {
                deserializer.deserialize_bytes(VisitorImpl)
            }
        }
    }

    struct VisitorImpl;

    impl<'de> de::Visitor<'de> for VisitorImpl {
        type Value = Uuid;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "a UUID representation")
        }

        fn visit_str<E: de::Error>(self, value: &str) -> Result<Self::Value, E> {
            value.parse::<Self::Value>().map_err(de::Error::custom)
        }

        fn visit_bytes<E: de::Error>(self, value: &[u8]) -> Result<Self::Value, E> {
            match <[u8; 16]>::try_from(value) {
                Ok(array_value) => Ok(Self::Value::from(array_value)),
                Err(err) => match str::from_utf8(value) {
                    Ok(str_value) => self.visit_str(str_value),
                    _ => Err(de::Error::custom(err)),
                },
            }
        }

        fn visit_u128<E: de::Error>(self, value: u128) -> Result<Self::Value, E> {
            Ok(Self::Value::from(value))
        }
    }

    #[cfg(test)]
    mod tests {
        use super::Uuid;
        use serde_test::{Configure, Token};

        /// Serializes and deserializes prepared cases correctly
        #[test]
        fn serializes_and_deserializes_prepared_cases_correctly() {
            let cases = [
                ("00000000-0000-0000-0000-000000000000", &[0u8; 16]),
                (
                    "0180ae59-078c-7b80-b113-2fe14a615fb3",
                    &[
                        1, 128, 174, 89, 7, 140, 123, 128, 177, 19, 47, 225, 74, 97, 95, 179,
                    ],
                ),
                (
                    "0180ae59-0790-7f6d-897d-79370b09dd07",
                    &[
                        1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 55, 11, 9, 221, 7,
                    ],
                ),
                (
                    "0180ae59-0790-7f6d-897d-7938e16176fc",
                    &[
                        1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 56, 225, 97, 118, 252,
                    ],
                ),
                (
                    "0180ae59-0790-7f6d-897d-7939dbb56111",
                    &[
                        1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 57, 219, 181, 97, 17,
                    ],
                ),
                (
                    "0180ae59-0790-7f6d-897d-793af4b611fb",
                    &[
                        1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 58, 244, 182, 17, 251,
                    ],
                ),
                (
                    "0180ae59-0790-7f6d-897d-793be80c6ca4",
                    &[
                        1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 59, 232, 12, 108, 164,
                    ],
                ),
                (
                    "0180ae59-0790-7f6d-897d-793c00a6b6d7",
                    &[
                        1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 60, 0, 166, 182, 215,
                    ],
                ),
                (
                    "0180ae59-0791-7e79-8804-02ce2b5bc8d2",
                    &[
                        1, 128, 174, 89, 7, 145, 126, 121, 136, 4, 2, 206, 43, 91, 200, 210,
                    ],
                ),
            ];

            for (text, bytes) in cases {
                let e = text.parse::<Uuid>().unwrap();
                serde_test::assert_tokens(&e.readable(), &[Token::Str(text)]);
                serde_test::assert_tokens(&e.compact(), &[Token::Bytes(bytes)]);
                serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(bytes)]);
                serde_test::assert_de_tokens(&e.compact(), &[Token::Str(text)]);
                serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(text.as_bytes())]);
                serde_test::assert_de_tokens(&e.compact(), &[Token::Bytes(text.as_bytes())]);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Uuid, Variant};

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

    /// Encodes and decodes prepared cases correctly
    #[test]
    fn encodes_and_decodes_prepared_cases_correctly() {
        for (fs, text) in prepare_cases() {
            let from_fields = Uuid::from_fields_v7(fs.0, fs.1, fs.2);
            assert_eq!(Ok(from_fields), text.parse());
            assert_eq!(Ok(from_fields), text.to_uppercase().parse());
            assert_eq!(&from_fields.encode() as &str, *text);
            #[cfg(feature = "std")]
            assert_eq!(&from_fields.to_string(), text);
            #[cfg(feature = "std")]
            assert_eq!(&from_fields.encode().to_string(), text);
            #[cfg(all(feature = "global_gen", feature = "uuid"))]
            assert_eq!(&uuid::Uuid::from(from_fields).to_string(), text);
            assert_eq!(from_fields.variant(), Variant::Var10);
            assert_eq!(from_fields.version(), Some(7));
        }
    }

    /// Returns error to invalid string representation
    #[test]
    fn returns_error_to_invalid_string_representation() {
        let cases = [
            "",
            " 0180a8f0-5b82-75b4-9fef-ecad657c30bb",
            "0180a8f0-5b84-7438-ab50-f0626f78002b ",
            " 0180a8f0-5b84-7438-ab50-f063bd5331af ",
            "+0180a8f0-5b84-7438-ab50-f06405d35edb",
            "-0180a8f0-5b84-7438-ab50-f06508df4c2d",
            "+180a8f0-5b84-7438-ab50-f066aa10a367",
            "-180a8f0-5b84-7438-ab50-f067cdce1d69",
            "0180a8f05b847438ab50f068decfbfd7",
            "0180a8f0-5b847438-ab50-f06991838802",
            "{0180a8f0-5b84-7438-ab50-f06ac2e5e082}",
            "0180a8f0-5b84-74 8-ab50-f06bed27bdc7",
            "0180a8g0-5b84-7438-ab50-f06c91175b8a",
            "0180a8f0-5b84-7438-ab50_f06d3ea24429",
        ];

        for e in cases {
            assert!(e.parse::<Uuid>().is_err());
        }
    }

    /// Returns Nil and Max UUIDs
    #[test]
    fn returns_nil_and_max_uuids() {
        assert_eq!(
            &Uuid::NIL.encode() as &str,
            "00000000-0000-0000-0000-000000000000"
        );

        assert_eq!(
            &Uuid::MAX.encode() as &str,
            "ffffffff-ffff-ffff-ffff-ffffffffffff"
        );
    }

    /// Has symmetric converters
    #[test]
    fn has_symmetric_converters() {
        for (fs, _) in prepare_cases() {
            let e = Uuid::from_fields_v7(fs.0, fs.1, fs.2);
            assert_eq!(Uuid::from(<[u8; 16]>::from(e)), e);
            assert_eq!(Uuid::from(u128::from(e)), e);
            assert_eq!(e.encode().parse(), Ok(e));
            assert_eq!(e.encode().to_uppercase().parse(), Ok(e));
            #[cfg(feature = "std")]
            assert_eq!(Uuid::try_from(e.to_string()), Ok(e));
            #[cfg(feature = "std")]
            assert_eq!(Uuid::try_from(e.to_string().to_uppercase()), Ok(e));
            #[cfg(feature = "uuid")]
            assert_eq!(Uuid::from(<uuid::Uuid>::from(e)), e);

            #[cfg(feature = "uuid")]
            assert_eq!(uuid::Uuid::from(e).as_bytes(), &<[u8; 16]>::from(e));
            #[cfg(feature = "uuid")]
            assert_eq!(uuid::Uuid::from(e).as_u128(), u128::from(e));
        }
    }

    /// Reports variant and version fields
    #[test]
    fn reports_variant_and_version_fields() {
        assert_eq!(Uuid::NIL.variant(), Variant::Nil);
        assert_eq!(Uuid::NIL.version(), None);

        assert_eq!(Uuid::MAX.variant(), Variant::Max);
        assert_eq!(Uuid::MAX.version(), None);

        let mut bytes = [42u8; 16];
        for oct6 in 0..=0xff {
            bytes[6] = oct6;
            for oct8 in 0..=0xff {
                bytes[8] = oct8;

                let e = Uuid::from(bytes);
                match e.variant() {
                    Variant::Var0 => {
                        assert_eq!(oct8 >> 7, 0b0);
                        assert_eq!(e.version(), None);
                    }
                    Variant::Var10 => {
                        assert_eq!(oct8 >> 6, 0b10);
                        assert_eq!(e.version(), Some(oct6 >> 4));
                    }
                    Variant::Var110 => {
                        assert_eq!(oct8 >> 5, 0b110);
                        assert_eq!(e.version(), None);
                    }
                    Variant::VarReserved => {
                        assert_eq!(oct8 >> 5, 0b111);
                        assert_eq!(e.version(), None);
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
}
