#[cfg(not(feature = "std"))]
use core as std;

use fstr::FStr;
use std::{fmt, str};

/// Represents a Universally Unique IDentifier.
#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
#[repr(transparent)]
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

    /// Returns the `u128` representation of the underlying byte array.
    const fn to_u128(self) -> u128 {
        u128::from_be_bytes(self.0)
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
    /// string-like type that can be handled like [`String`] through `Deref<Target = str>` and
    /// other common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use uuid7::Uuid;
    ///
    /// let x = "01809424-3e59-7c05-9219-566f82fff672".parse::<Uuid>()?;
    /// let y = x.encode();
    /// assert_eq!(y, "01809424-3e59-7c05-9219-566f82fff672");
    /// assert_eq!(format!("{}", y), "01809424-3e59-7c05-9219-566f82fff672");
    /// # Ok::<(), uuid7::ParseError>(())
    /// ```
    pub const fn encode(&self) -> FStr<36> {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";

        let mut buffer = [0u8; 36];
        let mut r = 0;
        let mut w = 0;
        while r < 16 {
            let e = self.0[r] as usize;
            buffer[w] = DIGITS[e >> 4];
            buffer[w + 1] = DIGITS[e & 15];
            if r == 3 || r == 5 || r == 7 || r == 9 {
                buffer[w + 2] = b'-';
                w += 1;
            }
            r += 1;
            w += 2;
        }

        // SAFETY: ok because buffer consists of ASCII bytes
        unsafe { FStr::from_inner_unchecked(buffer) }
    }

    /// Returns the 32-digit hexadecimal string representation without hyphens stored in a
    /// stack-allocated string-like type that can be handled like [`String`] through
    /// `Deref<Target = str>` and other common traits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use uuid7::Uuid;
    ///
    /// let x = "01809424-3e59-7c05-9219-566f82fff672".parse::<Uuid>()?;
    /// let y = x.encode_hex();
    /// assert_eq!(y, "018094243e597c059219566f82fff672");
    /// assert_eq!(format!("{}", y), "018094243e597c059219566f82fff672");
    /// # Ok::<(), uuid7::ParseError>(())
    /// ```
    pub const fn encode_hex(&self) -> FStr<32> {
        const DIGITS: &[u8; 16] = b"0123456789abcdef";

        let mut buffer = [0u8; 32];
        let mut r = 0;
        let mut w = 0;
        while r < 16 {
            let e = self.0[r] as usize;
            buffer[w] = DIGITS[e >> 4];
            buffer[w + 1] = DIGITS[e & 15];
            r += 1;
            w += 2;
        }

        // SAFETY: ok because buffer consists of ASCII bytes
        unsafe { FStr::from_inner_unchecked(buffer) }
    }

    /// Reports the variant field value of the UUID or, if appropriate, `Nil` or `Max`.
    ///
    /// For convenience, this function reports [`Variant::Nil`] or [`Variant::Max`] if `self`
    /// represents the Nil or Max UUID, although the Nil and Max UUIDs are technically subsumed
    /// under the variants `0b0` and `0b111`, respectively.
    pub const fn variant(&self) -> Variant {
        match self.0[8] >> 4 {
            0b0000..=0b0111 => {
                if self.is_nil() {
                    Variant::Nil
                } else {
                    Variant::Var0
                }
            }
            0b1000..=0b1011 => Variant::Var10,
            0b1100..=0b1101 => Variant::Var110,
            0b1110..=0b1111 => {
                if self.is_max() {
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
    pub const fn version(&self) -> Option<u8> {
        match self.variant() {
            Variant::Var10 => Some(self.0[6] >> 4),
            _ => None,
        }
    }

    /// Returns `true` if `self` is the Nil UUID.
    pub const fn is_nil(&self) -> bool {
        self.to_u128() == Self::NIL.to_u128()
    }

    /// Returns `true` if `self` is the Max UUID.
    pub const fn is_max(&self) -> bool {
        self.to_u128() == Self::MAX.to_u128()
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
        use ParseErrorKind::*;
        let (offset, is_hyphenated) = match src.len() {
            32 => (0, false),
            36 => (0, true),
            38 => match src.starts_with('{') && src.ends_with('}') {
                true => (1, true),
                _ => return Err(ParseError { kind: Format }),
            },
            45 => match src.get(..9).map(|h| h.eq_ignore_ascii_case("urn:uuid:")) {
                Some(true) => (9, true),
                _ => return Err(ParseError { kind: Format }),
            },
            _ => return Err(ParseError { kind: Format }),
        };

        let mut dst = [0u8; 16];
        let mut iter = src.chars().skip(offset);
        for (i, byte) in dst.iter_mut().enumerate() {
            let hi = {
                let chr = iter.next().unwrap();
                chr.to_digit(16).ok_or(ParseError { kind: Digit(chr) })?
            } as u8;
            let lo = {
                let chr = iter.next().unwrap();
                chr.to_digit(16).ok_or(ParseError { kind: Digit(chr) })?
            } as u8;
            *byte = (hi << 4) | lo;
            if is_hyphenated && (i == 3 || i == 5 || i == 7 || i == 9) {
                let chr = iter.next().unwrap();
                if chr != '-' {
                    return Err(ParseError { kind: Hyphen(chr) });
                }
            }
        }
        // `match src.len()` arms, `to_digit(16)`, or `!= '-'` fails if `src` includes non-ASCII
        debug_assert!(src.is_ascii());
        Ok(Self(dst))
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
        src.to_u128()
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
    Digit(char),
    Format,
    Hyphen(char),
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ParseErrorKind::*;
        write!(f, "could not parse string as UUID: ")?;
        match self.kind {
            Digit(chr) => write!(f, "invalid hex digit {:?} found", chr),
            Format => write!(f, "invalid length or unsupported format"),
            Hyphen(chr) => write!(f, "expected '-' not found but {:?}", chr),
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

    /// The variant `0b10` (RFC 9562).
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
mod with_std {
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
mod with_uuid {
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
mod with_serde {
    use super::{Uuid, fmt, str};
    use serde::{Deserializer, Serializer, de};

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

    impl de::Visitor<'_> for VisitorImpl {
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

    /// Serializes and deserializes prepared cases correctly
    #[cfg(test)]
    #[test]
    fn serializes_and_deserializes_prepared_cases_correctly() {
        use super::{Uuid, tests::EXAMPLE_UUIDS};
        use serde_test::{Configure, Token};

        for c in EXAMPLE_UUIDS {
            let e = c.hyphenated.parse::<Uuid>().unwrap();
            serde_test::assert_tokens(&e.readable(), &[Token::Str(c.hyphenated)]);
            serde_test::assert_tokens(&e.compact(), &[Token::Bytes(&c.bytes)]);
            serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(&c.bytes)]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Str(c.hyphenated)]);
            serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(c.hyphenated.as_bytes())]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Bytes(c.hyphenated.as_bytes())]);

            serde_test::assert_de_tokens(&e.readable(), &[Token::Str(c.hex)]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Str(c.hex)]);
            serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(c.hex.as_bytes())]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Bytes(c.hex.as_bytes())]);

            serde_test::assert_de_tokens(&e.readable(), &[Token::Str(c.braced)]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Str(c.braced)]);
            serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(c.braced.as_bytes())]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Bytes(c.braced.as_bytes())]);

            serde_test::assert_de_tokens(&e.readable(), &[Token::Str(c.urn)]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Str(c.urn)]);
            serde_test::assert_de_tokens(&e.readable(), &[Token::Bytes(c.urn.as_bytes())]);
            serde_test::assert_de_tokens(&e.compact(), &[Token::Bytes(c.urn.as_bytes())]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{Uuid, Variant};

    /// Encodes and decodes prepared cases correctly
    #[test]
    fn encodes_and_decodes_prepared_cases_correctly() {
        for c in EXAMPLE_UUIDS {
            let Some(fs) = c.fields_v7 else { break };
            let from_fields = Uuid::from_fields_v7(fs.0, fs.1, fs.2);
            assert_eq!(Ok(from_fields), c.hyphenated.parse());
            assert_eq!(Ok(from_fields), c.hyphenated.to_uppercase().parse());
            assert_eq!(Ok(from_fields), c.hex.parse());
            assert_eq!(Ok(from_fields), c.hex.to_uppercase().parse());
            assert_eq!(Ok(from_fields), c.braced.parse());
            assert_eq!(Ok(from_fields), c.braced.to_uppercase().parse());
            assert_eq!(Ok(from_fields), c.urn.parse());
            assert_eq!(Ok(from_fields), c.urn.to_uppercase().parse());

            assert_eq!(&from_fields.encode() as &str, c.hyphenated);
            assert_eq!(&from_fields.encode_hex() as &str, c.hex);
            assert_eq!(from_fields.variant(), Variant::Var10);
            assert_eq!(from_fields.version(), Some(7));

            #[cfg(feature = "std")]
            {
                assert_eq!(&from_fields.to_string(), c.hyphenated);
                assert_eq!(&from_fields.encode().to_string(), c.hyphenated);
                assert_eq!(&from_fields.encode_hex().to_string(), c.hex);
                #[cfg(feature = "uuid")]
                assert_eq!(&uuid::Uuid::from(from_fields).to_string(), c.hyphenated);
            }
        }
    }

    /// Returns error to invalid string representation
    #[test]
    fn returns_error_to_invalid_string_representation() {
        let cases = [
            "",
            "0",
            " 0180a8f0-5b82-75b4-9fef-ecad657c30bb",
            "0180a8f0-5b84-7438-ab50-f0626f78002b ",
            " 0180a8f0-5b84-7438-ab50-f063bd5331af ",
            "+0180a8f0-5b84-7438-ab50-f06405d35edb",
            "-0180a8f0-5b84-7438-ab50-f06508df4c2d",
            "+180a8f0-5b84-7438-ab50-f066aa10a367",
            "-180a8f0-5b84-7438-ab50-f067cdce1d69",
            "0180a8f0-5b847438-ab50-f06991838802",
            "0180a8f0-5b84-74 8-ab50-f06bed27bdc7",
            "0180a8g0-5b84-7438-ab50-f06c91175b8a",
            "0180a8f0-5b84-7438-ab50_f06d3ea24429",
            " 82f1dd3c-de95-075b-93ff-a240f135f8fd",
            "82f1dd3c-de95-075b-93ff-a240f135f8fd ",
            " 82f1dd3c-de95-075b-93ff-a240f135f8fd ",
            "82f1dd3cd-e95-075b-93ff-a240f135f8fd",
            "82f1dd3c-de95075b-93ff-a240f135f8fd",
            "82f1dd3c-de95-075b93ff-a240-f135f8fd",
            "{8273b64c5ed0a88b10dad09a6a2b963c}",
            "urn:uuid:8273b64c5ed0a88b10dad09a6a2b963c",
            "06536892-0g22-499d-8aaf-b0dd9cfa69a4",
            "864eh78f-0571-46jf-a1w4-538v0fdoacff",
            "45f63383 ef0e 0d9d b1ba 834a9726829e",
            "leading c86e2e5f-1962-42c9-85d6-cb127040b107",
            "97f43427-788b-47bb-b2e8-cc7d79432a75 trailing",
            "910e7851-4521-45c4-866b-fc5464",
            "44b1796d-9d0b-4aac-81cd-ef8ed2b90e18b6fe54",
            "{0189f965-7b27-7dc0-8f96-1d8eb026b7e2]",
            "(0189f965-7b27-7dc0-8f96-1d8eb026b7e2}",
            "urn:uuld:0189f965-7b27-7dc0-8f96-1d8eb026b7e2",
            "0189f965-7b27-7dc0-8f96-1d8ebſ6b7e2",
        ];

        for e in cases {
            assert!(e.parse::<Uuid>().is_err());
        }
    }

    /// Returns Nil and Max UUIDs
    #[test]
    fn returns_nil_and_max_uuids() {
        assert!(Uuid::NIL.is_nil());
        assert_eq!(
            &Uuid::NIL.encode() as &str,
            "00000000-0000-0000-0000-000000000000"
        );

        assert!(Uuid::MAX.is_max());
        assert_eq!(
            &Uuid::MAX.encode() as &str,
            "ffffffff-ffff-ffff-ffff-ffffffffffff"
        );
    }

    /// Has symmetric converters
    #[test]
    fn has_symmetric_converters() {
        for c in EXAMPLE_UUIDS {
            let Some(fs) = c.fields_v7 else { break };
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

        assert_eq!(Uuid::from([0x00u8; 16]).variant(), Variant::Nil);
        assert_eq!(Uuid::from([0xffu8; 16]).variant(), Variant::Max);

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

    #[derive(Debug)]
    pub struct ExampleUuid {
        pub hyphenated: &'static str,
        pub hex: &'static str,
        pub braced: &'static str,
        pub urn: &'static str,
        pub fields_v7: Option<(u64, u16, u64)>,
        #[cfg_attr(not(feature = "serde"), allow(dead_code))]
        pub bytes: [u8; 16],
    }

    pub const EXAMPLE_UUIDS: &[ExampleUuid] = &[
        ExampleUuid {
            hyphenated: "00000000-0000-7000-8000-000000000000",
            hex: "00000000000070008000000000000000",
            braced: "{00000000-0000-7000-8000-000000000000}",
            urn: "urn:uuid:00000000-0000-7000-8000-000000000000",
            fields_v7: Some((0x000000000000, 0x000, 0x0000000000000000)),
            bytes: [0, 0, 0, 0, 0, 0, 112, 0, 128, 0, 0, 0, 0, 0, 0, 0],
        },
        ExampleUuid {
            hyphenated: "00000000-0000-7000-bfff-ffffffffffff",
            hex: "0000000000007000bfffffffffffffff",
            braced: "{00000000-0000-7000-bfff-ffffffffffff}",
            urn: "urn:uuid:00000000-0000-7000-bfff-ffffffffffff",
            fields_v7: Some((0x000000000000, 0x000, 0x3fffffffffffffff)),
            bytes: [
                0, 0, 0, 0, 0, 0, 112, 0, 191, 255, 255, 255, 255, 255, 255, 255,
            ],
        },
        ExampleUuid {
            hyphenated: "00000000-0000-7fff-8000-000000000000",
            hex: "0000000000007fff8000000000000000",
            braced: "{00000000-0000-7fff-8000-000000000000}",
            urn: "urn:uuid:00000000-0000-7fff-8000-000000000000",
            fields_v7: Some((0x000000000000, 0xfff, 0x0000000000000000)),
            bytes: [0, 0, 0, 0, 0, 0, 127, 255, 128, 0, 0, 0, 0, 0, 0, 0],
        },
        ExampleUuid {
            hyphenated: "ffffffff-ffff-7000-8000-000000000000",
            hex: "ffffffffffff70008000000000000000",
            braced: "{ffffffff-ffff-7000-8000-000000000000}",
            urn: "urn:uuid:ffffffff-ffff-7000-8000-000000000000",
            fields_v7: Some((0xffffffffffff, 0x000, 0x0000000000000000)),
            bytes: [
                255, 255, 255, 255, 255, 255, 112, 0, 128, 0, 0, 0, 0, 0, 0, 0,
            ],
        },
        ExampleUuid {
            hyphenated: "ffffffff-ffff-7fff-bfff-ffffffffffff",
            hex: "ffffffffffff7fffbfffffffffffffff",
            braced: "{ffffffff-ffff-7fff-bfff-ffffffffffff}",
            urn: "urn:uuid:ffffffff-ffff-7fff-bfff-ffffffffffff",
            fields_v7: Some((0xffffffffffff, 0xfff, 0x3fffffffffffffff)),
            bytes: [
                255, 255, 255, 255, 255, 255, 127, 255, 191, 255, 255, 255, 255, 255, 255, 255,
            ],
        },
        ExampleUuid {
            hyphenated: "00c7ad2f-67fc-7775-aa5d-177c68e6c25e",
            hex: "00c7ad2f67fc7775aa5d177c68e6c25e",
            braced: "{00c7ad2f-67fc-7775-aa5d-177c68e6c25e}",
            urn: "urn:uuid:00c7ad2f-67fc-7775-aa5d-177c68e6c25e",
            fields_v7: Some((0x00c7ad2f67fc, 0x775, 0x2a5d177c68e6c25e)),
            bytes: [
                0, 199, 173, 47, 103, 252, 119, 117, 170, 93, 23, 124, 104, 230, 194, 94,
            ],
        },
        ExampleUuid {
            hyphenated: "017f22e2-79b0-7cc3-98c4-dc0c0c07398f",
            hex: "017f22e279b07cc398c4dc0c0c07398f",
            braced: "{017f22e2-79b0-7cc3-98c4-dc0c0c07398f}",
            urn: "urn:uuid:017f22e2-79b0-7cc3-98c4-dc0c0c07398f",
            fields_v7: Some((0x017f22e279b0, 0xcc3, 0x18c4dc0c0c07398f)),
            bytes: [
                1, 127, 34, 226, 121, 176, 124, 195, 152, 196, 220, 12, 12, 7, 57, 143,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-078c-7b80-b113-2fe14a615fb3",
            hex: "0180ae59078c7b80b1132fe14a615fb3",
            braced: "{0180ae59-078c-7b80-b113-2fe14a615fb3}",
            urn: "urn:uuid:0180ae59-078c-7b80-b113-2fe14a615fb3",
            fields_v7: Some((0x0180ae59078c, 0xb80, 0x31132fe14a615fb3)),
            bytes: [
                1, 128, 174, 89, 7, 140, 123, 128, 177, 19, 47, 225, 74, 97, 95, 179,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0790-7f6d-897d-79370b09dd07",
            hex: "0180ae5907907f6d897d79370b09dd07",
            braced: "{0180ae59-0790-7f6d-897d-79370b09dd07}",
            urn: "urn:uuid:0180ae59-0790-7f6d-897d-79370b09dd07",
            fields_v7: Some((0x0180ae590790, 0xf6d, 0x097d79370b09dd07)),
            bytes: [
                1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 55, 11, 9, 221, 7,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0790-7f6d-897d-7938e16176fc",
            hex: "0180ae5907907f6d897d7938e16176fc",
            braced: "{0180ae59-0790-7f6d-897d-7938e16176fc}",
            urn: "urn:uuid:0180ae59-0790-7f6d-897d-7938e16176fc",
            fields_v7: Some((0x0180ae590790, 0xf6d, 0x097d7938e16176fc)),
            bytes: [
                1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 56, 225, 97, 118, 252,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0790-7f6d-897d-7939dbb56111",
            hex: "0180ae5907907f6d897d7939dbb56111",
            braced: "{0180ae59-0790-7f6d-897d-7939dbb56111}",
            urn: "urn:uuid:0180ae59-0790-7f6d-897d-7939dbb56111",
            fields_v7: Some((0x0180ae590790, 0xf6d, 0x097d7939dbb56111)),
            bytes: [
                1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 57, 219, 181, 97, 17,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0790-7f6d-897d-793af4b611fb",
            hex: "0180ae5907907f6d897d793af4b611fb",
            braced: "{0180ae59-0790-7f6d-897d-793af4b611fb}",
            urn: "urn:uuid:0180ae59-0790-7f6d-897d-793af4b611fb",
            fields_v7: Some((0x0180ae590790, 0xf6d, 0x097d793af4b611fb)),
            bytes: [
                1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 58, 244, 182, 17, 251,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0790-7f6d-897d-793be80c6ca4",
            hex: "0180ae5907907f6d897d793be80c6ca4",
            braced: "{0180ae59-0790-7f6d-897d-793be80c6ca4}",
            urn: "urn:uuid:0180ae59-0790-7f6d-897d-793be80c6ca4",
            fields_v7: Some((0x0180ae590790, 0xf6d, 0x097d793be80c6ca4)),
            bytes: [
                1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 59, 232, 12, 108, 164,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0790-7f6d-897d-793c00a6b6d7",
            hex: "0180ae5907907f6d897d793c00a6b6d7",
            braced: "{0180ae59-0790-7f6d-897d-793c00a6b6d7}",
            urn: "urn:uuid:0180ae59-0790-7f6d-897d-793c00a6b6d7",
            fields_v7: Some((0x0180ae590790, 0xf6d, 0x097d793c00a6b6d7)),
            bytes: [
                1, 128, 174, 89, 7, 144, 127, 109, 137, 125, 121, 60, 0, 166, 182, 215,
            ],
        },
        ExampleUuid {
            hyphenated: "0180ae59-0791-7e79-8804-02ce2b5bc8d2",
            hex: "0180ae5907917e79880402ce2b5bc8d2",
            braced: "{0180ae59-0791-7e79-8804-02ce2b5bc8d2}",
            urn: "urn:uuid:0180ae59-0791-7e79-8804-02ce2b5bc8d2",
            fields_v7: Some((0x0180ae590791, 0xe79, 0x080402ce2b5bc8d2)),
            bytes: [
                1, 128, 174, 89, 7, 145, 126, 121, 136, 4, 2, 206, 43, 91, 200, 210,
            ],
        },
        ExampleUuid {
            hyphenated: "09ed4f9e-971f-7343-a8a7-40c969795aa6",
            hex: "09ed4f9e971f7343a8a740c969795aa6",
            braced: "{09ed4f9e-971f-7343-a8a7-40c969795aa6}",
            urn: "urn:uuid:09ed4f9e-971f-7343-a8a7-40c969795aa6",
            fields_v7: Some((0x09ed4f9e971f, 0x343, 0x28a740c969795aa6)),
            bytes: [
                9, 237, 79, 158, 151, 31, 115, 67, 168, 167, 64, 201, 105, 121, 90, 166,
            ],
        },
        ExampleUuid {
            hyphenated: "28c21084-2287-7e81-8f72-f0ca391ae12a",
            hex: "28c2108422877e818f72f0ca391ae12a",
            braced: "{28c21084-2287-7e81-8f72-f0ca391ae12a}",
            urn: "urn:uuid:28c21084-2287-7e81-8f72-f0ca391ae12a",
            fields_v7: Some((0x28c210842287, 0xe81, 0x0f72f0ca391ae12a)),
            bytes: [
                40, 194, 16, 132, 34, 135, 126, 129, 143, 114, 240, 202, 57, 26, 225, 42,
            ],
        },
        ExampleUuid {
            hyphenated: "36c6849e-d55a-740d-86e0-32eec9e03663",
            hex: "36c6849ed55a740d86e032eec9e03663",
            braced: "{36c6849e-d55a-740d-86e0-32eec9e03663}",
            urn: "urn:uuid:36c6849e-d55a-740d-86e0-32eec9e03663",
            fields_v7: Some((0x36c6849ed55a, 0x40d, 0x06e032eec9e03663)),
            bytes: [
                54, 198, 132, 158, 213, 90, 116, 13, 134, 224, 50, 238, 201, 224, 54, 99,
            ],
        },
        ExampleUuid {
            hyphenated: "3c118418-e261-7925-a2a0-bed422629452",
            hex: "3c118418e2617925a2a0bed422629452",
            braced: "{3c118418-e261-7925-a2a0-bed422629452}",
            urn: "urn:uuid:3c118418-e261-7925-a2a0-bed422629452",
            fields_v7: Some((0x3c118418e261, 0x925, 0x22a0bed422629452)),
            bytes: [
                60, 17, 132, 24, 226, 97, 121, 37, 162, 160, 190, 212, 34, 98, 148, 82,
            ],
        },
        ExampleUuid {
            hyphenated: "462a9021-a1fb-78ac-9b64-24bc29937258",
            hex: "462a9021a1fb78ac9b6424bc29937258",
            braced: "{462a9021-a1fb-78ac-9b64-24bc29937258}",
            urn: "urn:uuid:462a9021-a1fb-78ac-9b64-24bc29937258",
            fields_v7: Some((0x462a9021a1fb, 0x8ac, 0x1b6424bc29937258)),
            bytes: [
                70, 42, 144, 33, 161, 251, 120, 172, 155, 100, 36, 188, 41, 147, 114, 88,
            ],
        },
        ExampleUuid {
            hyphenated: "565aa057-c667-7112-b002-f21048341917",
            hex: "565aa057c6677112b002f21048341917",
            braced: "{565aa057-c667-7112-b002-f21048341917}",
            urn: "urn:uuid:565aa057-c667-7112-b002-f21048341917",
            fields_v7: Some((0x565aa057c667, 0x112, 0x3002f21048341917)),
            bytes: [
                86, 90, 160, 87, 198, 103, 113, 18, 176, 2, 242, 16, 72, 52, 25, 23,
            ],
        },
        ExampleUuid {
            hyphenated: "6ad0aeb5-2304-7b0c-9a8e-81248f251fd0",
            hex: "6ad0aeb523047b0c9a8e81248f251fd0",
            braced: "{6ad0aeb5-2304-7b0c-9a8e-81248f251fd0}",
            urn: "urn:uuid:6ad0aeb5-2304-7b0c-9a8e-81248f251fd0",
            fields_v7: Some((0x6ad0aeb52304, 0xb0c, 0x1a8e81248f251fd0)),
            bytes: [
                106, 208, 174, 181, 35, 4, 123, 12, 154, 142, 129, 36, 143, 37, 31, 208,
            ],
        },
        ExampleUuid {
            hyphenated: "748f153a-906f-74dc-bf75-b34645e00cf6",
            hex: "748f153a906f74dcbf75b34645e00cf6",
            braced: "{748f153a-906f-74dc-bf75-b34645e00cf6}",
            urn: "urn:uuid:748f153a-906f-74dc-bf75-b34645e00cf6",
            fields_v7: Some((0x748f153a906f, 0x4dc, 0x3f75b34645e00cf6)),
            bytes: [
                116, 143, 21, 58, 144, 111, 116, 220, 191, 117, 179, 70, 69, 224, 12, 246,
            ],
        },
        ExampleUuid {
            hyphenated: "936b5620-ef3d-7fc4-b44b-bd7257ac08aa",
            hex: "936b5620ef3d7fc4b44bbd7257ac08aa",
            braced: "{936b5620-ef3d-7fc4-b44b-bd7257ac08aa}",
            urn: "urn:uuid:936b5620-ef3d-7fc4-b44b-bd7257ac08aa",
            fields_v7: Some((0x936b5620ef3d, 0xfc4, 0x344bbd7257ac08aa)),
            bytes: [
                147, 107, 86, 32, 239, 61, 127, 196, 180, 75, 189, 114, 87, 172, 8, 170,
            ],
        },
        ExampleUuid {
            hyphenated: "a4f42edd-870a-7d95-8055-edd081914d74",
            hex: "a4f42edd870a7d958055edd081914d74",
            braced: "{a4f42edd-870a-7d95-8055-edd081914d74}",
            urn: "urn:uuid:a4f42edd-870a-7d95-8055-edd081914d74",
            fields_v7: Some((0xa4f42edd870a, 0xd95, 0x0055edd081914d74)),
            bytes: [
                164, 244, 46, 221, 135, 10, 125, 149, 128, 85, 237, 208, 129, 145, 77, 116,
            ],
        },
        ExampleUuid {
            hyphenated: "b5c73543-6c73-719f-8035-7b0dc5d14202",
            hex: "b5c735436c73719f80357b0dc5d14202",
            braced: "{b5c73543-6c73-719f-8035-7b0dc5d14202}",
            urn: "urn:uuid:b5c73543-6c73-719f-8035-7b0dc5d14202",
            fields_v7: Some((0xb5c735436c73, 0x19f, 0x00357b0dc5d14202)),
            bytes: [
                181, 199, 53, 67, 108, 115, 113, 159, 128, 53, 123, 13, 197, 209, 66, 2,
            ],
        },
        ExampleUuid {
            hyphenated: "b6b89352-7d5b-7683-9e97-df98d7a5b321",
            hex: "b6b893527d5b76839e97df98d7a5b321",
            braced: "{b6b89352-7d5b-7683-9e97-df98d7a5b321}",
            urn: "urn:uuid:b6b89352-7d5b-7683-9e97-df98d7a5b321",
            fields_v7: Some((0xb6b893527d5b, 0x683, 0x1e97df98d7a5b321)),
            bytes: [
                182, 184, 147, 82, 125, 91, 118, 131, 158, 151, 223, 152, 215, 165, 179, 33,
            ],
        },
        ExampleUuid {
            hyphenated: "c1074072-1c18-71d2-8fb4-869d5ad33723",
            hex: "c10740721c1871d28fb4869d5ad33723",
            braced: "{c1074072-1c18-71d2-8fb4-869d5ad33723}",
            urn: "urn:uuid:c1074072-1c18-71d2-8fb4-869d5ad33723",
            fields_v7: Some((0xc10740721c18, 0x1d2, 0x0fb4869d5ad33723)),
            bytes: [
                193, 7, 64, 114, 28, 24, 113, 210, 143, 180, 134, 157, 90, 211, 55, 35,
            ],
        },
        ExampleUuid {
            hyphenated: "d73eac55-5b53-7d53-bf85-0566d85ea524",
            hex: "d73eac555b537d53bf850566d85ea524",
            braced: "{d73eac55-5b53-7d53-bf85-0566d85ea524}",
            urn: "urn:uuid:d73eac55-5b53-7d53-bf85-0566d85ea524",
            fields_v7: Some((0xd73eac555b53, 0xd53, 0x3f850566d85ea524)),
            bytes: [
                215, 62, 172, 85, 91, 83, 125, 83, 191, 133, 5, 102, 216, 94, 165, 36,
            ],
        },
        ExampleUuid {
            hyphenated: "ee413d37-e4fc-71ba-942d-d8e5b3097832",
            hex: "ee413d37e4fc71ba942dd8e5b3097832",
            braced: "{ee413d37-e4fc-71ba-942d-d8e5b3097832}",
            urn: "urn:uuid:ee413d37-e4fc-71ba-942d-d8e5b3097832",
            fields_v7: Some((0xee413d37e4fc, 0x1ba, 0x142dd8e5b3097832)),
            bytes: [
                238, 65, 61, 55, 228, 252, 113, 186, 148, 45, 216, 229, 179, 9, 120, 50,
            ],
        },
        ExampleUuid {
            hyphenated: "00000000-0000-0000-0000-000000000000",
            hex: "00000000000000000000000000000000",
            braced: "{00000000-0000-0000-0000-000000000000}",
            urn: "urn:uuid:00000000-0000-0000-0000-000000000000",
            fields_v7: None,
            bytes: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        },
        ExampleUuid {
            hyphenated: "ffffffff-ffff-ffff-ffff-ffffffffffff",
            hex: "ffffffffffffffffffffffffffffffff",
            braced: "{ffffffff-ffff-ffff-ffff-ffffffffffff}",
            urn: "urn:uuid:ffffffff-ffff-ffff-ffff-ffffffffffff",
            fields_v7: None,
            bytes: [
                255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255,
            ],
        },
        ExampleUuid {
            hyphenated: "90252ae1-bdee-b5e6-4549-83a13e69d556",
            hex: "90252ae1bdeeb5e6454983a13e69d556",
            braced: "{90252ae1-bdee-b5e6-4549-83a13e69d556}",
            urn: "urn:uuid:90252ae1-bdee-b5e6-4549-83a13e69d556",
            fields_v7: None,
            bytes: [
                144, 37, 42, 225, 189, 238, 181, 230, 69, 73, 131, 161, 62, 105, 213, 86,
            ],
        },
        ExampleUuid {
            hyphenated: "19c63717-dd78-907f-153d-c2d12a357ebb",
            hex: "19c63717dd78907f153dc2d12a357ebb",
            braced: "{19c63717-dd78-907f-153d-c2d12a357ebb}",
            urn: "urn:uuid:19c63717-dd78-907f-153d-c2d12a357ebb",
            fields_v7: None,
            bytes: [
                25, 198, 55, 23, 221, 120, 144, 127, 21, 61, 194, 209, 42, 53, 126, 187,
            ],
        },
        ExampleUuid {
            hyphenated: "1df0de92-3543-c988-6d44-6b0ef75df795",
            hex: "1df0de923543c9886d446b0ef75df795",
            braced: "{1df0de92-3543-c988-6d44-6b0ef75df795}",
            urn: "urn:uuid:1df0de92-3543-c988-6d44-6b0ef75df795",
            fields_v7: None,
            bytes: [
                29, 240, 222, 146, 53, 67, 201, 136, 109, 68, 107, 14, 247, 93, 247, 149,
            ],
        },
        ExampleUuid {
            hyphenated: "14e0fa56-29c7-0c0d-663f-5d326e51f1ce",
            hex: "14e0fa5629c70c0d663f5d326e51f1ce",
            braced: "{14e0fa56-29c7-0c0d-663f-5d326e51f1ce}",
            urn: "urn:uuid:14e0fa56-29c7-0c0d-663f-5d326e51f1ce",
            fields_v7: None,
            bytes: [
                20, 224, 250, 86, 41, 199, 12, 13, 102, 63, 93, 50, 110, 81, 241, 206,
            ],
        },
        ExampleUuid {
            hyphenated: "bd3ba1d1-ed92-4804-b900-4b6f96124cf4",
            hex: "bd3ba1d1ed924804b9004b6f96124cf4",
            braced: "{bd3ba1d1-ed92-4804-b900-4b6f96124cf4}",
            urn: "urn:uuid:bd3ba1d1-ed92-4804-b900-4b6f96124cf4",
            fields_v7: None,
            bytes: [
                189, 59, 161, 209, 237, 146, 72, 4, 185, 0, 75, 111, 150, 18, 76, 244,
            ],
        },
        ExampleUuid {
            hyphenated: "e8e1d087-617c-3a88-e8f4-789ab4a7cf65",
            hex: "e8e1d087617c3a88e8f4789ab4a7cf65",
            braced: "{e8e1d087-617c-3a88-e8f4-789ab4a7cf65}",
            urn: "urn:uuid:e8e1d087-617c-3a88-e8f4-789ab4a7cf65",
            fields_v7: None,
            bytes: [
                232, 225, 208, 135, 97, 124, 58, 136, 232, 244, 120, 154, 180, 167, 207, 101,
            ],
        },
        ExampleUuid {
            hyphenated: "f309d5b0-2bf3-a736-7400-75948ad1ffc5",
            hex: "f309d5b02bf3a736740075948ad1ffc5",
            braced: "{f309d5b0-2bf3-a736-7400-75948ad1ffc5}",
            urn: "urn:uuid:f309d5b0-2bf3-a736-7400-75948ad1ffc5",
            fields_v7: None,
            bytes: [
                243, 9, 213, 176, 43, 243, 167, 54, 116, 0, 117, 148, 138, 209, 255, 197,
            ],
        },
        ExampleUuid {
            hyphenated: "171fd840-f315-e732-2796-dea092d372b2",
            hex: "171fd840f315e7322796dea092d372b2",
            braced: "{171fd840-f315-e732-2796-dea092d372b2}",
            urn: "urn:uuid:171fd840-f315-e732-2796-dea092d372b2",
            fields_v7: None,
            bytes: [
                23, 31, 216, 64, 243, 21, 231, 50, 39, 150, 222, 160, 146, 211, 114, 178,
            ],
        },
        ExampleUuid {
            hyphenated: "c885af25-4a61-954a-1687-c08e41f9940b",
            hex: "c885af254a61954a1687c08e41f9940b",
            braced: "{c885af25-4a61-954a-1687-c08e41f9940b}",
            urn: "urn:uuid:c885af25-4a61-954a-1687-c08e41f9940b",
            fields_v7: None,
            bytes: [
                200, 133, 175, 37, 74, 97, 149, 74, 22, 135, 192, 142, 65, 249, 148, 11,
            ],
        },
        ExampleUuid {
            hyphenated: "3d46fe79-7828-7d4f-f1e5-7bdf80ab30e1",
            hex: "3d46fe7978287d4ff1e57bdf80ab30e1",
            braced: "{3d46fe79-7828-7d4f-f1e5-7bdf80ab30e1}",
            urn: "urn:uuid:3d46fe79-7828-7d4f-f1e5-7bdf80ab30e1",
            fields_v7: None,
            bytes: [
                61, 70, 254, 121, 120, 40, 125, 79, 241, 229, 123, 223, 128, 171, 48, 225,
            ],
        },
        ExampleUuid {
            hyphenated: "e5d7215d-6e2c-3299-1506-498b84b32d33",
            hex: "e5d7215d6e2c32991506498b84b32d33",
            braced: "{e5d7215d-6e2c-3299-1506-498b84b32d33}",
            urn: "urn:uuid:e5d7215d-6e2c-3299-1506-498b84b32d33",
            fields_v7: None,
            bytes: [
                229, 215, 33, 93, 110, 44, 50, 153, 21, 6, 73, 139, 132, 179, 45, 51,
            ],
        },
        ExampleUuid {
            hyphenated: "c2416789-944c-b584-e886-ac162d9112b7",
            hex: "c2416789944cb584e886ac162d9112b7",
            braced: "{c2416789-944c-b584-e886-ac162d9112b7}",
            urn: "urn:uuid:c2416789-944c-b584-e886-ac162d9112b7",
            fields_v7: None,
            bytes: [
                194, 65, 103, 137, 148, 76, 181, 132, 232, 134, 172, 22, 45, 145, 18, 183,
            ],
        },
        ExampleUuid {
            hyphenated: "0947fa84-3806-088a-77aa-1b1ed69b7789",
            hex: "0947fa843806088a77aa1b1ed69b7789",
            braced: "{0947fa84-3806-088a-77aa-1b1ed69b7789}",
            urn: "urn:uuid:0947fa84-3806-088a-77aa-1b1ed69b7789",
            fields_v7: None,
            bytes: [
                9, 71, 250, 132, 56, 6, 8, 138, 119, 170, 27, 30, 214, 155, 119, 137,
            ],
        },
        ExampleUuid {
            hyphenated: "44e76ce2-1f2e-77bd-badb-64850026fd86",
            hex: "44e76ce21f2e77bdbadb64850026fd86",
            braced: "{44e76ce2-1f2e-77bd-badb-64850026fd86}",
            urn: "urn:uuid:44e76ce2-1f2e-77bd-badb-64850026fd86",
            fields_v7: None,
            bytes: [
                68, 231, 108, 226, 31, 46, 119, 189, 186, 219, 100, 133, 0, 38, 253, 134,
            ],
        },
        ExampleUuid {
            hyphenated: "7275ea47-7628-0fa8-2afb-0c4b47f148c3",
            hex: "7275ea4776280fa82afb0c4b47f148c3",
            braced: "{7275ea47-7628-0fa8-2afb-0c4b47f148c3}",
            urn: "urn:uuid:7275ea47-7628-0fa8-2afb-0c4b47f148c3",
            fields_v7: None,
            bytes: [
                114, 117, 234, 71, 118, 40, 15, 168, 42, 251, 12, 75, 71, 241, 72, 195,
            ],
        },
        ExampleUuid {
            hyphenated: "20a6bdda-fff4-faa1-4e8f-c0eb75a169f9",
            hex: "20a6bddafff4faa14e8fc0eb75a169f9",
            braced: "{20a6bdda-fff4-faa1-4e8f-c0eb75a169f9}",
            urn: "urn:uuid:20a6bdda-fff4-faa1-4e8f-c0eb75a169f9",
            fields_v7: None,
            bytes: [
                32, 166, 189, 218, 255, 244, 250, 161, 78, 143, 192, 235, 117, 161, 105, 249,
            ],
        },
    ];
}
