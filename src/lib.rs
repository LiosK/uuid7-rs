//! A Rust implementation of the proposed UUID Version 7
//!
//! ```rust
//! let uuid = uuid7::uuid7();
//! println!("{uuid}"); // e.g. "01809424-3e59-7c05-9219-566f82fff672"
//! println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
//!
//! let uuid_string: String = uuid7::uuid7().to_string();
//! ```
//!
//! See [draft-ietf-uuidrev-rfc4122bis-02](https://www.ietf.org/archive/id/draft-ietf-uuidrev-rfc4122bis-02.html).
//!
//! # Field and bit layout
//!
//! This implementation produces identifiers with the following bit layout:
//!
//! ```text
//!  0                   1                   2                   3
//!  0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                          unix_ts_ms                           |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |          unix_ts_ms           |  ver  |        counter        |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |var|                        counter                            |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! |                             rand                              |
//! +-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
//! ```
//!
//! Where:
//!
//! - The 48-bit `unix_ts_ms` field is dedicated to the Unix timestamp in
//!   milliseconds.
//! - The 4-bit `ver` field is set at `0111`.
//! - The 42-bit `counter` field accommodates the sequence counter that ensures the
//!   monotonic order of IDs generated within the same millisecond. The counter is
//!   incremented by one for each new ID generated within the same timestamp and is
//!   randomly initialized whenever the `unix_ts_ms` changes.
//! - The 2-bit `var` field is set at `10`.
//! - The remaining 32 `rand` bits are filled with a cryptographically strong random
//!   number.
//!
//! In the rare circumstances where the 42-bit `counter` field reaches its maximum
//! value and can no more be incremented within the same timestamp, this library
//! increments the `unix_ts_ms`; therefore, the `unix_ts_ms` may have a larger value
//! than that of the real-time clock. This library goes on with such larger
//! `unix_ts_ms` values caused by counter overflows and system clock rollbacks as
//! long as the difference from the system clock is small enough. If the system
//! clock moves back by ten seconds or more, this library resets the generator state
//! and thus breaks the monotonic order of generated identifiers.
//!
//! # Crate features
//!
//! Default features:
//!
//! - `std` enables the primary [`uuid7()`] function. Without `std`, this crate
//!   provides limited functionality available under `no_std` environments.
//!
//! Optional features:
//!
//! - `serde` enables the serialization and deserialization of [`Uuid`] objects.
//! - `uuid` (together with `std`) enables the [`new_v7()`] function that returns the
//!   popular [uuid](https://crates.io/crates/uuid) crate's [`Uuid`](uuid::Uuid) objects.
//!
//! # Other functionality
//!
//! This library also supports the generation of UUID version 4:
//!
//! ```rust
//! let uuid = uuid7::uuid4();
//! println!("{uuid}"); // e.g. "2ca4b2ce-6c13-40d4-bccf-37d222820f6f"
//! ```
//!
//! [`gen7::Generator`] provides a flexible interface to customize the various aspects
//! of the UUIDv7 generation:
//!
//! ```rust
//! use uuid7::gen7::Generator;
//!
//! let mut g = Generator::new(rand::rngs::OsRng);
//! let unix_ts_ms = 0x0123_4567_8901u64;
//! let x = g.generate_core(unix_ts_ms);
//! println!("{x}");
//! if let Some(y) = g.generate_core_monotonic(unix_ts_ms) {
//!     println!("{y}");
//! } else {
//!     panic!("clock moved back; monotonic order was broken");
//! }
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]

mod id;
pub use id::{ParseError, Uuid};

pub mod gen7;

mod entry;
#[cfg(feature = "std")]
pub use entry::{uuid4, uuid7};

/// Generates a UUIDv7 and returns it as an instance of [`uuid::Uuid`].
#[cfg(all(feature = "std", feature = "uuid"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "uuid"))))]
pub fn new_v7() -> uuid::Uuid {
    uuid7().into()
}
