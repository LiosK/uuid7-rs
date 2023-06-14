//! A Rust implementation of the proposed UUID Version 7
//!
//! ```rust
//! let uuid = uuid7::uuid7();
//! println!("{uuid}"); // e.g., "01809424-3e59-7c05-9219-566f82fff672"
//! println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
//!
//! let uuid_string: String = uuid7::uuid7().to_string();
//! ```
//!
//! See [draft-ietf-uuidrev-rfc4122bis-07](https://www.ietf.org/archive/id/draft-ietf-uuidrev-rfc4122bis-07.html).
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
//! - The 42-bit `counter` field accommodates a counter that ensures the increasing
//!   order of IDs generated within a millisecond. The counter is incremented by one
//!   for each new ID and is reset to a random number when the `unix_ts_ms` changes.
//! - The 2-bit `var` field is set at `10`.
//! - The remaining 32 `rand` bits are filled with a cryptographically strong random
//!   number.
//!
//! The 42-bit `counter` is sufficiently large, so you do not usually need to worry
//! about overflow, but in an extremely rare circumstance where it overflows, this
//! library increments the `unix_ts_ms` field. As a result, the `unix_ts_ms` may
//! have a greater value than that of the system's real-time clock.
//!
//! UUIDv7, by design, heavily relies on the system's wall clock to guarantee the
//! monotonically increasing order of generated IDs. A generator may not be able to
//! produce a monotonic sequence if the system clock goes backwards. This library
//! ignores a clock rollback and freezes the previously used `unix_ts_ms` unless the
//! clock rollback is considered significant (by default, ten seconds or more). If
//! such a significant rollback takes place, this library resets the generator and
//! thus breaks the monotonic order of generated IDs.
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
//! println!("{uuid}"); // e.g., "2ca4b2ce-6c13-40d4-bccf-37d222820f6f"
//! ```
//!
//! [`V7Generator`] provides an interface that allows finer control over the various
//! aspects of the UUIDv7 generation:
//!
//! ```rust
//! use uuid7::V7Generator;
//!
//! let mut g = V7Generator::new(rand::rngs::OsRng);
//! let custom_unix_ts_ms = 0x0123_4567_8901u64;
//! let x = g.generate_or_reset_core(custom_unix_ts_ms, 10_000);
//! println!("{x}");
//!
//! let y = g
//!     .generate_or_abort_core(custom_unix_ts_ms, 10_000)
//!     .expect("clock went backwards by 10_000 milliseconds or more");
//! println!("{y}");
//! ```

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]

mod id;
pub use id::{ParseError, Uuid, Variant};

mod gen7;
pub use gen7::V7Generator;

mod entry;
#[cfg(feature = "std")]
pub use entry::{uuid4, uuid7};

/// Generates a UUIDv7 and returns it as an instance of [`uuid::Uuid`].
#[cfg(all(feature = "std", feature = "uuid"))]
#[cfg_attr(docsrs, doc(cfg(all(feature = "std", feature = "uuid"))))]
pub fn new_v7() -> uuid::Uuid {
    uuid7().into()
}
