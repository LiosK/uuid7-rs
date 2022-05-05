//! An experimental implementation of the proposed UUID Version 7
//!
//! ```rust
//! use uuid7::uuid7;
//!
//! let uuid = uuid7();
//! println!("{}", uuid); // e.g. "01809424-3e59-7c05-9219-566f82fff672"
//! println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
//! ```
//!
//! See [draft-peabody-dispatch-new-uuid-format-03](https://www.ietf.org/archive/id/draft-peabody-dispatch-new-uuid-format-03.html).
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
//! In the very rare circumstances where the 42-bit `counter` field reaches the
//! maximum value and can no more be incremented within the same timestamp, this
//! library increments the `unix_ts_ms`; therefore, the `unix_ts_ms` may have a
//! larger value than that of the real-time clock. This library goes on with such
//! larger `unix_ts_ms` values caused by counter overflows and system clock
//! rollbacks as long as the difference from the system clock is small enough. If
//! the system clock moves back more than ten seconds, this library resets the
//! generator state and thus breaks the monotonic order of generated identifiers.
//!
//! # Other features
//!
//! This library also supports the generation of UUID version 4:
//!
//! ```rust
//! use uuid7::uuid4;
//!
//! let uuid = uuid4();
//! println!("{}", uuid); // e.g. "2ca4b2ce-6c13-40d4-bccf-37d222820f6f"
//! println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array
//! ```

mod uuid;
pub use uuid::Uuid;

pub mod v7;
#[doc(inline)]
pub use v7::uuid7;

mod v4;
pub use v4::uuid4;
