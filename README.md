# uuid7

[![Crates.io](https://img.shields.io/crates/v/uuid7)](https://crates.io/crates/uuid7)
[![License](https://img.shields.io/crates/l/uuid7)](https://github.com/LiosK/uuid7-rs/blob/main/LICENSE)

A Rust implementation of UUID version 7

```rust
let uuid = uuid7::uuid7();
println!("{}", uuid); // e.g., "01809424-3e59-7c05-9219-566f82fff672"
println!("{:?}", uuid.as_bytes()); // as 16-byte big-endian array

let uuid_string: String = uuid7::uuid7().to_string();
```

See [RFC 9562](https://www.rfc-editor.org/rfc/rfc9562).

## Field and bit layout

This implementation produces identifiers with the following bit layout:

```text
 0                   1                   2                   3
 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1 2 3 4 5 6 7 8 9 0 1
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                          unix_ts_ms                           |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|          unix_ts_ms           |  ver  |        counter        |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|var|                        counter                            |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
|                             rand                              |
+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+-+
```

Where:

- The 48-bit `unix_ts_ms` field is dedicated to the Unix timestamp in
  milliseconds.
- The 4-bit `ver` field is set at `0111`.
- The 42-bit `counter` field accommodates a counter that ensures the increasing
  order of IDs generated within a millisecond. The counter is incremented by one
  for each new ID and is reset to a random number when the `unix_ts_ms` changes.
- The 2-bit `var` field is set at `10`.
- The remaining 32 `rand` bits are filled with a cryptographically strong random
  number.

The 42-bit `counter` is sufficiently large, so you do not usually need to worry
about overflow, but in an extremely rare circumstance where it overflows, this
library increments the `unix_ts_ms` field to continue instant monotonic
generation. As a result, the `unix_ts_ms` may have a greater value than that of
the system's real-time clock. (See also [Why so large counter? (42bits)]).

UUIDv7, by design, relies on the system clock to guarantee the monotonically
increasing order of generated IDs. A generator may not be able to produce a
monotonic sequence if the system clock goes backwards. This library ignores a
clock rollback and reuses the previous `unix_ts_ms` unless the clock rollback is
considered significant (by default, more than ten seconds). If such a
significant rollback takes place, this library resets the generator by default
and thus breaks the increasing order of generated IDs.

[Why so large counter? (42bits)]: https://github.com/LiosK/uuidv7/issues/13#issuecomment-2306922356

## Crate features

Default features:

- `std` enables, among others, the default timestamp source for `V7Generator`
  using `std::time`. Without `std`, users must provide their own time source
  implementing the `TimeSource` trait.
- `global_gen` (implies `std`) provides the process-wide default UUIDv7
  generator and enables the primary `uuid7()` function.
- `rand08`: See below.

Optional features:

- `serde` enables serialization/deserialization of `Uuid` via serde.
- `rand010` enables an adapter for `rand::RngCore` to use `rand` (v0.10) and any
  other conforming random number generators with `V7Generator`.
- `rand09` enables an adapter for `rand::RngCore` to use `rand` (v0.9) and any
  other conforming random number generators with `V7Generator`.
- `rand08` enables an adapter for `rand::RngCore` to use `rand` (v0.8) and any
  other conforming random number generators with `V7Generator`. Currently, this
  feature is always enabled and cannot be turned off. This behavior is
  deprecated and for backward compatibility only. Enable `rand08` explicitly
  when needed.
- `uuid` (together with `global_gen`) enables the `new_v7()` function that
  returns the popular [uuid](https://crates.io/crates/uuid) crate's `Uuid`
  objects.

## Other functionality

This library also supports the generation of UUID version 4:

```rust
let uuid = uuid7::uuid4();
println!("{}", uuid); // e.g., "2ca4b2ce-6c13-40d4-bccf-37d222820f6f"
```

`V7Generator` provides an interface that allows finer control over the various
aspects of the UUIDv7 generation:

```rust
use uuid7::V7Generator;

let mut g = V7Generator::with_rand09(rand::rng());
let custom_unix_ts_ms = 0x0123_4567_8901u64;
let x = g.generate_or_reset_core(custom_unix_ts_ms, 10_000);
println!("{}", x);

let y = g
    .generate_or_abort_core(custom_unix_ts_ms, 10_000)
    .expect("clock went backwards by more than 10_000 milliseconds");
println!("{}", y);
```

## License

Licensed under the Apache License, Version 2.0.

## See also

- [docs.rs/uuid7](https://docs.rs/uuid7)
- Related project: [Uuid25: 25-digit case-insensitive UUID encoding](https://crates.io/crates/uuid25)
