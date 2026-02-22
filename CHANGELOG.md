# Changelog

## v1.6.0 - unreleased

- Migrated to Edition 2024 and upgraded MSRV from 1.70 to 1.85.
- Implemented `core::error::Error` for `ParseError` in `no_std` environments.
- Updated documentation and examples to reflect API changes in v1.5.0.

## v1.5.0 - 2026-02-21

### New features and improvements

- Customizable time sources: Introduced a generic `TimeSource` trait for
  `V7Generator`, allowing users to provide custom timestamp sources. This
  enhances flexibility, especially for testing or specific environments. The
  default implementation `StdSystemTime` uses `std::time::SystemTime`.
  - A new constructor, `with_rand_and_time_sources()`, is added to specify both
    random number and timestamp sources.
  - The `generate()` and `generate_or_abort()` methods that were gated behind
    `std` are now available in `no_std` where a custom `TimeSource` is provided.
- Generator-level rollback allowance: Added `set_rollback_allowance()` to
  `V7Generator` to configure the maximum allowed timestamp rollback for each
  generator instance. This dictates `generate()` and `generate_or_abort()` as
  well as eliminates the need for the `rollback_allowance` argument of the
  `*_core` variants, which are now superseded by the newly added `*_with_ts`
  variants that leverage the generator-level setting.
- `rand` v0.10 support: Added a new `rand010` feature to support the `rand`
  crate (v0.10).

### API changes and deprecations

- `RandSource` trait: Renamed `Rng` trait to `RandSource` for improved clarity
  and consistency. A deprecated type alias `Rng` is provided for backward
  compatibility.
- Deprecated core generator methods: Deprecated `generate_or_reset_core()` and
  `generate_or_abort_core()` of `V7Generator`. Users should migrate to the new
  `generate_or_reset_with_ts()` and `generate_or_abort_with_ts()` methods.
- Deprecated `rand` v0.8 support: Deprecated `rand08` cargo feature and related
  APIs to encourage migration to newer `rand` versions.

### Maintenance and other changes

- Added `is_nil()` and `is_max()` methods to `Uuid` for convenience in checking
  for the Nil and Max UUIDs.
- Test code refactoring.
- Minor documentation updates.

## v1.4.0 - 2025-11-30

- Adjusted `V7Generator` to accept zero as a valid timestamp

## v1.3.0 - 2025-10-13

- Marked `Uuid::variant()` and `Uuid::version()` as const-compatible
- Added `Eq` and `PartialEq` derives to `generator::with_rand09::Adapter`
- Changed impl `Debug` for `V7Generator` to conceal internal state
- Updated dev dependencies

## v1.2.0 - 2025-10-03

### Added

- `rand09` crate feature to integrate `rand` v0.9
- `rand08` crate feature to explicitly enable `rand` v0.8 integration
- `rust-version = "1.70"` key to Cargo.toml

### Changed

- Internal random number generator used by `global_gen` crate feature from
  `rand` v0.8 to v0.9

### Maintenance

- Updated dev dependencies

## v1.1.0 - 2024-09-07

### Changed

- Internal random number generator interface for `V7Generator` from
  `rand::RngCore` to `generator::Rng` to relax hard dependency on `rand` crate
  - Maintained backward compatibility, though is deprecated, by providing
    blanket implementation of `generator::Rng` for `rand::RngCore`

### Added

- `V7Generator::with_rand08()` to make integration with `rand` explicit
- `generator` module

## v1.0.2 - 2024-09-04

- Minor test case and document updates

## v1.0.1 - 2024-08-17

- Minor refactoring and document fixes

## v1.0.0 - 2024-05-11

- Initial stable release
