# Changelog

## Unreleased

### Added

- `Eq` and `PartialEq` derives to `generator::with_rand09::Adapter`

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
