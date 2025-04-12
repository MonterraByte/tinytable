# Changelog

## [0.2.0] - 2025-04-12

### Changed

- **Breaking:** remove the `CellIter` generic parameter from `write_table`
  ([#2](https://github.com/MonterraByte/tinytable/pull/2))
- **Breaking:** move the `I` generic parameter from `write_table` to an `impl Trait` parameter
  ([`32ee1fa`](https://github.com/MonterraByte/tinytable/commit/32ee1fa6690d867c2e169f9a513a07384303b0fa))
- Refactor `write_table` into smaller functions for reusability ([#8](https://github.com/MonterraByte/tinytable/pull/8))

### Added

- Add `write_table` variant that supports custom formatters ([#8](https://github.com/MonterraByte/tinytable/pull/8))
- Add support for [fallible iterators](https://docs.rs/fallible-iterator)
  ([#1](https://github.com/MonterraByte/tinytable/pull/1))

## [0.1.2] - 2025-03-13

### Fixed

- Reduce memory allocations by reusing the `String` that holds the cell value
  ([#6](https://github.com/MonterraByte/tinytable/pull/6))

## [0.1.1] - 2025-03-06

### Changed

- Accept a regular `Iterator` as the iterator over elements in a row, instead of requiring an `ExactSizeIterator`
  ([#3](https://github.com/MonterraByte/tinytable/pull/3))

## [0.1.0] - 2025-03-01

Initial release

[0.2.0]: https://github.com/MonterraByte/tinytable/releases/tag/v0.2.0

[0.1.2]: https://github.com/MonterraByte/tinytable/releases/tag/v0.1.2

[0.1.1]: https://github.com/MonterraByte/tinytable/releases/tag/v0.1.1

[0.1.0]: https://github.com/MonterraByte/tinytable/releases/tag/v0.1.0
