# tinytable

A tiny text table drawing library for Rust.

[![crates.io](https://img.shields.io/crates/v/tinytable.svg)](https://crates.io/crates/tinytable)
[![Documentation](https://docs.rs/tinytable/badge.svg)](https://docs.rs/tinytable)
[![Continuous Integration](https://github.com/MonterraByte/tinytable/actions/workflows/ci.yml/badge.svg)](https://github.com/MonterraByte/tinytable/actions/workflows/ci.yml)

### Features

* Small code size (it's one function!)
* Minimal dependencies (not zero, because Unicode is hard)
* Iterator support (you don't need to collect all the data to display at once, it can be streamed)
* Unicode support
* Nothing more!

### Usage

Run `cargo add tinytable`, or add `tinytable = "0.1"` to the `[dependencies]` section of your `Cargo.toml`.

After that, call [`tinytable::write_table()`](https://docs.rs/tinytable/0.1/tinytable/fn.write_table.html) in your code.

---

Copyright © 2025 Joaquim Monteiro

### License

Licensed under either of

* Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
