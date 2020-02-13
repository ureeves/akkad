# Akkad

[![Build Status](https://travis-ci.org/ureeves/akkad.svg?branch=master)](https://travis-ci.org/ureeves/akkad)
[![codecov](https://codecov.io/gh/ureeves/akkad/branch/master/graph/badge.svg)](https://codecov.io/gh/ureeves/akkad)

An experimental implementation of a Kademlia node.

## Dependencies

To build this project you'll need a [Rust toolchain](https://www.rust-lang.org/tools/install).
Unfortunately it only builds on nightly.

```sh
rustup toolchain add nightly
```

Make it your default toolchain.

```sh
rustup default nightly
```

## Building

To build the project run:

```sh
cargo build
```

To run the tests use:

```sh
cargo test
```

## License

This project is licensed under the MIT license.
See [license.txt](license.txt) file for the full text.
