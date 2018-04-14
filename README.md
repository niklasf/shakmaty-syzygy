shakmaty-syzygy
===============

A Rust library to probe Syzygy endgame tablebases, based on [shakmaty](https://github.com/niklasf/shakmaty).

[![Build Status](https://travis-ci.org/niklasf/shakmaty-syzygy.svg?branch=master)](https://travis-ci.org/niklasf/shakmaty-syzygy)
[![crates.io](https://img.shields.io/crates/v/shakmaty-syzygy.svg)](https://crates.io/crates/shakmaty-syzygy)

Syzygy tables allow optimal play under the 50-move rule. Tables are available for positions with up to 6 (and experimentally 7) pieces.

Example
-------

```rust
use shakmaty::Chess;
use shakmaty::fen::Fen;
use shakmaty_syzygy::{Tablebases, Wdl, Dtz, Syzygy};

let mut tables = Tablebases::new();
tables.add_directory("tables/regular")?;

let pos: Chess = "8/8/8/8/B7/N7/K2k4/8 b - - 0 1"
    .parse::<Fen>()?
    .position()?;

let wdl = tables.probe_wdl(&pos)?;
assert_eq!(wdl, Wdl::Loss);

let dtz = tables.probe_dtz(&pos)?;
assert_eq!(dtz, Dtz(-59));
```

Documentation
-------------

[Read the documentation](https://docs.rs/shakmaty-syzygy)

Changelog
---------

* 0.1.2
  - Cosmetic tweak to DTZ in case of mate in 1.
* 0.1.1
  - Optional `serde-1` feature.
  - Add `Dtz.add_plies()`.
* 0.1.0
  - First release.

Acknowledgement
---------------

Thanks to Ronald de Man for his [Syzygy tablebases](https://github.com/syzygy1/tb).
The probing code is closely based on his implementation for Stockfish.

License
-------

shakmaty-syzygy is licensed under the GPL-3.0 (or any later version at your
option). See the COPYING file for the full license text.
