// This file is part of the shakmaty-syzygy library.
// Copyright (C) 2017-2019 Niklas Fiekas <niklas.fiekas@backscattering.de>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <http://www.gnu.org/licenses/>.

//! Probe Syzygy endgame tablebases.
//!
//! [Syzygy tables](https://syzygy-tables.info/#syzygy) allow optimal play
//! under the 50-move rule. Tables are available for positions with up to
//! 7 pieces.
//!
//! # Example
//!
//! ```
//! # use std::error::Error;
//! #
//! use shakmaty::{CastlingMode, Chess};
//! use shakmaty::fen::Fen;
//! use shakmaty_syzygy::{Tablebase, Wdl, Dtz, Syzygy};
//!
//! let mut tables = Tablebase::new();
//! tables.add_directory("tables/chess")?;
//!
//! let pos: Chess = "8/8/8/8/B7/N7/K2k4/8 b - - 0 1"
//!     .parse::<Fen>()?
//!     .position(CastlingMode::Standard)?;
//!
//! let wdl = tables.probe_wdl(&pos)?;
//! assert_eq!(wdl, Wdl::Loss);
//!
//! let dtz = tables.probe_dtz(&pos)?;
//! assert_eq!(dtz, Dtz(-59));
//! #
//! # Ok::<_, Box<dyn Error>>(())
//! ```
//!
//! # Errors
//!
//! See [`SyzygyError`] for possible error
//! conditions.
//!
//! # Cargo features
//!
//! * `variant`: Enables support for Antichess and Atomic chess.
//! * `backtrace`: Provides a `backtrace` field on `ProbeError::CorruptedTable`.
//!   This may be useful to identify issues with corrupted tablebase files or
//!   to debug the probing code. Currently requires nightly Rust.

#![doc(html_root_url = "https://docs.rs/shakmaty-syzygy/0.16.1")]

#![forbid(unsafe_code)]
#![warn(missing_debug_implementations)]
#![warn(rust_2018_idioms)]

#![cfg_attr(feature = "backtrace", feature(backtrace))]

#[macro_use]
mod errors;
mod material;
mod table;
mod tablebase;
mod types;

pub use crate::errors::{ProbeError, SyzygyError};
pub use crate::tablebase::Tablebase;
pub use crate::types::{Dtz, Metric, Syzygy, TableType, Wdl};

#[cfg(fuzzing)]
pub use crate::table::{DtzTable, WdlTable};
#[cfg(fuzzing)]
pub use crate::types::DecisiveWdl;
