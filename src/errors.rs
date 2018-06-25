// This file is part of the shakmaty-syzygy library.
// Copyright (C) 2017-2018 Niklas Fiekas <niklas.fiekas@backscattering.de>
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

use std::io;

use failure::Backtrace;

use material::Material;
use types::Metric;

pub type SyzygyResult<T> = Result<T, SyzygyError>;

pub type ProbeResult<T> = Result<T, ProbeError>;

/// Error when probing tablebase.
#[derive(Debug, Fail)]
pub enum SyzygyError {
    /// Position has castling rights, but Syzygy tables do not contain
    /// positions with castling rights.
    #[fail(display = "syzygy tables do not contain positions with castling rights")]
    Castling,
    /// Position has too many pieces. Syzygy tables only support up to
    /// 6 or 7 pieces.
    #[fail(display = "too many pieces")]
    TooManyPieces,
    /// Missing table.
    #[fail(display = "required {} table not found: {}", metric, material)]
    MissingTable {
        metric: Metric,
        material: Material
    },
    /// Probe failed.
    #[fail(display = "failed to probe {} table {}: {}", metric, material, error)]
    ProbeFailed {
        metric: Metric,
        material: Material,
        #[cause]
        error: ProbeError,
    },
}

/// Error when probing a table.
#[doc(hidden)]
#[derive(Debug, Fail)]
pub enum ProbeError {
    /// I/O error.
    #[fail(display = "i/o error reading table file: {}", error)]
    Read {
        #[cause]
        error: io::Error
    },
    /// Table file has unexpected magic header bytes.
    #[fail(display = "invalid magic header bytes: {:x?}", magic)]
    Magic {
        magic: [u8; 4],
    },
    /// Corrupted table.
    #[fail(display = "corrupted table")]
    CorruptedTable(Backtrace),
}

pub trait ProbeResultExt<T> {
    fn ctx(self, metric: Metric, material: &Material) -> SyzygyResult<T>;
}

impl<T> ProbeResultExt<T> for ProbeResult<T> {
    fn ctx(self, metric: Metric, material: &Material) -> SyzygyResult<T> {
        self.map_err(|error| SyzygyError::ProbeFailed {
            metric,
            material: material.normalized(),
            error,
        })
    }
}

impl From<io::Error> for ProbeError {
    fn from(error: io::Error) -> ProbeError {
        match error.kind() {
            io::ErrorKind::UnexpectedEof => ProbeError::CorruptedTable(Backtrace::new()),
            _ => ProbeError::Read { error },
        }
    }
}

/// Return a `CorruptedTable` error.
macro_rules! throw {
    () => {
        return Err(::errors::ProbeError::CorruptedTable(::failure::Backtrace::new()))
    }
}

/// Unwrap an `Option` or return a `CorruptedTable` error.
macro_rules! u {
    ($e:expr) => {
        match $e {
            Some(ok) => ok,
            None => throw!(),
        }
    }
}

/// Ensure that a condition holds. Otherwise return a `CorruptedTable` error.
macro_rules! ensure {
    ($cond:expr) => {
        if !$cond {
            throw!();
        }
    }
}
