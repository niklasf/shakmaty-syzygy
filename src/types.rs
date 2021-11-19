// This file is part of the shakmaty-syzygy library.
// Copyright (C) 2017-2021 Niklas Fiekas <niklas.fiekas@backscattering.de>
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

use std::fmt;
use std::ops::Neg;
use std::convert::TryFrom;

use arrayvec::ArrayVec;

use shakmaty::{Chess, Color, Outcome, Piece};

/// File extension and magic header bytes of Syzygy tables.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TableType {
    /// File extension, e.g. `rtbw`.
    pub ext: &'static str,
    /// Magic header bytes.
    pub magic: [u8; 4],
}

/// A chess variant with Syzygy support.
pub trait Syzygy {
    /// WDL table type.
    const TBW: TableType;
    /// DTZ table type.
    const TBZ: TableType;

    /// Alternative WDL table type for pawnless endgames.
    const PAWNLESS_TBW: Option<TableType> = None;
    /// Alternative DTZ table type for pawnless endgames.
    const PAWNLESS_TBZ: Option<TableType> = None;

    /// Whether both players will have exactly one king unless the game
    /// is over.
    const ONE_KING: bool;
    /// Wether kings are allowed to be on adjacent squares.
    const CONNECTED_KINGS: bool;
    /// Whether captures are compulsory.
    const CAPTURES_COMPULSORY: bool;

    /// Maximum number of supported pieces.
    const MAX_PIECES: usize = 6;
}

impl Syzygy for Chess {
    const TBW: TableType = TableType { ext: "rtbw", magic: [0x71, 0xe8, 0x23, 0x5d] };
    const TBZ: TableType = TableType { ext: "rtbz", magic: [0xd7, 0x66, 0x0c, 0xa5] };

    const ONE_KING: bool = true;
    const CONNECTED_KINGS: bool = false;
    const CAPTURES_COMPULSORY: bool = false;

    const MAX_PIECES: usize = 7;
}

#[cfg(feature = "variant")]
#[cfg_attr(docs_rs, doc(cfg(feature = "variant")))]
impl Syzygy for shakmaty::variant::Atomic {
    const TBW: TableType = TableType { ext: "atbw", magic: [0x55, 0x8d, 0xa4, 0x49] };
    const TBZ: TableType = TableType { ext: "atbz", magic: [0x91, 0xa9, 0x5e, 0xeb] };

    const ONE_KING: bool = true;
    const CONNECTED_KINGS: bool = true;
    const CAPTURES_COMPULSORY: bool = false;
}

#[cfg(feature = "variant")]
#[cfg_attr(docs_rs, doc(cfg(feature = "variant")))]
impl Syzygy for shakmaty::variant::Antichess {
    const TBW: TableType = TableType {
        ext: "gtbw",
        magic: [0xbc, 0x55, 0xbc, 0x21],
    };
    const TBZ: TableType = TableType {
        ext: "gtbz",
        magic: [0xd6, 0xf5, 0x1b, 0x50],
    };

    const PAWNLESS_TBW: Option<TableType> = Some(TableType {
        ext: "stbw",
        magic: [0x7b, 0xf6, 0x93, 0x15],
    });
    const PAWNLESS_TBZ: Option<TableType> = Some(TableType {
        ext: "stbz",
        magic: [0xe4, 0xcf, 0xe7, 0x23],
    });

    const ONE_KING: bool = false;
    const CONNECTED_KINGS: bool = true;
    const CAPTURES_COMPULSORY: bool = true;
}

/// A value that may be affected by DTZ rounding.
///
/// Rounded [`Dtz`] values may be off by one:
///
/// * `MaybeRounded::Rounded(Dtz(-n))` can mean a loss with a forced
///   zeroing move in `n` or `n + 1` plies.
/// * `MaybeRounded::Rounded(Dtz(n))` can mean a win with a forced
///   zeroing move in `n` or `n + 1` plies.
///
/// This implies some primary tablebase lines may waste up to 1 ply.
/// Rounding is never used for endgame phases where wasting a single ply
/// would change the game theoretical outcome.
///
/// But users still need to be careful in positions that are nearly drawn
/// under the 50-move rule! Carelessly wasting 1 more ply by not following
/// the tablebase recommendation, for a total of 2 wasted plies, may change
/// the outcome of the game.
#[derive(Debug, Copy, Clone)]
pub enum MaybeRounded<T> {
    Rounded(T),
    Precise(T),
}

impl<T> MaybeRounded<T> {
    /// Applies a function to the inner value.
    pub fn map<U, F>(self, f: F) -> MaybeRounded<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            MaybeRounded::Rounded(v) => MaybeRounded::Rounded(f(v)),
            MaybeRounded::Precise(v) => MaybeRounded::Precise(f(v)),
        }
    }

    /// Gets the inner value.
    pub fn ignore_rounding(self) -> T {
        match self {
            MaybeRounded::Rounded(v) => v,
            MaybeRounded::Precise(v) => v,
        }
    }

    /// Gets the inner value, or `None` if it was affected by DTZ rounding.
    pub fn precise(self) -> Option<T> {
        match self {
            MaybeRounded::Precise(v) => Some(v),
            _ => None,
        }
    }
}

impl MaybeRounded<Dtz> {
    /// See [`Dtz::is_zero()`].
    pub fn is_zero(self) -> bool {
        self.ignore_rounding().is_zero()
    }

    /// See [`Dtz::signum()`].
    pub fn signum(self) -> i32 {
        self.ignore_rounding().signum()
    }

    /// See [`Dtz::add_plies()`].
    pub fn add_plies(self, plies: u32) -> MaybeRounded<Dtz> {
        self.map(|dtz| dtz.add_plies(plies))
    }

    /// See [`Dtz::add_plies_checked()`].
    pub fn add_plies_checked(self, plies: u32) -> MaybeRounded<Option<Dtz>> {
        self.map(|dtz| dtz.add_plies_checked(plies))
    }

    /// See [`Dtz::add_plies_saturating()`].
    pub fn add_plies_saturating(self, plies: u32) -> MaybeRounded<Dtz> {
        self.map(|dtz| dtz.add_plies_saturating(plies))
    }
}

impl<T: Neg> Neg for MaybeRounded<T> {
    type Output = MaybeRounded<<T as Neg>::Output>;

    fn neg(self) -> Self::Output {
        self.map(|v| -v)
    }
}

/// WDL<sub>50</sub>. 5-valued evaluation of a position in the context of the
/// 50-move drawing rule.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(i32)]
pub enum Wdl {
    /// Unconditional loss.
    Loss = -2,
    /// Loss that can be saved by the 50-move rule.
    BlessedLoss = -1,
    /// Unconditional draw.
    Draw = 0,
    /// Win that can be frustrated by the 50-move rule.
    CursedWin = 1,
    /// Unconditional win.
    Win = 2,
}

impl Wdl {
    /// Converts `outcome` to a `Wdl` from the given point of view.
    pub fn from_outcome(outcome: Outcome, pov: Color) -> Wdl {
        match outcome {
            Outcome::Draw => Wdl::Draw,
            Outcome::Decisive { winner } if winner == pov => Wdl::Win,
            _ => Wdl::Loss,
        }
    }

    /// Converts `dtz` to `Wdl`.
    ///
    /// In general the result would be
    /// [ambiguous for `MaybeRounded::Rounded(Dtz(100))` and
    /// `MaybeRounded::Rounded(Dtz(-100))`](MaybeRounded).
    /// This conversion assumes that such values were given
    /// immediately after a capture or pawn move, in which case
    /// the outcome is an unconditional win or loss.
    ///
    /// Since playing the tablebase mainline preserves the game theoretical
    /// outcome, this method may also be used on `dtz.add_plies(plies)`
    /// if the mainline has been followed for `plies` halfmoves since the last
    /// capture or pawn move.
    pub fn from_dtz_after_zeroing(dtz: MaybeRounded<Dtz>) -> Wdl {
        Wdl::from_dtz(dtz.ignore_rounding())
    }

    /// Converts `dtz` to `Wdl`.
    ///
    /// # Examples
    ///
    /// ```
    /// use shakmaty_syzygy::{Dtz, Wdl};
    ///
    /// assert_eq!(Wdl::from_dtz(Dtz(98).add_plies(3)), Wdl::CursedWin);
    /// ```
    pub fn from_dtz(dtz: Dtz) -> Wdl {
        match dtz {
            Dtz(n) if n < -100 => Wdl::BlessedLoss,
            Dtz(n) if n < 0 => Wdl::Loss,
            Dtz(0) => Wdl::Draw,
            Dtz(n) if n <= 100 => Wdl::Win,
            Dtz(_) => Wdl::CursedWin,
        }
    }

    pub(crate) fn decisive(self) -> Option<DecisiveWdl> {
        Some(match self {
            Wdl::Loss => DecisiveWdl::Loss,
            Wdl::BlessedLoss => DecisiveWdl::BlessedLoss,
            Wdl::Draw => return None,
            Wdl::CursedWin => DecisiveWdl::CursedWin,
            Wdl::Win => DecisiveWdl::Win,
        })
    }

    /// Returns a number representing the sign of `self`.
    ///
    /// * `1` if `self > Wdl::Draw`
    /// * `0` if `self == Wdl::Draw`
    /// * `-1` if `self < Wdl::Draw`
    pub fn signum(self) -> i32 {
        i32::from(self).signum()
    }
}

impl Neg for Wdl {
    type Output = Wdl;

    fn neg(self) -> Wdl {
        match self {
            Wdl::Loss => Wdl::Win,
            Wdl::BlessedLoss => Wdl::CursedWin,
            Wdl::Draw => Wdl::Draw,
            Wdl::CursedWin => Wdl::BlessedLoss,
            Wdl::Win => Wdl::Loss,
        }
    }
}

impl From<DecisiveWdl> for Wdl {
    fn from(wdl: DecisiveWdl) -> Wdl {
        match wdl {
            DecisiveWdl::Loss => Wdl::Loss,
            DecisiveWdl::BlessedLoss => Wdl::BlessedLoss,
            DecisiveWdl::CursedWin => Wdl::CursedWin,
            DecisiveWdl::Win => Wdl::Win,
        }
    }
}

macro_rules! from_wdl_impl {
    ($wdl:ty, $($t:ty)+) => {
        $(impl From<$wdl> for $t {
            #[inline]
            fn from(wdl: $wdl) -> $t {
                wdl as $t
            }
        })+
    }
}

from_wdl_impl! { Wdl, i8 i16 i32 i64 i128 isize }

/// 4-valued evaluation of a decisive (not drawn) position in the context of
/// the 50-move rule.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
#[repr(i32)]
pub enum DecisiveWdl {
    /// Unconditional loss for the side to move.
    Loss = -2,
    /// Loss that can be saved by the 50-move rule.
    BlessedLoss = -1,
    /// Win that can be frustrated by the 50-move rule.
    CursedWin = 1,
    /// Unconditional win.
    Win = 2,
}

impl DecisiveWdl {
    pub fn signum(self) -> i32 {
        i32::from(self).signum()
    }
}

impl Neg for DecisiveWdl {
    type Output = DecisiveWdl;

    fn neg(self) -> DecisiveWdl {
        match self {
            DecisiveWdl::Loss => DecisiveWdl::Win,
            DecisiveWdl::BlessedLoss => DecisiveWdl::CursedWin,
            DecisiveWdl::CursedWin => DecisiveWdl::BlessedLoss,
            DecisiveWdl::Win => DecisiveWdl::Loss,
        }
    }
}

from_wdl_impl! { DecisiveWdl, i8 i16 i32 i64 i128 isize }

/// WDL<sub>50</sub> with [ambiguity due to DTZ rounding](MaybeRounded).
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum AmbiguousWdl {
    /// Unconditional loss.
    Loss,
    /// Loss that can maybe be saved by the 50-move rule.
    MaybeLoss,
    /// Loss that can be saved by the 50-move rule.
    BlessedLoss,
    /// Unconditional draw.
    Draw,
    /// Win that can be frustrated by the 50-move rule.
    CursedWin,
    /// Win that can maybe be frustrated by the 50-move rule.
    MaybeWin,
    /// Unconditional win.
    Win,
}

impl AmbiguousWdl {
    /// See [`Wdl::signum()`].
    pub fn signum(self) -> i32 {
        match self {
            AmbiguousWdl::Loss | AmbiguousWdl::MaybeLoss | AmbiguousWdl::BlessedLoss => -1,
            AmbiguousWdl::Draw => 0,
            _ => 1,
        }
    }

    pub fn from_dtz(dtz: MaybeRounded<Dtz>) -> AmbiguousWdl {
        match dtz {
            MaybeRounded::Rounded(Dtz(100)) => AmbiguousWdl::MaybeWin,
            MaybeRounded::Rounded(Dtz(-100)) => AmbiguousWdl::MaybeLoss,
            MaybeRounded::Precise(dtz) | MaybeRounded::Rounded(dtz) => Wdl::from_dtz(dtz).into(),
        }
    }

    pub fn from_dtz_after_plies(dtz: MaybeRounded<Dtz>, plies: u32) -> AmbiguousWdl {
        AmbiguousWdl::from_dtz(dtz.add_plies_saturating(plies))
    }

    pub fn after_zeroing(self) -> Wdl {
        match self {
            AmbiguousWdl::Loss | AmbiguousWdl::MaybeLoss => Wdl::Loss,
            AmbiguousWdl::BlessedLoss => Wdl::BlessedLoss,
            AmbiguousWdl::Draw => Wdl::Draw,
            AmbiguousWdl::CursedWin => Wdl::CursedWin,
            AmbiguousWdl::MaybeWin | AmbiguousWdl::Win => Wdl::Win,
        }
    }

    pub fn is_ambiguous(self) -> bool {
        matches!(self, AmbiguousWdl::MaybeWin | AmbiguousWdl::MaybeLoss)
    }

    pub fn is_unambiguous(self) -> bool {
        !self.is_ambiguous()
    }

    pub fn unambiguous(self) -> Option<Wdl> {
        self.is_unambiguous().then(|| AmbiguousWdl::after_zeroing(self))
    }
}

impl Neg for AmbiguousWdl {
    type Output = AmbiguousWdl;

    fn neg(self) -> AmbiguousWdl {
        match self {
            AmbiguousWdl::Loss => AmbiguousWdl::Win,
            AmbiguousWdl::MaybeLoss => AmbiguousWdl::MaybeWin,
            AmbiguousWdl::BlessedLoss => AmbiguousWdl::CursedWin,
            AmbiguousWdl::Draw => AmbiguousWdl::Draw,
            AmbiguousWdl::CursedWin => AmbiguousWdl::BlessedLoss,
            AmbiguousWdl::MaybeWin => AmbiguousWdl::MaybeLoss,
            AmbiguousWdl::Win => AmbiguousWdl::Loss,
        }
    }
}

impl From<Wdl> for AmbiguousWdl {
    fn from(wdl: Wdl) -> AmbiguousWdl {
        match wdl {
            Wdl::Loss => AmbiguousWdl::Loss,
            Wdl::BlessedLoss => AmbiguousWdl::BlessedLoss,
            Wdl::Draw => AmbiguousWdl::Draw,
            Wdl::CursedWin => AmbiguousWdl::CursedWin,
            Wdl::Win => AmbiguousWdl::Win,
        }
    }
}

/// DTZ<sub>50</sub>′′. Based on the distance to zeroing of the
/// half-move clock.
///
/// Zeroing the half-move clock while keeping the game theoretical result in
/// hand guarantees making progress, so min-maxing `Dtz` values guarantees
/// achieving the optimal outcome under the 50-move rule.
///
/// | DTZ | WDL | |
/// | --- | --- | --- |
/// | `-100 <= n <= -1` | Loss | Unconditional loss (assuming the 50-move counter is zero). Zeroing move can be forced in `-n` plies. |
/// | `n < -100` | Blessed loss | Loss, but draw under the 50-move rule. A zeroing move can be forced in `-n` plies or `-n - 100` plies (if a later phase is responsible for the blessing). |
/// | 0 | Draw | |
/// | `100 < n` | Cursed win | Win, but draw under the 50-move rule. A zeroing move can be forced in `n` or `n - 100` plies (if a later phase is responsible for the curse). |
/// | `1 <= n <= 100` | Win | Unconditional win (assuming the 50-move counter is zero). Zeroing move can be forced in `n` plies. |
#[derive(Debug, Copy, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct Dtz(pub i32);

impl Dtz {
    /// Converts `wdl` to a `Dtz`, given that the best move is zeroing.
    ///
    /// | WDL | DTZ |
    /// | --- | --- |
    /// | Loss | -1 |
    /// | Blessed loss | -101 |
    /// | Draw | 0 |
    /// | Cursed win | 101 |
    /// | Win | 1 |
    pub fn before_zeroing(wdl: Wdl) -> Dtz {
        match wdl {
            Wdl::Loss => Dtz(-1),
            Wdl::BlessedLoss => Dtz(-101),
            Wdl::Draw => Dtz(0),
            Wdl::CursedWin => Dtz(101),
            Wdl::Win => Dtz(1),
        }
    }

    /// Increases the absolute non-zero value by `plies`.
    ///
    /// # Panics
    ///
    /// Panics if overflow occurrs.
    ///
    /// # Examples
    ///
    /// ```
    /// use shakmaty_syzygy::Dtz;
    ///
    /// assert_eq!(Dtz(1).add_plies(3), Dtz(4));
    /// assert_eq!(Dtz(0).add_plies(3), Dtz(0));
    /// assert_eq!(Dtz(-1).add_plies(3), Dtz(-4));
    /// ```
    #[must_use]
    pub fn add_plies(self, plies: u32) -> Dtz {
        self.add_plies_checked(plies).expect("dtz overflow")
    }

    /// Increases the absolute non-zero value by `plies`, returning `None`
    /// if overflow occurred.
    #[must_use]
    pub fn add_plies_checked(self, plies: u32) -> Option<Dtz> {
        match self {
            Dtz(0) => Some(Dtz(0)),
            Dtz(n) if n > 0 => i32::try_from(plies).ok().and_then(|plies| n.checked_add(plies)).map(Dtz),
            Dtz(n) => i32::try_from(plies).ok().and_then(|plies| n.checked_sub(plies)).map(Dtz),
        }
    }

    /// Increases the absolute non-zero value by `plies`, saturating if
    /// overflow occurred.
    #[must_use]
    pub fn add_plies_saturating(self, plies: u32) -> Dtz {
        match self {
            Dtz(0) => Dtz(0),
            Dtz(n) if n > 0 => i32::try_from(plies).ok().and_then(|plies| n.checked_add(plies)).map_or(Dtz(i32::MAX), Dtz),
            Dtz(n) => i32::try_from(plies).ok().and_then(|plies| n.checked_sub(plies)).map_or(Dtz(i32::MIN), Dtz),
        }
    }

    /// Returns a number representing the sign of `self`.
    ///
    /// * `1` if `self > Dtz(0)`
    /// * `0` if `self == Dtz(0)`
    /// * `-1` if `self < Dtz(0)`
    pub fn signum(self) -> i32 {
        self.0.signum()
    }

    /// Returns `self == Dtz(0)`.
    pub fn is_zero(self) -> bool {
        self.0 == 0
    }
}

macro_rules! from_dtz_impl {
    ($($t:ty)+) => {
        $(impl From<Dtz> for $t {
            #[inline]
            fn from(wdl: Dtz) -> $t {
                wdl.0.into()
            }
        })+
    }
}

from_dtz_impl! { i32 i64 i128 }

macro_rules! dtz_from_impl {
    ($($t:ty)+) => {
        $(impl From<$t> for Dtz {
            #[inline]
            fn from(dtz: $t) -> Dtz {
                Dtz(i32::from(dtz))
            }
        })+
    }
}

dtz_from_impl! { u8 i8 u16 i16 i32 }

impl Neg for Dtz {
    type Output = Dtz;

    #[inline]
    fn neg(self) -> Dtz {
        Dtz(-self.0)
    }
}

/// Syzygy tables are available for up to 7 pieces.
pub const MAX_PIECES: usize = 7;

/// List of up to `MAX_PIECES` pieces.
pub type Pieces = ArrayVec<Piece, MAX_PIECES>;

/// Metric stored in a table: WDL or DTZ.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Metric {
    /// WDL<sub>50</sub>.
    Wdl,
    /// DTZ<sub>50</sub>′′, potentially [with rounding](MaybeRounded).
    Dtz,
}

impl fmt::Display for Metric {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match *self {
            Metric::Wdl => "wdl",
            Metric::Dtz => "dtz",
        })
    }
}
