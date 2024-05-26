use serde::Serialize;
use serde_with::{serde_as, DisplayFromStr};
use shakmaty::Color;

use crate::{material::Material, types::Metric};

#[serde_as]
#[derive(Serialize)]
pub struct TableInfo {
    #[serde_as(as = "DisplayFromStr")]
    pub material: Material,
    pub metric: Metric,
    pub files: Vec<FileInfo>,
}

#[derive(Serialize)]
pub struct FileInfo {
    pub sides: Vec<SideInfo>,
}

#[derive(Serialize)]
pub struct SideInfo {
    pub flags: FlagsInfo,
    pub sparse_index: SparseIndexInfo,
    pub block_lengths: BlockLengthsInfo,
    pub blocks: BlocksInfo,
}

#[serde_as]
#[derive(Serialize)]
pub struct FlagsInfo {
    #[serde_as(as = "Option<DisplayFromStr>")]
    #[serde(skip_serializing_if = "Option::is_none")]
    pub side: Option<Color>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub mapped: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub win_plies: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub loss_plies: Option<bool>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub wide_dtz: Option<bool>,
    pub single_value: bool,
}

#[derive(Serialize)]
pub struct SparseIndexInfo {
    pub num: u32,
    pub bytes: u64,
    pub span: u32,
}

#[derive(Serialize)]
pub struct BlockLengthsInfo {
    pub num: u32,
    pub bytes: u64,
}

#[derive(Serialize)]
pub struct BlocksInfo {
    pub num: u32,
    pub bytes: u64,
    pub min_symbol_bits: u8,
}
