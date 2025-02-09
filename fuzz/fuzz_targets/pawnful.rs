#![no_main]

use futures_util::future::FutureExt as _;
use std::{
    io,
    path::{Path, PathBuf},
    rc::Rc,
};

use libfuzzer_sys::fuzz_target;
use shakmaty::{fen::Fen, CastlingMode, Chess};
use shakmaty_syzygy::aio::{Filesystem, RandomAccessFile, ReadHint, Tablebase};

struct FakeFilesystem {
    data: Rc<[u8]>,
}

impl Filesystem for FakeFilesystem {
    type RandomAccessFile = FakeFile;

    async fn regular_file_size(&self, _path: &Path) -> io::Result<u64> {
        Ok(self.data.len() as u64)
    }

    async fn read_dir(&self, _path: &Path) -> io::Result<Vec<PathBuf>> {
        Ok(vec!["KNvKP.rtbw".into()])
    }

    async fn open(&self, _path: &Path) -> io::Result<FakeFile> {
        Ok(FakeFile {
            data: Rc::clone(&self.data),
        })
    }
}

struct FakeFile {
    data: Rc<[u8]>,
}

impl RandomAccessFile for FakeFile {
    async fn read_at(&self, buf: &mut [u8], offset: u64, _hint: ReadHint) -> io::Result<usize> {
        let offset = offset as usize;
        let end = offset + buf.len();
        buf.copy_from_slice(
            self.data
                .get(offset..end)
                .ok_or(io::ErrorKind::UnexpectedEof)?,
        );
        Ok(buf.len())
    }
}

fuzz_target!(|data: &[u8]| {
    let pos: Chess = "8/2K5/8/8/8/8/3p4/1k2N3 b - - 0 1" // KNvKP
        .parse::<Fen>()
        .expect("valid fen")
        .into_position(CastlingMode::Standard)
        .expect("valid position");

    let tables = Tablebase::with_filesystem(FakeFilesystem { data: data.into() });

    let _ = tables
        .probe_wdl(&pos)
        .now_or_never()
        .expect("blocking probe");
});
