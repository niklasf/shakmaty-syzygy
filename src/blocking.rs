use crate::aio;
use crate::aio::Filesystem;
use crate::aio::RandomAccessFile;
use crate::aio::ReadHint;
use crate::errors::SyzygyResult;
use crate::AmbiguousWdl;
use crate::Dtz;
use crate::MaybeRounded;
use crate::Syzygy;
use crate::Wdl;
use futures_util::future::FutureExt;
use shakmaty::Move;
use shakmaty::Position;
use std::io;
use std::path::Path;
use std::path::PathBuf;

trait BlockingFilesystem: Sync + Send {
    fn regular_file_size_blocking(&self, path: &Path) -> io::Result<u64>;
    fn read_dir_blocking(&self, path: &Path) -> io::Result<Vec<PathBuf>>;
    fn open_blocking(&self, path: &Path) -> io::Result<Box<dyn BlockingRandomAccessFile>>;
}

impl Filesystem for Box<dyn BlockingFilesystem> {
    type RandomAccessFile = Box<dyn BlockingRandomAccessFile>;

    async fn regular_file_size(&self, path: &Path) -> io::Result<u64> {
        self.regular_file_size_blocking(path)
    }

    async fn read_dir(&self, path: &Path) -> io::Result<Vec<PathBuf>> {
        self.read_dir_blocking(path)
    }

    async fn open(&self, path: &Path) -> io::Result<Box<dyn BlockingRandomAccessFile>> {
        self.open_blocking(path)
    }
}

trait BlockingRandomAccessFile: Sync + Send {
    fn read_at_blocking(&self, buf: &mut [u8], offset: u64, hint: ReadHint) -> io::Result<usize>;
}

impl RandomAccessFile for Box<dyn BlockingRandomAccessFile> {
    async fn read_at(&self, buf: &mut [u8], offset: u64, hint: ReadHint) -> io::Result<usize> {
        self.read_at_blocking(buf, offset, hint)
    }
}

pub struct Tablebase<S> {
    inner: aio::Tablebase<S, Box<dyn BlockingFilesystem>>,
}

#[cfg(any(unix, windows))]
impl Default for Tablebase<()> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S> Tablebase<S> {
    #[cfg(any(unix, windows))]
    pub fn new() -> Self {
        Self::with_filesystem(Box::new(os::OsFilesystem::default()))
    }

    fn with_filesystem(filesystem: Box<dyn BlockingFilesystem>) -> Self {
        Self {
            inner: aio::Tablebase::with_filesystem(filesystem),
        }
    }

    #[inline]
    pub fn max_pieces(&self) -> usize {
        self.inner.max_pieces()
    }
}

impl<S: Syzygy> Tablebase<S> {
    pub fn add_directory<P: AsRef<Path>>(&mut self, path: P) -> io::Result<usize> {
        self.inner
            .add_directory(path)
            .now_or_never()
            .expect("blocking impl ready immediately")
    }

    pub fn add_file<P: AsRef<Path>>(&mut self, path: P) -> io::Result<()> {
        self.inner
            .add_file(path)
            .now_or_never()
            .expect("blocking impl ready immediately")
    }
}

impl<S: Syzygy + Position + Clone> Tablebase<S> {
    pub fn probe_wdl_after_zeroing(&self, pos: &S) -> SyzygyResult<Wdl> {
        self.inner
            .probe_wdl_after_zeroing(pos)
            .now_or_never()
            .expect("blocking impl ready immediately")
    }

    pub fn probe_wdl(&self, pos: &S) -> SyzygyResult<AmbiguousWdl> {
        self.inner
            .probe_wdl(pos)
            .now_or_never()
            .expect("blocking impl ready immediately")
    }

    pub fn probe_dtz(&self, pos: &S) -> SyzygyResult<MaybeRounded<Dtz>> {
        self.inner
            .probe_dtz(pos)
            .now_or_never()
            .expect("blocking impl ready immediately")
    }

    pub fn best_move(&self, pos: &S) -> SyzygyResult<Option<(Move, MaybeRounded<Dtz>)>> {
        self.inner
            .best_move(pos)
            .now_or_never()
            .expect("blocking impl ready immediately")
    }
}

#[cfg(any(unix, windows))]
mod os {
    use super::BlockingFilesystem;
    use super::*;
    use std::fs;

    #[derive(Default)]
    pub struct OsFilesystem {
        advise_random: bool,
    }

    impl BlockingFilesystem for OsFilesystem {
        fn regular_file_size_blocking(&self, path: &Path) -> io::Result<u64> {
            regular_file_size_impl(path)
        }

        fn read_dir_blocking(&self, path: &Path) -> io::Result<Vec<PathBuf>> {
            read_dir_impl(path)
        }

        fn open_blocking(&self, path: &Path) -> io::Result<Box<dyn BlockingRandomAccessFile>> {
            let file = fs::File::open(path)?;

            #[cfg(target_os = "linux")]
            if self.advise_random {
                // Safety: No requirements.
                unsafe {
                    libc::posix_fadvise(
                        std::os::unix::io::AsRawFd::as_raw_fd(&file),
                        0,
                        0,
                        libc::POSIX_FADV_RANDOM,
                    );
                }
            }

            Ok(Box::new(OsRandomAccessFile { file }))
        }
    }

    struct OsRandomAccessFile {
        file: fs::File,
    }

    impl BlockingRandomAccessFile for OsRandomAccessFile {
        #[cfg(unix)]
        fn read_at_blocking(
            &self,
            buf: &mut [u8],
            offset: u64,
            _hint: ReadHint,
        ) -> io::Result<usize> {
            std::os::unix::fs::FileExt::read_at(&self.file, buf, offset)
        }
        #[cfg(windows)]
        fn read_at_blocking(
            &self,
            buf: &mut [u8],
            offset: u64,
            _hint: ReadHint,
        ) -> io::Result<usize> {
            std::os::windows::fs::FileExt::seek_read(&self.file, buf, offset)
        }
    }
}

#[cfg(any(unix, windows, all(feature = "mmap", target_pointer_width = "64")))]
fn regular_file_size_impl(path: &Path) -> io::Result<u64> {
    let meta = path.metadata()?;
    if !meta.is_file() {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "not a regular file",
        ));
    }
    Ok(meta.len())
}

#[cfg(any(unix, windows, all(feature = "mmap", target_pointer_width = "64")))]
fn read_dir_impl(path: &Path) -> io::Result<Vec<PathBuf>> {
    std::fs::read_dir(path)?
        .map(|maybe_entry| maybe_entry.map(|entry| entry.path().to_owned()))
        .collect()
}

#[cfg(test)]
mod tests {
    use shakmaty::{fen::Fen, CastlingMode, Chess /* Square */};

    use super::*;

    #[test]
    fn test_send_sync() {
        fn assert_send<T: Send>(_: T) {}
        fn assert_sync<T: Sync>(_: T) {}

        assert_send(Tablebase::<Chess>::new());
        assert_sync(Tablebase::<Chess>::new());
    }

    /* #[test]
    fn test_mating_best_move() {
        let mut tables = Tablebase::new();
        tables
            .add_directory("tables/chess")
            .expect("read directory");

        let pos: Chess = "5BrN/8/8/8/8/2k5/8/2K5 b - -"
            .parse::<Fen>()
            .expect("valid fen")
            .into_position(CastlingMode::Chess960)
            .expect("legal position");

        assert!(matches!(
            tables.best_move(&pos),
            Ok(Some((
                Move::Normal {
                    role: Role::Rook,
                    from: Square::G8,
                    capture: None,
                    to: Square::G1,
                    promotion: None,
                },
                MaybeRounded::Rounded(Dtz(-1))
            )))
        ));
    } */

    /* #[test]
    fn test_black_escapes_via_underpromotion() {
        let mut tables = Tablebase::new();
        tables
            .add_directory("tables/chess")
            .expect("read directory");

        let pos: Chess = "8/6B1/8/8/B7/8/K1pk4/8 b - - 0 1"
            .parse::<Fen>()
            .expect("valid fen")
            .into_position(CastlingMode::Chess960)
            .expect("legal position");

        assert!(matches!(
            tables.best_move(&pos),
            Ok(Some((
                Move::Normal {
                    role: Role::Pawn,
                    from: Square::C2,
                    to: Square::C1,
                    capture: None,
                    promotion: Some(Role::Knight),
                },
                MaybeRounded::Rounded(Dtz(109))
            )))
        ));
    } */

    #[test]
    #[ignore]
    fn test_many_pawns() {
        let mut tables = Tablebase::new();
        tables
            .add_directory("tables/chess")
            .expect("read directory");

        let pos: Chess = "3k4/5P2/8/8/4K3/2P3P1/PP6/8 w - - 0 1"
            .parse::<Fen>()
            .expect("valid fen")
            .into_position(CastlingMode::Chess960)
            .expect("legal position");

        assert!(matches!(
            tables.probe_dtz(&pos),
            Ok(MaybeRounded::Precise(Dtz(1)))
        ));
    }
}
