use std::{error::Error, path::PathBuf};

use clap::{builder::PathBufValueParser, Parser};
use shakmaty::Chess;
use shakmaty_syzygy::Tablebase;

#[derive(Debug, Parser)]
struct Opt {
    /// Tablebase diretories
    #[arg(long = "path", value_parser = PathBufValueParser::new())]
    path: Vec<PathBuf>,
}

fn main() -> Result<(), Box<dyn Error>> {
    let opt = Opt::parse();

    let mut tablebase = Tablebase::<Chess>::new();
    for path in opt.path {
        tablebase.add_directory(path)?;
    }

    serde_json::to_writer_pretty(std::io::stdout(), &tablebase.meta()?)?;

    Ok(())
}
