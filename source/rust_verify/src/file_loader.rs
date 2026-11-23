pub use rustc_span::source_map::RealFileLoader;

pub trait FileLoaderClone {
    fn clone(&self) -> Self;
}

impl FileLoaderClone for RealFileLoader {
    fn clone(&self) -> Self {
        rustc_span::source_map::RealFileLoader
    }
}

use rustc_span::source_map::FileLoader;

/// -V alloc-check: a file loader that records what it reads, by path and a hash of the contents it
/// gives (each read: a file can be read more than once, and need not give the same contents), so
/// that what the compilation read can be compared with what the verification read
pub(crate) struct RecordingFileLoader {
    pub(crate) reads: FileReads,
}

/// What a `RecordingFileLoader` read
pub(crate) type FileReads = std::sync::Arc<std::sync::Mutex<Vec<(std::path::PathBuf, Vec<u8>)>>>;

impl RecordingFileLoader {
    fn record(&self, path: &std::path::Path, bytes: &[u8]) {
        let hash = rustc_span::SourceFileHash::new_in_memory(
            rustc_span::SourceFileHashAlgorithm::Sha256,
            bytes,
        );
        self.reads.lock().unwrap().push((path.to_path_buf(), hash.hash_bytes().to_vec()));
    }
}

impl rustc_span::source_map::FileLoader for RecordingFileLoader {
    fn file_exists(&self, path: &std::path::Path) -> bool {
        RealFileLoader.file_exists(path)
    }

    fn read_file(&self, path: &std::path::Path) -> std::io::Result<String> {
        let contents = RealFileLoader.read_file(path)?;
        self.record(path, contents.as_bytes());
        Ok(contents)
    }

    fn read_binary_file(&self, path: &std::path::Path) -> std::io::Result<std::sync::Arc<[u8]>> {
        let contents = RealFileLoader.read_binary_file(path)?;
        self.record(path, &contents);
        Ok(contents)
    }

    fn current_directory(&self) -> std::io::Result<std::path::PathBuf> {
        RealFileLoader.current_directory()
    }
}
