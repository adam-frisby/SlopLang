//! Loading a package with its dependencies.
//!
//! A package directory has `src/main.slop` or `src/lib.slop`, and may have a `package.slop`
//! manifest, evaluated for the target (see `Compiler::evaluate_package_manifest_for`). Each
//! dependency it names is fetched from its URL (`file://`, `http://`, or `https://`, the last two
//! through `curl`, or a path relative to the package), checked against the manifest's SHA-256,
//! and unpacked with `tar` into a cache named by that hash, so that it is fetched once. Its
//! modules join the build under its name: its `src/main.slop` is module `tls` for a dependency
//! named `tls`, and its own `root::x` is `tls::x`.

use std::path::{Path, PathBuf};

use crate::lower::{Compiler, EvaluatedDependency};

/// A package ready to compile: its modules and those of its dependencies, and what its
/// manifest says.
#[derive(Debug, Clone)]
pub struct LoadedPackage {
    pub sources: Vec<(String, String)>,
    /// The manifest's name, or the directory's.
    pub name: String,
    pub no_std: bool,
    /// What it and its dependencies link.
    pub system_libs: Vec<String>,
}

/// Where a build is for: the target's OS, architecture, and optimize mode, as a manifest's
/// `Target` names them (`Linux`, `X86_64`, `Debug`).
#[derive(Debug, Clone)]
pub struct BuildFor {
    pub os: String,
    pub arch: String,
    pub optimize: String,
    /// Where fetched dependencies are kept.
    pub cache: PathBuf,
}

/// The default dependency cache: `$SLOP_CACHE`, else `~/.cache/slop`.
pub fn default_cache() -> PathBuf {
    if let Some(dir) = std::env::var_os("SLOP_CACHE") {
        return PathBuf::from(dir);
    }
    let home = std::env::var_os("HOME").map_or_else(std::env::temp_dir, PathBuf::from);
    home.join(".cache").join("slop")
}

/// The package in `dir`, with its dependencies.
pub fn load_package(dir: &Path, build: &BuildFor) -> Result<LoadedPackage, String> {
    let mut seen = Vec::new();
    load_inner(dir, build, &mut seen)
}

fn load_inner(
    dir: &Path,
    build: &BuildFor,
    seen: &mut Vec<(String, [u64; 4])>,
) -> Result<LoadedPackage, String> {
    let mut sources = Compiler::load_package_dir(dir)?;
    let stem = dir.file_name().map_or("a".to_string(), |s| s.to_string_lossy().into_owned());
    let manifest = dir.join("package.slop");
    if !manifest.exists() {
        return Ok(LoadedPackage { sources, name: stem, no_std: false, system_libs: Vec::new() });
    }
    let src = std::fs::read_to_string(&manifest)
        .map_err(|e| format!("cannot read '{}': {e}", manifest.display()))?;
    let pkg = Compiler::evaluate_package_manifest_for(&src, &build.os, &build.arch, &build.optimize)
        .map_err(|e| format!("in '{}': {e}", manifest.display()))?;
    if pkg.root != "src/main.slop" && pkg.root != "src/lib.slop" {
        return Err(format!(
            "package '{}' has root '{}'; slop reads 'src/main.slop' or 'src/lib.slop'",
            pkg.name, pkg.root
        ));
    }
    let mut system_libs = pkg.system_libs.clone();
    for dep in &pkg.deps {
        // A package two others depend on is the same one, or they disagree.
        if let Some((_, hash)) = seen.iter().find(|(n, _)| *n == dep.name) {
            if *hash != dep.sha256 {
                return Err(format!(
                    "two packages depend on '{}' with different SHA-256s; a build has one of each",
                    dep.name
                ));
            }
            continue;
        }
        if matches!(dep.name.as_str(), "root" | "std" | "core") || dep.name.contains("::") {
            return Err(format!("a dependency cannot be named '{}'", dep.name));
        }
        seen.push((dep.name.clone(), dep.sha256));
        let dep_dir = fetch(dep, dir, &build.cache)?;
        let loaded = load_inner(&dep_dir, build, seen)
            .map_err(|e| format!("in dependency '{}': {e}", dep.name))?;
        for (module, text) in loaded.sources {
            // Its root is mounted under its name; its own dependencies are already under theirs.
            let mounted = match module.strip_prefix("root") {
                Some(rest) => format!("{}{rest}", dep.name),
                None => module,
            };
            if !sources.iter().any(|(m, _)| *m == mounted) {
                sources.push((mounted, text));
            }
        }
        for lib in loaded.system_libs {
            if !system_libs.contains(&lib) {
                system_libs.push(lib);
            }
        }
    }
    Ok(LoadedPackage { sources, name: pkg.name, no_std: pkg.no_std, system_libs })
}

/// The SHA-256 a manifest gives (a `u256`, as four words, least significant first), in hex.
pub fn hash_hex(words: [u64; 4]) -> String {
    words.iter().rev().map(|w| format!("{w:016x}")).collect()
}

/// The directory of `dep`, fetched and unpacked into the cache unless it is there already.
fn fetch(dep: &EvaluatedDependency, base: &Path, cache: &Path) -> Result<PathBuf, String> {
    let want = hash_hex(dep.sha256);
    let dest = cache.join(&want);
    if dest.join(".slop-complete").exists() {
        return package_root(&dest, &dep.name);
    }
    let bytes = download(&dep.url, base)?;
    let got = crate::sha256::hex(&crate::sha256::digest(&bytes));
    if got != want {
        return Err(format!(
            "dependency '{}' from '{}' has SHA-256 {got}, but the manifest says {want}",
            dep.name, dep.url
        ));
    }
    let staging = cache.join(format!("{want}.partial-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&staging);
    let unpacked = staging.join("unpacked");
    std::fs::create_dir_all(&unpacked).map_err(|e| format!("cannot make '{}': {e}", unpacked.display()))?;
    let archive = staging.join(dep.url.rsplit('/').next().filter(|f| !f.is_empty()).unwrap_or("archive"));
    std::fs::write(&archive, &bytes).map_err(|e| format!("cannot write '{}': {e}", archive.display()))?;
    let tar = std::process::Command::new("tar")
        .arg("-xf")
        .arg(&archive)
        .arg("-C")
        .arg(&unpacked)
        .output()
        .map_err(|e| format!("cannot run 'tar', which unpacks dependencies: {e}"))?;
    if !tar.status.success() {
        let _ = std::fs::remove_dir_all(&staging);
        return Err(format!(
            "cannot unpack dependency '{}': {}",
            dep.name,
            String::from_utf8_lossy(&tar.stderr).trim()
        ));
    }
    let _ = std::fs::remove_dir_all(&dest);
    std::fs::rename(&unpacked, &dest).map_err(|e| format!("cannot keep '{}': {e}", dest.display()))?;
    std::fs::write(dest.join(".slop-complete"), &dep.url).map_err(|e| format!("cannot finish '{}': {e}", dest.display()))?;
    let _ = std::fs::remove_dir_all(&staging);
    package_root(&dest, &dep.name)
}

/// What `url` names: a `file://` path or a path relative to the depending package, read; an
/// `http://` or `https://` URL, fetched with `curl`.
fn download(url: &str, base: &Path) -> Result<Vec<u8>, String> {
    if url.starts_with("http://") || url.starts_with("https://") {
        let out = std::process::Command::new("curl")
            .args(["-fsSL", url])
            .output()
            .map_err(|e| format!("cannot run 'curl', which fetches '{url}': {e}"))?;
        if !out.status.success() {
            return Err(format!("cannot fetch '{url}': {}", String::from_utf8_lossy(&out.stderr).trim()));
        }
        return Ok(out.stdout);
    }
    let path = Path::new(url.strip_prefix("file://").unwrap_or(url));
    let path = if path.is_absolute() { path.to_path_buf() } else { base.join(path) };
    std::fs::read(&path).map_err(|e| format!("cannot read '{}': {e}", path.display()))
}

/// The package in an unpacked archive: at its top, or in the one directory it holds.
fn package_root(dir: &Path, name: &str) -> Result<PathBuf, String> {
    if dir.join("src").is_dir() {
        return Ok(dir.to_path_buf());
    }
    let entries: Vec<PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("cannot read '{}': {e}", dir.display()))?
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    match entries.as_slice() {
        [one] if one.join("src").is_dir() => Ok(one.clone()),
        _ => Err(format!("dependency '{name}' holds no package (a 'src' directory)")),
    }
}
