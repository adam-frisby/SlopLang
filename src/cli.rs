//! The `slop` command: `slop run <path>`, `slop test <path>`, `slop check <path>`, `slop fmt <path>`, and
//! `slop build <path>`.
//!
//! A path is a `.slop` file, compiled as the root module, or a package directory (with
//! `src/main.slop` or `src/lib.slop`; see `Compiler::load_package_dir`), whose `package.slop`
//! manifest, if it has one, is evaluated for the host: its name names what `build` makes, its
//! `no_std` compiles it freestanding, its system libraries are linked, and its dependencies are
//! fetched (see `packages`); `slop fetch` fetches them and writes the package's lock. `run`
//! builds the program natively and runs it; `run --vm` and `test` run it under the VM instead,
//! with every check it has, so a program that leaks or has undefined behaviour fails;
//! `test --native` runs each test natively as well, and `build` makes an executable.
//! `check` compiles what `test` and `build` would, tests included, and runs nothing, so it works
//! on a library too. Every command prints the compiler's warnings.

use std::io::Write;

use crate::lower::Compiler;
use crate::testing::{self, TestOptions};
use crate::vm::{Value, Vm};

const USAGE: &str = "usage: slop new <dir>
       slop run <path> [--vm]
       slop fetch <dir>
       slop test <path> [--filter TEXT] [--jobs N] [--native]
       slop check <path> [--all-targets]
       slop fmt <path> [--check]
       slop build <path> [-o OUT] [--emit exe|ll|h] [-O0|-O1|-O2|-O3]

<path> is a .slop file or a package directory.";

/// The exit status when the program could not be compiled or run to the end.
pub const FAILED: i32 = 101;

/// Runs `slop` with `args` (without the program name), writing to `out` and `err`; returns the
/// exit status.
pub fn main_with(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> i32 {
    let result = match args.first().map(String::as_str) {
        Some("run") => run(&args[1..], out, err),
        Some("test") => test(&args[1..], out, err),
        Some("check") => check(&args[1..], out, err),
        Some("fmt") => fmt(&args[1..], out),
        Some("build") => build(&args[1..], out, err),
        Some("new") => new_package(&args[1..], out),
        Some("fetch") => fetch(&args[1..], out),
        Some("help" | "--help" | "-h") => {
            let _ = writeln!(out, "{USAGE}");
            Ok(0)
        }
        _ => Err(USAGE.to_string()),
    };
    match result {
        Ok(code) => code,
        Err(e) => {
            let _ = writeln!(err, "error: {e}");
            FAILED
        }
    }
}

/// A package to compile: its modules, and what its manifest says.
pub(crate) struct Package {
    pub(crate) sources: Vec<(String, String)>,
    /// The manifest's name, or the file's or directory's.
    pub(crate) name: String,
    pub(crate) no_std: bool,
    pub(crate) system_libs: Vec<String>,
}

impl Package {
    fn refs(&self) -> Vec<(&str, &str)> {
        self.sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect()
    }

    /// The compiled package, its warnings written to `err`.
    fn compile(&self, err: &mut dyn Write) -> Result<crate::ir::Program, String> {
        let (program, warnings) = Compiler::compile_package_with_warnings_in(&self.refs(), self.no_std)?;
        warn(err, &warnings);
        Ok(program)
    }
}

fn warn(err: &mut dyn Write, warnings: &[String]) {
    for w in warnings {
        let _ = writeln!(err, "warning: {w}");
    }
}

/// The host, as a manifest's `Target` names it.
fn host_target() -> Result<(&'static str, &'static str), String> {
    let os = match std::env::consts::OS {
        "linux" => "Linux",
        "macos" => "MacOs",
        "windows" => "Windows",
        "freebsd" => "FreeBsd",
        other => return Err(format!("no manifest target for the host's OS, '{other}'")),
    };
    let arch = match std::env::consts::ARCH {
        "x86_64" => "X86_64",
        "aarch64" => "Aarch64",
        "riscv64" => "Riscv64",
        other => return Err(format!("no manifest target for the host's architecture, '{other}'")),
    };
    Ok((os, arch))
}

/// A build for the host in `optimize` mode, with the default cache.
fn host_build(optimize: &str) -> Result<crate::packages::BuildFor, String> {
    let (os, arch) = host_target()?;
    Ok(crate::packages::BuildFor {
        os: os.to_string(),
        arch: arch.to_string(),
        optimize: optimize.to_string(),
        cache: crate::packages::default_cache(),
    })
}

/// Fetches the dependencies of the package in a directory, for every target, and writes its
/// lock.
fn fetch(args: &[String], out: &mut dyn Write) -> Result<i32, String> {
    let [dir] = args else {
        return Err(USAGE.to_string());
    };
    let p = std::path::Path::new(dir);
    if !p.is_dir() {
        return Err(format!("'{dir}' is not a package directory"));
    }
    let targets = crate::packages::all_targets(&crate::packages::default_cache());
    let fetched = crate::packages::fetch_package(p, &targets)?;
    for d in &fetched.deps {
        let _ = writeln!(out, "fetched {} {}", d.name, d.sha256);
    }
    if fetched.refused > 0 {
        let _ = writeln!(out, "{} of {} targets are ones the manifest does not build for", fetched.refused, targets.len());
    }
    let _ = writeln!(out, "wrote {}", fetched.lock.display());
    Ok(0)
}

/// The package at `path`, its manifest evaluated for the host in `optimize` mode.
pub(crate) fn load(path: &str, optimize: &str) -> Result<Package, String> {
    load_with(std::path::Path::new(path), &host_build(optimize)?)
}

/// The package at `path` with its manifest evaluated for `build`; `None` if the manifest
/// refuses that target.
fn load_for(path: &str, build: &crate::packages::BuildFor) -> Result<Option<Package>, String> {
    let p = std::path::Path::new(path);
    let manifest = p.join("package.slop");
    if p.is_dir() && manifest.is_file() {
        let src = std::fs::read_to_string(&manifest).map_err(|e| format!("cannot read '{}': {e}", manifest.display()))?;
        if Compiler::evaluate_package_manifest_for(&src, &build.os, &build.arch, &build.optimize).is_err() {
            return Ok(None);
        }
    }
    load_with(p, build).map(Some)
}

fn load_with(p: &std::path::Path, build: &crate::packages::BuildFor) -> Result<Package, String> {
    let path = p.to_string_lossy();
    let stem = p.file_stem().map_or("a".to_string(), |s| s.to_string_lossy().into_owned());
    if !p.is_dir() {
        let src = std::fs::read_to_string(p).map_err(|e| format!("cannot read '{path}': {e}"))?;
        return Ok(Package { sources: vec![("root".to_string(), src)], name: stem, no_std: false, system_libs: Vec::new() });
    }
    let pkg = crate::packages::load_package(p, build)?;
    Ok(Package { sources: pkg.sources, name: pkg.name, no_std: pkg.no_std, system_libs: pkg.system_libs })
}

/// Runs `main`, writing what it wrote; the status is what `main` returned, as a process's is.
fn run(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    let (path, vm) = match args {
        [path] => (path, false),
        [path, flag] | [flag, path] if flag == "--vm" => (path, true),
        _ => return Err(USAGE.to_string()),
    };
    if vm {
        return run_in_vm(path, out, err);
    }
    let package = load(path, "Debug")?;
    let program = package.compile(err)?;
    if !program.functions.iter().any(|f| f.export.as_deref() == Some("main")) {
        return Err("the package has no 'main'".to_string());
    }
    let ir = crate::llvm::LlvmLowering::lower(&program)?;
    let dir = std::env::temp_dir().join(format!("slop_run_{}_{}", std::process::id(), unique()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot make '{}': {e}", dir.display()))?;
    let exe = dir.join(&package.name);
    let ran = link_executable(&ir, "-O0", &package.system_libs, &exe).and_then(|()| run_executable(&exe, out, err));
    let _ = std::fs::remove_dir_all(&dir);
    ran
}

/// Runs `exe` with the terminal's stdin, passing on what it writes as it writes it; the
/// status is its exit code, or 101 when a signal ended it (a failed check traps).
fn run_executable(exe: &std::path::Path, out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    use std::io::Read;
    let mut child = std::process::Command::new(exe)
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run '{}': {e}", exe.display()))?;
    // Both streams are read at once, so a program filling one cannot stall on the other.
    let (send, receive) = std::sync::mpsc::channel::<(bool, Vec<u8>)>();
    let readers: Vec<_> = [
        (false, Box::new(child.stdout.take().expect("piped")) as Box<dyn Read + Send>),
        (true, Box::new(child.stderr.take().expect("piped"))),
    ]
    .into_iter()
    .map(|(is_err, mut stream)| {
        let send = send.clone();
        std::thread::spawn(move || {
            let mut buf = [0u8; 8192];
            while let Ok(n) = stream.read(&mut buf) {
                if n == 0 || send.send((is_err, buf[..n].to_vec())).is_err() {
                    break;
                }
            }
        })
    })
    .collect();
    drop(send);
    for (is_err, bytes) in receive {
        let w: &mut dyn Write = if is_err { &mut *err } else { &mut *out };
        let _ = w.write_all(&bytes);
        let _ = w.flush();
    }
    for r in readers {
        let _ = r.join();
    }
    let status = child.wait().map_err(|e| format!("cannot wait for the program: {e}"))?;
    if let Some(code) = status.code() {
        return Ok(code);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            let what = match signal {
                4 | 5 => "trapped: a check failed, such as an index out of bounds, an overflow, or an '@assert' ('slop run --vm' runs it with the VM's checks)".to_string(),
                11 => "crashed (signal 11, a segmentation fault)".to_string(),
                n => format!("was ended by signal {n}"),
            };
            let _ = writeln!(err, "error: the program {what}");
        }
    }
    Ok(FAILED)
}

/// Runs `main` under the VM, with every check it has; the status is what `main` returned.
fn run_in_vm(path: &str, out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    let mut program = load(path, "Debug")?.compile(err)?;
    let main = program
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .map(|f| f.id)
        .ok_or("the package has no 'main'")?;
    let mut vm = Vm::new(&mut program);
    vm.set_max_steps(usize::MAX);
    vm.check_aliasing();
    vm.allow_io();
    vm.limit_stack(8 << 20);
    // What the program writes goes out as it is written, each to its own stream, so a long
    // run (a server, say) shows its progress; the VM's own reports follow it.
    {
        let (out, err) = (&mut *out, &mut *err);
        vm.stream_output(move |fd, bytes| {
            let w: &mut dyn Write = if fd == 2 { &mut *err } else { &mut *out };
            let _ = w.write_all(bytes);
            let _ = w.flush();
        });
    }
    let ran = vm.eval_call(main, Vec::new());
    let leaks = vm.live_allocations();
    drop(vm);
    let value = ran?;
    if leaks > 0 {
        let _ = writeln!(err, "error: {leaks} heap block(s) leaked");
        return Ok(FAILED);
    }
    match value {
        Value::Int(n) => Ok((n & 0xff) as i32),
        _ => Ok(0),
    }
}

/// Runs the package's tests and reports them; the status is 1 if any failed.
fn test(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    let mut path = None;
    let mut options = TestOptions {
        filter: None,
        jobs: std::thread::available_parallelism().map_or(1, |n| n.get()),
        no_std: false,
    };
    let mut native = false;
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "--native" => native = true,
            "--filter" => options.filter = Some(rest.next().ok_or("'--filter' needs a value")?.clone()),
            "--jobs" => {
                let n = rest.next().ok_or("'--jobs' needs a value")?;
                options.jobs = n.parse().map_err(|_| format!("'--jobs {n}' is not a count"))?;
            }
            p if path.is_none() && !p.starts_with("--") => path = Some(p.to_string()),
            other => return Err(format!("unexpected '{other}'\n{USAGE}")),
        }
    }
    let path = path.ok_or(USAGE)?;
    let package = load(&path, "Debug")?;
    options.no_std = package.no_std;
    let refs = package.refs();
    let (mut outcomes, warnings) = testing::run_tests_warned(&refs, &options)?;
    warn(err, &warnings);
    if native {
        // What passed under the VM runs natively too, which must agree.
        let per_thread = outcomes.len().div_ceil(options.jobs.max(1)).max(1);
        std::thread::scope(|scope| {
            for chunk in outcomes.chunks_mut(per_thread) {
                let refs = &refs;
                scope.spawn(move || {
                    for o in chunk.iter_mut().filter(|o| o.result.is_ok()) {
                        o.result = testing::run_native_in(refs, o.index, package.no_std);
                    }
                });
            }
        });
    }
    let _ = write!(out, "{}", testing::report(&outcomes));
    Ok(if outcomes.iter().all(|o| o.result.is_ok()) { 0 } else { 1 })
}

/// Compiles the package, tests included, and its LLVM IR, running nothing and writing nothing:
/// what `test` and `build` would refuse, `check` refuses.
fn check(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    let (path, all_targets) = match args {
        [path] => (path, false),
        [path, flag] | [flag, path] if flag == "--all-targets" => (path, true),
        _ => return Err(USAGE.to_string()),
    };
    if all_targets {
        return check_all_targets(path, out, err);
    }
    let package = load(path, "Debug")?;
    let (program, warnings, tests) = Compiler::check_package(&package.refs(), package.no_std)?;
    warn(err, &warnings);
    // What only the native backend refuses (such as fibers on a target it cannot switch on).
    crate::llvm::LlvmLowering::lower(&program)?;
    let tests = match tests {
        1 => "1 test".to_string(),
        n => format!("{n} tests"),
    };
    let _ = writeln!(out, "checked {} ({tests})", package.name);
    Ok(0)
}

/// `check` for each C ABI the backend knows, with the manifest evaluated for an OS and
/// architecture that has it: what only some targets refuse (fibers off x86-64, say) shows
/// without a machine of each kind.
fn check_all_targets(path: &str, out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    use crate::c_abi::Target;
    let targets = [
        ("x86_64-linux", "Linux", "X86_64", Target::X86_64),
        ("aarch64-linux", "Linux", "Aarch64", Target::Aarch64 { apple: false }),
        ("aarch64-macos", "MacOs", "Aarch64", Target::Aarch64 { apple: true }),
        ("riscv64-linux", "Linux", "Riscv64", Target::Other),
    ];
    let (mut checked, mut failed, mut skipped) = (Vec::new(), 0, Vec::new());
    let mut name = None;
    let mut tests = 0;
    for (label, os, arch, target) in targets {
        let build = crate::packages::BuildFor {
            os: os.to_string(),
            arch: arch.to_string(),
            optimize: "Debug".to_string(),
            cache: crate::packages::default_cache(),
        };
        let Some(package) = load_for(path, &build)? else {
            skipped.push(label);
            continue;
        };
        name.get_or_insert(package.name.clone());
        let result = Compiler::check_package(&package.refs(), package.no_std).and_then(|(program, warnings, n)| {
            if checked.is_empty() && failed == 0 {
                warn(err, &warnings);
            }
            tests = n;
            crate::llvm::LlvmLowering::lower_for_target(&program, target).map(|_| ())
        });
        match result {
            Ok(()) => checked.push(label),
            Err(e) => {
                failed += 1;
                let _ = writeln!(err, "error: for {label}: {e}");
            }
        }
    }
    let name = name.ok_or("the manifest accepts none of the targets checked")?;
    let tests = if tests == 1 { "1 test".to_string() } else { format!("{tests} tests") };
    if !checked.is_empty() {
        let _ = writeln!(out, "checked {name} ({tests}) for {}", checked.join(", "));
    }
    if !skipped.is_empty() {
        let _ = writeln!(out, "not built for {}", skipped.join(", "));
    }
    Ok(if failed > 0 { FAILED } else { 0 })
}

/// Lays out the file, or a package's `package.slop` and every `.slop` file under its `src` (or
/// under a directory that is not a package),
/// rewriting what changes; with `--check`, only lists what would change, with status 1 if any.
fn fmt(args: &[String], out: &mut dyn Write) -> Result<i32, String> {
    let (mut path, mut check) = (None, false);
    for a in args {
        match a.as_str() {
            "--check" => check = true,
            p if path.is_none() && !p.starts_with("--") => path = Some(p.to_string()),
            other => return Err(format!("unexpected '{other}'\n{USAGE}")),
        }
    }
    let path = std::path::PathBuf::from(path.ok_or(USAGE)?);
    let mut files = Vec::new();
    if path.is_dir() {
        let manifest = path.join("package.slop");
        if manifest.is_file() {
            files.push(manifest);
        }
        // A package's sources, or, in any other directory, every `.slop` file under it.
        let src = path.join("src");
        slop_files(if src.is_dir() { &src } else { &path }, &mut files)?;
    } else {
        files.push(path);
    }
    let mut changed = 0;
    for file in &files {
        let src = std::fs::read_to_string(file).map_err(|e| format!("cannot read '{}': {e}", file.display()))?;
        let formatted = crate::fmt::format_checked(&src).map_err(|e| format!("{}: {e}", file.display()))?;
        if formatted == src {
            continue;
        }
        changed += 1;
        if check {
            let _ = writeln!(out, "would format {}", file.display());
        } else {
            std::fs::write(file, formatted).map_err(|e| format!("cannot write '{}': {e}", file.display()))?;
            let _ = writeln!(out, "formatted {}", file.display());
        }
    }
    Ok(if check && changed > 0 { 1 } else { 0 })
}

/// The `.slop` files under `dir`, in name order, recursively.
fn slop_files(dir: &std::path::Path, files: &mut Vec<std::path::PathBuf>) -> Result<(), String> {
    let mut entries: Vec<std::path::PathBuf> = std::fs::read_dir(dir)
        .map_err(|e| format!("cannot read '{}': {e}", dir.display()))?
        .filter_map(|e| e.ok().map(|e| e.path()))
        .collect();
    entries.sort();
    for p in entries {
        if p.is_dir() {
            slop_files(&p, files)?;
        } else if p.extension().is_some_and(|e| e == "slop") {
            files.push(p);
        }
    }
    Ok(())
}

/// Compiles the package to LLVM IR (`--emit ll`) or, with `clang`, to an executable.
fn build(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    let (mut path, mut output, mut emit, mut opt) = (None, None, "exe".to_string(), "-O2".to_string());
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "-o" => output = Some(rest.next().ok_or("'-o' needs a file")?.clone()),
            "--emit" => {
                emit = rest.next().ok_or("'--emit' needs 'exe', 'll', or 'h'")?.clone();
                if !matches!(emit.as_str(), "exe" | "ll" | "h") {
                    return Err(format!("'--emit {emit}': expected 'exe', 'll', or 'h'"));
                }
            }
            "-O0" | "-O1" | "-O2" | "-O3" => opt = a.clone(),
            p if path.is_none() && !p.starts_with('-') => path = Some(p.to_string()),
            other => return Err(format!("unexpected '{other}'\n{USAGE}")),
        }
    }
    let path = path.ok_or(USAGE)?;
    // The manifest sees the build's mode: `-O0` is a debug build, `-O3` a fast one.
    let optimize = match opt.as_str() {
        "-O0" => "Debug",
        "-O3" => "ReleaseFast",
        _ => "ReleaseSafe",
    };
    let package = load(&path, optimize)?;
    // Named after the package: `examples/ledger` builds `ledger`, `wordcount.slop` `wordcount`.
    let stem = package.name.clone();
    if emit == "h" {
        // The declarations C needs to call the package's `export fn`s and use its `export`
        // types; the object comes from `--emit ll` and `clang -c`, or from linking with C.
        let (header, warnings) = Compiler::c_header_of_package(&package.refs(), package.no_std)?;
        warn(err, &warnings);
        let target = output.unwrap_or(format!("{stem}.h"));
        std::fs::write(&target, header).map_err(|e| format!("cannot write '{target}': {e}"))?;
        let _ = writeln!(out, "wrote {target}");
        return Ok(0);
    }
    let ir = crate::llvm::LlvmLowering::lower(&package.compile(err)?)?;
    if emit == "ll" {
        let target = output.unwrap_or(format!("{stem}.ll"));
        std::fs::write(&target, ir).map_err(|e| format!("cannot write '{target}': {e}"))?;
        let _ = writeln!(out, "wrote {target}");
        return Ok(0);
    }
    let target = output.unwrap_or(stem);
    // A package built from the directory it is in would be written over that directory.
    if std::path::Path::new(&target).is_dir() {
        return Err(format!("'{target}' is a directory; name the executable with '-o'"));
    }
    link_executable(&ir, &opt, &package.system_libs, std::path::Path::new(&target))?;
    let _ = writeln!(out, "built {target}");
    Ok(0)
}

/// Links LLVM IR into an executable at `target` with `clang` at `opt`, with `-lm` and the
/// package's system libraries.
fn link_executable(ir: &str, opt: &str, system_libs: &[String], target: &std::path::Path) -> Result<(), String> {
    let dir = std::env::temp_dir().join(format!("slop_build_{}_{}", std::process::id(), unique()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot make '{}': {e}", dir.display()))?;
    let ll = dir.join("program.ll");
    std::fs::write(&ll, ir).map_err(|e| format!("cannot write '{}': {e}", ll.display()))?;
    let clang = std::process::Command::new("clang")
        .arg(opt)
        .arg("-Wno-override-module")
        .arg(&ll)
        .arg("-o")
        .arg(target)
        .arg("-lm")
        .args(system_libs.iter().map(|l| format!("-l{l}")))
        .output()
        .map_err(|e| format!("cannot run 'clang', which links the executable (or use '--emit ll'): {e}"));
    let _ = std::fs::remove_dir_all(&dir);
    let clang = clang?;
    if !clang.status.success() {
        return Err(format!("clang failed: {}", String::from_utf8_lossy(&clang.stderr).trim()));
    }
    Ok(())
}

/// A number no other call in this process gets, for naming temporary files.
fn unique() -> u64 {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// Starts a package in `dir`, named after it: a manifest, and a `src/main.slop` with a `main`
/// and a test. An existing directory is left alone.
fn new_package(args: &[String], out: &mut dyn Write) -> Result<i32, String> {
    let [dir] = args else {
        return Err(USAGE.to_string());
    };
    let root = std::path::Path::new(dir);
    if root.exists() {
        return Err(format!("'{dir}' exists already"));
    }
    let name = root
        .file_name()
        .map(|n| n.to_string_lossy().into_owned())
        .filter(|n| !n.is_empty() && n.chars().all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-'))
        .ok_or_else(|| format!("'{dir}' is not a package name (letters, digits, '_' and '-')"))?;
    let manifest = format!(
        "import std::build::{{Package, Target, Dependency}};

pub fn package[target: Target]() -> Package {{
    return Package {{
        name: \"{name}\",
        version: .{{ 0, 1, 0 }},
        root: \"src/main.slop\",
        no_std: false,
        deps: &[],
        system_libs: &[],
    }};
}}
"
    );
    let main = "fn greeting() -> String {
    return String::from(\"hello\");
}

pub fn main() -> i32 {
    println(greeting());
    return 0;
}

test \"greets\" {
    let g = greeting();
    @assert(g.as_str() == \"hello\");
}
";
    let src = root.join("src");
    std::fs::create_dir_all(&src).map_err(|e| format!("cannot make '{}': {e}", src.display()))?;
    std::fs::write(root.join("package.slop"), manifest).map_err(|e| format!("cannot write the manifest: {e}"))?;
    std::fs::write(src.join("main.slop"), main).map_err(|e| format!("cannot write 'src/main.slop': {e}"))?;
    let _ = writeln!(out, "created package '{name}' in {dir}");
    Ok(0)
}
