//! The `slop` command: `slop run <path>`, `slop test <path>`, and `slop build <path>`.
//!
//! A path is a `.slop` file, compiled as the root module, or a package directory (with
//! `src/main.slop` or `src/lib.slop`; see `Compiler::load_package_dir`). `run` and `test` run
//! under the VM, with every check it has, so a program that leaks or has undefined behaviour
//! fails; `test --native` runs each test natively as well, and `build` makes an executable.

use std::io::Write;

use crate::lower::Compiler;
use crate::testing::{self, TestOptions};
use crate::vm::{Value, Vm};

const USAGE: &str = "usage: slop run <path>
       slop test <path> [--filter TEXT] [--jobs N] [--native]
       slop build <path> [-o OUT] [--emit exe|ll] [-O0|-O1|-O2|-O3]

<path> is a .slop file or a package directory.";

/// The exit status when the program could not be compiled or run to the end.
pub const FAILED: i32 = 101;

/// Runs `slop` with `args` (without the program name), writing to `out` and `err`; returns the
/// exit status.
pub fn main_with(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> i32 {
    let result = match args.first().map(String::as_str) {
        Some("run") => run(&args[1..], out, err),
        Some("test") => test(&args[1..], out),
        Some("build") => build(&args[1..], out),
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

/// The package at `path`: its modules and their sources.
fn load(path: &str) -> Result<Vec<(String, String)>, String> {
    let p = std::path::Path::new(path);
    if p.is_dir() {
        return Compiler::load_package_dir(p);
    }
    let src = std::fs::read_to_string(p).map_err(|e| format!("cannot read '{path}': {e}"))?;
    Ok(vec![("root".to_string(), src)])
}

/// Runs `main`, writing what it wrote; the status is what `main` returned, as a process's is.
fn run(args: &[String], out: &mut dyn Write, err: &mut dyn Write) -> Result<i32, String> {
    let [path] = args else {
        return Err(USAGE.to_string());
    };
    let sources = load(path)?;
    let refs: Vec<(&str, &str)> = sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let mut program = Compiler::compile_package(&refs)?;
    let main = program
        .functions
        .iter()
        .find(|f| f.debug_name.as_deref() == Some("root::main"))
        .map(|f| f.id)
        .ok_or("the package has no 'main'")?;
    let mut vm = Vm::new(&mut program);
    vm.set_max_steps(usize::MAX);
    vm.check_aliasing();
    vm.allow_io();
    vm.limit_stack(8 << 20);
    let ran = vm.eval_call(main, Vec::new());
    let _ = out.write_all(vm.output());
    let value = ran?;
    let leaks = vm.live_allocations();
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
fn test(args: &[String], out: &mut dyn Write) -> Result<i32, String> {
    let mut path = None;
    let mut options = TestOptions {
        filter: None,
        jobs: std::thread::available_parallelism().map_or(1, |n| n.get()),
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
    let sources = load(&path)?;
    let refs: Vec<(&str, &str)> = sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let mut outcomes = testing::run_tests_with(&refs, &options)?;
    if native {
        // What passed under the VM runs natively too, which must agree.
        let per_thread = outcomes.len().div_ceil(options.jobs.max(1)).max(1);
        std::thread::scope(|scope| {
            for chunk in outcomes.chunks_mut(per_thread) {
                let refs = &refs;
                scope.spawn(move || {
                    for o in chunk.iter_mut().filter(|o| o.result.is_ok()) {
                        o.result = testing::run_native(refs, o.index);
                    }
                });
            }
        });
    }
    let _ = write!(out, "{}", testing::report(&outcomes));
    Ok(if outcomes.iter().all(|o| o.result.is_ok()) { 0 } else { 1 })
}

/// Compiles the package to LLVM IR (`--emit ll`) or, with `clang`, to an executable.
fn build(args: &[String], out: &mut dyn Write) -> Result<i32, String> {
    let (mut path, mut output, mut emit, mut opt) = (None, None, "exe".to_string(), "-O2".to_string());
    let mut rest = args.iter();
    while let Some(a) = rest.next() {
        match a.as_str() {
            "-o" => output = Some(rest.next().ok_or("'-o' needs a file")?.clone()),
            "--emit" => {
                emit = rest.next().ok_or("'--emit' needs 'exe' or 'll'")?.clone();
                if emit != "exe" && emit != "ll" {
                    return Err(format!("'--emit {emit}': expected 'exe' or 'll'"));
                }
            }
            "-O0" | "-O1" | "-O2" | "-O3" => opt = a.clone(),
            p if path.is_none() && !p.starts_with('-') => path = Some(p.to_string()),
            other => return Err(format!("unexpected '{other}'\n{USAGE}")),
        }
    }
    let path = path.ok_or(USAGE)?;
    let sources = load(&path)?;
    let refs: Vec<(&str, &str)> = sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let program = Compiler::compile_package(&refs)?;
    let ir = crate::llvm::LlvmLowering::lower(&program)?;
    // `examples/ledger` builds `ledger`; `wordcount.slop` builds `wordcount`.
    let stem = std::path::Path::new(&path)
        .file_stem()
        .map_or("a".to_string(), |s| s.to_string_lossy().into_owned());
    if emit == "ll" {
        let target = output.unwrap_or(format!("{stem}.ll"));
        std::fs::write(&target, ir).map_err(|e| format!("cannot write '{target}': {e}"))?;
        let _ = writeln!(out, "wrote {target}");
        return Ok(0);
    }
    let target = output.unwrap_or(stem);
    let dir = std::env::temp_dir().join(format!("slop_build_{}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot make '{}': {e}", dir.display()))?;
    let ll = dir.join("program.ll");
    std::fs::write(&ll, ir).map_err(|e| format!("cannot write '{}': {e}", ll.display()))?;
    let clang = std::process::Command::new("clang")
        .arg(&opt)
        .arg("-Wno-override-module")
        .arg(&ll)
        .arg("-o")
        .arg(&target)
        .arg("-lm")
        .output()
        .map_err(|e| format!("cannot run 'clang', which links the executable (or use '--emit ll'): {e}"));
    let _ = std::fs::remove_dir_all(&dir);
    let clang = clang?;
    if !clang.status.success() {
        return Err(format!("clang failed: {}", String::from_utf8_lossy(&clang.stderr).trim()));
    }
    let _ = writeln!(out, "built {target}");
    Ok(0)
}
