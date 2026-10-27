mod design_rules;
mod ffi_and_statics;
mod ir_and_codegen;
mod ownership_and_concurrency;
mod types_and_traits;

use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};

/// Exit code that traps are lowered to by `run_lli` and `link_with_c` (via
/// `LlvmLowering::lower_with_trap_exit`) rather than raising a signal, which keeps the system's
/// crash reporter out of the test run.
pub(crate) const TRAP_EXIT: i32 = 222;

/// Runs LLVM IR text under `lli`, fed on stdin.
pub(crate) fn lli(ir: &str) -> Output {
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child.stdin.as_mut().unwrap().write_all(ir.as_bytes()).unwrap();
    child.wait_with_output().expect("Failed to wait on lli")
}

/// Compiles `src`, runs it under `lli`, and returns its exit code (`TRAP_EXIT` for traps).
pub(crate) fn run_lli(name: &str, src: &str) -> Option<i32> {
    let program = crate::lower::Compiler::compile_source(src)
        .unwrap_or_else(|e| panic!("[{name}] expected to compile, got error: {e}"));
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT)
        .unwrap_or_else(|e| panic!("[{name}] LLVM lowering failed: {e}"));
    lli(&ir).status.code()
}

/// An executable linked by `link_with_c`; its temporary directory is removed on drop.
pub(crate) struct CBinary {
    dir: PathBuf,
}

impl CBinary {
    /// Runs the executable with `args`.
    pub(crate) fn run(&self, args: &[&str]) -> Output {
        Command::new(self.dir.join("a.out")).args(args).output().unwrap()
    }
}

impl Drop for CBinary {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.dir);
    }
}

/// Links LLVM IR into an executable with `clang` (the IR supplies `main`).
pub(crate) fn link_ir(name: &str, ir: &str) -> CBinary {
    link(name, ir, None)
}

/// Links LLVM IR with a C translation unit `c_main` (which can `#include "lib.h"`, the generated
/// `header`).
pub(crate) fn link_with_c(name: &str, ir: &str, header: &str, c_main: &str) -> CBinary {
    link(name, ir, Some((header, c_main)))
}

fn link(name: &str, ir: &str, c: Option<(&str, &str)>) -> CBinary {
    let dir = std::env::temp_dir().join(format!("lrrr_{name}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.ll"), ir).unwrap();
    let mut args = vec!["-Wno-override-module", "lib.ll", "-o", "a.out"];
    if let Some((header, c_main)) = c {
        std::fs::write(dir.join("lib.h"), header).unwrap();
        std::fs::write(dir.join("main.c"), c_main).unwrap();
        args.push("main.c");
    }
    let clang = Command::new("clang")
        .current_dir(&dir)
        .args(&args)
        .output()
        .expect("Failed to spawn clang");
    let bin = CBinary { dir };
    assert!(
        clang.status.success(),
        "[{name}] clang failed: {}",
        String::from_utf8_lossy(&clang.stderr)
    );
    bin
}
