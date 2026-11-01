mod design_rules;
mod differential;
mod ffi_and_statics;
mod fuzz;
mod model;
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

/// What running a whole program under the compile-time VM produced.
#[derive(Debug, PartialEq)]
pub(crate) struct VmRun {
    /// `main`'s return value.
    pub value: i128,
    /// Heap blocks still allocated when `main` returned.
    pub leaks: usize,
    /// What `main` wrote to stdout and stderr.
    pub output: String,
}

const STEP_LIMIT: usize = 5_000_000;

/// Runs an already compiled program's `main` under the compile-time VM, which detects
/// undefined behaviour (errors starting with `vm::UB_PREFIX`): access through a pointer whose
/// storage has ended, use of freed heap memory, double or interior frees, data races, and use
/// of a reference a conflicting access invalidated.
pub(crate) fn run_vm_program(program: &mut crate::ir::Program) -> Result<VmRun, String> {
    run_vm_scheduled(program, None)
}

/// `run_vm_program` with the interleaving `seed` selects, if any.
pub(crate) fn run_vm_scheduled(
    program: &mut crate::ir::Program,
    seed: Option<u64>,
) -> Result<VmRun, String> {
    run_vm_configured(program, seed, false, STEP_LIMIT)
}

/// `run_vm` with every other read or write of a pipe failing with `EINTR`.
pub(crate) fn run_vm_interrupted(name: &str, src: &str) -> Result<VmRun, String> {
    let mut program = crate::lower::Compiler::compile_source(src)
        .unwrap_or_else(|e| panic!("[{name}] expected to compile, got error: {e}"));
    run_vm_configured(&mut program, None, true, STEP_LIMIT)
}

fn run_vm_configured(
    program: &mut crate::ir::Program,
    seed: Option<u64>,
    interrupt_io: bool,
    max_steps: usize,
) -> Result<VmRun, String> {
    let main = program
        .functions
        .iter()
        .find(|f| f.debug_name.as_deref() == Some("root::main"))
        .map(|f| f.id)
        .ok_or("program has no 'root::main'")?;
    let mut vm = crate::vm::Vm::new(program);
    vm.set_max_steps(max_steps);
    vm.check_aliasing();
    vm.allow_io();
    if let Some(seed) = seed {
        vm.set_schedule(seed);
    }
    if interrupt_io {
        vm.set_interrupt_io();
    }
    let value = vm.eval_call(main, Vec::new())?;
    let crate::vm::Value::Int(value) = value else {
        return Err(format!("'main' returned {value:?}"));
    };
    Ok(VmRun {
        value,
        leaks: vm.live_allocations(),
        output: String::from_utf8_lossy(vm.output()).into_owned(),
    })
}

/// `run_vm_scheduled` for a program too long for the usual step limit.
pub(crate) fn run_vm_long(
    program: &mut crate::ir::Program,
    seed: Option<u64>,
    max_steps: usize,
) -> Result<VmRun, String> {
    run_vm_configured(program, seed, false, max_steps)
}

/// Compiles `src` and runs it under the compile-time VM (see `run_vm_program`).
pub(crate) fn run_vm(name: &str, src: &str) -> Result<VmRun, String> {
    let mut program = crate::lower::Compiler::compile_source(src)
        .unwrap_or_else(|e| panic!("[{name}] expected to compile, got error: {e}"));
    run_vm_program(&mut program)
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
    let dir = std::env::temp_dir().join(format!("sloplang_{name}_{}", std::process::id()));
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
