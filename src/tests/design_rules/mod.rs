use crate::lower::Compiler;
pub(super) use crate::tests::{lli, run_lli, run_vm, run_vm_interrupted, run_vm_program, run_vm_scheduled, TRAP_EXIT, VmRun};

mod ownership_and_borrows;
mod concurrency_and_async;
mod types_and_generics;
mod syntax_and_inference;
mod generators_and_allocators;
mod examples_and_docs;
mod ffi_and_vm;

/// A `linear` opaque type shared by the tests below.
pub(super) const LINEAR_TX: &str = "\
pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(self) -> i32 { return self.id; }
}
";

pub(super) fn accept(name: &str, src: &str) {
    if let Err(e) = Compiler::compile_source(src) {
        panic!("[{name}] expected to compile, got error: {e}");
    }
}

pub(super) fn reject(name: &str, src: &str, expected: &str) {
    match Compiler::compile_source(src) {
        Ok(_) => panic!("[{name}] expected a compile error containing {expected:?}"),
        Err(e) => assert!(
            e.contains(expected),
            "[{name}] expected error containing {expected:?}, got: {e}"
        ),
    }
}

pub(super) fn with_tx(body: &str) -> String {
    format!("{LINEAR_TX}\n{body}")
}

pub(super) const HASH: &str = "\
pub trait Hash { fn hash(&self) -> u64; }
fn h[T: Hash](x: &T) -> u64 { return x.hash(); }
";

pub(super) fn with_hash(body: &str) -> String {
    format!("{HASH}\n{body}")
}

/// Runs `src` on the VM and natively, and checks both give `value` with nothing leaked.
pub(super) fn assert_runs(name: &str, src: &str, value: i128) {
    let (run, native) = crate::tests::run_both(name, src);
    let run = run.unwrap_or_else(|e| panic!("[{name}] {e}"));
    assert_eq!((run.value, run.leaks), (value, 0), "[{name}]");
    assert_eq!(native, Some(value as i32), "[{name}]");
}

pub(super) fn assert_rejected(name: &str, src: &str, what: &str) {
    let err = Compiler::compile_source(src).expect_err(name);
    assert!(err.contains(what), "[{name}] {err}");
}

pub(super) const TX: &str = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(self) -> i32 { return self.id; }
}
";

pub(super) const COUNTING: &str = "static mut LIVE: i32 = 0;
static mut TOTAL: i32 = 0;
extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
";

pub(super) const KVSTORE: &str = include_str!("../../../examples/kvstore.slop");
pub(super) const WORDCOUNT: &str = include_str!("../../../examples/wordcount.slop");
pub(super) const SCRIPT: &str = include_str!("../../../examples/script.slop");
pub(super) const HTTPD: &str = include_str!("../../../examples/httpd.slop");
pub(super) const SERVE: &str = include_str!("../../../examples/serve.slop");
pub(super) const SCRIPT_OUT: &str = "line 8: division by zero
line 9: unbound variable
line 10: not a function
line 11: unexpected end
line 12: unexpected character 36
line 13: wrong arguments
14
144
-12
9
12
21
6 errors
";

/// An example compiled and run natively: its exit code and what it wrote.
pub(super) fn example_natively(name: &str, src: &str) -> (Option<i32>, String) {
    let program = Compiler::compile_source(src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    native_output(&program)
}

pub(super) fn native_output(program: &crate::ir::Program) -> (Option<i32>, String) {
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(program, 222).unwrap();
    let out = crate::tests::lli(&ir);
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned())
}

/// An example under the VM, for what it alone can see: races, leaks, and undefined behaviour.
pub(super) fn example_checked(name: &str, src: &str, seed: Option<u64>) -> (i128, String) {
    let mut program = Compiler::compile_source(src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    let run = crate::tests::run_vm_long(&mut program, seed, 30_000_000)
        .unwrap_or_else(|e| panic!("[{name}, seed {seed:?}] {e}"));
    assert_eq!(run.leaks, 0, "[{name}, seed {seed:?}]");
    (run.value, run.output)
}

/// The ledger package's modules, with its number of events replaced by `events`.
pub(super) fn ledger_modules(events: &str) -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/ledger");
    Compiler::load_package_dir(&dir)
        .unwrap()
        .into_iter()
        .map(|(m, src)| (m, src.replace("const EVENTS: i32 = 3000;", events)))
        .collect()
}

pub(super) fn compile_ledger(events: &str) -> crate::ir::Program {
    let modules = ledger_modules(events);
    let refs: Vec<(&str, &str)> = modules.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    Compiler::compile_package(&refs).unwrap_or_else(|e| panic!("[ledger] {e}"))
}

pub(super) const REFLECT: &str = include_str!("../../../examples/reflect.slop");

/// Virtual time a run that wakes threads as it should stays under: a lost wake is found only by
/// the 50 ms sweep. (Waits on different threads overlap, so a run that only waits for wakes
/// takes next to none.)
pub(super) const WAKE_LIMIT_MS: i128 = 20;

