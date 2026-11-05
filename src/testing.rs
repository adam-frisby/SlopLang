//! Running a package's `test "name" { ... }` blocks.
//!
//! Each test runs in a fresh VM with every check the VM has: undefined behaviour, aliasing, data
//! races, use after free, and the native stack's depth. It passes when its body finishes and
//! leaves nothing allocated; a trap (an `@assert` that failed, say), a leak, or undefined
//! behaviour fails it, with what happened. Its I/O is emulated, and what it wrote is kept.

use crate::lower::{Compiler, TestCase};
use crate::vm::Vm;

/// How long a test may run, in VM steps.
pub const TEST_STEPS: usize = 30_000_000;

/// The result of one `test` block.
#[derive(Debug, Clone)]
pub struct TestOutcome {
    /// Its place among the package's tests, for `Compiler::compile_test_entry`.
    pub index: usize,
    pub module: String,
    pub name: String,
    /// `Err` with why it failed.
    pub result: Result<(), String>,
    /// What it wrote to stdout and stderr.
    pub output: String,
}

/// Which tests to run, and on how many threads.
#[derive(Debug, Clone)]
pub struct TestOptions {
    /// Only tests whose name, or `module: name`, contains this.
    pub filter: Option<String>,
    /// Threads to run them on, each with its own copy of the program; 1 runs them in turn.
    pub jobs: usize,
    /// Compile freestanding, with `core` only (a manifest's `no_std`).
    pub no_std: bool,
}

impl Default for TestOptions {
    fn default() -> Self {
        TestOptions { filter: None, jobs: 1, no_std: false }
    }
}

/// Compiles `sources` with their tests and runs each, in module order.
pub fn run_tests(sources: &[(&str, &str)]) -> Result<Vec<TestOutcome>, String> {
    run_tests_with(sources, &TestOptions::default())
}

/// `run_tests` for the tests `options` picks, on its threads. Outcomes keep module order.
pub fn run_tests_with(sources: &[(&str, &str)], options: &TestOptions) -> Result<Vec<TestOutcome>, String> {
    let (mut program, cases) = Compiler::compile_tests_in(sources, options.no_std)?;
    let picked: Vec<(usize, TestCase)> = cases
        .into_iter()
        .enumerate()
        .filter(|(_, c)| {
            options.filter.as_deref().is_none_or(|f| {
                c.name.contains(f) || format!("{}: {}", c.module, c.name).contains(f)
            })
        })
        .collect();
    let jobs = options.jobs.clamp(1, picked.len().max(1));
    if jobs == 1 {
        return Ok(picked.into_iter().map(|(n, c)| run_case(&mut program, n, c)).collect());
    }
    // Test `i` runs on thread `i % jobs`; each thread has a program of its own, as the VM adds
    // to the program it runs.
    let mut slots: Vec<Option<TestOutcome>> = vec![None; picked.len()];
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..jobs)
            .map(|j| {
                let mut copy = program.clone();
                let mine: Vec<(usize, (usize, TestCase))> =
                    picked.iter().cloned().enumerate().filter(|(i, _)| i % jobs == j).collect();
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(scope, move || {
                        mine.into_iter()
                            .map(|(i, (n, c))| (i, run_case(&mut copy, n, c)))
                            .collect::<Vec<_>>()
                    })
                    .map_err(|e| format!("Cannot start a test thread: {e}"))
            })
            .collect::<Result<_, String>>()?;
        for h in handles {
            for (i, outcome) in h.join().unwrap_or_else(|panic| std::panic::resume_unwind(panic)) {
                slots[i] = Some(outcome);
            }
        }
        Ok::<(), String>(())
    })?;
    Ok(slots.into_iter().map(|o| o.expect("every test ran")).collect())
}

/// Runs test `index`, `case`, in a fresh VM.
fn run_case(program: &mut crate::ir::Program, index: usize, case: TestCase) -> TestOutcome {
    let mut vm = Vm::new(program);
    vm.set_max_steps(TEST_STEPS);
    vm.check_aliasing();
    vm.allow_io();
    vm.limit_stack(8 << 20);
    let ran = vm.eval_call(case.func, Vec::new());
    let leaks = vm.live_allocations();
    let output = String::from_utf8_lossy(vm.output()).into_owned();
    let result = match ran {
        Err(e) => Err(e),
        Ok(_) if leaks > 0 => Err(format!("{leaks} heap block(s) leaked")),
        Ok(_) => Ok(()),
    };
    TestOutcome { index, module: case.module, name: case.name, result, output }
}

/// The exit status a native test's traps exit with, rather than with a signal.
pub const NATIVE_TRAP_EXIT: i32 = 134;

/// Runs test `index` natively: compiled with a `main` of its own and run by `lli`. `Ok` when
/// it returns; otherwise its status and what it wrote to stderr (a failed `@assert` says so).
pub fn run_native(sources: &[(&str, &str)], index: usize) -> Result<(), String> {
    run_native_in(sources, index, false)
}

/// `run_native`, freestanding when `no_std`.
pub fn run_native_in(sources: &[(&str, &str)], index: usize, no_std: bool) -> Result<(), String> {
    let program = Compiler::compile_test_entry_in(sources, index, no_std)?;
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, NATIVE_TRAP_EXIT)?;
    let mut child = std::process::Command::new("lli")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .map_err(|e| format!("cannot run 'lli', which runs tests natively: {e}"))?;
    {
        use std::io::Write as _;
        let mut stdin = child.stdin.take().expect("stdin is piped");
        stdin.write_all(ir.as_bytes()).map_err(|e| format!("cannot give 'lli' the program: {e}"))?;
    }
    let out = child.wait_with_output().map_err(|e| format!("'lli' failed: {e}"))?;
    match out.status.code() {
        Some(0) => Ok(()),
        status => {
            let stderr = String::from_utf8_lossy(&out.stderr);
            let what = match status {
                Some(NATIVE_TRAP_EXIT) => "trapped".to_string(),
                Some(n) => format!("exited with {n}"),
                None => "was killed by a signal".to_string(),
            };
            Err(format!("natively, {what}{}", if stderr.trim().is_empty() { String::new() } else { format!(": {}", stderr.trim()) }))
        }
    }
}

/// A report of `outcomes`, one line a test, then a count: `ok`, or `FAILED` and why.
pub fn report(outcomes: &[TestOutcome]) -> String {
    let mut out = String::new();
    let mut failed = 0;
    for o in outcomes {
        let at = if o.module == "root" { String::new() } else { format!("{}: ", o.module) };
        match &o.result {
            Ok(()) => out.push_str(&format!("test {at}{} ... ok\n", o.name)),
            Err(why) => {
                failed += 1;
                out.push_str(&format!("test {at}{} ... FAILED: {why}\n", o.name));
            }
        }
    }
    out.push_str(&format!("{} passed, {failed} failed\n", outcomes.len() - failed));
    out
}
