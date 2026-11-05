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
}

impl Default for TestOptions {
    fn default() -> Self {
        TestOptions { filter: None, jobs: 1 }
    }
}

/// Compiles `sources` with their tests and runs each, in module order.
pub fn run_tests(sources: &[(&str, &str)]) -> Result<Vec<TestOutcome>, String> {
    run_tests_with(sources, &TestOptions::default())
}

/// `run_tests` for the tests `options` picks, on its threads. Outcomes keep module order.
pub fn run_tests_with(sources: &[(&str, &str)], options: &TestOptions) -> Result<Vec<TestOutcome>, String> {
    let (mut program, cases) = Compiler::compile_tests(sources)?;
    let picked: Vec<TestCase> = cases
        .into_iter()
        .filter(|c| {
            options.filter.as_deref().is_none_or(|f| {
                c.name.contains(f) || format!("{}: {}", c.module, c.name).contains(f)
            })
        })
        .collect();
    let jobs = options.jobs.clamp(1, picked.len().max(1));
    if jobs == 1 {
        return Ok(picked.into_iter().map(|c| run_case(&mut program, c)).collect());
    }
    // Test `i` runs on thread `i % jobs`; each thread has a program of its own, as the VM adds
    // to the program it runs.
    let mut slots: Vec<Option<TestOutcome>> = vec![None; picked.len()];
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..jobs)
            .map(|j| {
                let mut copy = program.clone();
                let mine: Vec<(usize, TestCase)> =
                    picked.iter().cloned().enumerate().filter(|(i, _)| i % jobs == j).collect();
                std::thread::Builder::new()
                    .stack_size(64 << 20)
                    .spawn_scoped(scope, move || {
                        mine.into_iter().map(|(i, c)| (i, run_case(&mut copy, c))).collect::<Vec<_>>()
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

/// Runs one test in a fresh VM.
fn run_case(program: &mut crate::ir::Program, case: TestCase) -> TestOutcome {
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
    TestOutcome { module: case.module, name: case.name, result, output }
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
