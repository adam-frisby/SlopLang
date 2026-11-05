//! Running a package's `test "name" { ... }` blocks.
//!
//! Each test runs in a fresh VM with every check the VM has: undefined behaviour, aliasing, data
//! races, use after free, and the native stack's depth. It passes when its body finishes and
//! leaves nothing allocated; a trap (an `@assert` that failed, say), a leak, or undefined
//! behaviour fails it, with what happened. Its I/O is emulated, and what it wrote is kept.

use crate::lower::Compiler;
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

/// Compiles `sources` with their tests and runs each, in module order.
pub fn run_tests(sources: &[(&str, &str)]) -> Result<Vec<TestOutcome>, String> {
    let (mut program, cases) = Compiler::compile_tests(sources)?;
    let mut outcomes = Vec::with_capacity(cases.len());
    for case in cases {
        let mut vm = Vm::new(&mut program);
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
        outcomes.push(TestOutcome { module: case.module, name: case.name, result, output });
    }
    Ok(outcomes)
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
