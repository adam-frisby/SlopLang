//! Model-based testing of std's containers, whose unsafe code the checkers cannot vouch for.
//! Each program is a random sequence of operations on one container, run first against a Rust
//! model, with every result asserted in the generated program. The program must return 0, under
//! the compile-time VM (which also reports undefined behaviour and leaks) and natively.
//!
//! `SLOPLANG_MODEL_CASES` (default 3), `SLOPLANG_MODEL_SEED` (default 1), and `SLOPLANG_FUZZ_WORKERS` (default
//! the number of cores) control the run; a failure prints the seed and the operation that
//! failed, numbered by the value `main` returned.

use super::fuzz::Rng;
use super::{TRAP_EXIT, VmRun, lli, run_vm_program};
use crate::lower::Compiler;
use std::collections::{HashMap, VecDeque};

const HELPERS: &str = "\
fn int_ref(o: ?&i32) -> i32 { if let x = o { return *x; } return -1; }
fn box_ref[B](o: ?&B) -> i32 { if let x = o { return *x.get(); } return -1; }
fn int_of(o: ?i32) -> i32 { if let x = o { return x; } return -1; }
fn box_of[B](o: ?B) -> i32 { if let x = o { return x.into_inner(); } return -1; }
static mut LIVE: i32 = 0;
extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
pub struct Tracked { x: i32 }
impl Allocator for Tracked {
    fn alloc(bytes: usize, align: usize) -> *mut u8 {
        unsafe { LIVE = LIVE + 1; return malloc(bytes); }
    }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        unsafe { return realloc(ptr, bytes); }
    }
    fn dealloc(ptr: *mut u8) { unsafe { LIVE = LIVE - 1; free(ptr); } }
}
";

/// How a container's element is written in the generated program: plain, or owning heap memory,
/// which makes a lost or doubled drop visible.
#[derive(Clone, Copy)]
struct Elem {
    boxed: bool,
    /// Whether the container and its elements use the `Tracked` allocator, whose count of live
    /// allocations must return to zero: a value freed by the wrong allocator leaves it off.
    tracked: bool,
}

impl Elem {
    fn pick(rng: &mut Rng) -> Elem {
        Elem { boxed: rng.below(2) == 0, tracked: rng.below(2) == 0 }
    }

    fn ty(self) -> &'static str {
        if self.boxed { "Box[i32]" } else { "i32" }
    }

    /// `expr` in this element's context.
    fn context(self, expr: String) -> String {
        if self.tracked { format!("@with_allocator(Tracked, {expr})") } else { expr }
    }

    fn new(self, v: i32) -> String {
        if self.boxed { self.context(format!("Box[i32]::new({v})")) } else { v.to_string() }
    }

    /// A value of type `?T`, read as an `i32` (-1 for null).
    fn of(self, e: &str) -> String {
        format!("{}({e})", if self.boxed { "box_of" } else { "int_of" })
    }

    /// A value of type `?&T`, read as an `i32`.
    fn of_ref(self, e: &str) -> String {
        format!("{}({e})", if self.boxed { "box_ref" } else { "int_ref" })
    }

    /// The `i32` behind `x`, a `&T`.
    fn deref(self, x: &str) -> String {
        if self.boxed { format!("*{x}.get()") } else { format!("*{x}") }
    }
}

/// A generated body: each `check` is numbered, and returns its number if it fails.
struct Body {
    out: String,
    checks: i32,
}

impl Body {
    fn line(&mut self, text: &str) {
        self.out.push_str("    ");
        self.out.push_str(text);
        self.out.push('\n');
    }

    fn check(&mut self, got: &str, want: i64) {
        self.checks += 1;
        self.line(&format!("if ({got}) as i64 != {want} {{ return {}; }}", self.checks));
    }

    /// The checks run in a function of their own, so the container is dropped before `main`
    /// looks at the live count.
    fn into_program(self, leaked: i32) -> String {
        format!(
            "{HELPERS}fn run() -> i32 {{\n{}    return 0;\n}}\npub fn main() -> i32 {{\n    let r = run();\n    if r != 0 {{ return r; }}\n    if unsafe {{ LIVE }} != 0 {{ return {leaked}; }}\n    return 0;\n}}\n",
            self.out
        )
    }
}

fn vec_program(rng: &mut Rng) -> String {
    let e = Elem::pick(rng);
    let ty = e.ty();
    let mut b = Body { out: String::new(), checks: 0 };
    let cap = rng.below(3) * 4;
    b.line(&if cap == 0 {
        format!("let mut v = {};", e.context(format!("Vec[{ty}]::new()")))
    } else {
        format!("let mut v = {};", e.context(format!("Vec[{ty}]::with_capacity({cap})")))
    });
    let mut model: Vec<i32> = Vec::new();
    let mut next = 1;
    for _ in 0..60 + rng.below(120) {
        let i = rng.below(model.len() + 2);
        next += 1;
        match rng.below(14) {
            0..=4 => {
                b.line(&format!("v.push({});", e.new(next)));
                model.push(next);
            }
            5 | 6 => {
                let want = model.pop().unwrap_or(-1);
                b.check(&e.of("v.pop()"), want as i64);
            }
            7 => b.check(&e.of_ref(&format!("v.get({i})")), model.get(i).copied().unwrap_or(-1) as i64),
            8 => {
                b.line(&format!("if let x = v.get_mut({i}) {{ *x = {}; }}", e.new(next)));
                if let Some(slot) = model.get_mut(i) {
                    *slot = next;
                }
            }
            9 => {
                let n = rng.below(model.len() + 2);
                b.line(&format!("v.truncate({n});"));
                model.truncate(n);
            }
            10 => {
                b.line(&format!("let mut t{next}: i64 = 0;"));
                b.line(&format!("for x in v.iter() {{ t{next} = t{next} + ({}) as i64; }}", e.deref("x")));
                b.check(&format!("t{next}"), model.iter().map(|&x| x as i64).sum());
            }
            11 => {
                if !e.boxed {
                    b.line("for x in v.iter_mut() { *x = *x + 1; }");
                    model.iter_mut().for_each(|x| *x += 1);
                }
            }
            12 => {
                if i < model.len() {
                    b.line(&format!("if true {{ let sl = v.as_mut_slice(); sl[{i}] = {}; }}", e.new(next)));
                    model[i] = next;
                    b.line(&format!("let sl{next} = v.as_slice();"));
                    b.check(&e.deref(&format!("(&sl{next}[{i}])")), next as i64);
                    b.check(&format!("sl{next}.len"), model.len() as i64);
                }
            }
            _ => {
                if rng.below(8) == 0 {
                    b.line("v.clear();");
                    model.clear();
                }
                b.check("v.len()", model.len() as i64);
                b.check("v.is_empty() as i32", model.is_empty() as i64);
                b.check("(v.capacity() >= v.len()) as i32", 1);
            }
        }
    }
    b.into_program(9999)
}

fn map_program(rng: &mut Rng) -> String {
    let e = Elem::pick(rng);
    let ty = e.ty();
    let mut b = Body { out: String::new(), checks: 0 };
    b.line(&format!("let mut m = {};", e.context(format!("HashMap[i32, {ty}]::new()"))));
    let mut model: HashMap<i32, i32> = HashMap::new();
    // Few keys, far apart or close: collisions, and slots freed and reused.
    let spread = [1, 16, 256][rng.below(3)];
    let keys = 4 + rng.below(60) as i32;
    let mut next = 1;
    for _ in 0..80 + rng.below(160) {
        let k = rng.below(keys as usize) as i32 * spread;
        next += 1;
        match rng.below(10) {
            0..=3 => {
                let want = model.insert(k, next).unwrap_or(-1);
                b.check(&e.of(&format!("m.insert({k}, {})", e.new(next))), want as i64);
            }
            4 | 5 => {
                let want = model.remove(&k).unwrap_or(-1);
                b.check(&e.of(&format!("m.remove({k})")), want as i64);
            }
            6 => b.check(&e.of_ref(&format!("m.get({k})")), model.get(&k).copied().unwrap_or(-1) as i64),
            7 => {
                b.line(&format!("if let x = m.get_mut({k}) {{ *x = {}; }}", e.new(next)));
                if let Some(slot) = model.get_mut(&k) {
                    *slot = next;
                }
            }
            8 => b.check(&format!("m.contains_key({k}) as i32"), model.contains_key(&k) as i64),
            _ => {
                b.check("m.len()", model.len() as i64);
                b.line(&format!("let ks{next} = m.keys();"));
                b.check(&format!("ks{next}.len()"), model.len() as i64);
                b.line(&format!("let mut t{next}: i64 = 0;"));
                b.line(&format!("for x in ks{next}.iter() {{ t{next} = t{next} + *x as i64; }}"));
                b.check(&format!("t{next}"), model.keys().map(|&x| x as i64).sum());
            }
        }
    }
    b.into_program(9999)
}

fn string_program(rng: &mut Rng) -> String {
    let mut b = Body { out: String::new(), checks: 0 };
    b.line("let mut s = String::new();");
    let mut model = String::new();
    for _ in 0..60 + rng.below(120) {
        match rng.below(8) {
            0 | 1 => {
                b.line("s.push_byte(b'x');");
                model.push('x');
            }
            2 | 3 => {
                let text = ["", "ab", "hello world", "a much longer piece of text to force growth"][rng.below(4)];
                b.line(&format!("s.push_str(\"{text}\");"));
                model.push_str(text);
            }
            4 => {
                let c = ['z', 'é', '€', '🦀'][rng.below(4)];
                b.line(&format!("s.push('{c}');"));
                model.push(c);
            }
            5 => b.line(&format!("s.reserve({});", rng.below(40))),
            6 => {
                if rng.below(6) == 0 {
                    b.line("s.clear();");
                    model.clear();
                }
                b.check("s.len()", model.len() as i64);
                b.check("(s.capacity() >= s.len()) as i32", 1);
            }
            _ => b.check(&format!("(s.as_str() == \"{model}\") as i32"), 1),
        }
    }
    b.into_program(9999)
}

fn channel_program(rng: &mut Rng) -> String {
    let e = Elem::pick(rng);
    let ty = e.ty();
    let mut b = Body { out: String::new(), checks: 0 };
    let cap = 1 + rng.below(5);
    b.line(&format!("let c = {};", e.context(format!("Channel[{ty}]::with_capacity({cap})"))));
    let mut model: VecDeque<i32> = VecDeque::new();
    let mut next = 1;
    for _ in 0..60 + rng.below(120) {
        next += 1;
        if rng.below(2) == 0 {
            // A full channel hands the value back.
            let want = if model.len() < cap {
                model.push_back(next);
                -1
            } else {
                next
            };
            b.check(&e.of(&format!("c.try_send({})", e.new(next))), want as i64);
        } else {
            let want = model.pop_front().unwrap_or(-1);
            b.check(&e.of("c.try_recv()"), want as i64);
        }
    }
    b.into_program(9999)
}

/// Why `src` fails: it must compile, return 0 on the VM with nothing leaked, and natively.
fn failure(src: &str) -> Option<String> {
    let mut program = match Compiler::compile_source(src) {
        Ok(program) => program,
        Err(e) => return Some(format!("does not compile: {e}")),
    };
    let native = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT)
        .map(|ir| lli(&ir).status.code());
    match run_vm_program(&mut program) {
        Err(e) => Some(format!("VM: {e}")),
        Ok(VmRun { value, .. }) if value != 0 => Some(format!("check {value} failed on the VM")),
        Ok(VmRun { leaks, .. }) if leaks > 0 => Some(format!("{leaks} heap block(s) leaked")),
        Ok(_) => (native != Ok(Some(0))).then(|| format!("native run gave {native:?}")),
    }
}

#[test]
fn model_std_containers() {
    let env = |name: &str, default: u64| {
        std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
    };
    let (cases, first) = (env("SLOPLANG_MODEL_CASES", 3), env("SLOPLANG_MODEL_SEED", 1));
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
    let generators: [(&str, fn(&mut Rng) -> String); 4] = [
        ("Vec", vec_program),
        ("HashMap", map_program),
        ("String", string_program),
        ("Channel", channel_program),
    ];
    let next = std::sync::atomic::AtomicU64::new(0);
    let total = cases * generators.len() as u64;
    let run = || {
        let mut failures = Vec::new();
        loop {
            let case = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            if case >= total {
                return failures;
            }
            let (name, generate) = generators[(case % generators.len() as u64) as usize];
            let seed = first + case / generators.len() as u64;
            let src = generate(&mut Rng::new(seed));
            if let Some(why) = failure(&src) {
                failures.push(format!("{name} failed on seed {seed}: {why}\n{src}"));
            }
        }
    };
    let failures: Vec<String> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..env("SLOPLANG_FUZZ_WORKERS", cores).min(total)).map(|_| scope.spawn(run)).collect();
        handles.into_iter().flat_map(|h| h.join().unwrap()).collect()
    });
    println!("model: {total} programs, {} failed", failures.len());
    assert!(failures.is_empty(), "{}", failures[0]);
}
