//! Differential testing: the compile-time VM and compiled code (via `lli`) must agree on the
//! value of every generated integer program, or both trap.

use super::{TRAP_EXIT, lli};
use crate::llvm::LlvmLowering;
use crate::lower::Compiler;
use crate::vm::{Value, Vm};

/// A small deterministic generator (xorshift64*), so failures reproduce from the seed.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len() as u64) as usize]
    }
}

/// `(name, signed, bits)` of the integer types programs use.
const TYPES: &[(&str, bool, u32)] = &[
    ("i8", true, 8),
    ("u8", false, 8),
    ("i16", true, 16),
    ("u16", false, 16),
    ("i32", true, 32),
    ("u32", false, 32),
    ("i64", true, 64),
    ("u64", false, 64),
];

/// A literal of the type: mostly small values, sometimes the type's extremes.
fn literal(rng: &mut Rng, signed: bool, bits: u32) -> String {
    let (min, max): (i128, i128) = if signed {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    } else {
        (0, (1i128 << bits) - 1)
    };
    let v = match rng.below(6) {
        0 => min,
        1 => max,
        2 => rng.below(4) as i128,
        3 => -(rng.below(4) as i128),
        _ => min + (rng.next() as i128).rem_euclid(max - min + 1),
    };
    v.clamp(min, max).to_string()
}

/// A random expression of type `ty` over the parameters `a`, `b`, `c`.
fn expr(rng: &mut Rng, depth: u32, ty: (&str, bool, u32)) -> String {
    let (name, signed, bits) = ty;
    if depth == 0 || rng.below(4) == 0 {
        return match rng.below(4) {
            0 => literal(rng, signed, bits),
            1 => "a".to_string(),
            2 => "b".to_string(),
            _ => "c".to_string(),
        };
    }
    let l = expr(rng, depth - 1, ty);
    let r = expr(rng, depth - 1, ty);
    match rng.below(9) {
        0 => {
            let op = rng.pick(&["+", "-", "*", "+%", "-%", "*%", "+|", "-|", "*|"]);
            format!("({l} {op} {r})")
        }
        1 => format!("({l} {} {r})", rng.pick(&["&", "|", "^"])),
        2 => format!("({l} {} {r})", rng.pick(&["/", "%"])),
        3 => format!("({l} {} ({r} & ({} as {name})))", rng.pick(&["<<", ">>"]), bits - 1),
        4 => {
            let op = rng.pick(&["+?", "-?", "*?"]);
            format!("(({l} {op} {r}) orelse ({} as {name}))", literal(rng, signed, bits))
        }
        5 => {
            let cmp = rng.pick(&["<", "<=", ">", ">=", "==", "!="]);
            format!("(if {l} {cmp} {r} {{ {l} }} else {{ {r} }})")
        }
        6 => {
            // Through another type and back: truncation, sign / zero extension.
            let other = rng.pick(TYPES).0;
            format!("(({l} as {other}) as {name})")
        }
        7 => format!("(0 -% {l})"),
        _ => format!("(({l} as ?{name}) orelse {r})"),
    }
}

/// The VM's result for `g(args)`, or `None` when it traps.
fn vm_result(src: &str, args: Vec<Value>) -> Result<Option<Value>, String> {
    let mut program = Compiler::compile_source(src)?;
    let g = program
        .functions
        .iter()
        .find(|f| f.debug_name.as_deref() == Some("root::g"))
        .ok_or("no function g")?
        .id;
    Ok(Vm::eval(&mut program, g, args).ok())
}

#[test]
fn test_vm_and_compiled_code_agree() {
    // `LRRR_DIFF_CASES` / `LRRR_DIFF_SEED` run a longer or different campaign.
    let env = |k: &str, d: u64| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
    let cases = env("LRRR_DIFF_CASES", 120);
    let mut rng = Rng(env("LRRR_DIFF_SEED", 0x9e37_79b9_7f4a_7c15));
    let mut compared = 0;
    for case in 0..cases {
        let ty = *rng.pick(TYPES);
        let (name, signed, bits) = ty;
        let body = expr(&mut rng, 3, ty);
        let args: Vec<String> = (0..3).map(|_| literal(&mut rng, signed, bits)).collect();
        let g = format!(
            "fn g(a: {name}, b: {name}, c: {name}) -> {name} {{ return {body}; }}\n"
        );
        let probe = format!("{g}pub fn main() -> i32 {{ return 0; }}\n");
        let vm_args = args.iter().map(|a| Value::Int(a.parse().unwrap())).collect();
        let expected = match vm_result(&probe, vm_args) {
            Ok(v) => v,
            // Rejected at compile time (e.g. a literal folded to an overflow): nothing to compare.
            Err(e) => {
                if std::env::var("LRRR_DIFF_VERBOSE").is_ok() {
                    println!("case {case} rejected: {e}");
                }
                continue;
            }
        };
        let call = "g(x, y, z)";
        let lets = format!(
            "let x: {name} = {}; let y: {name} = {}; let z: {name} = {};",
            args[0], args[1], args[2]
        );
        let (main, want) = match &expected {
            Some(Value::Int(v)) => (
                format!(
                    "pub fn main() -> i32 {{ {lets} let want: {name} = {v}; if {call} == want {{ return 42; }} return 1; }}"
                ),
                42,
            ),
            Some(other) => panic!("case {case}: unexpected VM value {other:?}\n{g}"),
            None => (format!("pub fn main() -> i32 {{ {lets} let _ = {call}; return 42; }}"), TRAP_EXIT),
        };
        let src = format!("{g}{main}\n");
        let program = Compiler::compile_source(&src)
            .unwrap_or_else(|e| panic!("case {case} does not compile: {e}\n{src}"));
        let ir = LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT).unwrap();
        let out = lli(&ir);
        assert_eq!(
            out.status.code(),
            Some(want),
            "case {case}: the VM gave {expected:?} for {call}, compiled code disagrees\n{src}\n{}",
            String::from_utf8_lossy(&out.stderr)
        );
        compared += 1;
    }
    assert!(compared * 3 >= cases * 2, "only {compared} of {cases} cases compared");
}
