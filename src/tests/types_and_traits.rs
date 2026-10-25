use std::io::Write;
use std::process::{Command, Stdio};

use crate::llvm::LlvmLowering;
use crate::lower::Compiler;

#[test]
fn test_struct_block_privacy_and_module_visibility() {
    // 1. Accessing a private opaque field from a free function in the SAME file must be rejected!
    let bad_field_src = "\
opaque Secret {
    hidden: i32,

    pub fn new(v: i32) -> Self {
        return Self { hidden: v };
    }
}

pub fn main() -> i32 {
    let s = Secret::new(42);
    return s.hidden;
}
";
    let err = Compiler::compile_source(bad_field_src)
        .expect_err("Expected private opaque field access outside opaque block to fail");
    assert!(
            err.contains("Cannot access private field 'hidden' of struct 'Secret' outside its 'struct { ... }' block"),
            "Unexpected error: {err}"
        );

    // 2. Constructing an opaque with private fields outside its `opaque { ... }` block must be rejected!
    let bad_lit_src = "\
opaque Secret {
    hidden: i32,
}

pub fn main() -> i32 {
    let s = Secret { hidden: 10 };
    return 0;
}
";
    let err = Compiler::compile_source(bad_lit_src)
        .expect_err("Expected opaque literal with private field outside opaque block to fail");
    assert!(
            err.contains("Cannot construct opaque 'Secret' with private field 'hidden' outside its 'opaque { ... }' block"),
            "Unexpected error: {err}"
        );

    // 3. Calling a private opaque method outside its `opaque { ... }` block must be rejected!
    let bad_method_src = "\
opaque Secret {
    hidden: i32,

    pub fn new(v: i32) -> Self {
        return Self { hidden: v };
    }

    fn internal_only(self: &Self) -> i32 {
        return self.hidden;
    }
}

pub fn main() -> i32 {
    let s = Secret::new(42);
    return s.internal_only();
}
";
    let err = Compiler::compile_source(bad_method_src)
        .expect_err("Expected private opaque method call outside opaque block to fail");
    assert!(
            err.contains("Cannot call private method 'internal_only' of struct 'Secret' outside its 'struct { ... }' block"),
            "Unexpected error: {err}"
        );

    // 4. Cross-module private item access must be rejected!
    let mod_a = "\
fn helper() -> i32 {
    return 1;
}
";
    let mod_b = "\
import root::a;

pub fn main() -> i32 {
    return a::helper();
}
";
    let err = Compiler::compile_package(&[("root::a", mod_a), ("root", mod_b)])
        .expect_err("Expected cross-module private function call to fail");
    assert!(
        err.contains("Item 'helper' in module 'root::a' is private"),
        "Unexpected error: {err}"
    );

    // 5. Out-of-range compile-time constant assigned to a Pattern type must be rejected!
    let bad_pattern_src = "\
type Percent = u8 in 0..=100;

pub fn main() -> i32 {
    let p: Percent = 150;
    return p as i32;
}
";
    let err = Compiler::compile_source(bad_pattern_src)
        .expect_err("Expected out-of-range pattern constant to fail");
    assert!(
        err.contains("outside valid pattern ranges"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_extension_methods_comptime_receivers_and_coherence() {
    use crate::lower::Compiler;
    use std::io::Write;
    use std::process::{Command, Stdio};

    let types_mod = "\
pub type Point = struct {
    x: i32,
    y: i32,

    pub fn sum(self: &Self) -> i32 {
        return self.x + self.y;
    }
};

pub fn Pair(comptime T: type) -> type {
    return struct {
        first: T,
        second: T,
    };
}
";

    let simd_ext_mod = "\
import root::types::Pair;

// Extension on built-in comptime-parameterized `simd[T; N]`
pub fn first_lane(comptime T: type, comptime N: usize, self: &simd[T; N]) -> T {
    return self[0];
}

// Extension on user-defined comptime-parameterized `Pair(T)`
pub fn dot(comptime T: type, self: &Pair(T), other: &Pair(T)) -> T {
    return self.first * other.first + self.second * other.second;
}

// Parameterized specificity (score = 2) vs concrete specificity (score = 3)
pub fn tag_rank(comptime T: type, self: &Pair(T)) -> i32 {
    return 10;
}
";

    let root_mod = "\
import root::types::{Point, Pair};
import root::simd_ext::{first_lane, dot, tag_rank};

// Localconcrete extension on `Point`
fn scale_x(self: &mut Point, factor: i32) {
    self.x *= factor;
}

// Concrete extension on `Pair(i32)` (specificity 3 > parameterized `tag_rank(comptime T, &Pair(T))` specificity 2)
fn tag_rank(self: &Pair(i32)) -> i32 {
    return 25;
}

// Shadowing test: inherent `Point::sum` must win over extension `sum(self: &Point)`
fn sum(self: &Point) -> i32 {
    return 999;
}

pub fn main() -> i32 {
    let mut pt = Point { x: 3, y: 4 };
    pt.scale_x(2);               // pt.x = 6, pt.y = 4
    let s = pt.sum();            // Inherent method wins: 6 + 4 = 10 (NOT 999)

    let v: simd[i32; 4] = simd[i32; 4]{ 7, 8, 9, 10 };
    let f = v.first_lane();      // Infers T = i32, N = 4 -> 7

    let p1 = Pair(i32){ first: 2, second: 3 };
    let p2 = Pair(i32){ first: 4, second: 5 };
    let d = p1.dot(&p2);         // Infers T = i32 -> 2*4 + 3*5 = 23
    let r = p1.tag_rank();       // Concrete `Pair(i32)` wins over `Pair(T)` -> 25

    // Also callable via normal function syntax with inferred comptime args:
    let f2 = first_lane(&v);     // 7

    // Total: 10 + 7 + 23 + 25 + 7 = 72
    return s + f + d + r + f2;
}
";

    let program = Compiler::compile_package(&[
        ("root::types", types_mod),
        ("root::simd_ext", simd_ext_mod),
        ("root", root_mod),
    ])
    .expect("Failed to compile package with extension methods");

    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(72),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify that ambiguous imported extension methods produce a compile-time error:
    let ext_a = "\
import root::types::Point;
pub fn metric(self: &Point) -> i32 { return self.x; }
";
    let ext_b = "\
import root::types::Point;
pub fn metric(self: &Point) -> i32 { return self.y; }
";
    let ambig_root = "\
import root::types::Point;
import root::ext_a::*;
import root::ext_b::*;

pub fn main() -> i32 {
    let p = Point { x: 1, y: 2 };
    return p.metric();
}
";
    let err = Compiler::compile_package(&[
        ("root::types", types_mod),
        ("root::ext_a", ext_a),
        ("root::ext_b", ext_b),
        ("root", ambig_root),
    ])
    .expect_err("Expected ambiguous extension method call to be rejected");
    assert!(
        err.contains("Ambiguous extension method 'metric'"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_numeric_metatype_hierarchy_number_integer_signed_unsigned_float() {
    use crate::lower::Compiler;
    use std::io::Write;
    use std::process::{Command, Stdio};

    let num_mod = "\
// 1. `number` matches both `integer` and `float`
pub fn clamp(comptime N: number, self: N, lo: N, hi: N) -> N {
    if self < lo {
        return lo;
    }
    if self > hi {
        return hi;
    }
    return self;
}

// 2. Disjoint overloads on `signed` vs `float` sharing the name `abs`
pub fn abs(comptime S: signed, self: S) -> S {
    if self < 0 {
        return -self;
    }
    return self;
}

pub fn abs(comptime F: float, self: F) -> F {
    if self < 0.0 {
        return -self;
    }
    return self;
}

// 3. `integer` matches both `signed` (`i32`) and arbitrary-width `unsigned` (`u24`)
pub fn low_nibble(comptime I: integer, self: I) -> I {
    return self & 15;
}

// 4. Full hierarchy specificity ladder: `unsigned` (4) > `integer` (3) > `number` (2) > `type` (1)
pub fn tier_rank(comptime T: type, self: T) -> i32 {
    return 1;
}

pub fn tier_rank(comptime N: number, self: N) -> i32 {
    return 2;
}

pub fn tier_rank(comptime I: integer, self: I) -> i32 {
    return 3;
}

pub fn tier_rank(comptime U: unsigned, self: U) -> i32 {
    return 4;
}
";

    let root_mod = "\
import root::num::*;

type Dummy = struct {
    v: i32,
};

pub fn main() -> i32 {
    let x: i32 = -12;
    let a = x.abs();                     // `signed` overload -> 12
    let clamped_i32 = a.clamp(0, 10);    // `number` on i32 -> 10

    let f: f64 = -4.0;
    let af = f.abs();                    // `float` overload -> 4.0
    let cf = af.clamp(0.0, 3.0);         // `number` on f64 -> 3.0
    let cf_int = cf as i32;              // 3

    let raw_u24: u24 = 31;               // 0x1F -> low_nibble = 15
    let nib = (raw_u24.low_nibble()) as i32;

    // Specificity ladder verification:
    let d = Dummy { v: 0 };
    let r_type = d.tier_rank();          // `type` -> 1
    let r_num = f.tier_rank();           // `float` matches `number` (2) > `type` (1) -> 2
    let r_int = x.tier_rank();           // `signed` matches `integer` (3) > `number` (2) -> 3
    let r_uns = raw_u24.tier_rank();     // `unsigned` matches `unsigned` (4) > `integer` (3) -> 4
    let ladder = r_type * 10 + r_num * 10 + r_int + r_uns; // 10 + 20 + 3 + 4 = 37

    // Total: 10 + 3 + 15 + 37 = 65
    return clamped_i32 + cf_int + nib + ladder;
}
";

    let program = Compiler::compile_package(&[("root::num", num_mod), ("root", root_mod)])
        .expect("Failed to compile numeric meta-type hierarchy package");

    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(65),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify that calling `abs` on `unsigned` (`u32`) is rejected because `abs` is only defined for `signed` and `float`:
    let bad_unsigned_abs = "\
import root::num::*;

pub fn main() -> i32 {
    let u: u32 = 5;
    return (u.abs()) as i32;
}
";
    let err = Compiler::compile_package(&[("root::num", num_mod), ("root", bad_unsigned_abs)])
        .expect_err("Expected `u.abs()` on unsigned u32 to be rejected");
    assert!(
        err.contains("Type 'u32' has no method 'abs'"),
        "Unexpected error: {err}"
    );

    // Verify that passing a non-number (`Dummy`) to `clamp(comptime N: number, ...)` is rejected at the signature boundary:
    let bad_explicit_clamp = "\
import root::num::clamp;

type Dummy = struct {
    v: i32,
};

pub fn main() -> i32 {
    let d = Dummy { v: 1 };
    let res = clamp(Dummy, d, d, d);
    return res.v;
}
";
    let err = Compiler::compile_package(&[("root::num", num_mod), ("root", bad_explicit_clamp)])
        .expect_err("Expected `clamp(Dummy, ...)` to fail `number` constraint");
    assert!(
        err.contains("Type 'Dummy' does not satisfy comptime constraint 'number'"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_composite_and_discriminated_metatype_hierarchy() {
    let meta_mod = "\
// 1. Disjoint overloads on open `aggregate` (`struct` | `tuple`) vs encapsulated `opaque`:
pub fn open_score(comptime A: aggregate, self: &A) -> i32 {
    return 10;
}

pub fn open_score(comptime S: opaque, self: &S) -> i32 {
    return 1;
}

// 2. Specificity ranking across `scalar`, `number`, and `aggregate`:
//    - `number` (rank 3) overrides `scalar` (rank 2), while `bool` and `rune` match `scalar` (rank 2)
//    - `struct` (rank 3) and `tuple` (rank 3) override `aggregate` (rank 2)
pub fn kind_code(comptime T: type, self: &T) -> i32 {
    return 0;
}

pub fn kind_code(comptime Sc: scalar, self: &Sc) -> i32 {
    return 11;
}

pub fn kind_code(comptime N: number, self: &N) -> i32 {
    return 12;
}

pub fn kind_code(comptime F: fn, self: &F) -> i32 {
    return 13;
}

pub fn kind_code(comptime Cal: callable, self: &Cal) -> i32 {
    return 14;
}

pub fn kind_code(comptime Cl: closure, self: &Cl) -> i32 {
    return 15;
}

pub fn kind_code(comptime A: aggregate, self: &A) -> i32 {
    return 20;
}

pub fn kind_code(comptime R: struct, self: &R) -> i32 {
    return 21;
}

pub fn kind_code(comptime Tp: tuple, self: &Tp) -> i32 {
    return 22;
}

pub fn kind_code(comptime V: simd, self: &V) -> i32 {
    return 23;
}

pub fn kind_code(comptime Arr: array, self: &Arr) -> i32 {
    return 24;
}

// 3. `discriminated` (`enum` | `union`) hierarchy & specificity:
pub fn tag_kind(comptime D: discriminated, self: &D) -> i32 {
    return 30;
}

pub fn tag_kind(comptime E: enum, self: &E) -> i32 {
    return 31;
}

pub fn tag_kind(comptime U: union, self: &U) -> i32 {
    return 32;
}

// Function that strictly requires an open `aggregate` (`struct` or `tuple`):
pub fn require_open(comptime A: aggregate, val: &A) -> i32 {
    return 5;
}
";

    let root_mod = "\
import root::meta::*;

pub struct Point {
    x: i32,
    y: i32,
}

pub opaque Vault {
    secret: i32,

    pub fn new(v: i32) -> Self {
        return Self { secret: v };
    }
}

pub enum Color {
    Red = 1,
    Green = 2,
    Blue = 3,
}

pub fn double_it(x: i32) -> i32 {
    return x * 2;
}

pub fn main() -> i32 {
    let p = Point { x: 3, y: 4 };
    let tup: tuple { i32, i32 } = { 7, 8 };
    let v = Vault::new(99);
    let c: Color = Color::Green;
    let opt: ?i32 = 42;

    // `open_score`: Point (`struct`) -> 10, tup (`tuple`) -> 10, Vault (`opaque`) -> 1 (sum = 21)
    let s1 = p.open_score() + tup.open_score() + v.open_score();

    // `kind_code`: Point (`struct` rank 3) -> 21, tup (`tuple` rank 3) -> 22, Vault (`type` rank 1) -> 0 (sum = 43)
    let s2 = p.kind_code() + tup.kind_code() + v.kind_code();

    // `scalar` vs `number` vs `fn` vs `discriminated`:
    //   flag (`bool` -> `scalar` rank 2) -> 11
    //   ch (`rune` -> `scalar` rank 2) -> 11
    //   n (`i32` -> `number` rank 3 > `scalar` rank 2) -> 12
    //   fp (`fn(i32) -> i32` -> `fn` rank 3 > `scalar` rank 2) -> 13, plus calling `fp(3)` -> 6
    //   c (`Color` `enum` is `discriminated`, NOT `scalar` -> `type` rank 1) -> 0
    //   (sum = 11 + 11 + 12 + 13 + 6 + 0 = 53)
    let flag: bool = true;
    let ch: rune = 'A';
    let n: i32 = 42;
    let fp: fn(i32) -> i32 = double_it;
    let s_scalar = flag.kind_code() + ch.kind_code() + n.kind_code() + fp.kind_code() + fp(3) + c.kind_code();

    // `simd` (rank 3 -> 23) and `array` (rank 3 -> 24):
    let vec4 = simd[i32; 4] { 1, 2, 3, 4 };
    let arr2: [i32; 2] = @default([i32; 2]);
    let s_seq = vec4.kind_code() + arr2.kind_code();

    // `tag_kind`: Color (`enum` rank 3) -> 31, ?i32 (`union` rank 3) -> 32 (sum = 63)
    let s3 = c.tag_kind() + opt.tag_kind();

    // `require_open` works on both `struct` and `tuple` (5 + 5 = 10)
    let s4 = require_open(Point, &p) + require_open(tuple { i32, i32 }, &tup);

    // Total = 21 + 43 + 53 + 47 + 63 + 10 = 237
    return s1 + s2 + s_scalar + s_seq + s3 + s4;
}
";

    let program = Compiler::compile_package(&[("root::meta", meta_mod), ("root", root_mod)])
        .expect("Failed to compile composite & discriminated meta-type hierarchy package");

    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(237),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify that passing an encapsulated `opaque` (`Vault`) to `require_open(comptime A: aggregate, ...)` is rejected!
    let bad_struct_as_aggregate = "\
import root::meta::require_open;

pub opaque Vault {
    secret: i32,
    pub fn new(v: i32) -> Self {
        return Self { secret: v };
    }
}

pub fn main() -> i32 {
    let v = Vault::new(10);
    return require_open(Vault, &v);
}
";
    let err =
        Compiler::compile_package(&[("root::meta", meta_mod), ("root", bad_struct_as_aggregate)])
            .expect_err("Expected `require_open(Vault, &v)` to fail `aggregate` constraint");
    assert!(
        err.contains("Type 'Vault' does not satisfy comptime constraint 'aggregate'"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_never_type_diverging_calls_and_orelse_return() {
    let src = "\
// 1. A diverging helper returning `never` via `@trap()`:
pub fn fatal_abort() -> never {
    @trap();
}

// 2. Non-void function ending in a call to a `-> never` function on one branch
//    without needing a dummy `return` afterward:
pub fn checked_positive(x: i32) -> i32 {
    if x > 0 {
        return x;
    }
    fatal_abort();
}

// 3. `orelse return <expr>` and `orelse fatal_abort()` where `never` coerces to `i32`:
pub fn add_optionals(a: ?i32, b: ?i32) -> i32 {
    let x: i32 = a orelse return 10;
    let y: i32 = b orelse return 20;
    return x + y;
}

pub fn unwrap_or_abort(a: ?i32) -> i32 {
    let v: i32 = a orelse fatal_abort();
    return v * 2;
}

pub fn main() -> i32 {
    let some5: ?i32 = 5;
    let some8: ?i32 = 8;
    let none_val: ?i32 = null;

    // 5 + 8 = 13
    let r1 = add_optionals(some5, some8);
    // `a` is null -> early returns 10 via `orelse return 10`
    let r2 = add_optionals(none_val, some8);
    // `b` is null -> early returns 20 via `orelse return 20`
    let r3 = add_optionals(some5, none_val);
    // `unwrap_or_abort(some5)` -> 10
    let r4 = unwrap_or_abort(some5);
    // `checked_positive(7)` -> 7
    let r5 = checked_positive(7);

    // 13 + 10 + 20 + 10 + 7 = 60
    return r1 + r2 + r3 + r4 + r5;
}
";

    let program = Compiler::compile_source(src).expect("Failed to compile `never` type test");
    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(60),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify that a function declared `-> never` that falls off the end is rejected at compile time:
    let bad_never_fn = "\
pub fn does_not_diverge() -> never {
    let x: i32 = 1;
}
";
    let err = Compiler::compile_source(bad_never_fn)
        .expect_err("Expected `-> never` function that falls through to be rejected");
    assert!(
        err.contains("declared '-> never' reaches end of function without diverging"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_lambdas_automatic_capture_closures_and_nll_borrows() {
    let src = "\
// 1. Disjoint overloads on `callable` (rank 2) vs `fn` (rank 3) and `closure` (rank 3):
pub fn callable_tag(comptime F: callable, self: &F) -> i32 {
    return 10;
}

pub fn callable_tag(comptime F: fn, self: &F) -> i32 {
    return 11;
}

pub fn invoke_callable(comptime F: callable, f: &mut F, x: i32) -> i32 {
    return f(x);
}

pub fn invoke_fn_only(comptime F: fn, f: F, x: i32) -> i32 {
    return f(x);
}

pub fn invoke_closure_only(comptime C: closure, c: &mut C, x: i32) -> i32 {
    return c(x);
}

// 2. Resource opaque with a `drop` hook to verify `move fn` automatic drop elaboration:
pub opaque ScopedAdd {
    target: &mut i32,
    delta: i32,

    pub fn new(t: &mut i32, d: i32) -> Self {
        return Self { target: t, delta: d };
    }

    pub fn bonus(self: &Self) -> i32 {
        return self.delta;
    }

    drop(self: &mut Self) {
        *self.target += self.delta;
    }
}

pub fn main() -> i32 {
    // A. Non-capturing lambda (`fn(i32) -> i32`) decays to bare function pointer (`fn` rank 3 > `callable` rank 2):
    let mut pure_lambda = fn(x: i32) -> i32 {
        return x * 3;
    };
    // `pure_lambda.callable_tag()` selects `fn` (rank 3) -> 11
    // `invoke_fn_only(pure_lambda, 4)` -> 12
    // `invoke_callable(&mut pure_lambda, 2)` -> 6
    let r_pure = pure_lambda.callable_tag()
        + invoke_fn_only(pure_lambda, 4)
        + invoke_callable(&mut pure_lambda, 2);

    // B. Automatic shared capture (`&factor`):
    let factor: i32 = 5;
    let mut scale = fn(x: i32) -> i32 {
        return x * factor;
    };
    // While `scale` holds a shared borrow `&factor`, reading `factor` in the outer scope is allowed!
    // `scale.callable_tag()` selects `callable` (rank 2, since `fn` rank 3 does not match `closure`) -> 10
    let r_shared = scale(3) + factor + scale.callable_tag() + invoke_callable(&mut scale, 2);

    // C. Automatic mutable capture (`&mut acc`) + NLL borrow release after last closure call:
    let mut acc: i32 = 10;
    let mut add_to_acc = fn(x: i32) -> i32 {
        acc += x;
        return acc;
    };
    let step1 = add_to_acc(7); // acc = 17
    let step2 = invoke_closure_only(&mut add_to_acc, 3); // acc = 20
    // After the last call to `add_to_acc`, NLL releases `&mut acc` so `acc` can be read & mutated directly:
    acc += 5; // acc = 25
    let r_mut = step1 + step2 + acc; // 17 + 20 + 25 = 62

    // D. `move fn` capturing an owned `ScopedAdd` struct with a `drop` hook:
    let mut drop_log: i32 = 0;
    let mut r_move: i32 = 0;
    if true {
        let guard = ScopedAdd::new(&mut drop_log, 19);
        let moved_closure = move fn(x: i32) -> i32 {
            return x + guard.bonus();
        };
        r_move = moved_closure(1); // 1 + 19 = 20
        // `moved_closure` goes out of scope here, running `ScopedAdd::drop` and adding 19 to `drop_log`!
    }

    // Total:
    //   r_pure   = 11 + 12 + 6 = 29
    //   r_shared = 15 + 5 + 10 + 10 = 40
    //   r_mut    = 17 + 20 + 25 = 62
    //   r_move   = 20
    //   drop_log = 19
    //   Sum = 29 + 40 + 62 + 20 + 19 = 170
    return r_pure + r_shared + r_mut + r_move + drop_log;
}
";

    let program = Compiler::compile_source(src)
        .expect("Failed to compile lambdas & automatic-capture closures test");
    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(170),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify that reading a mutably-captured variable BEFORE the last call to the closure is rejected by Stage 3 NLL borrow checking:
    let bad_conflict_src = "\
pub fn main() -> i32 {
    let mut total: i32 = 10;
    let bump = fn(x: i32) -> i32 {
        total += x;
        return total;
    };
    let illegal_read: i32 = total;
    let after = bump(5);
    return illegal_read + after;
}
";
    let err = Compiler::compile_source(bad_conflict_src).expect_err(
            "Expected reading `total` while mutably captured by live closure `bump` to fail borrow check",
        );
    assert!(
        err.contains("Borrow check error") && err.contains("mutably borrowed"),
        "Unexpected error: {err}"
    );

    // Verify that passing a stateful capturing `closure` to a function constrained by `comptime F: fn` is rejected:
    let bad_closure_as_fn = "\
pub fn require_stateless_fn(comptime F: fn, f: F) -> i32 {
    return f(1);
}

pub fn main() -> i32 {
    let k: i32 = 10;
    let cap = fn(x: i32) -> i32 {
        return x + k;
    };
    return require_stateless_fn(cap);
}
";
    let err2 = Compiler::compile_source(bad_closure_as_fn)
        .expect_err("Expected passing capturing closure to `comptime F: fn` to fail");
    assert!(
        err2.contains("No overload of 'require_stateless_fn'"),
        "Unexpected error: {err2}"
    );
}

#[test]
fn test_slices_range_slicing_sequence_metatype_and_nll_borrows() {
    let src = "\
// 1. Generic function over `sequence` (`array` | `slice`) using `.len` and `s[i]`:
pub fn sum_seq(comptime S: sequence, s: &S) -> i32 {
    let mut i: usize = 0;
    let mut total: i32 = 0;
    while i < s.len {
        total += s[i];
        i += 1;
    }
    return total;
}

// 2. Specificity ranking between `sequence` (rank 2) and `slice` (rank 3):
pub fn seq_tag(comptime S: sequence, self: &S) -> i32 {
    return 20;
}

pub fn seq_tag(comptime S: slice, self: &S) -> i32 {
    return 30;
}

// 3. Function taking a slice `&[T]` directly (inferring `T` from either `&[T]` or `&[T; N]`):
pub fn first_plus_len(comptime T: integer, s: &[T]) -> T {
    return s[0] + (s.len as T);
}

// 4. Function mutating through `&mut [i32]`:
pub fn bump_slice(s: &mut [i32], delta: i32) {
    let mut i: usize = 0;
    while i < s.len {
        s[i] += delta;
        i += 1;
    }
}

pub fn main() -> i32 {
    let mut arr: [i32; 5] = [i32; 5] { 2, 4, 6, 8, 10 };

    // A. `sum_seq` on fixed-length `array` (`[i32; 5]`): 2 + 4 + 6 + 8 + 10 = 30
    let sum_arr = sum_seq(&arr);
    // `arr.seq_tag()` matches `sequence` (rank 2) -> 20
    let tag_arr = arr.seq_tag();

    // B. Coerce `&arr` (`&[i32; 5]`) to `&[i32]` and range-slice `&arr[1..4]` (`{4, 6, 8}`):
    let full_slice: &[i32] = &arr;
    let mid_slice: &[i32] = &arr[1..4];
    // `mid_slice` has elements {4, 6, 8} -> sum_seq = 18, seq_tag (`slice` rank 3 > `sequence` rank 2) = 30
    let sum_mid = sum_seq(&mid_slice);
    let tag_slice = mid_slice.seq_tag();

    // C. Sub-slicing an existing slice (`mid_slice[1..3]` -> `{6, 8}`) and `first_plus_len`:
    let sub_slice: &[i32] = mid_slice[1..3];
    // `sub_slice[0]` = 6, `sub_slice.len` = 2 -> `first_plus_len(sub_slice)` = 8
    // Also pass `&arr` directly to `first_plus_len(&arr)` -> `arr[0]` (2) + 5 = 7
    let sub_val = first_plus_len(sub_slice) + first_plus_len(&arr) + (full_slice.len as i32); // 8 + 7 + 5 = 20

    // D. After the last read of `full_slice`, `mid_slice`, and `sub_slice`, NLL releases the shared borrows on `arr`!
    //    Now take a mutable range slice `&mut arr[1..4]` and mutate through it:
    let mut_mid: &mut [i32] = &mut arr[1..4];
    bump_slice(mut_mid, 3); // arr[1..4] becomes {7, 9, 11}
    mut_mid[0] += 1;        // arr[1] becomes 8

    // After the last use of `mut_mid`, NLL releases the mutable borrow on `arr`, allowing direct access:
    // `arr` is now {2, 8, 9, 11, 10} -> sum_seq(&arr) = 40
    let sum_after = sum_seq(&arr);

    // Total:
    //   sum_arr   = 30
    //   tag_arr   = 20
    //   sum_mid   = 18
    //   tag_slice = 30
    //   sub_val   = 20
    //   sum_after = 40
    //   Sum = 30 + 20 + 18 + 30 + 20 + 40 = 158
    return sum_arr + tag_arr + sum_mid + tag_slice + sub_val + sum_after;
}
";

    let program =
        Compiler::compile_source(src).expect("Failed to compile slices & sequence meta-type test");
    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(158),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify Stage 3 NLL borrow checker rejects mutating `arr` while a slice `s` (or sub-slice `sub`) is still live:
    let bad_mutate_while_sliced = "\
pub fn main() -> i32 {
    let mut arr: [i32; 4] = [i32; 4] { 1, 2, 3, 4 };
    let s: &[i32] = &arr[1..3];
    let sub: &[i32] = s[0..1];
    arr[2] = 99;
    return sub[0];
}
";
    let err1 = Compiler::compile_source(bad_mutate_while_sliced).expect_err(
        "Expected mutating `arr` while sub-slice `sub` is live to fail NLL borrow check",
    );
    assert!(
        err1.contains("Borrow check error") && err1.contains("currently borrowed"),
        "Unexpected error: {err1}"
    );

    // Verify Stage 3 NLL borrow checker rejects mutating through an immutable `&[i32]` slice:
    let bad_write_immutable_slice = "\
pub fn main() -> i32 {
    let mut arr: [i32; 3] = [i32; 3] { 10, 20, 30 };
    let s: &[i32] = &arr[0..2];
    s[0] = 99;
    return s[0];
}
";
    let err2 = Compiler::compile_source(bad_write_immutable_slice)
        .expect_err("Expected writing through immutable slice `&[i32]` to fail borrow check");
    assert!(
        err2.contains("through an immutable reference"),
        "Unexpected error: {err2}"
    );
}

#[test]
fn test_core_and_std_library_prelude_and_no_std() {
    use crate::lower::Compiler;

    // 1. Hosted mode (`std::prelude::*` injected automatically; zero `import` or `extern fn` needed):
    let hosted_src = r"
pub fn main() -> i32 {
    // `core::math` & `core::cmp` from prelude
    let neg: i32 = -15;
    let raw: i32 = 25;
    let a: i32 = neg.abs();
    let b: i32 = raw.clamp(0, 10);
    let c: i32 = min(a, b);
    let d: i32 = max(a, b);

    // `core::mem` from prelude
    let mut x: i32 = 10;
    let mut y: i32 = 20;
    swap(&mut x, &mut y);
    let old_x = replace(&mut x, 50);

    // `core::slice` & `core::option` from prelude
    let arr: [i32; 3] = {7, 8, 9};
    let s: &[i32] = &arr;
    let first_opt: ?i32 = s.first();
    let last_opt: ?i32 = s.last();
    let first_val = first_opt orelse 0;
    let last_val = last_opt orelse 0;
    let empty_check = !arr.is_empty() && first_opt.is_some() && !last_opt.is_none();

    // `std::mem::Box(T)` from prelude (heap-allocated with automatic `free` on scope exit)
    let mut boxed = Box(i32)::new(30);
    let p: &mut i32 = boxed.get_mut();
    *p = *p + 12;
    let box_val: i32 = *boxed.get();

    // `std::sync::Mutex(T)` and `std::thread::spawn_scoped` from prelude
    let mtx = Mutex(i32)::new(box_val);
    let worker = spawn_scoped(fn() -> i32 {
        return mtx.with_lock(fn(v: &mut i32) -> i32 {
            *v = *v + 8;
            return *v;
        });
    });
    let worker_res = worker.join();
    let final_mtx = mtx.with_lock(fn(v: &mut i32) -> i32 { return *v; });

    if a == 15
        && b == 10
        && c == 10
        && d == 15
        && x == 50
        && y == 10
        && old_x == 20
        && first_val == 7
        && last_val == 9
        && empty_check
        && box_val == 42
        && worker_res == 50
        && final_mtx == 50
    {
        return 42;
    }
    return 1;
}
";
    let program = Compiler::compile_source(hosted_src)
        .expect("Failed to compile zero-import hosted std::prelude program");
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

    let tmp_path = std::env::temp_dir().join("lrrr_stdlib_prelude_test.ll");
    std::fs::write(&tmp_path, &llvm_ir).unwrap();
    let output = std::process::Command::new("lli")
        .arg(&tmp_path)
        .output()
        .expect("Failed to execute lli");
    assert_eq!(
        output.status.code(),
        Some(42),
        "Expected exit code 42 from lli, got {:?}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    // 2. Explicit stdlib module imports (`import core::math;`) & lexical shadowing of prelude items:
    let shadowing_src = r"
import core::math;

// Local definition cleanly shadows `std::prelude::min` without ambiguity
fn min(a: i32, b: i32) -> i32 {
    return a + b;
}

pub fn main() -> i32 {
    let custom = min(10, 20);
    let std_min = core::cmp::min(10, 20);
    let m = math::abs(-12);
    if custom == 30 && std_min == 10 && m == 12 {
        return 0;
    }
    return 1;
}
";
    let shadow_prog = Compiler::compile_source(shadowing_src)
        .expect("Failed to compile lexical prelude shadowing program");
    assert!(
        shadow_prog.externs.is_empty(),
        "Expected zero extern declarations when no OS/libc std functions are referenced, got {:?}",
        shadow_prog.externs
    );

    // 3. Freestanding `no_std` mode (`Compiler::compile_source_no_std`):
    //    `core::prelude::*` is available, while `std::*` (`Box`, `Mutex`, `spawn_scoped`) is absent.
    let no_std_ok_src = r"
pub fn main() -> i32 {
    let n: i32 = -7;
    let r: i32 = 99;
    let mut a: i32 = n.abs();
    let mut b: i32 = r.clamp(0, 5);
    swap(&mut a, &mut b);
    if a == 5 && b == 7 {
        return 0;
    }
    return 1;
}
";
    Compiler::compile_source_no_std(no_std_ok_src)
        .expect("Expected `no_std` program using `core::prelude` to compile cleanly");

    let no_std_err_src = r"
pub fn main() -> i32 {
    let b = Box(i32)::new(1);
    return *b.get();
}
";
    let err = Compiler::compile_source_no_std(no_std_err_src)
        .expect_err("Expected `Box` from `std` to be unavailable in `no_std` mode");
    assert!(
        err.contains("Undefined symbol 'Box'"),
        "Unexpected error in no_std mode: {err}"
    );
}

#[test]
fn test_string_formatting_fstrings_transparent_vs_struct_and_specifiers() {
    use crate::lower::Compiler;

    let src = r#"
pub struct Point {
    x: i32,
    y: i32,
}

pub enum Status {
    Ok = 0,
    Pending = 1,
}

pub opaque Ipv4Addr {
    octets: [u8; 4],

    format(self: &Self, f: &mut Formatter) {
        f.write(f"{self.octets[0]}.{self.octets[1]}.{self.octets[2]}.{self.octets[3]}");
    }

    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Self {
        return Self {
            octets: { a, b, c, d },
        };
    }
}

pub opaque TagId {
    id: u32,

    format(self: &Self, f: &mut Formatter, spec: &str) {
        if str_eq(spec, "x") {
            f.write(f"id(0x{self.id:04x})");
        } else {
            f.write(f"id({self.id})");
        }
    }

    pub fn new(id: u32) -> Self {
        return Self { id: id };
    }
}

pub fn main() -> i32 {
    // 1. Primitives & inline format specifiers (`:x`, `:04X`, `:08b`, `:o`, `:?`, `:.2`, `{{` / `}}`)
    let name: &str = "Alice";
    let ch: rune = 'A';
    let hex_v: u32 = 255;
    let bin_v: u8 = 10;
    let oct_v: u32 = 15;
    let neg_v: i32 = -42;
    let pi: f64 = 3.14159;

    let mut buf1: [u8; 256] = @default([u8; 256]);
    let s1: &str = fmt_buf(
        &mut buf1,
        f"{{name={name:?}, ch={ch:?}, hex={hex_v:04x}/{hex_v:04X}, bin={bin_v:08b}, oct={oct_v:o}, neg={neg_v:4}, pi={pi:.2}}}"
    );
    let ok1 = str_eq(
        s1,
        "{name=\"Alice\", ch='A', hex=00ff/00FF, bin=00001010, oct=17, neg= -42, pi=3.14}"
    );

    // 2. Auto-formatting of transparent types (`struct`, `tuple`, `[T; N]`, `&[T]`, `?T`, `enum`)
    let pt = Point { x: 10, y: 20 };
    let tup: tuple { i32, bool } = { 7, true };
    let arr: [i32; 3] = { 1, 2, 3 };
    let sl: &[i32] = &arr[1..3];
    let opt_some: ?i32 = 99;
    let opt_none: ?i32 = null;
    let st: Status = Status::Pending;

    let mut buf2: [u8; 256] = @default([u8; 256]);
    let s2: &str = fmt_buf(
        &mut buf2,
        f"pt={pt} tup={tup} arr={arr} sl={sl} some={opt_some} none={opt_none} st={st}({st:d})"
    );
    let ok2 = str_eq(
        s2,
        "pt=Point { x: 10, y: 20 } tup={ 7, true } arr=[1, 2, 3] sl=[2, 3] some=99 none=null st=Status::Pending(1)"
    );

    // 3. Encapsulated `opaque` with lowercase `format` hook (2-param & 3-param `spec`) + nested lazy `f"..."` + heap `String`
    let ip = Ipv4Addr::new(127, 0, 0, 1);
    let tag = TagId::new(255);
    let mut port: u16 = 8080;
    let endpoint = f"{ip}:{port}";
    let full_msg = f"connect({endpoint}) [{tag} / {tag:x}]";
    let owned: String = format(full_msg);
    // Once `format(full_msg)` finishes, NLL borrow of `port` ends so `port` can be mutated!
    port = 9090;

    let mut buf3: [u8; 256] = @default([u8; 256]);
    let s3: &str = fmt_buf(&mut buf3, f"{owned} next_port={port}");
    let ok3 = str_eq(
        s3,
        "connect(127.0.0.1:8080) [id(255) / id(0x00ff)] next_port=9090"
    );

    if ok1 && ok2 && ok3 {
        return 42;
    }
    return 1;
}
"#;
    let program =
        Compiler::compile_source(src).expect("Failed to compile string formatting program");
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

    let tmp_path = std::env::temp_dir().join("lrrr_string_formatting_test.ll");
    std::fs::write(&tmp_path, &llvm_ir).unwrap();
    let output = std::process::Command::new("lli")
        .arg(&tmp_path)
        .output()
        .expect("Failed to execute lli");
    assert_eq!(
        output.status.code(),
        Some(42),
        "Expected exit code 42 from lli, got {:?}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    // Negative Test 1: Defining a `format` hook on a transparent `struct` is forbidden at compile time
    let bad_record_format_src = r#"
pub struct Point {
    x: i32,
    y: i32,
    format(self: &Self, f: &mut Formatter) {
        f.write_str("custom");
    }
}
pub fn main() -> i32 { return 0; }
"#;
    let err1 = Compiler::compile_source(bad_record_format_src)
        .expect_err("Expected defining `format` hook on transparent `struct` to be rejected");
    assert!(
        err1.contains("Lifecycle hook 'format' is forbidden on transparent 'struct' types"),
        "Unexpected error: {err1}"
    );

    // Negative Test 2: Interpolating an encapsulated `opaque` that has no `format` hook is rejected at compile time
    let bad_struct_no_format_src = r#"
pub opaque SecretKey {
    raw: u64,
    pub fn new(raw: u64) -> Self { return Self { raw: raw }; }
}
pub fn main() -> i32 {
    let k = SecretKey::new(12345);
    let _msg = f"secret={k}";
    return 0;
}
"#;
    let err2 = Compiler::compile_source(bad_struct_no_format_src)
        .expect_err("Expected formatting an `opaque` without a `format` hook to be rejected");
    assert!(
        err2.contains("Struct 'SecretKey' does not define a 'format' hook"),
        "Unexpected error: {err2}"
    );

    // Negative Test 3: Stage 3c NLL borrow checker rejects mutating a variable while a lazy `f"..."` borrowing it is still live
    let bad_nll_mutation_while_borrowed_src = r#"
pub fn main() -> i32 {
    let mut x: i32 = 10;
    let lazy = f"val={x}";
    x = 20;
    let _s = format(lazy);
    return 0;
}
"#;
    let err3 = Compiler::compile_source(bad_nll_mutation_while_borrowed_src)
            .expect_err("Expected mutating `x` while `lazy = f\"val={x}\"` is live to fail Stage 3c NLL borrow check");
    assert!(
        err3.contains("Borrow check error") && err3.contains("borrowed"),
        "Unexpected error: {err3}"
    );
}

#[test]
fn test_unified_error_adhoc_unions_try_catch_and_match() {
    // 1. Positive end-to-end test:
    //    - Unified `error` declarations (unit leaves, payload leaves, inline struct leaves, embedded error types)
    //    - Ad-hoc error unions `IoError || DbError` and `DbError || IoError` (algebraic commutativity/idempotence + conflicting `Timeout` leaves)
    //    - `E!T` result types, `try` automatic widening, `catch` / `catch |err|`, `match` with leaf and subtype group narrowing
    //    - Tagged `union` declarations and `match`
    //    - Automatic formatting of `error`, `union`, and `E!T`
    let valid_src = r#"
pub error IoError {
    Timeout,
    NotFound,
}

pub error DbError {
    Timeout,
    Deadlock(u32),
}

pub error ParseError {
    UnexpectedToken: u32,
    Eof,
}

pub error ConfigError {
    IoError,
    ParseError,
    SyntaxError: struct {
        line: u32,
        col: u32,
    },
}

pub union Shape {
    Unit,
    Circle(i32),
    Rect: struct {
        w: i32,
        h: i32,
    },
}

fn read_io(mode: i32) -> IoError!i32 {
    if mode == 1 {
        return IoError::Timeout;
    }
    if mode == 2 {
        return IoError::NotFound;
    }
    return 10;
}

fn query_db(mode: i32) -> DbError!i32 {
    if mode == 1 {
        return DbError::Timeout;
    }
    if mode == 2 {
        return DbError::Deadlock(7);
    }
    return 20;
}

// `IoError || DbError` and `DbError || IoError` are the exact same canonical error set:
fn fetch_ab(io_mode: i32, db_mode: i32) -> (IoError || DbError)!i32 {
    let a: i32 = try read_io(io_mode);
    let b: i32 = try query_db(db_mode);
    return a + b;
}

fn fetch_ba(io_mode: i32, db_mode: i32) -> (DbError || IoError)!i32 {
    return try fetch_ab(io_mode, db_mode);
}

fn load_config(mode: i32) -> ConfigError!i32 {
    if mode == 1 {
        return try read_io(1);
    }
    if mode == 2 {
        return ParseError::UnexpectedToken(99);
    }
    if mode == 3 {
        return ConfigError::SyntaxError { line: 4, col: 12 };
    }
    return 50;
}

fn area(s: Shape) -> i32 {
    return match s {
        Shape::Unit => 0,
        Shape::Circle(r) => r * r,
        Shape::Rect(rect) => rect.w * rect.h,
    };
}

pub fn main() -> i32 {
    // 1. Happy path through `try` and `catch`:
    let ok_sum: i32 = fetch_ba(0, 0) catch -1;
    if ok_sum != 30 {
        return 1;
    }

    // 2. Conflicting variant names (`IoError::Timeout` vs `DbError::Timeout`) preserved distinctly:
    let err_io_code: i32 = fetch_ba(1, 0) catch |err| match err {
        IoError::Timeout => 101,
        IoError::NotFound => 102,
        DbError::Timeout => 201,
        DbError::Deadlock(code) => (200 + code) as i32,
    };
    if err_io_code != 101 {
        return 2;
    }

    let err_db_code: i32 = fetch_ab(0, 1) catch |err| match err {
        IoError::Timeout => 101,
        IoError::NotFound => 102,
        DbError::Timeout => 201,
        DbError::Deadlock(code) => (200 + code) as i32,
    };
    if err_db_code != 201 {
        return 3;
    }

    // 3. Subtype group matching (`IoError(io_err) => ...` and `DbError(db_err) => ...`):
    let group_code: i32 = fetch_ab(0, 2) catch |err| match err {
        IoError(io_err) => match io_err {
            IoError::Timeout => 10,
            IoError::NotFound => 20,
        },
        DbError(db_err) => match db_err {
            DbError::Timeout => 30,
            DbError::Deadlock(c) => (40 + c) as i32,
        },
    };
    if group_code != 47 {
        return 4;
    }

    // 4. Hierarchical `ConfigError` with payload and inline record variant:
    let cfg2: i32 = load_config(2) catch |err| match err {
        IoError(_) => 1,
        ParseError::UnexpectedToken(tok) => tok as i32,
        ParseError::Eof => 2,
        ConfigError::SyntaxError(syn) => (syn.line * 10 + syn.col) as i32,
    };
    if cfg2 != 99 {
        return 5;
    }

    let cfg3: i32 = load_config(3) catch |err| match err {
        IoError(_) => 1,
        ParseError(_) => 2,
        ConfigError::SyntaxError(syn) => (syn.line * 10 + syn.col) as i32,
    };
    if cfg3 != 52 {
        return 6;
    }

    // 5. General `union` construction and `match`:
    let s1 = Shape::Circle(3);
    let s2 = Shape::Rect { w: 4, h: 5 };
    if area(s1) + area(s2) != 29 {
        return 7;
    }

    // 6. Automatic string formatting of `error`:
    let e_val: IoError = IoError::Timeout;
    let mut buf: [u8; 64] = @default([u8; 64]);
    let formatted: &str = fmt_buf(&mut buf, f"{e_val}");
    if !str_eq(formatted, "IoError::Timeout") {
        return 8;
    }

    return 42;
}
"#;
    let program = Compiler::compile_source(valid_src)
        .expect("Expected unified error, ad-hoc unions, try/catch, and match to compile");
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");
    let tmp_path = std::env::temp_dir().join("lrrr_unified_error_test.ll");
    std::fs::write(&tmp_path, &llvm_ir).unwrap();
    let output = std::process::Command::new("lli")
        .arg(&tmp_path)
        .output()
        .expect("Failed to execute lli");
    let _ = std::fs::remove_file(&tmp_path);
    assert_eq!(
        output.status.code(),
        Some(42),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // 2. Negative test: explicit integer discriminant `= 1` on `error` is rejected:
    let explicit_disc_src = r#"
pub error BadError {
    Timeout = 1,
}
pub fn main() -> i32 { return 0; }
"#;
    let err1 = Compiler::compile_source(explicit_disc_src)
        .expect_err("Expected explicit discriminant on `error` to be rejected");
    assert!(
        err1.contains("Explicit integer discriminants ('= N') are forbidden on 'error'"),
        "Unexpected error: {err1}"
    );

    // 3. Negative test: explicit backing integer type `error(u8)` is rejected:
    let backing_ty_src = r#"
pub error(u8) BadError {
    Timeout,
}
pub fn main() -> i32 { return 0; }
"#;
    let err2 = Compiler::compile_source(backing_ty_src)
        .expect_err("Expected backing type on `error` to be rejected");
    assert!(
        err2.contains("Explicit backing integer types ('error(...)') are forbidden"),
        "Unexpected error: {err2}"
    );

    // 4. Negative test: non-exhaustive `match` on `error` is rejected:
    let non_exhaustive_src = r#"
pub error IoError {
    Timeout,
    NotFound,
}
pub fn main() -> i32 {
    let e: IoError = IoError::Timeout;
    return match e {
        IoError::Timeout => 1,
    };
}
"#;
    let err3 = Compiler::compile_source(non_exhaustive_src)
        .expect_err("Expected non-exhaustive match on `IoError` to be rejected");
    assert!(
        err3.contains("Non-exhaustive `match` on error type") && err3.contains("IoError::NotFound"),
        "Unexpected error: {err3}"
    );

    // 5. Negative test: `try` on incompatible error set is rejected:
    let incompatible_try_src = r#"
pub error IoError { Timeout }
pub error DbError { Deadlock }
fn fail_db() -> DbError!i32 {
    return DbError::Deadlock;
}
fn caller() -> IoError!i32 {
    return try fail_db();
}
pub fn main() -> i32 { return 0; }
"#;
    let err4 = Compiler::compile_source(incompatible_try_src)
        .expect_err("Expected `try` with incompatible error set to be rejected");
    assert!(
        err4.contains(
            "Error type 'DbError' is not a subset of 'IoError': missing variant 'DbError::Deadlock'"
        ),
        "Unexpected error: {err4}"
    );
}

#[test]
fn test_traits_static_bounds_and_dynamic_dispatch_fat_pointers() {
    use crate::llvm::LlvmLowering;
    use crate::lower::Compiler;
    use crate::vm::{Value, Vm};

    // 1. End-to-end positive test:
    //    - `pub trait Name { ... }`, `type Name = trait { ... };`, and `fn From(comptime Src: type) -> trait`
    //    - Static `comptime` bounds: `comptime T: Trait`, `comptime T: A + B`, `comptime T: From(i32)`
    //    - Static monomorphized calls (`a: T`, `a: &T`) and `comptime a: &Trait`
    //    - Dynamic dispatch via `&Trait` and `&mut Trait` fat pointers (without `dyn`), including
    //      coercing `&T` -> `&Trait`, `&mut T` -> `&mut Trait`, `&mut Trait` -> `&Trait`, and reborrowing
    let valid_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
    fn add(self: &mut Self, delta: i32);
}

type Describable = trait {
    fn code(self: &Self) -> i32;
};

pub fn ScaleBy(comptime Factor: type) -> trait {
    return trait {
        fn scale(self: &Self, k: Factor) -> i32;
    };
}

// Non-object-safe trait (takes `self: Self` by value and returns `Self`) — valid for `comptime T: Doubler`
pub trait Doubler {
    fn doubled(self: Self) -> Self;
}

pub struct StepCounter {
    val: i32,
    step: i32,

    pub fn get(self: &Self) -> i32 {
        return self.val;
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.val = self.val + delta * self.step;
    }

    pub fn doubled(self: Self) -> Self {
        return Self { val: self.val * 2, step: self.step };
    }
}

// Extension methods in the same module satisfying `Describable` and `ScaleBy(i32)` for `StepCounter`
pub fn code(self: &StepCounter) -> i32 {
    return self.val + 100;
}

pub fn scale(self: &StepCounter, k: i32) -> i32 {
    return self.val * k;
}

pub struct SimpleBox {
    n: i32,

    pub fn get(self: &Self) -> i32 {
        return self.n;
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.n = self.n + delta;
    }
}

// Static dispatch with single trait bound (by value and by reference)
fn static_read(comptime T: Counter, c: &T) -> i32 {
    return c.get();
}

fn static_double(comptime T: Doubler, v: T) -> T {
    return v.doubled();
}

// Static dispatch with multi-trait `+` bounds and parameterized trait `ScaleBy(i32)`
fn static_combo(comptime T: Counter + Describable + ScaleBy(i32), c: &T) -> i32 {
    return c.get() + c.code() + c.scale(3);
}

// Compile-time constant trait reference (`comptime a: &Counter`) — no runtime vtable
fn eval_const_counter(comptime c: &Counter) -> i32 {
    return c.get() + 5;
}

// Dynamic dispatch via `&Counter` and `&mut Counter` fat pointers (no `dyn` keyword)
fn dyn_read(c: &Counter) -> i32 {
    return c.get();
}

fn dyn_bump_and_read(c: &mut Counter, delta: i32) -> i32 {
    c.add(delta);
    // Automatic reborrow / coercion of `&mut Counter` -> `&Counter`
    return dyn_read(c);
}

pub fn main() -> i32 {
    let mut sc = StepCounter { val: 10, step: 2 };
    let mut sb = SimpleBox { n: 7 };

    // 1. Static dispatch (inferred `T` and explicit `T`)
    if static_read(&sc) != 10 {
        return 1;
    }
    if static_read(SimpleBox, &sb) != 7 {
        return 2;
    }
    let sc2 = static_double(sc);
    if sc2.val != 20 {
        return 3;
    }

    // 2. Multi-trait `+` bounds + generic trait `ScaleBy(i32)`
    // 10 + (10 + 100) + (10 * 3) = 150
    if static_combo(&sc) != 150 {
        return 4;
    }

    // 3. `comptime c: &Counter`
    let ct_res = eval_const_counter(&StepCounter { val: 37, step: 1 });
    if ct_res != 42 {
        return 5;
    }

    // 4. Dynamic dispatch through `&Counter` and `&mut Counter` over heterogeneous types
    if dyn_bump_and_read(&mut sc, 5) != 20 {
        return 6;
    }
    if dyn_bump_and_read(&mut sb, 5) != 12 {
        return 7;
    }

    let dyn_ref: &Counter = &sc;
    if dyn_ref.get() != 20 {
        return 8;
    }

    return 42;
}
"#;
    let mut program = Compiler::compile_source(valid_src)
        .expect("Expected valid traits program (static + dynamic dispatch) to compile");

    // Verify execution on Stage 3 VM
    let main_fn = program
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret =
        Vm::eval(&mut program, main_fn, Vec::new()).expect("VM execution of traits program failed");
    assert_eq!(vm_ret, Value::Int(42));

    // Verify execution on Stage 4 LLVM (`lli`)
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower traits program to LLVM IR");
    let tmp_path = std::env::temp_dir().join("lrrr_traits_test.ll");
    std::fs::write(&tmp_path, &llvm_ir).unwrap();
    let output = std::process::Command::new("lli")
        .arg(&tmp_path)
        .output()
        .expect("Failed to execute lli");
    let _ = std::fs::remove_file(&tmp_path);
    assert_eq!(
        output.status.code(),
        Some(42),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // 2. Negative test: bare `fn bad(a: Counter)` by value is rejected:
    let bare_param_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
}
fn bad(a: Counter) -> i32 {
    return 0;
}
pub fn main() -> i32 { return 0; }
"#;
    let err_bare = Compiler::compile_source(bare_param_src)
        .expect_err("Expected bare trait parameter by value to be rejected");
    assert!(
        err_bare.contains(
            "Trait 'Counter' is an unsized meta-type constraint and cannot be passed by value"
        ),
        "Unexpected error: {err_bare}"
    );

    // 3. Negative test: calling `&mut Self` trait method on shared `&Counter` is rejected:
    let mut_on_shared_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
    fn add(self: &mut Self, delta: i32);
}
fn bad(c: &Counter) {
    c.add(1);
}
pub fn main() -> i32 { return 0; }
"#;
    let err_mut = Compiler::compile_source(mut_on_shared_src)
        .expect_err("Expected calling `&mut Self` method on `&Counter` to be rejected");
    assert!(
        err_mut.contains(
            "Cannot call '&mut Self' method 'Counter.add' on shared trait object '&Counter'"
        ),
        "Unexpected error: {err_mut}"
    );

    // 4. Negative test: coercing immutable `&T` to `&mut Counter` is rejected:
    let immut_to_mut_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
}
pub struct Boxed {
    v: i32,
    pub fn get(self: &Self) -> i32 { return self.v; }
}
fn take_mut(c: &mut Counter) -> i32 {
    return c.get();
}
pub fn main() -> i32 {
    let b = Boxed { v: 1 };
    return take_mut(&b);
}
"#;
    let err_immut = Compiler::compile_source(immut_to_mut_src)
        .expect_err("Expected coercing `&Boxed` to `&mut Counter` to be rejected");
    assert!(
        err_immut.contains(
            "Cannot coerce immutable reference '&Boxed' to mutable trait object '&mut Counter'"
        ),
        "Unexpected error: {err_immut}"
    );

    // 5. Negative test: non-object-safe trait (`self: Self` by value or returning `Self`) cannot form `&Trait`:
    let obj_safety_src = r#"
pub trait Cloneable {
    fn duplicate(self: &Self) -> Self;
}
fn bad(c: &Cloneable) -> i32 {
    return 0;
}
pub fn main() -> i32 { return 0; }
"#;
    let err_obj_safety = Compiler::compile_source(obj_safety_src)
        .expect_err("Expected non-object-safe trait to be rejected when forming `&Cloneable`");
    assert!(
        err_obj_safety
            .contains("Trait 'Cloneable' is not object-safe and cannot form '&Cloneable'"),
        "Unexpected error: {err_obj_safety}"
    );

    // 6. Negative test: built-in structural constraint `&number` cannot be used as a dynamic trait object:
    let builtin_obj_src = r#"
fn bad(x: &number) -> i32 {
    return 0;
}
pub fn main() -> i32 { return 0; }
"#;
    let err_builtin =
        Compiler::compile_source(builtin_obj_src).expect_err("Expected `&number` to be rejected");
    assert!(
            err_builtin.contains("Built-in meta-type constraint 'number' cannot be used as a dynamic trait object '&number'"),
            "Unexpected error: {err_builtin}"
        );

    // 7. Negative test: Orphan rule coherence violation across modules:
    let trait_mod_src = r#"
pub trait Hasher {
    fn hash_val(self: &Self) -> i32;
}
pub fn compute_hash(comptime T: Hasher, x: &T) -> i32 {
    return x.hash_val();
}
"#;
    let type_mod_src = r#"
pub struct ForeignKey {
    id: i32,
}
"#;
    let root_orphan_src = r#"
import root::trait_mod::{Hasher, compute_hash};
import root::type_mod::ForeignKey;

// Orphan extension method in `root` (neither `root::trait_mod` nor `root::type_mod`)
pub fn hash_val(self: &ForeignKey) -> i32 {
    return self.id;
}

pub fn main() -> i32 {
    let k = ForeignKey { id: 7 };
    return compute_hash(&k);
}
"#;
    let err_orphan = Compiler::compile_package(&[
        ("root::trait_mod", trait_mod_src),
        ("root::type_mod", type_mod_src),
        ("root", root_orphan_src),
    ])
    .expect_err(
        "Expected orphan extension method satisfying foreign trait for foreign type to be rejected",
    );
    assert!(
        err_orphan.contains("Orphan rule violation"),
        "Unexpected error: {err_orphan}"
    );

    // 8. Negative test: NLL borrow checker tracks loan through `&Counter` trait object fat pointer:
    let nll_trait_obj_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
}
pub struct Val {
    n: i32,
    pub fn get(self: &Self) -> i32 { return self.n; }
}
pub fn main() -> i32 {
    let mut v = Val { n: 10 };
    let obj: &Counter = &v;
    v = Val { n: 20 };
    return obj.get();
}
"#;
    let err_nll = Compiler::compile_source(nll_trait_obj_src).expect_err(
        "Expected NLL borrow checker to reject mutating `v` while `obj: &Counter` is live",
    );
    assert!(
        err_nll.contains("because it is currently borrowed"),
        "Unexpected error: {err_nll}"
    );
}
