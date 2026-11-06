
use crate::llvm::LlvmLowering;
use crate::lower::Compiler;
use super::lli;

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
            err.contains("Cannot access private field 'hidden' of opaque 'Secret' outside its 'opaque { ... }' block"),
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
            err.contains("Cannot call private method 'internal_only' of 'Secret' outside its block"),
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
alias Percent = u8 in 0..=100;

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
    
    

    let types_mod = "\
pub struct Point {
    x: i32,
    y: i32,

    pub fn sum(self: &Self) -> i32 {
        return self.x + self.y;
    }
}

pub fn Pair[T] -> type {
    return struct {
        first: T,
        second: T,
    };
}
";

    let simd_ext_mod = "\
import root::types::Pair;

// Extension on built-in comptime-parameterized `simd[T; N]`
pub fn first_lane[T: number, N: usize](self: &simd[T; N]) -> T {
    return self[0];
}

// Extension on user-defined comptime-parameterized `Pair[T]`
pub fn dot[T: number](self: &Pair[T], other: &Pair[T]) -> T {
    return self.first * other.first + self.second * other.second;
}

// Parameterized specificity (score = 2) vs concrete specificity (score = 3)
pub fn tag_rank[T](self: &Pair[T]) -> i32 {
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

// Concrete extension on `Pair[i32]` (specificity 3 > parameterized `tag_rank[comptime T](&Pair[T])` specificity 2)
fn tag_rank(self: &Pair[i32]) -> i32 {
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

    let p1 = Pair[i32]{ first: 2, second: 3 };
    let p2 = Pair[i32]{ first: 4, second: 5 };
    let d = p1.dot(&p2);         // Infers T = i32 -> 2*4 + 3*5 = 23
    let r = p1.tag_rank();       // Concrete `Pair[i32]` wins over `Pair[T]` -> 25

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
    let output = lli(&llvm_ir);
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
    
    

    let num_mod = "\
// 1. `number` matches both `integer` and `float`
pub fn clamp[N: number](self: N, lo: N, hi: N) -> N {
    if self < lo {
        return lo;
    }
    if self > hi {
        return hi;
    }
    return self;
}

// 2. Disjoint overloads on `signed` vs `float` sharing the name `abs`
pub fn abs[S: signed](self: S) -> S {
    if self < 0 {
        return -self;
    }
    return self;
}

pub fn abs[F: float](self: F) -> F {
    if self < 0.0 {
        return -self;
    }
    return self;
}

// 3. `integer` matches both `signed` (`i32`) and arbitrary-width `unsigned` (`u24`)
pub fn low_nibble[I: integer](self: I) -> I {
    return self & 15;
}

// 4. Full hierarchy specificity ladder: `unsigned` (4) > `integer` (3) > `number` (2) > `type` (1)
pub fn tier_rank[T](self: T) -> i32 {
    return 1;
}

pub fn tier_rank[N: number](self: N) -> i32 {
    return 2;
}

pub fn tier_rank[I: integer](self: I) -> i32 {
    return 3;
}

pub fn tier_rank[U: unsigned](self: U) -> i32 {
    return 4;
}
";

    let root_mod = "\
import root::num::*;

struct Dummy {
    v: i32,
}

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
    let output = lli(&llvm_ir);
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

struct Dummy {
    v: i32,
}

pub fn main() -> i32 {
    let d = Dummy { v: 1 };
    let res = clamp[Dummy](d, d, d);
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
pub fn open_score[A: aggregate](self: &A) -> i32 {
    return 10;
}

pub fn open_score[S: opaque](self: &S) -> i32 {
    return 1;
}

// 2. Specificity ranking across `scalar`, `number`, and `aggregate`:
//    - `number` (rank 3) overrides `scalar` (rank 2), while `bool` and `rune` match `scalar` (rank 2)
//    - `struct` (rank 3) and `tuple` (rank 3) override `aggregate` (rank 2)
pub fn kind_code[T](self: &T) -> i32 {
    return 0;
}

pub fn kind_code[Sc: scalar](self: &Sc) -> i32 {
    return 11;
}

pub fn kind_code[N: number](self: &N) -> i32 {
    return 12;
}

pub fn kind_code[F: fn](self: &F) -> i32 {
    return 13;
}

pub fn kind_code[Cal: callable](self: &Cal) -> i32 {
    return 14;
}

pub fn kind_code[Cl: closure](self: &Cl) -> i32 {
    return 15;
}

pub fn kind_code[A: aggregate](self: &A) -> i32 {
    return 20;
}

pub fn kind_code[R: struct](self: &R) -> i32 {
    return 21;
}

pub fn kind_code[Tp: tuple](self: &Tp) -> i32 {
    return 22;
}

pub fn kind_code[V: simd](self: &V) -> i32 {
    return 23;
}

pub fn kind_code[Arr: array](self: &Arr) -> i32 {
    return 24;
}

// 3. `discriminated` (`enum` | `union`) hierarchy & specificity:
pub fn tag_kind[D: discriminated](self: &D) -> i32 {
    return 30;
}

pub fn tag_kind[E: enum](self: &E) -> i32 {
    return 31;
}

pub fn tag_kind[U: union](self: &U) -> i32 {
    return 32;
}

// Function that strictly requires an open `aggregate` (`struct` or `tuple`):
pub fn require_open[A: aggregate](val: &A) -> i32 {
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
    let s4 = require_open[Point](&p) + require_open[tuple { i32, i32 }](&tup);

    // Total = 21 + 43 + 53 + 47 + 63 + 10 = 237
    return s1 + s2 + s_scalar + s_seq + s3 + s4;
}
";

    let program = Compiler::compile_package(&[("root::meta", meta_mod), ("root", root_mod)])
        .expect("Failed to compile composite & discriminated meta-type hierarchy package");

    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(237),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Verify that passing an encapsulated `opaque` (`Vault`) to `require_open[comptime A: aggregate](...)` is rejected!
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
    return require_open[Vault](&v);
}
";
    let err =
        Compiler::compile_package(&[("root::meta", meta_mod), ("root", bad_struct_as_aggregate)])
            .expect_err("Expected `require_open[Vault](&v)` to fail `aggregate` constraint");
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
    let output = lli(&llvm_ir);
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
pub fn callable_tag[F: callable](self: &F) -> i32 {
    return 10;
}

pub fn callable_tag[F: fn](self: &F) -> i32 {
    return 11;
}

pub fn invoke_callable[F: callable](f: &mut F, x: i32) -> i32 {
    return f(x);
}

pub fn invoke_fn_only[F: fn](f: F, x: i32) -> i32 {
    return f(x);
}

pub fn invoke_closure_only[C: closure](c: &mut C, x: i32) -> i32 {
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

    impl drop {
        fn drop(self: &mut Self) {
            *self.target += self.delta;
        }
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
    let output = lli(&llvm_ir);
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
pub fn require_stateless_fn[F: fn](f: F) -> i32 {
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
pub fn sum_seq[S: sequence](s: &S) -> i32 {
    let mut i: usize = 0;
    let mut total: i32 = 0;
    while i < s.len {
        total += s[i];
        i += 1;
    }
    return total;
}

// 2. Specificity ranking between `sequence` (rank 2) and `slice` (rank 3):
pub fn seq_tag[S: sequence](self: &S) -> i32 {
    return 20;
}

pub fn seq_tag[S: slice](self: &S) -> i32 {
    return 30;
}

// 3. Function taking a slice `&[T]` directly (inferring `T` from either `&[T]` or `&[T; N]`):
pub fn first_plus_len[T: integer](s: &[T]) -> T {
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
    let output = lli(&llvm_ir);
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

    // `std::mem::Box[T]` from prelude (heap-allocated with automatic `free` on scope exit)
    let mut boxed = Box[i32]::new(30);
    let p: &mut i32 = boxed.get_mut();
    *p = *p + 12;
    let box_val: i32 = *boxed.get();

    // `std::sync::Mutex[T]` and `std::thread::spawn_scoped` from prelude
    let mtx = Mutex[i32]::new(box_val);
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

    let output = lli(&llvm_ir);
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
    let b = Box[i32]::new(1);
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

    impl format {
        fn format(self: &Self, f: &mut Formatter) {
            f.write(f"{self.octets[0]}.{self.octets[1]}.{self.octets[2]}.{self.octets[3]}");
        }
    }

    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Self {
        return Self {
            octets: { a, b, c, d },
        };
    }
}

pub opaque TagId {
    id: u32,

    impl format {
        fn format(self: &Self, f: &mut Formatter, spec: &str) {
            if str_eq(spec, "x") {
                f.write(f"id(0x{self.id:04x})");
            } else {
                f.write(f"id({self.id})");
            }
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
        "pt=Point { x: 10, y: 20 } tup={ 7, true } arr=[1, 2, 3] sl=[2, 3] some=some(99) none=null st=Status::Pending(1)"
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

    let output = lli(&llvm_ir);
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
    impl format {
        fn format(self: &Self, f: &mut Formatter) {
            f.write_str("custom");
        }
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
        err2.contains("Opaque type 'SecretKey' does not define a 'format' hook"),
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
    UnexpectedToken(u32),
    Eof,
}

pub error ConfigError {
    IoError,
    ParseError,
    SyntaxError(struct {
        line: u32,
        col: u32,
    }),
}

pub union Shape {
    Unit,
    Circle(i32),
    Rect(struct {
        w: i32,
        h: i32,
    }),
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
    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(42),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // 2. Negative test: mixing embedded error sets with explicit `= 1` discriminant is rejected:
    let explicit_disc_src = r#"
pub error ChildErr {
    Disconnected,
}
pub error BadError {
    ChildErr,
    Timeout = 1,
}
pub fn main() -> i32 { return 0; }
"#;
    let err1 = Compiler::compile_source(explicit_disc_src)
        .expect_err("Expected mixing embedded error with explicit discriminant on `error` to be rejected");
    assert!(
        err1.contains("cannot mix embedded error sets with explicit"),
        "Unexpected error: {err1}"
    );

    // 3. Negative test: non-integer backing type `error(f32)` is rejected:
    let backing_ty_src = r#"
pub error(f32) BadError {
    Timeout,
}
pub fn main() -> i32 { return 0; }
"#;
    let err2 = Compiler::compile_source(backing_ty_src)
        .expect_err("Expected non-integer backing type on `error` to be rejected");
    assert!(
        err2.contains("Backing type 'f32' of 'error(BadError)' must be a C-compatible integer type"),
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
    //    - `pub trait Name { ... }`, `type Name = trait { ... };`, and `fn From[Src] -> trait`
    //    - Static `comptime` bounds: `comptime T: Trait`, `comptime T: A + B`, `comptime T: From[i32]`
    //    - Static monomorphized calls (`a: T`, `a: &T`) and `comptime a: &Trait`
    //    - Dynamic dispatch via `&Trait` and `&mut Trait` fat pointers (without `dyn`), including
    //      coercing `&T` -> `&Trait`, `&mut T` -> `&mut Trait`, `&mut Trait` -> `&Trait`, and reborrowing
    let valid_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
    fn add(self: &mut Self, delta: i32);
}

trait Describable {
    fn code(self: &Self) -> i32;
}

pub fn ScaleBy[Factor] -> trait {
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

    impl Counter {
        fn get(self: &Self) -> i32 {
            return self.val;
        }

        fn add(self: &mut Self, delta: i32) {
            self.val = self.val + delta * self.step;
        }
    }

    impl Doubler {
        fn doubled(self: Self) -> Self {
            return Self { val: self.val * 2, step: self.step };
        }
    }
}

// Module-level impls in the type's module satisfying `Describable` and `ScaleBy[i32]` for `StepCounter`
impl Describable for StepCounter {
    fn code(self: &Self) -> i32 {
        return self.val + 100;
    }
}

impl ScaleBy[i32] for StepCounter {
    fn scale(self: &Self, k: i32) -> i32 {
        return self.val * k;
    }
}

pub struct SimpleBox {
    n: i32,

    impl Counter {
        fn get(self: &Self) -> i32 {
            return self.n;
        }

        fn add(self: &mut Self, delta: i32) {
            self.n = self.n + delta;
        }
    }
}

// Static dispatch with single trait bound (by value and by reference)
fn static_read[T: Counter](c: &T) -> i32 {
    return c.get();
}

fn static_double[T: Doubler](v: T) -> T {
    return v.doubled();
}

// Static dispatch with multi-trait `+` bounds and parameterized trait `ScaleBy[i32]`
fn static_combo[T: Counter + Describable + ScaleBy[i32]](c: &T) -> i32 {
    return c.get() + c.code() + c.scale(3);
}

// Compile-time constant trait reference (`comptime a: &Counter`) — no runtime vtable
fn eval_const_counter[c: &Counter]() -> i32 {
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
    if static_read[SimpleBox](&sb) != 7 {
        return 2;
    }
    let sc2 = static_double(sc);
    if sc2.val != 20 {
        return 3;
    }

    // 2. Multi-trait `+` bounds + generic trait `ScaleBy[i32]`
    // 10 + (10 + 100) + (10 * 3) = 150
    if static_combo(&sc) != 150 {
        return 4;
    }

    // 3. `comptime c: &Counter`
    let ct_res = eval_const_counter[&StepCounter { val: 37, step: 1 }]();
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
    let output = lli(&llvm_ir);
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
    impl Counter { fn get(self: &Self) -> i32 { return self.v; } }
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
pub fn compute_hash[T: Hasher](x: &T) -> i32 {
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

// Orphan impl in `root` (neither `root::trait_mod` nor `root::type_mod`)
impl Hasher for ForeignKey {
    fn hash_val(self: &Self) -> i32 {
        return self.id;
    }
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
    impl Counter { fn get(self: &Self) -> i32 { return self.n; } }
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

#[test]
fn test_scalar_arithmetic_checked_casts_computed_int_bswap_and_packed_layouts() {
    // 1. Positive end-to-end LLVM execution test covering all 5 extensions:
    //    - Fallible arithmetic (`+?`, `-?`, `*?`) chaining with `orelse` and `try`
    //    - Checked narrowing casts (`x as ?P`, `x as ?u8`, `x as ?rune`)
    //    - Unchecked arithmetic intrinsics (`@add_unchecked`, `@sub_unchecked`, `@mul_unchecked`) and `@bswap`
    //    - `@Int(.unsigned | .signed, bits)` and integer reflection (`T::MIN`, `T::MAX`, `T.bits`, `x.bits`, `T.signed`, `x.signed`)
    //    - `enum(Int)` explicit backing widths and `packed struct` / `packed opaque` bit-level layouts
    let src = r#"
pub alias Percent = u8 in 0..=100;

pub fn NonZero[Int: integer] -> type {
    return Int in 1..=Int::MAX;
}

pub enum Priority {
    Low    = 0,
    Normal = 1,
    High   = 2,
    Urgent = 3,
}

pub packed struct Ipv4Header {
    ihl:       u4 = 5,
    version:   u4 = 4,
    prio:      Priority = Priority::Normal,
    dscp:      u6 = 0,
    total_len: u16,
}

pub packed opaque BitFlags {
    enabled: bool = true,
    mode:    u3 = 5,
    delta:   i4 = -3,

    pub fn new(enabled: bool, mode: u3, delta: i4) -> Self {
        return Self { enabled: enabled, mode: mode, delta: delta };
    }

    pub fn get_delta(self: Self) -> i32 {
        return self.delta as i32;
    }

    pub fn add_delta(self: &mut Self, d: i4) {
        self.delta += d;
    }
}

pub fn widen_mul[A: unsigned, B: unsigned](a: A, b: B) -> @Int(.unsigned, A.bits + B.bits) {
    return (a as @Int(.unsigned, a.bits + b.bits)) * (b as @Int(.unsigned, a.bits + b.bits));
}

pub fn try_add_mul(a: u8, b: u8, c: u8) -> ?u8 {
    let sum = try (a +? b);
    let prod = try (sum *? c);
    return prod;
}

pub fn main() -> i32 {
    // 1. Fallible arithmetic `+`, `-?`, `*?` with `orelse` and `try`
    let ok_add: u8 = ((200 as u8) +? (50 as u8)) orelse 0;
    if ok_add != 250 { return 1; }

    let ovf_add: u8 = ((200 as u8) +? (100 as u8)) orelse 99;
    if ovf_add != 99 { return 2; }

    let ok_sub: u8 = ((10 as u8) -? (3 as u8)) orelse 99;
    if ok_sub != 7 { return 3; }

    let ovf_sub: u8 = ((3 as u8) -? (10 as u8)) orelse 77;
    if ovf_sub != 77 { return 4; }

    let ok_mul: i8 = ((10 as i8) *? (12 as i8)) orelse 0;
    if ok_mul != 120 { return 5; }

    let ovf_mul: i8 = ((20 as i8) *? (10 as i8)) orelse -1;
    if ovf_mul != -1 { return 6; }

    let chain_ok = try_add_mul(10, 15, 4) orelse 0;
    if chain_ok != 100 { return 7; }

    let chain_ovf = try_add_mul(100, 100, 3) orelse 55;
    if chain_ovf != 55 { return 8; }

    // 2. Checked narrowing casts `x as ?P`, `x as ?DestInt`, `x as ?rune`
    let raw_ok: i32 = 85;
    let p_ok: u8 = ((raw_ok as ?Percent) orelse (0 as Percent)) as u8;
    if p_ok != 85 { return 9; }

    let raw_hi: i32 = 150;
    if let p_bad = (raw_hi as ?Percent) {
        return 10;
    }

    let raw_neg: i32 = -5;
    if let u_bad = (raw_neg as ?u8) {
        return 11;
    }

    let nz_zero: u32 = 0;
    if let nz_bad = (nz_zero as ?NonZero[u32]) {
        return 12;
    }
    let nz_five: u32 = 5;
    let nz_ok = ((nz_five as ?NonZero[u32]) orelse return 13) as u32;
    if nz_ok != 5 { return 14; }

    let surrogate_code: u32 = 0xD800;
    if let r_bad = (surrogate_code as ?rune) {
        return 15;
    }
    let crab_code: u32 = 0x1F980;
    let r_ok = (crab_code as ?rune) orelse return 16;
    if (r_ok as u32) != 0x1F980 { return 17; }

    // 3. `@add_unchecked`, `@sub_unchecked`, `@mul_unchecked`, and `@bswap`
    let unchk = unsafe {
        let s = @add_unchecked(10, 20);
        let d = @sub_unchecked(s, 5);
        @mul_unchecked(d, 2)
    };
    if unchk != 50 { return 18; }

    let swapped16 = @bswap(0x1234 as u16);
    if swapped16 != 0x3412 { return 19; }

    let swapped32 = @bswap(0x01020304 as u32);
    if swapped32 != 0x04030201 { return 20; }

    // 4. `@Int` and integer reflection (`.bits`, `.signed`, `::MIN`, `::MAX`)
    if u8::MAX != 255 || i8::MIN != -128 || i8::MAX != 127 { return 21; }
    if u16.bits != 16 || u16.signed || !i16.signed { return 22; }
    let wm = widen_mul[u8, u12](200 as u8, 3000 as u12);
    if wm.bits != 20 || wm.signed { return 23; }
    if (wm as u32) != 600000 { return 24; }

    // 5. `packed struct`, `packed opaque`, and `enum(u2)`
    let mut hdr = Ipv4Header { total_len: 0x1234 };
    if Ipv4Header.bits != 32 || hdr.bits != 32 { return 25; }
    if (hdr.ihl as u32) != 5 || (hdr.version as u32) != 4 { return 26; }
    if hdr.prio != Priority::Normal || (hdr.total_len as u32) != 0x1234 { return 27; }

    // Verify LSB-0 bit packing: ihl (4b) = 5, version (4b) = 4 -> low byte 0x45!
    // prio (2b) = 1, dscp (6b) = 0 -> second byte 0x01!
    // total_len (16b) = 0x1234 -> upper 16 bits 0x1234!
    let raw_hdr = hdr as u32;
    if raw_hdr != 0x12340145 { return 28; }

    hdr.ihl = 6;
    hdr.prio = Priority::Urgent;
    hdr.dscp = 0b101010;
    hdr.total_len += 10;
    if (hdr.ihl as u32) != 6 || hdr.prio != Priority::Urgent { return 29; }
    if (hdr.dscp as u32) != 42 || (hdr.total_len as u32) != 0x123E { return 30; }

    // Packed opaque with signed 4-bit field (`i4`) sign-extension and compound assignment
    let mut bf = BitFlags::new(true, 0b101, -3);
    if BitFlags.bits != 8 { return 31; }
    if bf.get_delta() != -3 { return 32; }
    bf.add_delta(2);
    if bf.get_delta() != -1 { return 33; }

    return 42;
}
"#;

    let mut prog = Compiler::compile_source(src)
        .expect("Failed to compile scalar, arithmetic, and packed layout test");

    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of scalar, arithmetic, and packed layout test failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));

    let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
    assert!(
        llvm_ir.contains("@llvm.bswap.i16") && llvm_ir.contains("@llvm.bswap.i32"),
        "Expected @llvm.bswap intrinsics in LLVM IR:\n{llvm_ir}"
    );
    assert!(
        llvm_ir.contains("add nsw i32") && llvm_ir.contains("mul nsw i32"),
        "Expected unchecked nsw arithmetic in LLVM IR:\n{llvm_ir}"
    );

    let out = lli(&llvm_ir);
    assert_eq!(
        out.status.code(),
        Some(42),
        "lli execution failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    // 2. Negative test: Taking a reference `&hdr.version` to a packed field must be rejected!
    let bad_ref_packed = r#"
pub packed struct Hdr {
    a: u4,
    b: u4,
}
pub fn main() -> i32 {
    let h = Hdr { a: 1, b: 2 };
    let r = &h.a;
    return 0;
}
"#;
    let err_ref = Compiler::compile_source(bad_ref_packed)
        .expect_err("Expected taking reference to packed field to fail");
    assert!(
        err_ref.contains("Cannot take a reference or pointer to bit-packed field"),
        "Unexpected error: {err_ref}"
    );

    // 3. Negative test: Calling `@add_unchecked` outside an `unsafe` block must be rejected!
    let bad_unchecked = r#"
pub fn main() -> i32 {
    return @add_unchecked(1, 2);
}
"#;
    let err_unchk = Compiler::compile_source(bad_unchecked)
        .expect_err("Expected @add_unchecked outside unsafe block to fail");
    assert!(
        err_unchk.contains("'@add_unchecked' is unsafe and requires an 'unsafe { ... }' block"),
        "Unexpected error: {err_unchk}"
    );

    // 4. Negative test: `@bswap` on a non-byte-multiple integer (`u12`) must be rejected!
    let bad_bswap = r#"
pub fn main() -> i32 {
    let x: u12 = 10;
    let y = @bswap(x);
    return 0;
}
"#;
    let err_bswap = Compiler::compile_source(bad_bswap)
        .expect_err("Expected @bswap on u12 to fail");
    assert!(
        err_bswap.contains("'@bswap' requires a byte-multiple bit width"),
        "Unexpected error: {err_bswap}"
    );

    // 5. Negative test: `enum(u2)` with discriminant out of `u2` range (`0..=3`) must be rejected!
    let bad_enum_width = r#"
pub enum(u2) BadEnum {
    A = 0,
    B = 4,
}
pub fn main() -> i32 {
    let x = BadEnum::A;
    return 0;
}
"#;
    let err_enum = Compiler::compile_source(bad_enum_width)
        .expect_err("Expected out-of-range enum(u2) discriminant to fail");
    assert!(
        err_enum.contains("does not fit in backing integer type"),
        "Unexpected error: {err_enum}"
    );
}

#[test]
fn test_comptime_associative_maps_invert_and_lowering() {
    let src = r#"
pub enum Method {
    Get,
    Post,
    Delete,
}

pub enum SparseCode {
    Ok = 200,
    NotFound = 404,
    ServerError = 500,
}

comptime UNSIGNED_OF: map[type, type] = {
    i8  => u8,
    i16 => u16,
    i32 => u32,
    i64 => u64,
};

comptime HTTP_METHODS: map[Method, &str] = {
    Method::Get    => "GET",
    Method::Post   => "POST",
    Method::Delete => "DELETE",
};

comptime PARSE_METHOD: map[&str, Method] = @invert(HTTP_METHODS);

comptime METHOD_ID: map[Method, i32] = {
    Method::Get    => 10,
    Method::Post   => 20,
    Method::Delete => 30,
};

comptime SPARSE_MSG: map[SparseCode, i32] = {
    SparseCode::Ok          => 1,
    SparseCode::NotFound    => 2,
    SparseCode::ServerError => 3,
};

comptime DENSE_SQUARES: map[i32, i32] = {
    0 => 0,
    1 => 1,
    2 => 4,
    3 => 9,
    4 => 16,
};

pub fn to_unsigned_bits[T: signed](x: T) -> UNSIGNED_OF[T] {
    return x as UNSIGNED_OF[T];
}

pub fn lookup_dense_enum(m: Method) -> i32 {
    return METHOD_ID[m];
}

pub fn lookup_sparse_enum(c: SparseCode) -> i32 {
    return SPARSE_MSG[c];
}

pub fn parse_http(s: &str) -> ?Method {
    return PARSE_METHOD.get(s);
}

pub fn main() -> i32 {
    // 1. Type-to-type map in type position (`UNSIGNED_OF[i16]` and `UNSIGNED_OF[T]`)
    let u_val: UNSIGNED_OF[i16] = to_unsigned_bits[i16](-1 as i16);
    if (u_val as u32) != 65535 {
        return 1;
    }

    // 2. Comptime key constant folding (`HTTP_METHODS[Method::Post]` and `PARSE_METHOD.get("DELETE")`)
    let post_str = HTTP_METHODS[Method::Post];
    if post_str.len != 4 || post_str[0] != 80 {
        return 2;
    }
    let comptime_del = PARSE_METHOD.get("DELETE") orelse return 3;
    if comptime_del != Method::Delete {
        return 4;
    }

    // 3. Runtime dense enum `MAP[k]` (O(1) Global array indexing)
    if lookup_dense_enum(Method::Get) != 10 { return 5; }
    if lookup_dense_enum(Method::Post) != 20 { return 6; }
    if lookup_dense_enum(Method::Delete) != 30 { return 7; }

    // 4. Runtime sparse enum `MAP[k]` (`SwitchInt` jump table)
    if lookup_sparse_enum(SparseCode::Ok) != 1 { return 8; }
    if lookup_sparse_enum(SparseCode::NotFound) != 2 { return 9; }
    if lookup_sparse_enum(SparseCode::ServerError) != 3 { return 10; }

    // 5. Runtime dense integer `MAP.get(k)` (range-checked Global array indexing)
    let mut k: i32 = 3;
    let sq3 = DENSE_SQUARES.get(k) orelse return 11;
    if sq3 != 9 { return 12; }
    k = 99;
    if let _bad = DENSE_SQUARES.get(k) {
        return 13;
    }

    // 6. Runtime string `MAP.get(s)` via compiler-synthesized Perfect Hash Table (PHF)
    let m1 = parse_http("GET") orelse return 14;
    if m1 != Method::Get { return 15; }
    let m2 = parse_http("POST") orelse return 16;
    if m2 != Method::Post { return 17; }
    let m3 = parse_http("DELETE") orelse return 18;
    if m3 != Method::Delete { return 19; }
    if let _m_bad = parse_http("PATCH") {
        return 20;
    }
    if let _m_bad2 = parse_http("GE") {
        return 21;
    }

    return 42;
}
"#;

    let mut prog = Compiler::compile_source(src).expect("Failed to compile comptime map test");
    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of comptime map test failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));

    let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
    let out = lli(&llvm_ir);
    assert_eq!(
        out.status.code(),
        Some(42),
        "lli execution failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    // Negative 1: Duplicate key in map literal must be rejected at compile time
    let dup_key_src = r#"
comptime BAD_MAP: map[i32, i32] = {
    1 => 10,
    2 => 20,
    1 => 30,
};
pub fn main() -> i32 {
    return BAD_MAP.get(1) orelse 0;
}
"#;
    let err_dup_key = Compiler::compile_source(dup_key_src)
        .expect_err("Expected duplicate map key to be rejected");
    assert!(
        err_dup_key.contains("Duplicate key"),
        "Unexpected error: {err_dup_key}"
    );

    // Negative 2: Duplicate value in `@invert(MAP)` must be rejected at compile time
    let dup_invert_src = r#"
comptime NON_BIJECTIVE: map[i32, &str] = {
    1 => "same",
    2 => "same",
};
comptime INV: map[&str, i32] = @invert(NON_BIJECTIVE);
pub fn main() -> i32 {
    return INV.get("same") orelse 0;
}
"#;
    let err_dup_inv = Compiler::compile_source(dup_invert_src)
        .expect_err("Expected @invert on non-bijective map to be rejected");
    assert!(
        err_dup_inv.contains("Cannot '@invert' map: duplicate value"),
        "Unexpected error: {err_dup_inv}"
    );

    // Negative 3: Non-exhaustive enum in runtime `MAP[k]` must be rejected at compile time
    let non_exhaustive_src = r#"
pub enum Color {
    Red,
    Green,
    Blue,
}
comptime PARTIAL: map[Color, i32] = {
    Color::Red   => 1,
    Color::Green => 2,
};
pub fn get_color(c: Color) -> i32 {
    return PARTIAL[c];
}
pub fn main() -> i32 {
    return get_color(Color::Red);
}
"#;
    let err_non_exh = Compiler::compile_source(non_exhaustive_src)
        .expect_err("Expected non-exhaustive runtime enum map indexing to fail");
    assert!(
        err_non_exh.contains("requires exhaustive coverage of enum"),
        "Unexpected error: {err_non_exh}"
    );
}

#[test]
fn test_first_class_comptime_modules_and_declarations_reflection() {
    let fast_math_src = r#"
pub const SCALE: i32 = 10;

pub struct Vec2 {
    pub x: i32,
    pub y: i32,
}

pub fn transform(v: Vec2) -> i32 {
    return (v.x + v.y) * SCALE;
}

fn private_helper() -> i32 {
    return 999;
}
"#;

    let slow_math_src = r#"
pub const SCALE: i32 = 2;

pub struct Vec2 {
    pub x: i32,
    pub y: i32,
}

pub fn transform(v: Vec2) -> i32 {
    return (v.x * v.y) + SCALE;
}
"#;

    let main_src = r#"
import root::fast_math;
import root::slow_math;

pub fn compute_with_backend[M: module](a: i32, b: i32) -> i32 {
    let v = M::Vec2 { x: a, y: b };
    return M::transform(v) + M::SCALE;
}

pub fn count_exports[M: module]() -> usize {
    let decls = @declarations(M);
    return decls.len;
}

pub fn main() -> i32 {
    // 1. Pass modules as first-class `comptime` arguments (`comptime M: module`)
    let r_fast = compute_with_backend[fast_math](3, 4);
    if r_fast != 80 {
        return 1;
    }

    let r_slow = compute_with_backend[slow_math](3, 4);
    if r_slow != 16 {
        return 2;
    }

    // 2. Bind a module to a `comptime` constant and reflect over `@declarations(mod_val)`
    comptime SELECTED: module = fast_math;
    if compute_with_backend[SELECTED](1, 2) != 40 {
        return 3;
    }

    let fast_decls = @declarations(fast_math);
    if fast_decls.len != 3 {
        return 4;
    }
    if fast_decls[0].len != 5 || fast_decls[1].len != 4 || fast_decls[2].len != 9 {
        return 5;
    }

    if count_exports[slow_math]() != 3 {
        return 6;
    }

    return 42;
}
"#;

    let mut prog = Compiler::compile_package(&[
        ("root::fast_math", fast_math_src),
        ("root::slow_math", slow_math_src),
        ("root", main_src),
    ])
    .expect("Failed to compile first-class comptime modules test");

    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of first-class comptime modules failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));
}

#[test]
fn test_pure_comptime_package_manifest_evaluation_and_sandbox() {
    let manifest_src = r#"
import std::build::{Package, Target, OptimizeMode, Dependency};

pub fn package[target: Target]() -> Package {
    return Package {
        name: "http_server",
        version: { 0, 2, 0 },
        root: "src/main.slop",
        no_std: target.os == Target::Os::Freestanding,
        deps: &[
            Dependency {
                name: "tls",
                url: "https://pkg.sloplang.dev/tls-1.4.0.tar.zst",
                sha256: 0x9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08_u256,
            },
        ],
        system_libs: if target.os == Target::Os::Linux {
            &["pthread", "c"]
        } else {
            &["System"]
        },
    };
}
"#;

    // 1. Evaluate for Linux x86_64
    let pkg_linux = Compiler::evaluate_package_manifest(manifest_src, "Linux", "X86_64")
        .expect("Failed to evaluate package.slop for Linux");
    assert_eq!(pkg_linux.name, "http_server");
    assert_eq!(pkg_linux.version, (0, 2, 0));
    assert_eq!(pkg_linux.root, "src/main.slop");
    assert!(!pkg_linux.no_std);
    assert_eq!(pkg_linux.deps.len(), 1);
    assert_eq!(pkg_linux.deps[0].name, "tls");
    assert_eq!(
        pkg_linux.deps[0].url,
        "https://pkg.sloplang.dev/tls-1.4.0.tar.zst"
    );
    assert_eq!(
        pkg_linux.deps[0].sha256,
        [
            0xd15d6c15b0f00a08,
            0xa3bf4f1b2b0b822c,
            0x9a2feaa0c55ad015,
            0x9f86d081884c7d65,
        ]
    );
    assert_eq!(pkg_linux.system_libs, vec!["pthread", "c"]);

    // 2. Evaluate for Freestanding Riscv64
    let pkg_free = Compiler::evaluate_package_manifest(manifest_src, "Freestanding", "Riscv64")
        .expect("Failed to evaluate package.slop for Freestanding");
    assert!(pkg_free.no_std);
    assert_eq!(pkg_free.system_libs, vec!["System"]);

    // 3. Sandbox violation: calling an `extern fn` inside `package.slop` must be rejected by the VM!
    let evil_manifest_src = r#"
import std::build::{Package, Target};

extern fn system(cmd: *const u8) -> i32;

pub fn package[target: Target]() -> Package {
    let s: &str = "rm -rf /";
    unsafe {
        let _ = system(&s[0] as *const u8);
    }
    return Package {
        name: "evil",
    };
}
"#;
    let err_sandbox = Compiler::evaluate_package_manifest(evil_manifest_src, "Linux", "X86_64")
        .expect_err("Expected extern call inside package.slop to be blocked by VM sandbox");
    assert!(
        err_sandbox.contains("Comptime VM sandbox violation: cannot call extern function 'system'"),
        "Unexpected error: {err_sandbox}"
    );
}

#[test]
fn test_reflection_intrinsics_and_comptime_for() {
    let src = r#"
trait Describable {
    fn id(self: &Self) -> i32;
}

struct Point {
    pub x: i32,
    pub y: i32 = 10,

    pub fn sum(self: &Self) -> i32 {
        return self.x + self.y;
    }

    impl Describable {
        fn id(self: &Self) -> i32 {
            return self.x;
        }
    }
}

packed struct PackedBits {
    pub a: u3,
    pub b: u5,
    pub c: u8,
}

overlay WordBytes {
    word: u32,
    lo: u16,
}

opaque SecretVault {
    code: i32,
    salt: i32,

    pub const ORIGIN_X: i32 = 0;

    pub fn new(c: i32, s: i32) -> Self {
        return Self { code: c, salt: s };
    }

    pub fn internal_field_sum(self: &Self) -> i32 {
        let mut total: i32 = 0;
        comptime for f in @fields(Self) {
            if @has_field(Self, f.name) && f.ty == i32 {
                total += @field(self, f.name);
            }
        }
        return total;
    }
}

enum(u8) Color {
    Red = 1,
    Green = 2,
    Blue = 5,
}

union Msg {
    Ping,
    Val(i32),
    Pair(tuple { i32, i32 }),
}

error NetErr {
    Timeout,
    Code(i32),
}

const HTTP_CODES: map[u16, &str] = {
    200 => "OK",
    404 => "NotFound",
};

const TYPE_REG: map[&str, type] = {
    "int" => i32,
    "flag" => bool,
};

fn generic_struct_eq[T: struct](a: &T, b: &T) -> bool {
    comptime for f in @fields(T) {
        if @field(a, f.name) != @field(b, f.name) {
            return false;
        }
    }
    return true;
}

fn scale_all_i32_fields[T: struct](val: &mut T, factor: i32) {
    comptime for (f, idx) in @fields(T) {
        if f.ty == i32 && idx < 10 {
            let p: &mut i32 = &mut @field(val, f.name);
            *p = *p * factor;
        }
    }
}

fn sample_fn(a: i32, b: bool) -> i64 {
    if b {
        return a as i64;
    }
    return 0;
}

export fn main() -> i32 {
    // 1. @type_name & @satisfies
    if @type_name(Point) != "Point" { return 1; }
    if @type_name(i32) != "i32" { return 2; }
    if !@satisfies(Point, copy) { return 3; }
    if !@satisfies(Point, Describable) { return 4; }
    if @satisfies(SecretVault, copy) { return 5; }
    if !@satisfies(i32, integer) { return 6; }
    if @satisfies(Point, integer) { return 7; }

    // 2. @has_field & @fields on struct, packed struct, tuple, overlay, and opaque (inside Self)
    if !@has_field(Point, "x") || !@has_field(Point, "y") || @has_field(Point, "z") {
        return 8;
    }
    if !@has_field(tuple { i32, bool }, 0) || !@has_field(tuple { i32, bool }, 1) || @has_field(tuple { i32, bool }, 2) {
        return 9;
    }
    if !@has_field(WordBytes, "word") || @has_field(WordBytes, "nope") {
        return 10;
    }

    let mut p1 = Point { x: 3 };
    let p2 = Point { x: 3, y: 10 };
    if !generic_struct_eq[Point](&p1, &p2) { return 11; }
    scale_all_i32_fields[Point](&mut p1, 4);
    if p1.x != 12 || p1.y != 40 { return 12; }

    let mut default_count: usize = 0;
    let mut y_offset: usize = 0;
    comptime for f in @fields(Point) {
        if f.has_default {
            default_count += 1;
        }
        if f.name == "y" {
            y_offset = f.offset;
        }
    }
    if default_count != 1 || y_offset != 4 { return 13; }

    // Packed struct bit offsets: a at 0, b at 3, c at 8
    let mut c_bit_offset: usize = 0;
    comptime for f in @fields(PackedBits) {
        if f.name == "c" {
            c_bit_offset = f.offset;
        }
    }
    if c_bit_offset != 8 { return 14; }

    // Tuple reflection & @field with integer index
    let mut tup: tuple { i32, i32 } = { 7, 8 };
    let mut tup_sum: i32 = 0;
    comptime for tf in @fields(tuple { i32, i32 }) {
        @field(tup, tf.index) += 1;
        tup_sum += @field(tup, tf.index);
    }
    if tup_sum != 17 { return 15; }

    // Opaque self-reflection inside its own block
    let vault = SecretVault::new(15, 27);
    if vault.internal_field_sum() != 42 { return 16; }

    // 3. @backing_type & @variants on enum (both comptime for and runtime slice)
    if @backing_type(Color) != u8 { return 17; }
    let mut enum_val_sum: u8 = 0;
    comptime for v in @variants(Color) {
        enum_val_sum += v.value;
    }
    if enum_val_sum != 8 { return 18; }
    let rt_vars = @variants(Color);
    if rt_vars.len != 3 { return 19; }
    if rt_vars[2].name != "Blue" || rt_vars[2].val != Color::Blue { return 20; }

    // 4. @variants, @variant, and @make_union on union & error
    let mut m = @make_union(Msg, "Val", 99);
    let mut extracted: i32 = 0;
    comptime for v in @variants(Msg) {
        if m.tag == v.tag && v.payload == i32 {
            @variant(m, v.name) += 1;
            extracted = @variant(m, v.name);
        }
    }
    if extracted != 100 { return 21; }

    let e_val = @make_union(NetErr, "Code", 503);
    let mut err_count: usize = 0;
    comptime for ev in @variants(NetErr) {
        if ev.error_name == "NetErr" {
            err_count += 1;
        }
    }
    if err_count != 2 { return 22; }
    match e_val {
        NetErr::Code(c) => {
            if c != 503 { return 23; }
        }
        _ => return 24,
    }

    // 5. @entries, .keys, .values on map[K, V]
    let mut code_sum: u16 = 0;
    comptime for entry in @entries(HTTP_CODES) {
        code_sum += entry.key;
    }
    if code_sum != 604 { return 25; }
    if HTTP_CODES.keys.len != 2 || HTTP_CODES.values[0] != "OK" { return 26; }

    let mut type_bits_sum: u32 = 0;
    comptime for te in @entries(TYPE_REG) {
        if @satisfies(te.val, integer) {
            type_bits_sum += te.val.bits;
        }
    }
    if type_bits_sum != 32 { return 27; }

    // 6. @declarations on type and @fn_info on callable
    let pt_decls = @declarations(Point);
    if pt_decls.len != 2 || pt_decls[0] != "id" || pt_decls[1] != "sum" {
        return 28;
    }
    let vault_decls = @declarations(SecretVault);
    if vault_decls.len != 3 || vault_decls[0] != "ORIGIN_X" {
        return 280;
    }
    let finfo = @fn_info(sample_fn);
    if finfo.params.len != 2 || finfo.params[0] != i32 || finfo.params[1] != bool || finfo.ret != i64 {
        return 29;
    }

    return 42;
}
"#;
    let mut prog =
        Compiler::compile_source(src).expect("Failed to compile reflection intrinsics test");
    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of reflection intrinsics failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));
}

#[test]
fn test_opaque_reflection_encapsulation_enforced() {
    let bad_fields_src = r#"
opaque Vault {
    secret: i32,
}

export fn main() -> i32 {
    comptime for f in @fields(Vault) {
        let _ = f.name;
    }
    return 0;
}
"#;
    let err1 = Compiler::compile_source(bad_fields_src)
        .expect_err("Expected @fields(Vault) outside Vault's opaque block to fail");
    assert!(
        err1.contains("Cannot reflect over private fields of opaque type 'Vault'"),
        "Unexpected error: {err1}"
    );

    let bad_has_field_src = r#"
opaque Vault {
    secret: i32,
}

export fn main() -> i32 {
    if @has_field(Vault, "secret") {
        return 1;
    }
    return 0;
}
"#;
    let err2 = Compiler::compile_source(bad_has_field_src)
        .expect_err("Expected @has_field(Vault, ...) outside Vault's opaque block to fail");
    assert!(
        err2.contains("Cannot reflect over private fields of opaque type 'Vault'"),
        "Unexpected error: {err2}"
    );
}

#[test]
fn test_programmatic_type_and_map_synthesis() {
    let src = r#"
struct Vec2 {
    pub x: i32,
    pub y: i32,
}

fn SoA[T: struct, N: usize] -> type {
    let src = @fields(T);
    let mut specs: [FieldSpec; src.len] = uninit;
    comptime for (f, i) in src {
        specs[i] = FieldSpec { name: f.name, ty: [f.ty; N] };
    }
    return @Struct(&specs);
}

fn MakeFlags() -> type {
    return @PackedStruct(&[
        FieldSpec { name: "lo", ty: u4 },
        FieldSpec { name: "hi", ty: u4 },
    ]);
}

fn MakeStatusEnum() -> type {
    return @Enum(u8, &[
        EnumSpec { name: "Idle", value: 0 },
        EnumSpec { name: "Running", value: 1 },
        EnumSpec { name: "Done", value: 9 },
    ]);
}

fn MakeEventUnion() -> type {
    return @Union(null, &[
        UnionSpec { name: "Empty" },
        UnionSpec { name: "Count", payload: i32 },
    ]);
}

fn MakeSynthError() -> type {
    return @Error(&[
        ErrorSpec { name: "BadInput" },
        ErrorSpec { name: "Errno", payload: i32 },
    ]);
}

alias Status = MakeStatusEnum();
alias Event = MakeEventUnion();
alias SynthErr = MakeSynthError();
alias Flags = MakeFlags();
alias PairTuple = @Tuple(&[i32, i32]);

const STATUS_BY_NAME: map[&str, Status] = @Map(&str, Status, &[
    { "Idle", Status::Idle },
    { "Running", Status::Running },
    { "Done", Status::Done },
]);

fn might_fail(x: i32) -> SynthErr!i32 {
    if x < 0 {
        return @make_union(SynthErr, "Errno", -x);
    }
    return x * 2;
}

export fn main() -> i32 {
    // 1. Synthesized SoA struct from @fields(Vec2) and @Struct
    let mut batches: SoA[Vec2, 4] = @default(SoA[Vec2, 4]);
    batches.x[2] = 10;
    batches.y[2] = 20;
    if batches.x[2] + batches.y[2] != 30 { return 1; }

    // 2. Synthesized @PackedStruct
    let mut fl = Flags { lo: 3, hi: 12 };
    fl.lo = 5;
    if fl.lo != 5 || fl.hi != 12 || @size_of(Flags) != 1 { return 2; }

    // 3. Synthesized @Tuple
    let pt: PairTuple = { 11, 22 };
    if pt.0 + pt.1 != 33 { return 3; }

    // 4. Synthesized @Enum & @Map
    let st = STATUS_BY_NAME.get("Done") orelse Status::Idle;
    if st != Status::Done || (st as u8) != 9 { return 4; }

    // 5. Synthesized @Union
    let ev = Event::Count(77);
    match ev {
        Event::Count(n) => {
            if n != 77 { return 5; }
        }
        Event::Empty => return 6,
    }

    // 6. Synthesized @Error
    let res = might_fail(-7) catch |err| match err {
        SynthErr::Errno(code) => code,
        SynthErr::BadInput => 0,
    };
    if res != 7 { return 7; }

    return 42;
}
"#;
    let mut prog = Compiler::compile_source(src)
        .expect("Failed to compile programmatic type synthesis test");
    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of programmatic type synthesis failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));
}

#[test]
fn test_float_literal_suffixes() {
    let src = r#"
pub fn float_size[T: float](x: T) -> usize {
    return @size_of(T);
}

export fn main() -> i32 {
    if float_size(1.5f32) != 4 { return 1; }
    if float_size(1.5f64) != 8 { return 2; }
    if float_size(2f32) != 4 { return 3; }
    if float_size(-2.5f32) != 4 { return 4; }
    if float_size(-3f64) != 8 { return 5; }
    let a = 1.25f32 + 0.75f32;
    if a != 2.0f32 { return 6; }
    return 42;
}
"#;
    let mut prog = Compiler::compile_source(src).expect("Failed to compile float suffix test");
    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of float suffix test failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));
}

#[test]
fn test_type_of_intrinsic() {
    let src = r#"
pub struct Point {
    pub x: i32,
    pub y: u64,

    pub fn sum(self: &Self) -> u64 {
        return (self.x as u64) + self.y;
    }
}

pub fn id[T: copy](v: T) -> @type_of(v) {
    return v;
}

const TOP_CONST: u16 = 99;
static mut TOP_STATIC: i64 = 7;

export fn main() -> i32 {
    let a = 5;
    if @type_of(a) != i32 { return 1; }
    let name_a = @type_name(@type_of(a));
    if name_a.len != 3 || name_a[0] != 105 || name_a[1] != 51 || name_a[2] != 50 { return 2; }

    let b = 3u32;
    if @type_of(b) != u32 { return 3; }
    let name_b = @type_name(@type_of(b));
    if name_b.len != 3 || name_b[0] != 117 || name_b[1] != 51 || name_b[2] != 50 { return 4; }

    let c = 1.5f32;
    if @type_of(c) != f32 { return 5; }
    let name_c = @type_name(@type_of(c));
    if name_c.len != 3 || name_c[0] != 102 || name_c[1] != 51 || name_c[2] != 50 { return 6; }

    let d: @type_of(b) = 40;
    if d != 40u32 { return 7; }

    let pt = Point { x: 10, y: 20 };
    if @type_of(pt) != Point { return 8; }
    if @type_of(pt.x) != i32 { return 9; }
    if @type_of(pt.y) != u64 { return 10; }
    if @type_of(pt.sum()) != u64 { return 11; }
    let name_pt = @type_name(@type_of(pt));
    if name_pt.len != 5 || name_pt[0] != 80 { return 12; }

    if @type_of(&pt) != &Point { return 13; }
    if @type_of(TOP_CONST) != u16 { return 14; }
    if @type_of(TOP_STATIC) != i64 { return 15; }
    if @type_of(id(123u8)) != u8 { return 16; }
    if @size_of(@type_of(pt.y)) != 8 { return 17; }
    if !@satisfies(@type_of(b), unsigned) { return 18; }

    let T = @type_of(pt.x);
    if T != i32 { return 19; }
    if @type_of(T) != type { return 20; }

    return 42;
}
"#;
    let mut prog = Compiler::compile_source(src).expect("Failed to compile @type_of test");
    let main_fn = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_ret = crate::vm::Vm::eval(&mut prog, main_fn, Vec::new())
        .expect("VM execution of @type_of test failed");
    assert_eq!(vm_ret, crate::vm::Value::Int(42));
}




