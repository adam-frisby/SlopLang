use super::*;

#[test]
fn test_language_fixes_round_two() {
    // `where` clauses on free functions are enforced, and `[T: !C]` is a negative bound.
    reject(
        "where_on_free_fn",
        "fn f[T](x: T) -> i32 where T: copy { return 1; }\npub fn main() -> i32 { let b = Box[i32]::new(1); return f(b); }",
        "where-clause constraint 'T: copy' is not satisfied",
    );
    reject(
        "negative_bound",
        "fn f[T: !sync](x: T) -> i32 { return 1; }\npub fn main() -> i32 { return f(1); }",
        "'T: !sync' is not satisfied",
    );
    assert_eq!(
        run_lli(
            "overload_by_negative_bound",
            "fn kind[T: sync](x: &T) -> i32 { return 1; }
fn kind[T: !sync](x: &T) -> i32 { return 2; }
pub opaque(!sync) L { n: i32, pub fn new() -> Self { return Self { n: 1 }; } }
pub fn main() -> i32 { let l = L::new(); let n: i32 = 0; return kind(&l) * 10 + kind(&n); }",
        ),
        Some(21)
    );

    // `@clone(&e)` of a `&T` clones the reference; `Vec[&T]` clones.
    assert_eq!(
        run_lli(
            "clone_vec_of_refs",
            "pub fn main() -> i32 {
    let a: i32 = 4;
    let b: i32 = 5;
    let mut v = Vec[&i32]::new();
    v.push(&a);
    v.push(&b);
    let w = @clone(&v);
    let mut sum: i32 = 0;
    for x in w.iter() { sum += **x; }
    let n: i32 = 7;
    let r = &n;
    let m: i32 = @clone(r);
    return sum + m;
}",
        ),
        Some(16)
    );

    // `extern fn` values are C function pointers, `unsafe` unless declared `safe extern fn`.
    assert_eq!(
        run_lli(
            "extern_fn_values",
            "safe extern fn abs(x: i32) -> i32;
fn apply(f: extern fn(i32) -> i32, v: i32) -> i32 { return f(v); }
pub fn main() -> i32 { let f = abs; return f(-6) + apply(abs, -3); }",
        ),
        Some(9)
    );
    reject(
        "unsafe_extern_fn_value",
        "extern fn abs(x: i32) -> i32;\npub fn main() -> i32 { let f = abs; return f(-9); }",
        "unsafe extern fn(i32) -> i32",
    );

    // Closures written inside `unsafe` are inside it.
    assert_eq!(
        run_lli(
            "closure_in_unsafe",
            "pub fn main() -> i32 { let mut x: i32 = 4; let p = &raw mut x; unsafe { let g = fn() -> i32 { return *p; }; return g(); } }",
        ),
        Some(4)
    );

    // std APIs that trust a caller's raw pointer are `unsafe fn`.
    reject(
        "string_from_raw",
        "pub fn main() -> i32 { let s = String::from_raw(0 as *mut u8, 0); return 0; }",
        "Calling 'unsafe fn' 'from_raw'",
    );
    reject(
        "formatter_new",
        "pub fn main() -> i32 { let f = Formatter::new(0 as *mut u8, 4); return 0; }",
        "Calling 'unsafe fn' 'new'",
    );
    assert_eq!(
        run_lli(
            "string_is_send",
            "pub fn main() -> i32 { if @satisfies(String, send) { return 1; } return 0; }",
        ),
        Some(1)
    );

    // Diagnostics name fields.
    reject(
        "field_names_in_diagnostics",
        &with_tx(
            "pub struct P { t: Tx, n: i32 }
pub opaque(linear) Wrap {
    p: P,
    pub fn new(t: Tx) -> Self { return Self { p: P { t: t, n: 1 } }; }
    pub fn take_n(self) -> i32 { return self.p.n; }
}
pub fn main() -> i32 { let w = Wrap::new(Tx::new(1)); return w.take_n(); }",
        ),
        "Linear field 'self.p.t' of type 'Tx'",
    );
}

#[test]
fn test_while_let_ref_bindings_super_imports_and_layout_intrinsics() {
    assert_eq!(
        run_lli(
            "while_let_and_ref",
            "opaque Ctr {
    n: i32,
    pub fn new() -> Self { return Self { n: 0 }; }
    pub fn next(&mut self) -> ?i32 {
        if self.n >= 5 { return null; }
        self.n = self.n + 1;
        return self.n;
    }
}
pub union Cell { Num(i32), Boxed(Box[i32]), Empty }
pub fn main() -> i32 {
    let mut c = Ctr::new();
    let mut sum: i32 = 0;
    while let ?v = c.next() { sum = sum + v; }
    if sum != 15 { return 1; }

    let b = Cell::Boxed(Box[i32]::new(41));
    // `ref` borrows the payload without moving `b` out, so `b` can be matched again.
    let first: i32 = match b { Cell::Boxed(ref bx) => *bx.get(), Cell::Num(n) => n, Cell::Empty => 0, };
    let again: i32 = match b { Cell::Boxed(ref bx) => *bx.get() + 1, Cell::Num(n) => n, Cell::Empty => 0, };
    if first != 41 || again != 42 { return 2; }

    let mut n = Cell::Num(1);
    match n { Cell::Num(ref mut v) => { *v = 7; }, Cell::Boxed(ref bx) => {}, Cell::Empty => {}, }
    let seven: i32 = match n { Cell::Num(v) => v, Cell::Boxed(ref bx) => 0, Cell::Empty => 0, };
    if seven != 7 { return 3; }
    return 42;
}"
        ),
        Some(42)
    );

    // `super` imports resolve against the importing module's parent.
    Compiler::compile_package(&[
        ("root", "import root::net::http::get;\npub fn top() -> i32 { return 2; }\npub fn main() -> i32 { return get(); }"),
        ("root::net", "pub fn base() -> i32 { return 40; }"),
        (
            "root::net::http",
            "import super::base;\nimport super;\nimport super::super::top;\npub fn get() -> i32 { return base() + super::base() - 40 + top(); }",
        ),
    ])
    .expect("super imports should resolve");
    let err = Compiler::compile_package(&[("root", "import super::x;\npub fn main() -> i32 { return 0; }")])
        .expect_err("super above the root should be rejected");
    assert!(err.contains("goes above the package root"), "Unexpected error: {err}");

    // `@size_of` / `@align_of` are comptime constants; `try_alloc` reports overflow as `null`.
    assert_eq!(
        run_lli(
            "layout_and_try_alloc",
            "import std::mem::try_alloc;
struct P { a: u8, b: u32 }
const N: usize = @size_of(u64);
pub fn main() -> i32 {
    let arr: array[u8; @size_of(u32)] = [1, 2, 3, 4];
    if @size_of(P) != 8 || @align_of(P) != 4 || N != 8 || arr.len != 4 { return 1; }
    let p = try_alloc[i32](4) orelse return 2;
    unsafe { *p = 7; @dealloc(p); }
    let huge: usize = 18446744073709551615;
    if let ?q = try_alloc[i64](huge) { return 3; }
    return 42;
}"
        ),
        Some(42)
    );
}

#[test]
fn test_break_and_continue() {
    assert_eq!(
        run_lli(
            "break_continue",
            "opaque D {
    p: *mut i32,
    pub fn new(p: *mut i32) -> Self { return Self { p: p }; }
    impl drop { fn drop(&mut self) { unsafe { *self.p = *self.p + 1; } } }
}
fn get(i: i32) -> ?i32 { if i < 3 { return i; } return null; }
opaque C { n: i32, pub fn new() -> Self { return Self { n: 0 }; } pub fn next(&mut self) -> ?i32 { if self.n >= 6 { return null; } self.n = self.n + 1; return self.n; } }
pub fn main() -> i32 {
    // 1 + 3 + 5 + 7 + 9 = 25
    let mut i: i32 = 0;
    let mut odd: i32 = 0;
    while true { i = i + 1; if i > 10 { break; } if i % 2 == 0 { continue; } odd = odd + i; }
    if odd != 25 { return 1; }
    // `orelse break` in expression position: 10 + 11 + 12 = 33
    let mut j: i32 = 0;
    let mut acc: i32 = 0;
    while true { let v = get(j) orelse break; acc = acc + v + 10; j = j + 1; }
    if acc != 33 { return 2; }
    // Locals of the left iteration are dropped on `continue` and `break`.
    let mut drops: i32 = 0;
    let mut k: i32 = 0;
    while k < 5 { k = k + 1; let d = D::new(&raw mut drops); if k == 3 { continue; } if k == 4 { break; } }
    if drops != 4 { return 3; }
    // `continue` in `while let`: 2 + 4 + 6 = 12
    let mut c = C::new();
    let mut evens: i32 = 0;
    while let ?v = c.next() { if v % 2 == 1 { continue; } evens = evens + v; }
    if evens != 12 { return 4; }
    // Bare `{ ... }` statement blocks: lexical scope, early drop, `defer`, and unlabeled `break` passing through to loop.
    let mut blk_drops: i32 = 0;
    let mut blk_defers: i32 = 0;
    {
        let _d = D::new(&raw mut blk_drops);
        defer blk_defers = blk_defers + 10;
        let odd: i32 = 999;
        if odd != 999 { return 5; }
    }
    if blk_drops != 1 || blk_defers != 10 || odd != 25 { return 6; }
    let mut loop_sum: i32 = 0;
    for n in 0..5 {
        {
            if n == 3 { break; }
            loop_sum = loop_sum + n;
        }
    }
    if loop_sum != 3 { return 7; }
    // Labelled `label: { ... }` blocks and `break label` (including `orelse break label`).
    let mut lbl_drops: i32 = 0;
    let mut lbl_defers: i32 = 0;
    let mut reached_after_break: bool = false;
    outer_blk: {
        let _d1 = D::new(&raw mut lbl_drops);
        defer {
            in_defer: {
                lbl_defers = lbl_defers + 100;
                break in_defer;
            }
        }
        inner_blk: {
            let _d2 = D::new(&raw mut lbl_drops);
            defer lbl_defers = lbl_defers + 1;
            let _v = get(5) orelse break outer_blk;
            break inner_blk;
        }
        reached_after_break = true;
    }
    if reached_after_break || lbl_drops != 2 || lbl_defers != 101 { return 8; }
    return 42;
}"
        ),
        Some(42)
    );
    reject(
        "break_outside_loop",
        "pub fn main() -> i32 { break; return 0; }",
        "'break' outside of a loop",
    );
    reject(
        "unlabeled_break_in_labeled_block_outside_loop",
        "pub fn main() -> i32 { blk: { break; } return 0; }",
        "'break' outside of a loop",
    );
    reject(
        "continue_targeting_labeled_block",
        "pub fn main() -> i32 { blk: { continue blk; } return 0; }",
        "labels a block, not a loop",
    );
    reject(
        "duplicate_block_label",
        "pub fn main() -> i32 { blk: { blk: { break blk; } } return 0; }",
        "already used by an enclosing",
    );
    reject(
        "break_outer_labeled_block_from_defer",
        "pub fn main() -> i32 { blk: { defer { break blk; } } return 0; }",
        "defer",
    );
    reject(
        "break_labeled_block_skips_linear_consumption",
        &with_tx("pub fn main() -> i32 { blk: { let t = Tx::new(1); break blk; } return 0; }"),
        "Linear value",
    );
    reject(
        "break_skips_linear_consumption",
        &with_tx("pub fn main() -> i32 { while true { let t = Tx::new(1); break; } return 0; }"),
        "Linear value",
    );
}

#[test]
fn test_audit_fixes_literals_runes_tuples_enums_and_partial_moves() {
    // Byte literals are `u8`; rune literals accept `\u{...}` and ASCII `\x..` escapes.
    assert_eq!(
        run_lli(
            "char_literals",
            "pub fn main() -> i32 {
    let a = b'a';
    let nl = b'\\n';
    let hi = b'\\x7F';
    let crab: rune = '\\u{1F980}';
    let x: rune = '\\x41';
    if (crab as u32) != 129408 || (x as u32) != 65 || hi != 127 || nl != 10 { return 1; }
    return (a as i32) - 55;
}"
        ),
        Some(42)
    );
    reject("rune_arithmetic", "pub fn main() -> i32 { let a: rune = 'a'; let b = a * a; return 0; }", "is not defined on 'rune'");
    accept("rune_comparison", "pub fn main() -> i32 { let a: rune = 'a'; if a < 'b' { return 1; } return 0; }");
    reject("rune_escape_not_ascii", "pub fn main() -> i32 { let r: rune = '\\xFF'; return 0; }", "is not ASCII");
    // An empty tuple is a type, and an aggregate, which `void` is not.
    assert_runs(
        "empty_tuple",
        "fn f() -> tuple {} { return .{}; }
fn agg[T: aggregate](t: T) -> usize { return @size_of(T); }
struct Holder { e: tuple {}, n: i32 }
pub fn main() -> i32 {
    let e = f();
    let h = Holder { e: .{}, n: 42 };
    let shown = format(f\"{e} {@type_name(tuple {})}\");
    @assert(shown.as_str() == \"{} tuple {}\" && @size_of(tuple {}) == 0);
    @assert(@satisfies(tuple {}, aggregate) && !@satisfies(void, aggregate));
    let parts = tuple_split[0](tuple_concat(.{}, .{ 1, 2 }));
    @assert(@fields(TupleTake[tuple { i32 }, 0]).len == 0 && parts.1.1 == 2);
    let none = tuple_split[2](parts.1);
    return h.n + agg(e.clone()) as i32 + none.0.1 - 2;
}",
        42,
    );

    // Default enum width is the smallest that fits; `export enum` keeps the C `enum` size.
    assert_eq!(
        run_lli(
            "enum_width",
            "pub enum Small { A, B }
pub enum Wide16 { A = 0, B = 300 }
pub enum Neg { A = -1, B = 1 }
export enum Ffi { A, B }
pub fn main() -> i32 {
    // 1 + 2 * 10 + 1 * 100 = 121, plus 4 for the C-sized export enum
    return (@size_of(Small) + @size_of(Wide16) * 10 + @size_of(Neg) * 100) as i32 - 83 + (@size_of(Ffi) as i32);
}"
        ),
        Some(42)
    );

    // Fields may not be moved out of a value whose type has a `drop` hook (it would run afterwards
    // on the partially moved value); without a hook, partial moves are allowed.
    reject(
        "move_out_of_drop_type",
        "opaque O {
    b: Box[i32],
    pub fn new() -> Self { return Self { b: Box[i32]::new(1) }; }
    impl drop { fn drop(&mut self) { let x = *self.b.get(); } }
    pub fn take(self) -> Box[i32] { return self.b; }
}
pub fn main() -> i32 { let o = O::new(); let b = o.take(); return 0; }",
        "because that type has a 'drop' hook",
    );
    accept(
        "move_out_of_plain_opaque",
        "opaque O { b: Box[i32], pub fn new() -> Self { return Self { b: Box[i32]::new(1) }; } pub fn take(self) -> Box[i32] { return self.b; } }
pub fn main() -> i32 { let o = O::new(); let b = o.take(); return 0; }",
    );
}

#[test]
fn test_implicit_conversions_are_an_explicit_list() {
    // Mismatches that match no implicit conversion are type errors (they used to pass through
    // and produce invalid LLVM IR or silent miscompiles).
    for (name, src, expected) in [
        (
            "arg_i64_to_i32",
            "fn f(x: i32) -> i32 { return x; }\npub fn main() -> i32 { let y: i64 = 5; return f(y); }",
            "cannot implicitly convert 'i64' to 'i32'",
        ),
        (
            "let_bool_to_i32",
            "pub fn main() -> i32 { let b = true; let z: i32 = b; return z; }",
            "cannot implicitly convert 'bool' to 'i32'",
        ),
        (
            "nominal_structs",
            "struct A { x: i32 }\nstruct B { x: i32 }\nfn f(b: B) -> i32 { return b.x; }\npub fn main() -> i32 { return f(A { x: 1 }); }",
            "cannot implicitly convert 'A' to 'B'",
        ),
        (
            "return_i64_as_i32",
            "fn f() -> i32 { let y: i64 = 7; return y; }\npub fn main() -> i32 { return f(); }",
            "cannot implicitly convert 'i64' to 'i32'",
        ),
        (
            "binop_mixed_signedness",
            "pub fn main() -> i32 { let a: i32 = 1; let b: u32 = 2; let c = a + b; return 0; }",
            "cannot implicitly convert 'u32' to 'i32' (in '+')",
        ),
        (
            "binop_narrow_shift",
            "pub fn main() -> i32 { let a: u32 = 1; let b: u64 = 3; return (a << b) as i32; }",
            "cannot implicitly convert 'u64' to 'u32' (in '<<')",
        ),
    ] {
        reject(name, src, expected);
    }
    assert_eq!(
        run_lli(
            "numeric_widening",
            "fn widen_u8_to_u32(x: mut u8) -> u32 { x = x + 1; return x; }
fn widen_u8_to_i16(x: u8) -> i16 { return x; }
fn widen_f32_to_f64(x: f32) -> f64 { return x; }
pub fn main() -> i32 {
    let a: i32 = 10;
    let b: i64 = 20;
    let sum: i64 = a + b;
    let sh: u64 = 1u64 << 3u32;
    let f: f64 = widen_f32_to_f64(1.5f32) + 0.5;
    let u: u32 = widen_u8_to_u32(1);
    let s: i32 = widen_u8_to_i16(2);
    return (sum as i32) + (sh as i32) + (f as i32) + (u as i32) - s; // 30 + 8 + 2 + 2 - 2 + 2 = 42
}"
        ),
        Some(40)
    );
    // Anonymous structs and overlays are structural; `&str` compares with string literals; a
    // literal initializes a distinct type; `-128` is one `i8` literal at compile time.
    assert_eq!(
        run_lli(
            "structural_and_literals",
            "fn sum(p: struct { x: i32, y: i32 }) -> i32 { return p.x + p.y; }
type Id = distinct i64;
fn next(i: Id) -> Id { return i - 1; }
const LOW: i8 = -128;
pub fn main() -> i32 {
    let p: struct { x: i32, y: i32 } = struct { x: i32, y: i32 } { x: 20, y: 22 };
    let mut o: overlay { a: i32, b: u32 } = overlay { a: i32, b: u32 } { a: 1 };
    let q: overlay { a: i32, b: u32 } = o;
    let s: &str = \"slop\";
    if s != \"slop\" || unsafe { q.a } != 1 || (next(43 as Id) as i64) != 42 || LOW != -128 {
        return 1;
    }
    return sum(p);
}"
        ),
        Some(42)
    );
    // `let` of an integer reflection value is an ordinary typed local (it used to vanish into the
    // compile-time environment, losing its type: `u64::MAX >> 60` shifted arithmetically).
    assert_eq!(
        run_lli(
            "let_reflection_values",
            "pub fn main() -> i32 {
    let a: u64 = u64::MAX;
    let b = u128::MAX;
    return ((a >> 60) as i32) + ((b >> 122) as i32) - 36;
}"
        ),
        Some(42)
    );
    // The compile-time VM shares the runtime integer semantics (shift amounts, `MIN / -1`).
    reject(
        "vm_shift_out_of_range",
        "fn shl(a: i32, b: i32) -> i32 { return a << b; }\nconst X: i32 = shl(1, 40);\npub fn main() -> i32 { return X; }",
        "shift amount",
    );
    reject(
        "vm_min_div_neg_one",
        "fn div(a: i8, b: i8) -> i8 { return a / b; }\nconst X: i8 = div(-128, -1);\npub fn main() -> i32 { return X as i32; }",
        "overflow",
    );
}

#[test]
fn test_unannotated_literal_bindings_infer_their_type() {
    // A `let` initialized by a literal takes its type from its first typed use: an argument,
    // the other operand of an operator, an index, or a return value; otherwise `i32` / `f64`.
    assert_eq!(
        run_lli(
            "literal_inference",
            "fn take_i64(x: i64) -> i32 { return x as i32; }
fn take_f32(x: f32) -> f32 { return x; }
fn wide() -> u64 { let x = 7; return x; }
pub fn main() -> i32 {
    let a: array[i64; 4] = [10, 20, 3, 4];
    let n: usize = 4;
    let mut i = 0;
    let mut s = 0;
    while i < n { s = s + a[i]; i = i + 1; }
    let b = 250;
    let wrapped: u8 = b +% 10;
    let half = 2.5;
    let dflt = 500000;
    // 37 + 4 + 2 + 7 + 1 - 9 = 42
    return take_i64(s) + (wrapped as i32) + (take_f32(half) as i32)
        + (wide() as i32) + (dflt / 500000) - 9;
}"
        ),
        Some(42)
    );
    // A binding used before its first typed use in a way that needs a settled type (captured by a
    // closure, in a tuple, borrowed) still takes the type of that later use.
    assert_eq!(
        run_lli(
            "literal_inference_after_escape",
            "fn take(x: i64) -> i32 { return x as i32; }
fn take_u8(x: u8) -> i32 { return x as i32; }
pub fn main() -> i32 {
    let mut c = 0;
    let g = fn() { c += 20; };
    g();
    let a = 20;
    let t = .{ a, 2 };
    return take(c) + take_u8(a) + t.1;
}"
        ),
        Some(42)
    );
    // Literals are checked against the type their binding settles on.
    reject(
        "inferred_literal_too_big",
        "fn f(x: u8) -> i32 { return x as i32; }\npub fn main() -> i32 { let x = 300; return f(x); }",
        "Integer literal 300 does not fit in 'u8'",
    );
    reject(
        "inferred_conflict",
        "fn f(x: i8) -> i32 { return x; }\nfn g(x: u8) -> i32 { return x; }\npub fn main() -> i32 { let x = 5; return f(x) + g(x); }",
        "cannot implicitly convert 'i8' to 'u8'",
    );
}

#[test]
fn test_for_loops_and_destructuring() {
    assert_eq!(
        run_lli(
            "for_loops",
            "opaque Count {
    n: i32,
    pub fn new() -> Self { return Self { n: 0 }; }
    pub fn next(&mut self) -> ?i32 {
        if self.n >= 3 { return null; }
        self.n = self.n + 1;
        return self.n;
    }
}
fn sum(s: &slice[i32]) -> i32 { let mut t = 0; for x in s { t += x; } return t; }
pub fn main() -> i32 {
    let mut a: array[i32; 4] = [1, 2, 3, 4];
    let mut r = 0;
    for i in 0..4 { r += a[i]; }                 // 10, `i` inferred as usize
    for ref mut x in a { *x = *x * 2; }          // a = { 2, 4, 6, 8 }
    for i in 0..a.len { if i == 3 { r += a[i]; } }    // 18
    let lo: u8 = 254;
    for b in lo..=255 { r += 1; }                // 20: no overflow at u8::MAX
    for k in 0..100 { if k % 2 == 0 { continue; } if k > 5 { break; } r += k; }  // 29
    for c in Count::new() { r += c; }            // 35
    while false { }                              // an empty body is a block
    return r + sum(&a) - 13;                     // 35 + 20 - 13 = 42
}"
        ),
        Some(42)
    );
    assert_eq!(
        run_lli(
            "destructuring",
            "struct P { x: i32, y: i32, z: i32 }
fn dm(a: i32, b: i32) -> tuple { i32, i32 } { return .{ a / b, a % b }; }
pub fn main() -> i32 {
    let .{ q, r } = dm(17, 5);                    // 3, 2
    let P { x, y: why, .. } = P { x: 30, y: 7, z: 0 };
    let t: tuple { i32, i32 } = .{ 0, 99 };
    let .{ a, _ } = t;
    return q + r + x + why + a;
}"
        ),
        Some(42)
    );
    for (name, src, expected) in [
        (
            "for_moves_noncopy",
            "opaque B { v: i32, pub fn new() -> Self { return Self { v: 1 }; } }\npub fn main() -> i32 { let a: array[B; 1] = [B::new()]; for b in a { } return 0; }",
            "iterate with 'for ref b in ...'",
        ),
        (
            "destructure_missing",
            "struct P { x: i32, y: i32 }\npub fn main() -> i32 { let P { x } = P { x: 1, y: 2 }; return x; }",
            "does not name field(s) y; add '..'",
        ),
        (
            "destructure_opaque",
            "opaque O { v: i32, pub fn new() -> Self { return Self { v: 1 }; } }\npub fn main() -> i32 { let O { v } = O::new(); return v; }",
            "its fields are private",
        ),
        (
            "compound_assign_mismatch",
            "pub fn main() -> i32 { let mut a: i32 = 1; let b: i64 = 2; a += b; return a; }",
            "cannot implicitly convert 'i64' to 'i32' (in '+=')",
        ),
    ] {
        reject(name, src, expected);
    }
}

#[test]
fn test_bindings_are_immutable_unless_mut() {
    // `mut` governs a binding's own memory: assignment, `&mut` / `&raw mut`, `&mut self` calls,
    // `for ref mut`, and closures writing a capture. Writes through a reference are governed by
    // the reference instead.
    for (name, src) in [
        ("assign", "pub fn main() -> i32 { let a = 1; a = 2; return a; }"),
        ("compound", "pub fn main() -> i32 { let a = 1; a += 1; return a; }"),
        ("field", "struct P { x: i32 }\npub fn main() -> i32 { let p = P { x: 1 }; p.x = 2; return p.x; }"),
        ("element", "pub fn main() -> i32 { let a: array[i32; 2] = [1, 2]; a[0] = 5; return a[0]; }"),
        ("borrow_mut", "pub fn main() -> i32 { let a = 1; let p = &mut a; *p = 2; return a; }"),
        ("param", "fn f(x: i32) -> i32 { x = x + 1; return x; }\npub fn main() -> i32 { return f(1); }"),
        ("loop_var", "pub fn main() -> i32 { for i in 0..3 { i = 5; } return 0; }"),
        ("for_ref_mut", "pub fn main() -> i32 { let a: array[i32; 2] = [1, 2]; for ref mut x in a { *x = 0; } return 0; }"),
        ("capture", "pub fn main() -> i32 { let c = 0; let f = fn() { c += 1; }; f(); return c; }"),
        (
            "mut_self_method",
            "opaque C { n: i32, pub fn new() -> Self { return Self { n: 0 }; } pub fn inc(&mut self) { self.n = self.n + 1; } }\npub fn main() -> i32 { let c = C::new(); c.inc(); return 0; }",
        ),
    ] {
        reject(name, src, "it is not declared 'mut'");
    }
    assert_eq!(
        run_lli(
            "mut_allowed",
            "struct P { x: i32 }
fn bump(mut x: i32) -> i32 { x += 1; return x; }
fn foo(x: mut u8) -> u32 { x = x + 1; return x; }
fn set(p: &mut P) { p.x = 20; }
pub fn main() -> i32 {
    let mut p = P { x: 1 };
    set(&mut p);
    let r = &mut p;
    let f = fn() { r.x = r.x + 1; };   // writes through the captured reference
    f();
    let mut c: i32 = 0;
    let g = fn() { c += 20; };
    g();
    let h = fn(y: mut i32) -> i32 { y += 2; return y; };
    if foo(9) != 10 || h(3) != 5 { return 1; }
    return p.x + c + bump(0);           // 21 + 20 + 1
}"
        ),
        Some(42)
    );
}

#[test]
fn test_if_expression_branches_ending_in_new_blocks() {
    // A branch whose value comes from a call or `orelse` ends in a different block than it
    // started in; the result used to be stored in the start block, overwriting the call.
    assert_eq!(
        run_lli(
            "if_expr_calls",
            "fn twenty() -> i32 { return 20; }
fn pick(c: bool, o: ?i32) -> i32 {
    let a = if c { twenty() } else { twenty() + 1 };
    let b = if c { o orelse 0 } else { twenty() };
    return a + b;
}
pub fn main() -> i32 { return pick(true, 22) + pick(false, null) - 41; }"
        ),
        Some(42)
    );
}

#[test]
fn test_cast_kinds_and_diagnostic_names() {
    for (name, src, expected) in [
        (
            "error_to_int",
            "error E { A, B }\nfn f(e: E) -> i32 { return e as i32; }\npub fn main() -> i32 { return f(E::B); }",
            "Cannot cast 'E' to 'i32'",
        ),
        (
            "struct_to_int",
            "struct P { x: i32 }\nfn f(p: P) -> i32 { return p as i32; }\npub fn main() -> i32 { return 0; }",
            "Cannot cast 'P' to 'i32'",
        ),
        (
            "linear_leak_named",
            "opaque(linear) Tx { id: i32, pub fn new(i: i32) -> Self { return Self { id: i }; } pub fn commit(self) -> i32 { return self.id; } }\npub fn main() -> i32 { let pair: tuple { Tx, Tx } = .{ Tx::new(1), Tx::new(2) }; let .{ a, .. } = pair; return a.commit(); }",
            "Linear value '<destructured value>.1'",
        ),
    ] {
        reject(name, src, expected);
    }
}

#[test]
fn test_labelled_break_and_continue() {
    assert_eq!(
        run_lli(
            "labels",
            "pub fn main() -> i32 {
    let mut c = 0;
    outer: for i in 0..10 {
        for j in 0..10 {
            if j == 3 { continue outer; }
            if i == 6 { break outer; }
            c += 1;
        }
    }
    let mut k = 0;
    scan: while k < 100 {
        k += 1;
        let none: ?i32 = null;
        for x in 0..3 { let v = none orelse break scan; c += v; }
    }
    return c + 24 + k - 1;                     // 18 + 24 + 1 - 1
}"
        ),
        Some(42)
    );
    reject(
        "unknown_label",
        "pub fn main() -> i32 { for i in 0..2 { break nope; } return 0; }",
        "no enclosing loop or block is labelled 'nope'",
    );
}

#[test]
fn test_one_spelling_per_construct() {
    // `t.1.0` indexes twice; a call through a type is `Type::f(...)` (`.` is for values); each
    // kind of type has one declaration form; an export is written `export`, not `pub export`;
    // a struct literal is `Type { ... }`, not `Type.{ ... }`.
    let src = "struct P { x: i32, pub fn new(x: i32) -> Self { return Self { x: x }; } }
pub fn main() -> i32 {
    let t: tuple { i32, tuple { i32, i32 } } = .{ 1, .{ 2, 3 } };
    return t.1.0 + t.1.1 + P::new(37).x;
}";
    assert_eq!(run_lli("one_spelling", src), Some(42));
    for (src, want) in [
        (
            "struct P { x: i32, pub fn new() -> Self { return Self { x: 1 }; } }\npub fn main() -> i32 { return P.new().x; }",
            "write 'P::new(...)'",
        ),
        ("type P = struct { x: i32 };\npub fn main() -> i32 { return 0; }", "write 'struct P ...'"),
        ("type E = enum { A };\npub fn main() -> i32 { return 0; }", "write 'enum E ...'"),
        ("type H = extern opaque;\npub fn main() -> i32 { return 0; }", "write 'extern opaque H ...'"),
        ("pub export fn f() -> i32 { return 1; }\npub fn main() -> i32 { return 0; }", "Write 'export', not 'pub export'"),
        (
            "struct P { x: i32 }\npub fn main() -> i32 { let p = P.{ x: 1 }; return p.x; }",
            "Write a struct literal as 'Type { field: value }'",
        ),
    ] {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains(want), "{src}\nexpected '{want}', got: {err}");
    }
}

#[test]
fn test_dot_variants_in_patterns_and_values() {
    // `.Name` names a variant of the type the context expects: in a pattern the scrutinee's
    // type, in a value the expected type (through `?T` and both sides of `E!T`). A bare name in
    // a pattern always binds, so spelling a variant without the dot is an error rather than a
    // silent catch-all.
    let src = "enum Color { Red, Green, Blue }
union Shape { Dot, Circle(i32) }
error IoErr { NotFound, Denied(i32) }
fn score(c: Color) -> i32 {
    match c { .Red => { return 1; } .Green => { return 2; } other => { return 3; } }
}
fn area(s: Shape) -> i32 { match s { .Dot => { return 0; } .Circle(r) => { return r * r; } } }
fn open(ok: bool) -> IoErr!i32 { if ok { return 5; } return .Denied(7); }
fn code(e: IoErr) -> i32 { match e { .NotFound => { return 100; } .Denied(n) => { return n; } } }
pub fn main() -> i32 {
    let c: Color = .Blue;
    let maybe: ?Color = .Green;
    let s: Shape = .Circle(5);
    let e: IoErr = .NotFound;
    let mut t = score(c) + score(.Red) + area(s) + area(.Dot);
    if let .Circle(r) = s { t += r; }
    if let ?v = maybe { t += score(v); }
    let o = open(false) catch |err| code(err);
    return t + o + code(e) - 105;
}";
    // 3 + 1 + 25 + 0 + 5 + 2 + 7 + 100 - 105 = 38
    assert_eq!(run_lli("dot_variants", src), Some(38));
    for (body, want) in [
        ("match c { Red => { return 1; } _ => { return 0; } }", "write '.Red' to match it"),
        ("match s { Circle(r) => { return r; } _ => { return 0; } }", "Write '.Circle(r)'"),
        ("match c { .Redd => { return 1; } _ => { return 0; } }", "has no variant 'Redd'"),
        ("let x = .Red; return 0;", "'.Red' needs a known type"),
        ("let x: Color = .Circle(1); return 0;", "'.Circle' is not a variant of 'Color'"),
    ] {
        let src = format!(
            "enum Color {{ Red, Green }}\nunion Shape {{ Dot, Circle(i32) }}
fn f(c: Color, s: Shape) -> i32 {{ {body} }}\npub fn main() -> i32 {{ return f(Color::Red, Shape::Dot); }}"
        );
        let err = Compiler::compile_source(&src).unwrap_err();
        assert!(err.contains(want), "{body}\nexpected '{want}', got: {err}");
    }
}

#[test]
fn test_record_literals_take_the_expected_type() {
    // `{ x: 1, y: 2 }` is a literal of the struct type the context expects (return type,
    // annotation, argument, field, constant, `?T`, the ok side of `E!T`, a variant payload);
    // with none expected it is the structural anonymous struct of its fields.
    let src = "struct P { x: i32, y: i32 }
union Msg { Quit, Move(struct { dx: i32, dy: i32 }) }
error E { Bad }
const ORIGIN: P = .{ x: 1, y: 1 };
fn make(x: i32) -> P { return .{ x: x, y: x + 1 }; }
fn sum(p: P) -> i32 { return p.x + p.y; }
fn checked(x: i32) -> E!P { if x < 0 { return .Bad; } return .{ x: x, y: 0 }; }
fn T() -> type { return @Struct(&[.{ name: \"v\", ty: i32 }]); }
pub fn main() -> i32 {
    let a: P = .{ x: 2, y: 3 };
    let o: ?P = .{ x: 4, y: 0 };
    let anon = .{ u: 5, w: 6 };
    let same: struct { u: i32, w: i32 } = anon;
    let m: Msg = .Move(.{ dx: 1, dy: 1 });
    let t: T() = .{ v: 1 };
    let mut total = sum(a) + make(3).y + sum(.{ x: 1, y: 1 }) + sum(ORIGIN);
    total += same.u + same.w;
    if let ?v = o { total += v.x; }
    if let .Move(d) = m { total += d.dx + d.dy; }
    let c = checked(7) catch |e| ORIGIN;
    return total + c.x + t.v - 17;
}";
    // 5 + 4 + 2 + 2 + 11 + 4 + 2 + 7 + 1 - 17 = 21
    assert_eq!(run_lli("record_literals", src), Some(21));
    // A literal naming a field the struct lacks (or one twice) is an error, in either form.
    for lit in [".{ x: 1, z: 2 }", "P { x: 1, z: 2 }", "P { x: 1, x: 2 }"] {
        let err = Compiler::compile_source(&format!(
            "struct P {{ x: i32 }}\npub fn main() -> i32 {{ let p: P = {lit}; return 0; }}"
        ))
        .unwrap_err();
        assert!(
            err.contains("has no field 'z'") || err.contains("is given twice"),
            "{lit}: {err}"
        );
    }
}

#[test]
fn test_dot_variant_and_record_lit_corner_cases() {
    // 1. `.Variant` and `{ ... }` through `E!?T`, in `const`, and in struct default fields;
    //    embedded error subtype pattern `IoErr` alongside `.Leaf` in `match` on `error`.
    let src = "enum Color { Red = 1, Green = 2, Blue = 4 }
struct Point { x: i32, y: i32 = 10 }
struct Cfg { color: Color = .Green, pt: Point = .{ x: 5 } }
error IoErr { Disconnected }
error AppErr { IoErr, BadInput(i32) }

const C_BLUE: Color = .Blue;
const C_OPT: ?Color = .Red;
const C_CFG: Cfg = .{};

fn pick_color(mode: i32) -> AppErr!?Color {
    if mode < 0 { return .BadInput(-mode); }
    if mode == 0 { return null; }
    return .Green;
}

fn pick_point(mode: i32) -> AppErr!?Point {
    if mode < 0 { return .Disconnected; }
    if mode == 0 { return null; }
    return .{ x: mode, y: 20 };
}

fn handle_err(e: AppErr) -> i32 {
    match e {
        .BadInput(code) => return code,
        IoErr => return 9,
    }
}

pub fn main() -> i32 {
    let c1 = (pick_color(1) catch |e| null) orelse .Red;
    let p1 = (pick_point(3) catch |e| null) orelse .{ x: 0, y: 0 };
    let e_val = pick_color(-4) catch |e| {
        return handle_err(e) + (C_BLUE as i32) + (C_CFG.color as i32) + C_CFG.pt.x + C_CFG.pt.y + (c1 as i32) + p1.x + p1.y - 8;
    };
    return 0;
}";
    // 4 + 4 + 2 + 5 + 10 + 2 + 3 + 20 - 8 = 42
    assert_eq!(run_lli("dot_variant_and_record_corner_cases", src), Some(42));

    // 2. Ambiguous `.Variant` when both sides of `E!T` have a variant of that name.
    let err = Compiler::compile_source(
        "enum Status { Timeout, Ok }
error Err { Timeout, Other }
fn run() -> Err!Status { return .Timeout; }
pub fn main() -> i32 { return 0; }",
    )
    .unwrap_err();
    assert!(
        err.contains("Variant '.Timeout' is ambiguous")
            && err.contains("both 'Status' and 'Err' have a variant 'Timeout'"),
        "Unexpected error: {err}"
    );

    // 3. Bare leaf variant name in `match` on `error` / `errorcode` is rejected.
    for (pat, want) in [
        ("NotFound", "Pattern 'NotFound' would bind the value, but 'NotFound' is a variant; write '.NotFound'"),
        ("Denied(c)", "Write '.Denied(c)' to match variant 'Denied'"),
    ] {
        let err = Compiler::compile_source(&format!(
            "error E {{ NotFound, Denied(i32) }}
pub fn main() -> i32 {{
    let e: E = .NotFound;
    match e {{
        {pat} => return 1,
        _ => return 0,
    }}
}}"
        ))
        .unwrap_err();
        assert!(err.contains(want), "pat={pat}, got: {err}");
    }

    // 4. Duplicate field in untyped record literal in runtime, `const`, and `comptime`.
    for code in [
        "pub fn main() -> i32 { let r = .{ a: 1, a: 2 }; return r.a; }",
        "const R = .{ a: 1, a: 2 };\npub fn main() -> i32 { return R.a; }",
        "fn check[r: struct { a: i32 }]() -> i32 { return r.a; }\npub fn main() -> i32 { return check[.{ a: 1, a: 2 }](); }",
    ] {
        let err = Compiler::compile_source(code).unwrap_err();
        assert!(
            err.contains("Duplicate field 'a'") || err.contains("is given twice"),
            "code={code}, got: {err}"
        );
    }
}

#[test]
fn test_comptime_parameters_in_brackets() {
    // Comptime parameters and arguments are written in brackets. A type function still returns
    // any kind of type; `f(x)` infers comptime arguments and `f[T](x)` gives them; `F[T]` with
    // one argument is a type-function call only when `F` names a function, so indexing a local
    // array (including an array of function pointers) is unchanged.
    let src = "fn Pick[N: usize]() -> type {
    if N == 0 { return array[u8; 2]; }
    if N == 1 { return struct { a: i32, b: i32 }; }
    return opaque {
        v: i32,
        pub fn new(v: i32) -> Self { return Self { v: v }; }
        pub fn get(&self) -> i32 { return self.v; }
    };
}
fn Pair[T]() -> type { return struct { first: T, second: T }; }
fn Grid[T, w: usize, h: usize]() -> type { return array[array[T; w]; h]; }
fn id[T](v: T) -> T { return v; }
fn size[T]() -> usize { return @size_of(T); }
fn add1(x: i32) -> i32 { return x + 1; }
pub fn main() -> i32 {
    let a: Pick[0] = [1, 2];
    let b: Pick[1] = .{ a: 3, b: 4 };
    let c = Pick[2]::new(5);
    let p = Pair[i32] { first: 6, second: 7 };
    let t: type = Grid[u8, 2, 3];
    let fs: array[fn(i32) -> i32; 1] = [add1];
    let y: u8 = id[u8](10);
    return (a[0] + a[1]) as i32 + b.a + b.b + c.get() + p.first + p.second
        + size[t]() as i32 + fs[0](8) + y as i32 + id(b.a) + 8 - 22;
}";
    assert_eq!(run_lli("comptime_brackets", src), Some(42));

    reject(
        "comptime_in_parens",
        "fn id(comptime T: type, v: T) -> T { return v; }\npub fn main() -> i32 { return 0; }",
        "Comptime parameters are declared in brackets",
    );
    reject(
        "positional_comptime_arg",
        "fn id[T](v: T) -> T { return v; }\npub fn main() -> i32 { return id(i32, 1); }",
        "expects 1 argument(s), got 2",
    );
    reject(
        "not_inferable",
        "fn size[T]() -> usize { return @size_of(T); }\npub fn main() -> i32 { return size() as i32; }",
        "pass it in brackets",
    );
    reject(
        "type_call_in_parens",
        "fn Pair[T]() -> type { return struct { a: T }; }\npub fn main() -> i32 { let p: Pair(i32) = { a: 1 }; return 0; }",
        "Type function arguments go in brackets",
    );
    reject(
        "impl_in_parens",
        "trait Tr { fn f(&self) -> i32; }\nfn W[T]() -> type { return struct { x: T }; }\nimpl(comptime T: type) Tr for W[T] { fn f(&self) -> i32 { return 1; } }\npub fn main() -> i32 { return 0; }",
        "Generic 'impl' parameters go in brackets",
    );
}

#[test]
fn test_general_pattern_matching_str_primitives_structs_tuples_arrays_and_exhaustiveness() {
    let src = "static mut DROPS: i32 = 0;

const MAGIC_VERB: &str = \"DELETE\";
const MAX_SMALL: i32 = 10;

struct Point {
    x: i32,
    y: i32,
}

packed struct PackedHdr {
    ver: u4,
    kind: u4,
    len: u8,
}

opaque SecretBox {
    code: i32,
    tag: i32,
    pub fn new(code: i32, tag: i32) -> Self {
        return Self { code: code, tag: tag };
    }
    pub fn classify(&self) -> i32 {
        return match *self {
            Self { code: 0, tag } => tag,
            .{ code: 1..=9, tag: 100 } => 50,
            .{ code, .. } => code,
        };
    }
}

opaque Tracked {
    v: i32,
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn val(&self) -> i32 { return self.v; }
    impl drop {
        fn drop(&mut self) {
            unsafe { DROPS += self.v; }
        }
    }
}

opaque(linear) Ticket {
    v: i32,
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn consume(self) -> i32 { return self.v; }
}

union Event {
    Quit,
    Move(Point),
    Pair(tuple { i32, i32 }),
    Bytes(array[u8; 3]),
}

error NetErr {
    Disconnected,
    Code(Point),
}

alias SmallScore = u8 in 0..=10;

const CONST_MATCH_VAL: i32 = match Point { x: 2, y: 7 } {
    Point { x: 0, y } => y,
    .{ x: 1 | 2, y } => y + 3,
    _ => 0,
};

fn match_str(s: &str) -> i32 {
    return match s {
        \"\" => 0,
        \"GET\" => 1,
        \"POST\" | \"PUT\" => 2,
        MAGIC_VERB => 3,
        other => other.len as i32,
    };
}

fn match_prims(b: bool, r: rune, x: i32, f: f64, u: u8, sc: SmallScore) -> i32 {
    // Exhaustive `bool` match without `_`
    let b_score = match b {
        true => 10,
        false => 20,
    };
    let r_score = match r {
        '0'..='9' => 1,
        'a'..='z' | 'A'..='Z' => 2,
        '🦀' => 3,
        _ => 4,
    };
    let x_score = match x {
        -100..=-1 => -1,
        0 => 0,
        1..=MAX_SMALL => 1,
        _ => 2,
    };
    let f_score = match f {
        0.0 => 0,
        -1.5 | 2.5 => 5,
        1 => 3,
        _ => 9,
    };
    // Exhaustive `u8` match via two ranges without `_`
    let u_score = match u {
        b'A'..=b'Z' => 7,
        0..=64 | 91..=255 => 2,
    };
    // Exhaustive `SmallScore` (`u8 in 0..=10`) match without `_`
    let sc_score = match sc {
        0 => 0,
        1..=9 => 4,
        10 => 8,
    };
    return b_score + r_score + x_score + f_score + u_score + sc_score;
}

fn match_opt_and_res(opt: ?Point, ob: ?bool, res: NetErr!Point) -> i32 {
    // Direct inner struct patterns + `null` on `?Point`
    let a = match opt {
        null => 0,
        .{ x: 0, y } => y,
        .Some(.{ x, y }) => x + y,
    };
    // Exhaustive `?bool` without `_`
    let b = match ob {
        .None => 1,
        true => 2,
        false => 3,
    };
    // Exhaustive `NetErr!Point` without top-level `_`
    let c = match res {
        .Ok(.{ x: 0, y }) => y,
        .Ok(.{ x, y }) => x - y,
        .Err(.Disconnected) => -1,
        .Err(.Code(.{ x, y })) => x * y,
    };
    return a + b + c;
}

fn match_composites(p: Point, hdr: PackedHdr, tup: tuple { i32, i32, i32 }, flags: tuple { bool, bool }) -> i32 {
    let p_val = match p {
        Point { x: 0, y: 0 } => 0,
        Point { x, y: 0 } | Point { x: 0, y: x } => x,
        .{ x, y } => x + y,
    };
    let h_val = match hdr {
        PackedHdr { ver: 1, kind: 2, len } => len as i32,
        PackedHdr { ver, .. } => ver as i32,
    };
    let t_val = match tup {
        .{ 0, .., last } => last,
        .{ first, 10, last } => first + last,
        .{ a, b, c } => a + b + c,
    };
    // Multi-arm exhaustive tuple of bools without `_`
    let f_val = match flags {
        .{ true, true } => 4,
        .{ true, false } => 3,
        .{ false, _ } => 1,
    };
    return p_val + h_val + t_val + f_val;
}

fn match_arrays_and_slices(arr: array[i32; 4], sl: &slice[i32]) -> i32 {
    let a_val = match arr {
        [0, 0, ..] => 0,
        [first, .., 99] => first,
        [a, b, c, d] => a + b + c + d,
    };
    // Exhaustive slice match (`[]`, `[only]`, `[first, second, ..]`) without `_`
    let s_val = match sl {
        [] => 0,
        [only] => only,
        [first, .., last] => first + last,
    };
    return a_val + s_val;
}

fn match_events_and_ownership(ev: Event) -> i32 {
    let ev_val = match ev {
        .Quit => 0,
        .Move(.{ x: 0, y }) => y,
        .Move(.{ x, y }) => x + y,
        .Pair(.{ a, b }) => a * b,
        .Bytes([b'O', b'K', code]) => code as i32,
        .Bytes([head, ..]) => head as i32,
    };
    // Failed branches must not move affine or linear fields before the matching arm is chosen:
    let pair = .{ Tracked::new(5), 2 };
    let tr_val = match pair {
        .{ _t, 1 } => 100,
        .{ t, 2 } => t.val(),
        .{ _t, _ } => 0,
    };
    let lin_struct = .{ a: Ticket::new(4), b: 9 as i32 };
    let lin_val = match lin_struct {
        .{ a: t, b: 0 } => t.consume(),
        .{ a: t, b: n } => t.consume() + n,
    };
    return ev_val + tr_val + lin_val;
}

pub fn main() -> i32 {
    if CONST_MATCH_VAL != 10 { return 1; }
    if match_str(\"\") != 0 || match_str(\"GET\") != 1 || match_str(\"PUT\") != 2 || match_str(\"DELETE\") != 3 || match_str(\"HELLO\") != 5 {
        return 2;
    }
    if match_prims(true, '7', -5, -1.5, b'C', 5 as SmallScore) != (10 + 1 - 1 + 5 + 7 + 4) {
        return 3;
    }
    if match_opt_and_res(Point { x: 0, y: 6 }, false, .Code(Point { x: 2, y: 3 })) != (6 + 3 + 6) {
        return 4;
    }
    let hdr = PackedHdr { ver: 1, kind: 2, len: 11 };
    if match_composites(Point { x: 0, y: 8 }, hdr, .{ 3, 10, 4 }, .{ true, false }) != (8 + 11 + 7 + 3) {
        return 5;
    }
    let xs: array[i32; 3] = [4, 20, 6];
    if match_arrays_and_slices([7, 1, 2, 99], &xs) != (7 + 10) {
        return 6;
    }
    let sb = SecretBox::new(3, 99);
    if sb.classify() != 3 {
        return 7;
    }
    let mut pt = Point { x: 4, y: 9 };
    if let Point { x: 4, ref mut y } = pt {
        *y = 12;
    }
    if pt.y != 12 {
        return 8;
    }
    let ev_res = match_events_and_ownership(.Bytes([b'O', b'K', 7]));
    if ev_res != (7 + 5 + 13) {
        return 9;
    }
    if unsafe { DROPS } != 5 {
        return 10;
    }
    return 42;
}";
    assert_eq!(run_lli("general_pattern_matching", src), Some(42));

    // Negative / diagnostic tests for general pattern matching:
    for (name, bad_src, expected_msg) in [
        (
            "non_exhaustive_bool",
            "pub fn main() -> i32 {
    let b = true;
    return match b {
        true => 1,
    };
}",
            "Non-exhaustive `match` on `bool`: missing `true` or `false`",
        ),
        (
            "non_exhaustive_str",
            "pub fn main() -> i32 {
    let s: &str = \"a\";
    return match s {
        \"a\" => 1,
        \"b\" => 2,
    };
}",
            "Non-exhaustive `match` on `&str` requires a wildcard `_` arm",
        ),
        (
            "non_exhaustive_u8_range",
            "pub fn main() -> i32 {
    let x: u8 = 5;
    return match x {
        0..=100 => 1,
        102..=255 => 2,
    };
}",
            "Non-exhaustive `match` on integer requires a wildcard `_` arm",
        ),
        (
            "non_exhaustive_slice",
            "pub fn main() -> i32 {
    let xs: &slice[i32] = &[1, 2];
    return match xs {
        [a, ..] => a,
    };
}",
            "Non-exhaustive `match` on slice '&slice[i32]' requires a wildcard `_` or rest `..` arm",
        ),
        (
            "struct_missing_field_without_rest",
            "struct P { x: i32, y: i32 }
pub fn main() -> i32 {
    let p = P { x: 1, y: 2 };
    return match p {
        P { x } => x,
    };
}",
            "Pattern for struct 'P' is missing field 'y' (list all fields or add '..')",
        ),
        (
            "opaque_private_field_in_pattern",
            "opaque Secret {
    x: i32,
    pub fn new(x: i32) -> Self { return Self { x: x }; }
}
pub fn main() -> i32 {
    let s = Secret::new(1);
    return match s {
        Secret { x } => x,
    };
}",
            "private",
        ),
        (
            "or_pattern_mismatched_bindings",
            "pub fn main() -> i32 {
    let p = .{ 1, 2 };
    return match p {
        .{ x, 0 } | .{ 0, y } => 1,
        _ => 0,
    };
}",
            "All alternatives of an `|` pattern must bind the same variables",
        ),
        (
            "duplicate_binding_in_pattern",
            "pub fn main() -> i32 {
    let p = .{ 1, 2 };
    return match p {
        .{ x, x } => x,
    };
}",
            "Identifier 'x' is bound more than once in the same pattern",
        ),
        (
            "multiple_rest_in_seq_pattern",
            "pub fn main() -> i32 {
    let xs: &slice[i32] = &[1, 2, 3];
    return match xs {
        [.., a, ..] => a,
        _ => 0,
    };
}",
            "Pattern may contain at most one '..'",
        ),
        (
            "int_pattern_out_of_range",
            "pub fn main() -> i32 {
    let x: u8 = 1;
    return match x {
        300 => 1,
        _ => 0,
    };
}",
            "Integer pattern 300 does not fit in 'u8'",
        ),
    ] {
        let err = Compiler::compile_source(bad_src)
            .expect_err(&format!("Expected '{name}' to fail compilation"));
        assert!(
            err.contains(expected_msg),
            "case '{name}': expected '{expected_msg}', got:\n{err}"
        );
    }
}

#[test]
fn test_field_paths() {
    let types = "pub struct In { a: i32, b: tuple { i32, i32 } }
pub struct Out { x: i32, i: In }
";
    let v = "let mut o: Out = Out { x: 1, i: In { a: 2, b: .{ 3, 4 } } };";
    for (name, body, value) in [
        ("read", "return @field(o, &[\"i\", \"b\", \"1\"]);", 4),
        ("bound", "comptime let p = &[\"i\", \"a\"]; @field(o, p) = 9; return o.i.a;", 9),
        ("indices", "let t: tuple { i32, tuple { i32, i32 } } = .{ 1, .{ 2, 3 } }; return @field(t, &[1, 1]);", 3),
        ("disjoint", "let a = &mut @field(o, &[\"i\", \"a\"]); let b = &mut @field(o, &[\"i\", \"b\", \"0\"]); *a = 5; *b = 6; return o.i.a + o.i.b.0;", 11),
        ("leaves", "let mut t: i32 = 0; comptime for p in @leaves(Out) { t = t * 2 + @field(o, p); } return t;", 26),
        ("leaves_write", "comptime for p in @leaves(Out) { @field(o, p) += 1; } return o.x + o.i.b.1;", 7),
        ("leaves_count", "comptime let l = @leaves(Out); return l.len as i32;", 4),
        ("tuple_names", "let t: tuple { i32, i32 } = .{ 4, 5 }; let mut s: i32 = 0; comptime for f in @fields(tuple { i32, i32 }) { s += @field(t, f.name); } return s;", 9),
        ("field_at", "return @size_of(FieldAt[Out, &[\"i\", \"b\"]]) as i32;", 8),
    ] {
        assert_runs(name, &format!("{types}pub fn main() -> i32 {{ {v} {body} }}"), value);
    }
    // Leaves stop at encapsulated types, and each linear leaf is consumed exactly once.
    assert_runs(
        "leaves_linear",
        &format!(
            "{TX}pub fn main() -> i32 {{
    let t: tuple {{ Tx, tuple {{ Tx, Tx }} }} = .{{ Tx::new(1), .{{ Tx::new(2), Tx::new(3) }} }};
    let mut s: i32 = 0;
    comptime for p in @leaves(tuple {{ Tx, tuple {{ Tx, Tx }} }}) {{ s += (@field(t, p)).commit(); }}
    return s;
}}"
        ),
        6,
    );
    assert_rejected(
        "overlap",
        &format!("{types}pub fn main() -> i32 {{ {v} let a = &mut @field(o, &[\"i\"]); let b = &mut @field(o, &[\"i\", \"a\"]); *b = 6; a.a = 1; return 0; }}"),
        "already borrowed as mutable",
    );
    assert_rejected(
        "unknown",
        &format!("{types}pub fn main() -> i32 {{ {v} return @field(o, &[\"i\", \"zz\"]); }}"),
        "has no field 'zz'",
    );
    // A path is a comptime parameter: generic code borrows disjoint branches, and an overlapping
    // pair is rejected when instantiated.
    let two = "fn two[T, P: &slice[&str], Q: &slice[&str]](t: &mut T) -> tuple { &mut FieldAt[T, P], &mut FieldAt[T, Q] } borrows(t) {
    return .{ &mut @field(t, P), &mut @field(t, Q) };
}
";
    assert_runs(
        "generic_disjoint",
        &format!("{types}{two}pub fn main() -> i32 {{ {v} let r = two[Out, &[\"x\"], &[\"i\", \"a\"]](&mut o); *r.0 = 7; *r.1 = 8; return o.x + o.i.a; }}"),
        15,
    );
    assert_rejected(
        "generic_overlap",
        &format!("{types}{two}pub fn main() -> i32 {{ {v} let r = two[Out, &[\"i\"], &[\"i\", \"a\"]](&mut o); return 0; }}"),
        "already borrowed as mutable",
    );
}

#[test]
fn test_compile_error() {
    // Fires on the path a type function takes, and only there.
    let checked = "fn Checked[N: usize]() -> type {
    if N > 2 {
        return @compile_error(\"Checked: \", N, \" is too big for \", i32);
    }
    return array[i32; N];
}
";
    assert_runs(
        "not_taken",
        &format!("{checked}pub fn main() -> i32 {{ return @size_of(Checked[2]) as i32; }}"),
        8,
    );
    assert_rejected(
        "taken",
        &format!("{checked}pub fn main() -> i32 {{ return @size_of(Checked[3]) as i32; }}"),
        "Checked: 3 is too big for i32",
    );
    // In an ordinary function, a branch pruned at compile time does not fire.
    let generic = "fn only_ints[T: unchecked](x: T) -> i32 {
    if @satisfies(T, integer) { return 1; } else { @compile_error(\"only_ints: got \", T); }
}
";
    assert_runs("pruned", &format!("{generic}pub fn main() -> i32 {{ return only_ints(1); }}"), 1);
    assert_rejected(
        "kept",
        &format!("{generic}pub fn main() -> i32 {{ return only_ints(true); }}"),
        "only_ints: got bool",
    );
    let split = |n: usize| {
        format!(
            "pub fn main() -> i32 {{ let t: tuple {{ i32, i32 }} = .{{ 1, 2 }}; let p = tuple_split[{n}, tuple {{ i32, i32 }}](t); return 0; }}"
        )
    };
    // Either piece may be the empty tuple.
    Compiler::compile_source(&split(0)).expect("split_none");
    Compiler::compile_source(&split(2)).expect("split_all");
    assert_rejected("split_past", &split(3), "TupleTake: cannot take 3 elements of tuple { i32, i32 }");
    assert_rejected(
        "field_at",
        "pub struct S { a: i32 }\npub fn main() -> i32 { return @size_of(FieldAt[S, &[\"zz\"]]) as i32; }",
        "FieldAt: S has no field zz",
    );
}

#[test]
fn test_errors_report_line_and_column() {
    // Every error found in a statement says where the statement starts, or where the call in it
    // that it came from does; the innermost says it, and a parse error says where the parser
    // stopped.
    for (name, src, at) in [
        ("type", "pub fn main() -> i32 {\n    let x: i32 = 1;\n    let y: bool = x;\n    return 0;\n}", "convert 'i32' to 'bool' (line 3, column 5)"),
        ("symbol", "pub fn main() -> i32 {\n  return nope(1);\n}", "Undefined symbol 'nope' in module 'root' (line 2, column 10)"),
        ("inner_call", "fn f(x: i32) -> i32 { return x; }\npub fn main() -> i32 {\n    return f(1) + f(f(true));\n}", "convert 'bool' to 'i32' (line 3, column 21)"),
        ("method", "pub fn main() -> i32 {\n    let mut v = Vec[i32]::new();\n    v.push(1);\n    let n = v.len() + v.nope();\n    return 0;\n}", "(line 4, column 25)"),
        ("nested", "pub fn main() -> i32 {\n    if true {\n        while false {\n          let b: bool = 1;\n        }\n    }\n    return 0;\n}", "(line 4, column 11)"),
        ("move", "pub fn main() -> i32 {\n    let s = String::from(\"a\");\n    let t = s;\n      let u = s;\n    return 0;\n}", "'s' in root::main (fn0) (line 4, column 7)"),
        // Moves and borrows found in a call are placed at the call.
        ("move_into_a_call", "fn take(s: String) -> i32 { return s.len() as i32; }\npub fn main() -> i32 {\n    let s = String::from(\"a\");\n    let n = take(s) + take(s);\n    return n;\n}", ") (line 4, column 23)"),
        ("borrow_in_a_call", "fn grow(v: &mut Vec[i32], x: i32) -> i32 { return x; }\npub fn main() -> i32 {\n    let mut v = Vec[i32]::new();\n    let r = &v;\n    let k = 1 + grow(&mut v, 0) + v.len() as i32;\n    return r.len() as i32 + k;\n}", "cannot borrow 'v' as mutable because 'v' is already borrowed as immutable (borrowed on line 4, column 5) (line 5, column 17)"),
        ("parse", "pub fn main() -> i32 {\n    let x = 1 +;\n}", "Expected expression, found ';' (line 2, column 16)"),
        ("parse_unplaced", "pub fn main() -> i32 {\n    return 0;\n}\npub fn f() -> i32 { return @nope(); }", "(line 4, column "),
    ] {
        let err = Compiler::compile_source(src).expect_err(name);
        assert!(err.contains(at), "[{name}] {err}");
        assert_eq!(err.matches("(line ").count(), 1, "[{name}] one position: {err}");
    }
    // Outside the root module, the position names its module.
    let err = Compiler::compile_package(&[
        ("root", "import util;\npub fn main() -> i32 { return util::f(); }"),
        ("util", "pub fn f() -> i32 {\n    let b: bool = 1;\n    return 0;\n}"),
    ])
    .expect_err("util");
    assert!(err.contains("(line 2, column 5 of module 'util')"), "{err}");
}

#[test]
fn test_small_language_fixes() {
    // Open-ended ranges, to the end or from the start.
    for (name, body, value) in [
        ("from", "let a: array[i32; 4] = [1, 2, 3, 4]; let s: &slice[i32] = &a; let t = s[1..]; return t.len as i32 + t[0];", 5),
        ("to", "let a: array[i32; 4] = [1, 2, 3, 4]; let s: &slice[i32] = &a; let t = s[..2]; return t.len as i32 * 10 + t[1];", 22),
        ("all", "let a: array[i32; 4] = [1, 2, 3, 4]; let s: &slice[i32] = &a; let t = s[..]; return t.len as i32;", 4),
        ("str", "let s: &str = \"hello\"; return s[2..].len as i32;", 3),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "open_end_of_a_call",
        "fn mk(a: &slice[i32]) -> &slice[i32] { return a; }\npub fn main() -> i32 { let a: array[i32; 2] = .{ 1, 2 }; let s: &slice[i32] = &a; let t = mk(s)[1..]; return 0; }",
        "write the end explicitly",
    );
    // A compile-time path can be sliced in place.
    assert_runs(
        "open_range_in_a_path",
        "pub struct S { a: tuple { i32, i32 } }
fn At[T, P: &slice[&str]]() -> type {
    if P.len == 0 { return T; }
    comptime for f in @fields(T) {
        if f.name == P[0] { return At[f.ty, P[1..]]; }
    }
    return void;
}
pub fn main() -> i32 { return @size_of(At[S, &[\"a\", \"1\"]]) as i32; }",
        4,
    );
    // A trait object's `&mut self` borrow starts after the arguments too.
    assert_runs(
        "trait_object_receiver",
        "pub trait Count { fn get(&self) -> i32; fn add(&mut self, x: i32); }
pub struct C { n: i32 }
impl Count for C {
    fn get(&self) -> i32 { return self.n; }
    fn add(&mut self, x: i32) { self.n = self.n + x; }
}
pub fn main() -> i32 {
    let mut c = C { n: 2 };
    let o: &mut Count = &mut c;
    o.add(o.get());
    return c.n;
}",
        4,
    );
    // A `drop` hook means built whole, which the error now says.
    assert_rejected(
        "hook_by_fields",
        "pub opaque Hook {
    n: i32,
    impl drop { fn drop(&mut self) { } }
    pub fn new() -> Self { let mut s: Self; s.n = 3; return s; }
}
pub fn main() -> i32 { let h = Hook::new(); return 0; }",
        "must be initialized whole",
    );
    // A broken contract names where its function starts.
    assert_rejected(
        "contract_line",
        "\n\nfn f(a: &i32, b: &i32) -> &i32 borrows(a) {\n    return b;\n}\npub fn main() -> i32 { return 0; }",
        "(function body at line 4, column 5)",
    );
}

#[test]
fn test_const_calls_infer_comptime_arguments() {
    // A compile-time call infers a generic's comptime arguments from its arguments, as a
    // run-time call does.
    for (name, src, value) in [
        ("a_type_argument", "fn second[T](x: T, n: i32) -> i32 { return n; }\nconst W: i32 = second(i64, 8);\npub fn main() -> i32 { return W; }", 8),
        ("a_number", "fn twice[T: number](x: T) -> T { return x + x; }\nconst W: i64 = twice(21);\npub fn main() -> i32 { return W as i32; }", 42),
        ("shared", "fn pick[T](a: T, b: T, c: bool) -> T { if c { return a; } return b; }\nconst W: i32 = pick(3, 4, false);\npub fn main() -> i32 { return W; }", 4),
        ("a_bool", "fn first[T](a: T, b: bool) -> T { return a; }\nconst W: bool = first(true, false);\npub fn main() -> i32 { if W { return 9; } return 0; }", 9),
    ] {
        assert_runs(name, src, value);
    }
    // Its bounds still hold.
    assert_rejected(
        "bound",
        "fn twice[T: number](x: T) -> T { return x + x; }\nconst W: bool = twice(true);\npub fn main() -> i32 { return 0; }",
        "number",
    );
}

#[test]
fn test_inference_through_optionals() {
    // A value that is not optional, given to a `?T` parameter, is a `T`, and infers `T` so.
    let decls = "fn opt[T](x: ?&T) -> i32 { if let ?r = x { return 4; } return 0; }\nfn wrap[T](x: ?T) -> i32 { if let ?v = x { return 6; } return 0; }\nfn named[T](label: &str, x: &T) -> i32 { return 7; }\n";
    for (name, body, value) in [
        ("a_reference", "let n: i32 = 3; return opt(&n);", 4),
        ("already_optional", "let n: i32 = 3; let o: ?&i32 = &n; return opt(o);", 4),
        ("a_value", "return wrap(5);", 6),
        ("null_with_the_type_given", "let b: ?&i32 = null; return opt[i32](b);", 0),
        // A string literal is a `&str` for inference too.
        ("beside_a_string_literal", "let n: i32 = 3; return named(\"x\", &n);", 7),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_pointer_comparison() {
    // Raw pointers compare by address under the VM as natively: within one allocation by byte
    // offset (so every element of an array of a zero-sized type is one address), across
    // allocations as distinct addresses.
    for (name, body, value) in [
        ("same_element", "let a: array[i32; 3] = zeroinit; let p = &a[1] as *const i32; let q = &a[1] as *const i32; if p == q { return 1; } return 2;", 1),
        ("ordered", "let a: array[i32; 3] = zeroinit; let p = &a[0] as *const i32; let q = &a[2] as *const i32; if p != q && p < q && q >= p { return 1; } return 2;", 1),
        ("zero_sized", "let a: array[void; 3] = zeroinit; let p = &a[0] as *const void; let q = &a[2] as *const void; if p == q { return 1; } return 2;", 1),
        ("separate", "let x: i32 = 1; let y: i32 = 2; let p = &x as *const i32; let q = &y as *const i32; if p != q { return 1; } return 2;", 1),
        ("moved_and_back", "let b = Box[i32]::new(1); let p = b.get() as *const i32; let q = p + 1; let ok = p == q - 1 && p < q; let n = b.into_inner(); if ok { return n; } return 2;", 1),
        // A vector of a zero-sized type holds no memory, and counts.
        ("vec_of_void", "let mut v = Vec[void]::new(); for i in 0..100 { v.push(void); } let mut n: i32 = 0; while let ?x = v.pop() { n = n + 1; } return n + @size_of(array[void; 1000]) as i32;", 100),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_unused_results() {
    // A statement may not leave a value unused, unless it is `void`, or comes from a function
    // declared `discardable`; `_ = ...` discards one on purpose. An error union is never
    // discardable, and a linear value cannot be discarded at all.
    let decls = format!("{TX}error E {{ Bad }}
fn fallible() -> E!i32 {{ return 1; }}
fn quiet() -> E!i32 discardable {{ return 1; }}
fn plain() -> i32 {{ return 1; }}
fn spare() -> i32 discardable {{ return 1; }}
fn nothing() {{ }}
pub opaque Counter {{ n: i32, pub fn new() -> Self {{ return Self {{ n: 0 }}; }} pub fn bump(&mut self) -> i32 discardable {{ self.n = self.n + 1; return self.n; }} }}
");
    for (name, body, value) in [
        ("void", "nothing(); return 0;", 0),
        ("discardable", "spare(); return 0;", 0),
        ("discardable_method", "let mut c = Counter::new(); c.bump(); c.bump(); return c.bump();", 3),
        ("on_purpose", "_ = plain(); _ = fallible(); let mut v = Vec[i32]::new(); _ = v.pop(); return 0;", 0),
        ("std_insert_and_println", "let mut m = HashMap[i32, i32]::new(); m.insert(1, 2); println(1); return 0;", 0),
        ("handled", "let n = fallible() catch return 1; return n;", 1),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, body, message) in [
        ("a_value", "plain(); return 0;", "This discards a value of type 'i32'; use it, or discard it with '_ = ...'"),
        ("an_optional", "let mut v = Vec[i32]::new(); v.pop(); return 0;", "This discards a value of type '?i32'"),
        ("an_error", "fallible(); return 0;", "This discards an error union 'E!i32', and with it any error"),
        ("an_error_marked_discardable", "quiet(); return 0;", "This discards an error union 'E!i32'"),
        ("a_caught_value", "fallible() catch 0; return 0;", "This discards a value of type 'i32'"),
        ("linear", "Tx::new(1); return 0;", "must be explicitly consumed"),
    ] {
        assert_rejected(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), message);
    }
}

#[test]
fn test_underscore_discards() {
    // `let _ = expr;` and `_ = expr;` drop a value at once; given a variable's place they leave
    // it alone. `let _name` is an ordinary variable, dropped at its scope's end.
    let decls = format!("{TX}static mut LOG: i32 = 0;
pub opaque Loud {{ n: i32, impl drop {{ fn drop(&mut self) {{ unsafe {{ LOG = LOG * 10 + self.n; }} }} }} pub fn new(n: i32) -> Self {{ return Self {{ n: n }}; }} }}
fn log() -> i32 {{ return unsafe {{ LOG }}; }}
");
    for (name, body, value) in [
        ("dropped_at_once", "let _ = Loud::new(1); let k = Loud::new(2); return log();", 1),
        ("assigned", "_ = Loud::new(3); let k = Loud::new(2); return log();", 3),
        ("a_named_one_lives", "let _a = Loud::new(1); let k = Loud::new(2); return log();", 0),
        ("in_a_pattern", "let .{ a, _ } = .{ Loud::new(1), Loud::new(2) }; return log();", 2),
        ("typed", "let _: i64 = 5; return 7;", 7),
        // A variable is neither moved nor dropped, even one moved out of before.
        ("a_place", "let a = Loud::new(4); let _ = a; let n = log(); let b = a; return n;", 0),
        ("moved_already", "let s = String::from(\"x\"); let t = s; let _ = s; return t.len() as i32;", 1),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, body) in [
        ("linear", "let _ = Tx::new(1); return 0;"),
        ("linear_assigned", "_ = Tx::new(1); return 0;"),
        ("linear_in_a_pattern", "let .{ t, _ } = .{ Tx::new(1), Tx::new(2) }; return t.commit();"),
    ] {
        assert_rejected(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), "'_' would discard a linear value of type 'Tx'");
    }
}

#[test]
fn test_void_values() {
    // `void` is the type and its one value; where a value is expected, it is the value, and
    // converts as a `void` does.
    let decls = "error E { Bad }\nunion U[T] { A(T), B(i32) }\nfn mk[T](x: T) -> U[T] { return .A(x); }\nfn h(b: bool) -> E!void { if b { return .Bad; } return void; }\n";
    for (name, body, value) in [
        ("optional", "let o: ?void = void; if o == null { return 1; } return 2;", 2),
        ("error_union", "h(false) catch return 1; h(true) catch return 3; return 0;", 3),
        ("a_type_still", "let t: type = void; return @size_of(t) as i32 + 4;", 4),
        ("in_a_map", "let mut m = HashMap[i32, void]::new(); m.insert(1, void); m.insert(1, void); return m.len() as i32 + 4;", 5),
        // A variant whose payload is `T`, with `T = void`, is made as generic code makes it.
        ("generic_payload", "let v: void = void; let u = mk(v); match u { .A(x) => return 6, .B(n) => return n }", 6),
        ("given_its_payload", "let u: U[void] = .A(void); match u { .A => return 7, .B(n) => return n }", 7),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, body, message) in [
        ("not_an_i32", "let x: i32 = void; return x;", "cannot implicitly convert 'void' to 'i32'"),
        ("not_a_payload", "let u: U[void] = .A(4); return 0;", "has no payload, but 1 arguments were provided"),
    ] {
        assert_rejected(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), message);
    }
    // With nothing expected, outside a type function, `void` is the value too.
    assert_runs(
        "inferred",
        &format!("{decls}pub fn main() -> i32 {{ let u = mk(void); match u {{ .A(x) => return 1, .B(n) => return n }} }}"),
        1,
    );
    assert_rejected(
        "called_at_run_time",
        &format!("{decls}fn second[T](x: T, n: i32) -> i32 {{ return n; }}\nfn f() -> i32 {{ return second(i32, 1); }}\npub fn main() -> i32 {{ return f(); }}"),
        "is called at run time, by 'root::f'",
    );
    // At compile time it is fine.
    assert_runs("in_a_const", &format!("{decls}fn second[T](x: T, n: i32) -> i32 {{ return n; }}\nconst W: i32 = second(i64, 8);\npub fn main() -> i32 {{ return W; }}"), 8);
}

#[test]
fn test_string_literals_are_str() {
    let prelude = "fn id[T](x: T) -> T { return x; }
fn len_of(s: &str) -> i32 { return s.len as i32; }
";
    for (name, body, value) in [
        ("let_binding", "let s = \"abc\"; return len_of(s);", 3),
        ("generic_argument", "let s = id(\"abcd\"); return len_of(s);", 4),
        ("annotated", "let s: &str = \"ab\"; return s.len as i32;", 2),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // The bytes on request. The VM cannot read through a pointer to a literal.
    for (name, body) in [
        ("bytes_on_request", "let p = \"hi\" as *const u8; return unsafe { *p } as i32;"),
        ("reference_to_bytes", "let b: &u8 = \"hi\"; return *b as i32;"),
    ] {
        assert_eq!(run_lli(name, &format!("pub fn main() -> i32 {{ {body} }}")), Some(104), "[{name}]");
    }
}

#[test]
fn test_comparing_with_null() {
    let prelude = "fn some() -> ?i32 { return 1; }
fn none() -> ?i32 { return null; }
fn boxed() -> ?Box[i32] { return Box[i32]::new(1); }
fn large() -> ?u64 { return 7; }
pub struct H { o: ?i32 }
";
    for (name, body, value) in [
        ("holds", "return (some() == null) as i32 * 10 + (some() != null) as i32;", 1),
        ("empty", "return (none() == null) as i32 * 10 + (none() != null) as i32;", 10),
        ("on_the_left", "return (null == none()) as i32;", 1),
        ("a_variable", "let x: ?i32 = null; let mut y: ?i32 = 3; return (x == null) as i32 + (y != null) as i32;", 2),
        ("a_field", "let h = H { o: 1 }; return (h.o != null) as i32;", 1),
        ("a_wider_payload", "return (large() != null) as i32;", 1),
        ("a_pointer", "let x: i32 = 1; let p: ?&i32 = &x; return (p != null) as i32;", 1),
        ("a_temporary_is_dropped", "return (boxed() != null) as i32;", 1),
        ("in_a_condition", "if none() == null { return 5; } return 0;", 5),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected("not_optional", "pub fn main() -> i32 { let x: i32 = 1; return (x == null) as i32; }", "Only an optional");
}

#[test]
fn test_compound_assignment_operators() {
    for (name, body, value) in [
        ("add", "let mut a: u8 = 12; a += 5; return a as i32;", 17),
        ("sub", "let mut a: u8 = 12; a -= 5; return a as i32;", 7),
        ("mul", "let mut a: u8 = 12; a *= 5; return a as i32;", 60),
        ("div", "let mut a: u8 = 12; a /= 5; return a as i32;", 2),
        ("rem", "let mut a: u8 = 12; a %= 5; return a as i32;", 2),
        ("and", "let mut a: u8 = 12; a &= 10; return a as i32;", 8),
        ("or", "let mut a: u8 = 12; a |= 3; return a as i32;", 15),
        ("xor", "let mut a: u8 = 12; a ^= 6; return a as i32;", 10),
        ("shl", "let mut a: u8 = 12; a <<= 2; return a as i32;", 48),
        ("shr", "let mut a: u8 = 12; a >>= 2; return a as i32;", 3),
        // Arithmetic on signed integers.
        ("signed_shr", "let mut a: i8 = -100; a >>= 2; return a as i32 + 100;", 75),
        ("signed_div", "let mut a: i32 = -7; a /= 2; return a + 100;", 97),
        ("not", "let a: u8 = 12; return (!a) as i32;", 243),
        // A literal behind '&' takes the type the reference is expected to point to.
        ("reference_to_a_literal", "let h: &u8 = &200; let k: &f32 = &1.5; return (*h as i32) + (*k * 2.0) as i32;", 203),
        ("not_signed", "let a: i8 = 12; return (!a) as i32 + 100;", 87),
        ("not_wide", "let a: u32 = 0; return ((!a) >> 24) as i32;", 255),
        ("not_simd", "let v = !simd[u8; 4] { 0, 1, 2, 255 }; return (v[0] as i32) + (v[3] as i32);", 255),
        // Wrapping and saturating forms.
        ("add_wrap", "let mut a: u8 = 250; a +%= 10; return a as i32;", 4),
        ("sub_wrap", "let mut a: u8 = 3; a -%= 5; return a as i32;", 254),
        ("mul_wrap", "let mut a: u8 = 100; a *%= 3; return a as i32;", 44),
        ("add_sat", "let mut a: u8 = 250; a +|= 10; return a as i32;", 255),
        ("sub_sat", "let mut a: u8 = 3; a -|= 5; return a as i32;", 0),
        ("mul_sat", "let mut a: i8 = 100; a *|= 3; return a as i32;", 127),
        // Wrapping negation of an unsigned value is spelled out.
        ("neg_unsigned_wrapping", "let a: u8 = 3; return ((0 -% a) as i32) / 2;", 126),
        ("neg_signed", "let a: i16 = 3; return (-a) as i32 + 10;", 7),
        ("neg_float", "let a: f64 = 2.5; return (-a * 2.0) as i32 + 10;", 5),
        // Bits shifted out are lost.
        ("shl_drops_bits", "let mut a: u8 = 200; a <<= 2; return a as i32;", 32),
        ("bool", "let mut b = true; b &= false; b |= true; b ^= true; return if b { 1 } else { 0 };", 0),
        // Any place: a field, an element, through a reference.
        ("field", "let mut p: tuple { u32, u32 } = .{ 6, 0 }; p.0 <<= 4; p.0 |= 1; return p.0 as i32;", 97),
        ("element", "let mut a: array[u16; 2] = [255, 0]; a[0] &= 15; a[1] ^= 3; return (a[0] + a[1]) as i32;", 18),
        ("through_a_reference", "let mut x: u64 = 1; let r = &mut x; *r <<= 10; *r >>= 3; return x as i32;", 128),
        ("simd", "let mut v = simd[u32; 4] { 1, 2, 3, 4 }; v <<= simd[u32; 4] { 1, 1, 1, 1 }; v &= simd[u32; 4] { 6, 6, 6, 6 }; return (v[0] + v[1] + v[2] + v[3]) as i32;", 12),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
    // A shift count has the shifted value's type, as for `<<`.
    assert_rejected(
        "shift_count_type",
        "pub fn main() -> i32 { let mut a: u8 = 1; let n: u32 = 2; a <<= n; return a as i32; }",
        "Type mismatch",
    );
    // Each operator takes the types its binary or unary form does.
    for (name, body, what) in [
        ("and_on_float", "let mut a: f64 = 1.0; a &= 2.0;", "Operator '&=' is not defined on 'f64'"),
        ("shift_on_bool", "let mut b = true; b <<= true;", "Operator '<<=' is not defined on 'bool'"),
        ("add_on_bool", "let mut b = true; b += true;", "Operator '+=' is not defined on 'bool'"),
        ("wrap_on_float", "let mut a: f64 = 1.0; a +%= 2.0;", "Operator '+%=' is not defined on 'f64'"),
        ("saturate_on_float", "let a: f64 = 1.0; let b = a +| 2.0;", "Operator '+|' is not defined on 'f64'"),
        ("not_on_float", "let a: f64 = 1.0; let b = !a;", "Operator '!' is not defined on 'f64'"),
        ("neg_on_bool", "let b = -true;", "Operator '-' is not defined on 'bool'"),
        ("neg_on_unsigned", "let a: u8 = 3; let b = -a;", "Operator '-' is not defined on unsigned 'u8'; write '0 -% x' to wrap"),
        ("neg_on_unsigned_lanes", "let v = simd[u32; 2] { 1, 2 }; let w = -v;", "Operator '-' is not defined on unsigned"),
        ("neg_on_usize_literal", "let a: usize = -1;", "Integer literal -1 does not fit in 'u64'"),
        // A binding typed by a later use is held to it.
        ("neg_on_inferred_unsigned", "let a = 3; let b = -a; let c: u8 = a;", "Operator '-' is not defined on unsigned 'u8': this makes unsigned a value negated in the statement on line 1, column 35"),
    ] {
        assert_rejected(name, &format!("pub fn main() -> i32 {{ {body} return 0; }}"), what);
    }
}

#[test]
fn test_calls_infer_from_the_type_they_are_expected_to_give() {
    let prelude = "fn id[T](x: T) -> T { return x; }
fn zero[T: integer]() -> T { return 0; }
fn wrap[T](x: T) -> ?T { return x; }
fn take(x: u8) -> i32 { return x as i32; }
struct H[T] { v: T, pub fn make(v: T) -> Self { return Self { v: v }; } }
opaque E[T] { v: ?T, pub fn empty() -> Self { return Self { v: null }; } pub fn has(&self) -> bool { return self.v != null; } }
";
    for (name, body, value) in [
        ("binding", "let a: i32 = id(7); return a;", 7),
        ("no_arguments", "let z: u16 = zero(); return z as i32 + 1;", 1),
        ("through_an_optional", "let w: ?u8 = wrap(5); return (w orelse 0) as i32;", 5),
        ("argument", "return take(id(9));", 9),
        ("return", "return id(4);", 4),
        ("static", "let h: H[i8] = H::make(3); return h.v as i32;", 3),
        ("static_nothing_else", "let e: E[i32] = E::empty(); return if e.has() { 1 } else { 2 };", 2),
        // An argument's type wins over the hint.
        ("argument_wins", "let x: u8 = 6; let a: i32 = id(x) as i32; return a;", 6),
        ("unhinted_literal", "let b = id(500000); return b / 100000;", 5),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "hint_is_not_a_conversion",
        &format!("{prelude}pub fn main() -> i32 {{ let x: i64 = 1; let a: bool = id(x); return 0; }}"),
        "Type mismatch",
    );
}

#[test]
fn test_one_compile_reports_each_function_s_errors() {
    // Bodies refused while lowering: each one, not just the first.
    let err = Compiler::compile_source(
        "fn a() -> i32 { let x: bool = 5; return 0; }
fn b() -> i32 { return a() + undefined_name; }
pub fn main() -> i32 { let q: bool = 1; return b(); }",
    )
    .unwrap_err();
    assert_eq!(
        err,
        "Type mismatch: cannot implicitly convert 'i32' to 'bool' (line 1, column 17)
error: Cannot resolve value path 'undefined_name' (line 2, column 17)
error: Type mismatch: cannot implicitly convert 'i32' to 'bool' (line 3, column 24)"
    );
    // Moves, and borrows in the functions whose moves were fine.
    let err = Compiler::compile_source(
        "fn a() -> i32 { let b = Box[i32]::new(1); let c = b; let d = b; return 0; }
fn r() -> &i32 { let x: i32 = 1; return &x; }
fn s() -> i32 { let mut v: i32 = 1; let p = &mut v; let q = &v; *p = 2; return *q; }
pub fn main() -> i32 { return a() + s(); }",
    )
    .unwrap_err();
    let lines: Vec<&str> = err.lines().collect();
    assert_eq!(lines.len(), 3, "{err}");
    assert!(lines[0].starts_with("Use of moved or uninitialized value 'b' in root::a"), "{err}");
    assert!(lines[1].contains("in root::r") && lines[1].contains("'x' goes out of scope while still borrowed"), "{err}");
    assert!(lines[2].contains("in root::s") && lines[2].contains("already borrowed as mutable"), "{err}");
}

#[test]
fn test_string_literals_are_str_unless_bytes_are_wanted() {
    assert_runs(
        "where_str_converts",
        "error E { Bad }
fn pick(b: bool) -> E!&str { if b { return \"yes\"; } return E::Bad; }
fn name(s: ?&str) -> &str { return s orelse \"none\"; }
fn len_c(p: *const u8) -> usize { let mut n: usize = 0; while unsafe { *(p + n) } != 0 { n += 1; } return n; }
pub fn main() -> i32 {
    let s: ?&str = \"hi\";
    let raw: *const u8 = \"c\";
    let maybe_raw: ?*const u8 = \"d\";
    @assert((s orelse \"x\") == \"hi\" && name(\"given\") == \"given\" && name(null) == \"none\");
    @assert((pick(true) catch \"no\") == \"yes\");
    // Its bytes, through the pointer, end with a 0 as a C string's do, in the VM as natively.
    let m = maybe_raw orelse return 1;
    @assert(unsafe { *raw } == 99 && unsafe { *(m + 0) } == 100);
    return len_c(\"four\") as i32;
}",
        4,
    );
}

#[test]
fn test_byte_strings() {
    // `b"..."` is the `array[u8; N]` of its bytes: escapes, ASCII only, no terminating zero.
    assert_runs(
        "arrays",
        "const MAGIC: array[u8; 4] = b\"\\x7fELF\";
static GREETING: array[u8; 5] = b\"hello\";
fn sum(bytes: &slice[u8]) -> i32 { let mut n = 0; for b in bytes { n += b as i32; } return n; }
pub fn main() -> i32 {
    let a: array[u8; 4] = b\"blah\";
    let inferred = b\"ab\";
    let two: array[u8; 2] = inferred;
    let escaped = b\"a\\n\\t\\0\\\\\\\"'\\x41\";
    @assert(a[0] == b'b' && a[3] == b'h' && two.len == 2);
    @assert(escaped.len == 8 && escaped[1] == 10 && escaped[3] == 0 && escaped[4] == 92 && escaped[5] == 34 && escaped[7] == 65);
    @assert(sum(&b\"ab\") == 195);
    @assert(MAGIC[0] == 127 && MAGIC[1] == b'E' && GREETING[4] == b'o');
    let empty = b\"\";
    @assert(empty.len == 0);
    return 0;
}",
        0,
    );
    for (name, body, what) in [
        ("size", "let a: array[u8; 8] = b\"blah\";", "cannot implicitly convert 'array[u8; 4]' to 'array[u8; 8]'"),
        ("non_ascii", "let a = b\"caf\u{e9}\";", "is not ASCII, so a byte string cannot hold it as one byte"),
        ("escape", "let a = b\"\\q\";", "Unknown escape '\\q' in byte string"),
    ] {
        assert_rejected(name, &format!("pub fn main() -> i32 {{ {body} return 0; }}"), what);
    }
    // `b` is a name otherwise.
    assert_runs("a_variable", "pub fn main() -> i32 { let b = 1; return b - 1; }", 0);
    // As a pattern, it matches an array or slice of exactly those bytes.
    assert_runs(
        "patterns",
        "fn method(line: &slice[u8]) -> i32 {
    match line {
        b\"GET\" => { return 1; }
        b\"POST\" | b\"PUT\" => { return 2; }
        b\"\" => { return 3; }
        _ => { return 0; }
    }
}
pub fn main() -> i32 {
    let tag: array[u8; 4] = b\"\\x7fELF\";
    @assert(match tag { b\"\\x7fELF\" => true, _ => false });
    @assert(method(&b\"GET\") == 1 && method(&b\"PUT\") == 2 && method(&b\"\") == 3 && method(&b\"GETS\") == 0);
    let buf: array[u8; 8] = b\"GET /ok!\";
    if let b\"GET /ok!\" = buf { return 0; }
    return 9;
}",
        0,
    );
    assert_rejected(
        "pattern_length",
        "pub fn main() -> i32 { let t: array[u8; 4] = b\"abcd\"; return match t { b\"abc\" => 1, _ => 0 }; }",
        "Array pattern has 3 element(s), but 'array[u8; 4]' has length 4",
    );
}

#[test]
fn test_integer_literal_suffixes() {
    let prelude = "fn bits_set[T: unsigned](x: T) -> u32 {
    let mut n: u32 = 0;
    let mut v = x;
    while v != 0 {
        n += (v & 1) as u32;
        v = v >> 1;
    }
    return n;
}
";
    assert_runs(
        "suffixed_literals",
        &format!(
            "{prelude}pub fn main() -> i32 {{
    let a = bits_set(3u32) as i32;
    let b = bits_set(0xFFu8) as i32;
    let c = bits_set(0b101u4) as i32;
    let d = -128i8;
    let e = 5_000_000_000i64 / 1_000_000_000i64;
    let f = 10usize;
    let w = 1000000000000000000000000000000000000000u256 / 1000000000000000000000000000000000000000u256;
    return a + b + c + (d + 127i8) as i32 + e as i32 + f as i32 + w as i32;
}}"
        ),
        27,
    );
    for (name, body, msg) in [
        ("overflow_u8", "let x = 300u8; return 0;", "Integer literal 300 does not fit in 'u8'"),
        ("overflow_pos_i8", "let x = 128i8; return 0;", "Integer literal 128 does not fit in 'i8'"),
        ("overflow_neg_i8", "let x = -129i8; return 0;", "Integer literal -129 does not fit in 'i8'"),
        ("neg_unsigned", "let x = -3u32; return 0;", "Operator '-' is not defined on unsigned 'u32'"),
    ] {
        assert_rejected(name, &format!("pub fn main() -> i32 {{ {body} }}"), msg);
    }
}

#[test]
fn test_lighter_closures_and_signature_inference() {
    assert_runs(
        "lighter_closures_positive",
        &with_tx(
            "fn apply[T, R, F: callable(T) -> R](v: T, f: F) -> R {
    return f(v);
}

struct BoxedInt {
    v: i32,
    pub fn map_val[R, F: callable(i32) -> R](&self, f: F) -> R {
        return f(self.v);
    }
}

fn ext_map[R, F: callable(i32) -> R](self: &BoxedInt, f: F) -> R {
    return f(self.v + 1);
}

fn upto(n: i32) -> gen i32 {
    for i in 0..n {
        yield i;
    }
}

pub fn main() -> i32 {
    let add_fn: fn(i32, i32) -> i32 = fn(a, b) => a + b;
    let opt_fn: ?fn(i32) -> i32 = fn(mut x) => {
        x += 2;
        x * 2
    };
    let unwrapped = opt_fn orelse return 1;

    let mut acc = 0;
    let bump = fn(d: i32) {
        acc += d;
    };
    bump(3);

    let offset = 4;
    let c_eager = fn(x: i32) => x + offset;
    let c_branch = move fn(x: i32) {
        if x < 0 {
            return 0;
        }
        return x + offset;
    };

    let tx = Tx::new(5);
    let consume_tx = move fn(scale: i32) => tx.commit() * scale;
    let tx_val = consume_tx(2);

    let bi = BoxedInt { v: 3 };
    let r1 = apply(10, fn(x) => x - 4);
    let r2 = bi.map_val(fn(x) => x * 2);
    let r3 = bi.ext_map(fn(x) => x + 1);

    let mut iter_sum = 0;
    for v in upto(5).filter(fn(x) => *x % 2 == 1).map(fn(x) => x * 3) {
        iter_sum += v;
    }

    // 3 + 6 + 3 + 5 + 4 + 10 + 6 + 6 + 5 + 12 - 18 = 42
    return add_fn(1, 2) + unwrapped(1) + acc + c_eager(1) + c_branch(0) + tx_val + r1 + r2 + r3 + iter_sum - 18;
}",
        ),
        42,
    );

    assert_rejected(
        "closure_missing_param_type",
        "pub fn main() -> i32 { let f = fn(x) => x + 1; return f(1); }",
        "Cannot infer type of closure parameter 'x'",
    );
    assert_rejected(
        "closure_arity_mismatch_expected_fn",
        "pub fn main() -> i32 { let f: fn(i32, i32) -> i32 = fn(x) => x; return f(1, 2); }",
        "parameter",
    );
    assert_rejected(
        "closure_conflicting_return_types",
        "pub fn main() -> i32 {
    let f = fn(x: i32) {
        if x > 0 { return true; }
        return 0;
    };
    _ = f;
    return 0;
}",
        "bool",
    );
    assert_rejected(
        "iterator_filter_wrong_closure_return",
        "fn upto(n: i32) -> gen i32 { for i in 0..n { yield i; } }
pub fn main() -> i32 {
    for x in upto(3).filter(fn(v) => *v + 1) { _ = x; }
    return 0;
}",
        "bool",
    );
}

#[test]
fn test_struct_literal_field_punning() {
    assert_runs(
        "struct_field_punning_positive",
        &with_tx(
            "struct Point {
    x: i32,
    y: i32,
    pub fn make(x: i32, y: i32) -> Self {
        return Self { x, y };
    }
}

fn Pair[T]() -> type {
    return struct { a: T, b: T };
}

struct TxHolder {
    tx: Tx,
    tag: i32,
}

union Shape {
    Rect(struct { w: i32, h: i32 }),
    Dot,
}

pub fn main() -> i32 {
    let x = 5;
    let y = 7;
    let p1 = Point { x, y };
    let p2 = Point::make(2, 3);
    let a = 4;
    let b = 6;
    let pr = Pair[i32] { a, b };
    let rec = .{ x: 1, y };
    let tup = .{ x, y };
    let w = 2;
    let h = 3;
    let sh: Shape = .Rect { w, h };
    let area = match sh {
        .Rect(r) => r.w * r.h,
        .Dot => 0,
    };
    let tx = Tx::new(3);
    let tag = 1;
    let holder = TxHolder { tx, tag };
    let committed = holder.tx.commit() + holder.tag;
    // 12 + 5 + 10 + 8 + 12 + 6 + 4 - 15 = 42
    return p1.x + p1.y + p2.x + p2.y + pr.a + pr.b + rec.x + rec.y + tup.0 + tup.1 + area + committed - 15;
}",
        ),
        42,
    );

    assert_rejected(
        "punned_duplicate_field",
        "struct Point { x: i32, y: i32 }
pub fn main() -> i32 { let x = 1; let p = Point { x, x: 2, y: 3 }; return p.x; }",
        "x",
    );
    assert_rejected(
        "punned_unknown_field",
        "struct Point { x: i32, y: i32 }
pub fn main() -> i32 { let x = 1; let y = 2; let z = 3; let p = Point { x, y, z }; return p.x; }",
        "z",
    );
    assert_rejected(
        "move_punned_with_colon",
        "struct Point { x: i32, y: i32 }
pub fn main() -> i32 { let x = 1; let p = Point { move x: 1, y: 2 }; return p.x; }",
        "'move' in a field shorthand changes nothing",
    );
}

#[test]
fn test_receiver_shorthand() {
    assert_runs(
        "receiver_shorthand_positive",
        "trait CounterOps {
    fn get(&self) -> i32;
    fn add(&mut self, d: i32);
}

opaque Counter {
    val: i32,
    drops: *mut i32,
    pub fn new(v: i32, drops: *mut i32) -> Self {
        return Self { val: v, drops };
    }
    pub fn peek(&self) -> i32 {
        return self.val;
    }
    pub fn bump(&mut self) {
        self.val += 1;
    }
    impl drop {
        fn drop(&mut self) {
            unsafe { *self.drops += 1; }
        }
    }
    impl clone {
        fn clone(&self) -> Self {
            return Self { val: self.val, drops: self.drops };
        }
    }
}

impl CounterOps for Counter {
    fn get(&self) -> i32 {
        return self.peek();
    }
    fn add(&mut self, d: i32) {
        for _ in 0..d {
            self.bump();
        }
    }
}

struct Plain {
    n: i32,
    pub fn read(&self) -> i32 { return self.n; }
    pub fn inc(&mut self, k: i32) { self.n += k; }
}

pub fn main() -> i32 {
    let mut drops = 0;
    let mut sum = 0;
    {
        let mut c = Counter::new(10, &raw mut drops);
        c.add(5);
        let c2 = c.clone();
        sum += c.get() + c2.peek();
    }
    let mut p = Plain { n: 7 };
    p.inc(3);
    // 30 + 2 + 10 = 42
    return sum + drops + p.read();
}",
        42,
    );

    assert_rejected(
        "ref_non_self_param",
        "struct S { x: i32, fn f(&other) -> i32 { return 0; } }
pub fn main() -> i32 { return 0; }",
        "Receiver shorthand '&other' is only valid for 'self'",
    );
    assert_rejected(
        "ref_self_with_colon_type",
        "struct S { x: i32, fn f(&self: &Self) -> i32 { return self.x; } }
pub fn main() -> i32 { return 0; }",
        "Unexpected ':' after '&self'",
    );
    assert_rejected(
        "ref_self_outside_type",
        "fn free_fn(&self) -> i32 { return 0; }
pub fn main() -> i32 { return 0; }",
        "Self",
    );
}

#[test]
fn test_let_else_and_optional_patterns() {
    assert_runs(
        "let_else_and_qmark_pat_positive",
        "error MyErr { Bad(i32) }
struct Pair { a: i32, b: i32 }
union Item { Text(String), Num(i32) }

fn unwrap_or_ten(opt: ?i32) -> i32 {
    let mut ?v = opt else {
        return 10;
    };
    v += 1;
    return v;
}

fn unwrap_res(r: MyErr!i32) -> i32 {
    let .Ok(v) = r else {
        return 5;
    };
    return v;
}

pub fn main() -> i32 {
    let a = unwrap_or_ten(4);
    let b = unwrap_or_ten(null);
    let c = unwrap_res(7);
    let d = unwrap_res(.Bad(99));

    let opt_pair: ?Pair = Pair { a: 3, b: 6 };
    let m1 = match opt_pair {
        ?Pair { a: pa, b: pb } => pa + pb,
        null => 0,
    };

    let mut arr: array[?i32; 3] = [2, 4, null];
    let mut idx: usize = 0;
    let mut wsum = 0;
    while let ?k = arr[idx] {
        wsum += k;
        idx += 1;
    }

    let mut u_val = 0;
    for round in 0..2 {
        let it: Item = if round == 0 { .Text(String::from(\"hello\")) } else { .Num(99) };
        let .Text(s) = it else {
            break;
        };
        u_val += s.len() as i32;
    }

    // 5 + 10 + 7 + 5 + 9 + 6 + 5 - 5 = 42
    return a + b + c + d + m1 + wsum + u_val - 5;
}",
        42,
    );

    assert_rejected(
        "let_else_irrefutable",
        "pub fn main() -> i32 { let x = 5 else { return 1; }; return x; }",
        "Irrefutable",
    );
    assert_rejected(
        "let_else_non_diverging",
        "pub fn main() -> i32 {
    let opt: ?i32 = 1;
    let ?x = opt else { _ = 0; };
    return x;
}",
        "diverge",
    );
    assert_rejected(
        "qmark_pat_on_non_optional",
        "pub fn main() -> i32 { return match 5 { ?x => x, _ => 0 }; }",
        "optional",
    );
}

#[test]
fn test_expression_blocks_and_control_flow_uniformity() {
    assert_runs(
        "expr_blocks_and_control_flow_positive",
        "struct Pt { x: i32, y: i32 }

pub fn main() -> i32 {
    let opt1: ?i32 = 8;
    let opt2: ?i32 = null;
    let a = if let ?x = opt1 { x + 2 } else { 0 };
    let b = if let ?x = opt2 { x } else { 4 };

    let mut side = 0;
    let c = opt2 orelse {
        side += 3;
        7
    };
    let pt_opt: ?Pt = null;
    let pt = pt_opt orelse .{ x: 2, y: 5 };
    let tup_opt: ?tuple { i32, i32 } = null;
    let tup = tup_opt orelse .{ 1, 2 };
    let rep_opt: ?array[i32; 2] = null;
    let rep = rep_opt orelse [3; 2];

    let d = oomsafe {
        nosuspend {
            if a > 5 {
                unsafe { 6 }
            } else {
                0
            }
        }
    };

    // 10 + 4 + 3 + 7 + 7 + 3 + 6 + 6 - 4 = 42
    return a + b + side + c + pt.x + pt.y + tup.0 + tup.1 + rep[0] + rep[1] + d - 4;
}",
        42,
    );

    assert_rejected(
        "oomsafe_expr_rejects_alloc",
        "pub fn main() -> i32 {
    let s = oomsafe { String::from(\"alloc\") };
    return s.len() as i32;
}",
        "can trap for want of memory",
    );
    assert_rejected(
        "nosuspend_expr_rejects_lock",
        "pub fn main() -> i32 {
    let m = Mutex[i32]::new(1);
    let v = nosuspend {
        let _g = m.lock();
        1
    };
    return v;
}",
        "nosuspend",
    );
}

#[test]
fn test_array_repeat_literals() {
    assert_runs(
        "array_repeat_literals_positive",
        &with_tx(
            "const CONST_REP: array[i32; 3] = [4; 3];

fn bump(calls: &mut i32) -> i32 {
    *calls += 1;
    return 5;
}

pub fn main() -> i32 {
    let mut calls = 0;
    let a = [bump(&mut calls); 4];
    let b: array[i64; 2] = [3; 2];
    let empty_owned: array[String; 0] = [String::from(\"dropped_immediately\"); 0];
    let single_owned: array[String; 1] = [String::from(\"abc\"); 1];
    let single_tx: array[Tx; 1] = [Tx::new(2); 1];
    let tx0 = unsafe { @transmute(Tx, single_tx) };
    let ty_check: @type_of([1 as i32; 2]) = [0, 1];

    // 12 + 20 + 1 + 6 + 0 + 3 + 2 + 1 - 3 = 42
    return CONST_REP[0] * 3
        + (a[0] + a[1] + a[2] + a[3])
        + calls
        + ((b[0] + b[1]) as i32)
        + (empty_owned.len as i32)
        + (single_owned[0].len() as i32)
        + tx0.commit()
        + ty_check[1]
        - 3;
}",
        ),
        42,
    );

    assert_rejected(
        "array_repeat_non_copy_gt_one",
        "pub fn main() -> i32 { let a = [String::from(\"no\"); 2]; return a.len as i32; }",
        "copy",
    );
    assert_rejected(
        "array_repeat_linear_zero_len",
        &with_tx("pub fn main() -> i32 { let a: array[Tx; 0] = [Tx::new(1); 0]; return a.len as i32; }"),
        "linear",
    );
    assert_rejected(
        "array_repeat_linear_gt_one",
        &with_tx("pub fn main() -> i32 { let a = [Tx::new(1); 2]; return a.len as i32; }"),
        "copy",
    );
    assert_rejected(
        "array_repeat_linear_one_unconsumed",
        &with_tx("pub fn main() -> i32 { let a: array[Tx; 1] = [Tx::new(1); 1]; return a.len as i32; }"),
        "Linear value",
    );
}

#[test]
fn test_lexer_at_intrinsics() {
    assert_runs(
        "valid_at_intrinsics",
        "pub fn main() -> i32 {
    let x: @type_of(40 as i32) = 38;
    @assert(@align_of(i32) == 4);
    return x + (@size_of(i32) as i32);
}",
        42,
    );
    assert_rejected(
        "unknown_at_intrinsic",
        "pub fn main() -> i32 { return @definitely_not_a_real_intrinsic(1); }",
        "@definitely_not_a_real_intrinsic",
    );
}

#[test]
fn test_one_spelling_for_each_form() {
    // `.{ ... }` is a literal of the type expected, `{ ... }` a block; patterns are written as
    // literals are; `..base` fills in a struct literal; `loop`; `record` is a name.
    assert_runs(
        "one_spelling",
        "struct P { x: i32, y: i32 }
struct Named { name: String, n: i32 }
fn pair() -> tuple { i32, i32 } { return .{ 3, 4 }; }
fn sum(xs: &slice[i32]) -> i32 { let mut t = 0; for x in xs { t += x; } return t; }
fn Wrap[T]() -> type { return struct { v: T }; }
pub fn main() -> i32 {
    let one = .{ 5 };
    let block = { 5 };
    let unit: tuple {} = .{};
    let arr: array[i32; 3] = [1, 2, 3];
    let rep = [0; 4];
    let p: P = .{ x: 1, y: 2 };
    let q = P { x: 10, ..p };
    let s = Named { name: String::from(\"abc\"), n: 1 };
    let t = Named { n: 2, ..s };
    let .{ a, b } = pair();
    let w: Wrap[i32] = .{ v: 1 };
    let mut total = one.0 + block + arr[2] + rep[3] + q.x + q.y + a + b + sum(&[1, 2]) + t.name.len() as i32 + t.n + w.v;
    let mut v = Vec[i32]::new();
    v.push(7);
    v.push(8);
    for .{ i, x } in v.iter().enumerate() {
        total += i as i32 * *x;
    }
    match .{ 1, 2 } {
        .{ 1, y } => { total += y; }
        _ => {}
    }
    let opt: ?i32 = 4;
    if let ?k = opt { total += k; }
    let mut n = 0;
    outer: loop {
        loop {
            n += 1;
            if n == 3 { break outer; }
        }
    }
    let record = n;
    let rt = &(.{ 1, 2 });
    total += rt.1;
    let s2 = Named { name: String::from(\"replaced\"), n: 0 };
    let t2 = Named { name: String::from(\"xy\"), ..s2 };
    total += t2.name.len() as i32;
    let f = fn(x: i32) -> i32 { return x + 1; };
    let g = fn(x: i32) => x + 1;
    _ = unit;
    return total + record + f(0) + g(0);
}",
        64,
    );
    let refused = [
        ("pub fn main() -> i32 { let t = { 1, 2 }; return t.0; }", "A tuple, array, or record literal is written '.{ ... }'"),
        ("pub fn main() -> i32 { let t = .{ 1, 2 }; let { a, b } = t; return a; }", "A tuple or record pattern is written '.{ ... }'"),
        ("pub fn main() -> i32 { let t = .{ 1, 2 }; return match t { (a, b) => a + b }; }", "A tuple pattern is written '.{ a, b }'"),
        ("pub fn main() -> i32 { let o: ?i32 = 1; if let n = o { return n; } return 0; }", "'let n = ...' always matches, binding the whole value; write 'let ?n = ...'"),
        ("pub fn main() -> i32 { let o: ?i32 = 1; while let n = o { return n; } return 0; }", "write 'let ?n = ...'"),
        ("pub fn main() -> i32 { let o: ?i32 = 1; if let ref n = o { return *n; } return 0; }", "write 'let ?ref n = ...'"),
        ("pub fn main() -> i32 { let o: ?i32 = 1; if let _ = o { return 1; } return 0; }", "write 'let ?_ = ...'"),
        ("pub fn main() -> i32 { let f = fn(x: i32) -> i32 { x }; return f(0); }", "A function literal's '{ ... }' body gives its result with 'return'"),
        ("fn f() -> i32 { 0 } pub fn main() -> i32 { return f(); }", "Expected ';' after this expression (line 1, column 19): a statement ends with ';', and a function gives its result with 'return ...;'"),
        ("fn Pair[T] -> type { return struct { a: T }; } pub fn main() -> i32 { return 0; }", "A function's parameter list is written even when it is empty: 'fn Name[...]() -> ...'"),
        ("struct S { x: i32, fn f(self: &Self) -> i32 { return self.x; } } pub fn main() -> i32 { return 0; }", "Write '&self', not 'self: &Self'"),
        ("struct S { x: i32, fn f(self: &mut Self) { self.x = 1; } } pub fn main() -> i32 { return 0; }", "Write '&mut self', not 'self: &mut Self'"),
        ("pub fn main() -> i32 { let a: array[i32; 2] = .{ 0, 1 }; return a[0]; }", "An array literal is written '[a, b, c]'"),
        ("pub fn main() -> i32 { let a = .{ 0; 2 }; return a[0]; }", "An array of copies is written '[v; N]'"),
        ("pub fn main() -> i32 { let a = array[i32; 2] { 0, 1 }; return a[0]; }", "An array literal is written '[a, b]' or '[v; N]'"),
        ("pub fn main() -> i32 { let a = [3, 4]; let mut t = 0; for (x, i) in a { t += x; } return t; }", "'for (x, i)' is gone"),
        ("fn f[T: struct]() -> usize { comptime for (f, i) in @fields(T) { } return 0; } pub fn main() -> i32 { return 0; }", "'comptime for (x, i)' is gone"),
        ("struct P { x: i32, y: i32 } pub fn main() -> i32 { let p = P { x: 1, y: 2 }; let q: P = .{ x: 0, ..p }; return q.x; }", "'..base' fills in the fields of a literal that names its type"),
        ("struct P { x: i32, y: i32 } pub fn main() -> i32 { let p = P { x: 1, y: 2 }; let q = P { ..p, x: 0 }; return q.x; }", "'..base' comes after the fields given"),
        ("struct N { s: String, n: i32 } pub fn main() -> i32 { let a = N { s: String::from(\"a\"), n: 1 }; let b = N { n: 2, ..a }; return a.s.len() as i32; }", "moved"),
        ("pub fn main() -> i32 {\n    let x = 1 +;\n}", "Expected expression, found ';' (line 2, column 16)"),
    ];
    for (i, (src, what)) in refused.iter().enumerate() {
        assert_rejected(&format!("one_spelling_refused_{i}"), src, what);
    }
}

#[test]
fn test_arrays_are_written_in_brackets() {
    // `[a, b]`, `[v; N]`, `[]`, and `&[a, b]`; a bracket is a type when its element is spelled
    // as one; indices come from a range, at compile time too.
    assert_runs(
        "bracket_arrays",
        "union Shape { Dot, Sq(i32) }
struct Point { x: i32 }
const MAX: i32 = 2;
fn first(s: &slice[i32]) -> i32 { return s[0]; }
fn count[T: struct]() -> usize {
    comptime let fs = @fields(T);
    let mut n: usize = 0;
    comptime for i in 0..fs.len {
        comptime let f = fs[i];
        if f.ty == i32 { n += 1; }
    }
    comptime for i in 1..=2 { n += i; }
    return n;
}
fn Twice[T]() -> type { return array[T; 2]; }
pub fn main() -> i32 {
    let x = 7;
    let a = [1, 2, 3];
    let one = [x];
    let rep = [MAX; 2];
    let dots = [Shape::Dot; 3];
    let ps: array[Point; 2] = [Point { x: 1 }, Point { x: 2 }];
    let empty: array[i32; 0] = [];
    let names: array[&str; 2] = [\"a\", \"bc\"];
    let t: Twice[u8] = [4, 5];
    let rt = &.{ 1, 2 };
    let n = match a { [h, .., l] => h + l, };
    let mut s = 0;
    for i in 0..a.len { s += a[i]; }
    _ = dots;
    _ = empty;
    return n + one[0] + rep[1] + ps[1].x + first(&[x, 1]) + names[1].len as i32 + t[1] as i32 + rt.1 + s + count[Point]() as i32 - 41;
}",
        0,
    );
}


#[test]
fn test_unambiguous_array_and_slice_syntax() {
    assert_runs(
        "unambiguous_array_and_slice",
        "const N: usize = 2;
alias my_arr = array[u8; 4];
fn pair_arr[t: copy](v: t) -> array[t; 2] { return [v; 2]; }
fn sum_slice(s: &slice[i32]) -> i32 { return s[0] + s[1]; }
fn bump_first(s: &mut slice[i32]) -> i32 { s[0] += 5; return s[0]; }
pub fn main() -> i32 {
    let a: my_arr = [1, 2, 3, 4];
    let p = pair_arr[i32](6);
    let mut buf = [N as i32, 3];
    let s1 = sum_slice(&[p[0], a[1] as i32]);
    let s2 = bump_first(&mut buf);
    let sz = @size_of(array[i32; 3]) as i32;
    return s1 + s2 + sz - 27;
}",
        0,
    );
    assert_rejected(
        "reject_bracket_array_type",
        "fn bad(a: [i32; 3]) -> i32 { return a[0]; }\npub fn main() -> i32 { return 0; }",
        "array[T; N]",
    );
    assert_rejected(
        "reject_ref_bracket_slice_type",
        "fn bad(s: &[i32]) -> i32 { return s[0]; }\npub fn main() -> i32 { return 0; }",
        "&slice[T]",
    );
    assert_rejected(
        "reject_ref_mut_bracket_slice_type",
        "fn bad(s: &mut [i32]) -> i32 { return s[0]; }\npub fn main() -> i32 { return 0; }",
        "&mut slice[T]",
    );
    assert_rejected(
        "reject_unborrowed_slice_type",
        "fn bad(s: slice[i32]) -> i32 { return 0; }\npub fn main() -> i32 { return 0; }",
        "&slice[T]",
    );
}

#[test]
fn test_main_may_return_an_error() {
    // `main` returns `i32`, `void`, `E!void`, or `E!i32`; an error is written to stderr and the
    // status is 1, whatever its tag.
    for (name, src, status, said) in [
        ("void", "pub fn main() { let n = 1; _ = n; }", 0, ""),
        ("ok", "error E { Bad } pub fn main() -> E!void { }", 0, ""),
        ("ok_status", "error E { Bad } fn f() -> E!i32 { return 42; } pub fn main() -> E!i32 { return try f(); }", 42, ""),
        ("error", "error E { First, Code(i32) } pub fn main() -> E!void { return E::Code(9); }", 1, "error: E::Code(9)"),
        ("error_status", "error E { First } pub fn main() -> E!i32 { return .First; }", 1, "error: E::First"),
        ("composed", "error E { A } error F { B } fn f() -> F!void { return .B; } pub fn main() -> (E || F)!void { try f(); }", 1, "error: F::B"),
        ("errdefer_first", "error E { A } pub fn main() -> E!void { errdefer eprintln(\"undo\"); return .A; }", 1, "undo\nerror: E::A"),
    ] {
        let (vm, native) = crate::tests::run_both(name, src);
        let vm = vm.unwrap_or_else(|e| panic!("[{name}] {e}"));
        assert_eq!((vm.value, native), (status, Some(status as i32)), "[{name}]");
        assert!(vm.output.contains(said), "[{name}] wrote: {}", vm.output);
    }
    assert_rejected(
        "main_bool",
        "pub fn main() -> bool { return true; }",
        "'main' returns 'i32', 'void', 'E!void', or 'E!i32'; 'bool' is none of these",
    );
    assert_rejected(
        "main_error_names_main",
        "error E { A } pub fn main() -> E!void { let s = String::from(\"a\"); let t = s; let n = s.len(); }",
        "in root::main (",
    );
    // In a test, a failed `try` fails the test, as a failed `@assert` does; a function literal's
    // `try` is its own.
    let dir = std::env::temp_dir().join(format!("sloplang_try_in_tests_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("t.slop");
    std::fs::write(
        &file,
        "error E { Bad }
fn f(ok: bool) -> E!i32 { if ok { return 1; } return .Bad; }
test \"passes\" { let x = try f(true); @assert(x == 1); }
test \"fails\" { let x = try f(false); @assert(x == 1); }
test \"own\" { let g = fn() -> E!i32 { return try f(false); }; @assert((g() catch 7) == 7); }
pub fn main() -> i32 { return 0; }
",
    )
    .unwrap();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let status = crate::cli::main_with(&["test".to_string(), file.display().to_string()], &mut out, &mut err);
    let out = String::from_utf8_lossy(&out).into_owned() + &String::from_utf8_lossy(&err);
    let _ = std::fs::remove_dir_all(&dir);
    assert_eq!(status, 1, "{out}");
    assert!(out.contains("test fails ... FAILED: error returned: E::Bad (line 4, column 24)"), "{out}");
    assert!(out.contains("2 passed, 1 failed"), "{out}");
}

#[test]
fn test_error_return_traces() {
    // The VM keeps where an error was returned from, each function it passed through, and
    // drops an error once it is handled; `main` prints it after the error.
    let src = "error ConfigError { Missing(i32), Bad }
fn parse(n: i32) -> ConfigError!i32 {
    if n < 0 {
        return ConfigError::Missing(n);
    }
    return n;
}
fn recovered() -> i32 {
    return parse(-1) catch 0;
}
fn load(n: i32) -> ConfigError!i32 {
    errdefer eprintln(\"load failed\");
    let r = recovered();
    let v = try parse(n);
    return v + r;
}
fn replaced() -> ConfigError!i32 {
    return parse(-2) catch |e| return .Bad;
}
pub fn main() -> ConfigError!void {
    let a = try load(1);
    _ = a;
    let c = replaced() catch 0;
    _ = c;
    let b = try load(-5);
    _ = b;
}";
    let run = crate::tests::run_vm("error_trace", src).unwrap();
    assert_eq!(run.value, 1);
    assert_eq!(
        run.output,
        "load failed
error: ConfigError::Missing(-5)
error return trace:
  returned at line 4, column 9 in root::parse
  returned at line 14, column 5 in root::load
  returned at line 25, column 5 in root::main
"
    );
    // An error replaced by another keeps the first's trace; the test failure shows it.
    let dir = std::env::temp_dir().join(format!("sloplang_error_traces_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let file = dir.join("t.slop");
    std::fs::write(
        &file,
        "error E { Bad, Worse }
fn g() -> E!i32 { return .Bad; }
fn f() -> E!i32 { return g() catch |e| return .Worse; }
test \"fails\" { let x = try f(); @assert(x == 1); }
pub fn main() -> i32 { return 0; }
",
    )
    .unwrap();
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let _ = crate::cli::main_with(&["test".to_string(), file.display().to_string()], &mut out, &mut err);
    let out = String::from_utf8_lossy(&out).into_owned() + &String::from_utf8_lossy(&err);
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        out.contains(
            "FAILED: error returned: E::Worse (line 4, column 24)
error return trace:
  returned at line 2, column 19 in root::g
  returned at line 3, column 19 in root::f"
        ),
        "{out}"
    );
}

#[test]
fn test_error_return_traces_natively_and_through_tasks() {
    // A native build keeps the trace too, and prints the same one; an error a generator
    // yields, or a task returns to `await`, keeps where it started.
    let through_task = "error E { Bad }
fn deep(n: i32) -> E!i32 { if n > 1 { return .Bad; } return n; }
fn nums() -> gen i32 { for i in 0..3 { yield i; } }
fn work(n: i32) -> E!i32 { return try deep(n); }
fn run() -> E!i32 {
    let mut t = 0;
    for x in nums() { t += try work(x); }
    return t;
}
fn task_body() -> E!i32 { return try work(5); }
fn via_task() -> E!i32 {
    let t = async task_body();
    return try t.await();
}
pub fn main() -> E!void {
    let a = run() catch 0;
    _ = a;
    let b = try via_task();
    _ = b;
}";
    let through_generator = "error E { Bad }
fn check(n: i32) -> E!i32 { if n == 2 { return .Bad; } return n; }
fn items() -> gen i32 {
    for i in 0..4 {
        let v = check(i) catch 99;
        yield v;
    }
}
fn checked_items() -> gen E!i32 {
    for i in 0..4 {
        yield check(i);
    }
}
fn sum() -> E!i32 {
    let mut t = 0;
    for x in items() { t += x; }
    for r in checked_items() { t += try r; }
    return t;
}
pub fn main() -> E!void {
    let s = try sum();
    _ = s;
}";
    for (name, src, trace) in [
        ("task", through_task, "error: E::Bad
error return trace:
  returned at line 2, column 39 in root::deep
  returned at line 4, column 28 in root::work
  returned at line 10, column 27 in root::task_body
  returned at line 13, column 5 in root::via_task
  returned at line 18, column 5 in root::main
"),
        ("generator", through_generator, "error: E::Bad
error return trace:
  returned at line 2, column 41 in root::check
  returned at line 17, column 32 in root::sum
  returned at line 21, column 5 in root::main
"),
    ] {
        let dir = std::env::temp_dir().join(format!("sloplang_native_traces_{name}_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("p.slop");
        std::fs::write(&file, src).unwrap();
        for vm in [true, false] {
            let mut args = vec!["run".to_string(), file.display().to_string()];
            if vm {
                args.push("--vm".to_string());
            }
            let (mut out, mut err) = (Vec::new(), Vec::new());
            let status = crate::cli::main_with(&args, &mut out, &mut err);
            let err = String::from_utf8_lossy(&err).into_owned();
            assert_eq!((status, err.as_str()), (1, trace), "[{name}, vm: {vm}]");
        }
        let _ = std::fs::remove_dir_all(&dir);
    }
}
