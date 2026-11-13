use super::*;

#[test]
fn test_linear_types_do_not_cross_the_c_boundary() {
    const EXPECTED: &str = "cannot cross the C boundary by value";
    reject(
        "extern_param",
        &with_tx("extern fn sink(t: Tx);\npub fn main() -> i32 { sink(Tx::new(1)); return 0; }"),
        EXPECTED,
    );
    // A value returned from C could be forged: a `ScopedHandle` for a thread that never existed.
    reject(
        "extern_return_forges_handle",
        "extern fn forge() -> ScopedHandle[fn() -> i32];
pub fn main() -> i32 { let h = forge(); return h.join(); }",
        EXPECTED,
    );
    reject(
        "extern_return_struct_holding_linear",
        &with_tx(
            "pub struct P { t: Tx }
extern fn forge() -> P;
pub fn main() -> i32 { return forge().t.commit(); }",
        ),
        EXPECTED,
    );
    reject(
        "extern_fn_pointer_type",
        &with_tx("pub fn main() -> i32 { let f: ?extern fn(Tx) = null; return 0; }"),
        EXPECTED,
    );
    reject(
        "export_param",
        &with_tx(
            "export fn take(t: Tx) -> i32 { return t.commit(); }\npub fn main() -> i32 { return 0; }",
        ),
        EXPECTED,
    );
    reject(
        "export_return",
        &with_tx("export fn give() -> Tx { return Tx::new(1); }\npub fn main() -> i32 { return 0; }"),
        EXPECTED,
    );
    // Behind a raw pointer the value stays owned on this side.
    accept(
        "extern_pointer",
        &with_tx(
            "extern fn peek(t: *const Tx) -> i32;
pub fn main() -> i32 { let t = Tx::new(1); let n = unsafe { peek(&t as *const Tx) }; return t.commit() + n; }",
        ),
    );
}

#[test]
fn test_unsafe_fn_and_safe_extern_fn() {
    const WRITE_RAW: &str = "unsafe fn write_raw(p: *mut i32, v: i32) { unsafe { *p = v; } }\n";
    const UNSAFE_CALL: &str = "requires an 'unsafe { ... }' block";
    // Calling an `unsafe fn` (free, method, or static) needs an `unsafe` block.
    reject(
        "free_fn",
        &format!("{WRITE_RAW}pub fn main() -> i32 {{ let mut x: i32 = 0; write_raw(&raw mut x, 1); return x; }}"),
        "Calling 'unsafe fn' 'write_raw'",
    );
    accept(
        "free_fn_in_unsafe",
        &format!("{WRITE_RAW}pub fn main() -> i32 {{ let mut x: i32 = 0; unsafe {{ write_raw(&raw mut x, 1); }} return x; }}"),
    );
    reject(
        "method",
        "pub struct S { n: i32, pub unsafe fn get(&self) -> i32 { return self.n; } }
pub fn main() -> i32 { let s = S { n: 1 }; return s.get(); }",
        UNSAFE_CALL,
    );
    reject(
        "static_method",
        "pub struct S { n: i32, pub unsafe fn make() -> Self { return Self { n: 1 }; } }
pub fn main() -> i32 { return S::make().n; }",
        UNSAFE_CALL,
    );
    // The body of an `unsafe fn` is not itself an `unsafe` block.
    reject(
        "body_not_unsafe",
        "unsafe fn deref(p: *mut i32) -> i32 { return *p; }\npub fn main() -> i32 { return 0; }",
        "requires an 'unsafe { ... }' block",
    );

    // Function pointers: an `unsafe fn` value has an `unsafe fn(...)` type, calls through it need
    // `unsafe`, and it never converts to a safe pointer (a safe function may become an unsafe one).
    reject(
        "unsafe_fn_value_call",
        &format!("{WRITE_RAW}pub fn main() -> i32 {{ let mut x: i32 = 0; let f = write_raw; f(&raw mut x, 1); return x; }}"),
        "through an unsafe function pointer type ('unsafe fn(*mut i32, i32)')",
    );
    reject(
        "unsafe_to_safe_pointer",
        &format!("{WRITE_RAW}pub fn main() -> i32 {{ let f: fn(*mut i32, i32) = write_raw; return 0; }}"),
        "an 'unsafe fn' pointer cannot become a safe one",
    );
    assert_eq!(
        run_lli(
            "safe_to_unsafe_pointer",
            "fn add(a: i32) -> i32 { return a + 1; }
pub fn main() -> i32 { let f: unsafe fn(i32) -> i32 = add; return unsafe { f(41) }; }",
        ),
        Some(42)
    );

    // Trait methods: implementations must match, and dynamic calls go through an unsafe vtable slot.
    const TRAIT: &str = "trait T { unsafe fn f(&self) -> i32; }\n";
    reject(
        "impl_must_match",
        &format!("{TRAIT}pub struct S {{ n: i32, impl T {{ fn f(&self) -> i32 {{ return self.n; }} }} }}
pub fn main() -> i32 {{ let s = S {{ n: 1 }}; return unsafe {{ s.f() }}; }}"),
        "is declared 'fn', but trait 'T' declares it 'unsafe fn'",
    );
    reject(
        "dyn_call",
        &format!("{TRAIT}pub struct S {{ n: i32, impl T {{ unsafe fn f(&self) -> i32 {{ return self.n; }} }} }}
pub fn main() -> i32 {{ let s = S {{ n: 1 }}; let t: &T = &s; return t.f(); }}"),
        UNSAFE_CALL,
    );
    accept(
        "dyn_call_in_unsafe",
        &format!("{TRAIT}pub struct S {{ n: i32, impl T {{ unsafe fn f(&self) -> i32 {{ return self.n; }} }} }}
pub fn main() -> i32 {{ let s = S {{ n: 1 }}; let t: &T = &s; return unsafe {{ t.f() }}; }}"),
    );

    // `extern fn` is unsafe to call unless declared `safe extern fn`; safety belongs to each
    // declaration, so another module's `safe` declaration of the same symbol does not leak in.
    reject(
        "extern_call",
        "extern fn abs(x: i32) -> i32;\npub fn main() -> i32 { return abs(-1); }",
        "Calling extern function 'abs' requires an 'unsafe { ... }' block",
    );
    assert_eq!(
        run_lli(
            "safe_extern_call",
            "safe extern fn abs(x: i32) -> i32;\npub fn main() -> i32 { return abs(-7); }",
        ),
        Some(7)
    );
    reject(
        "unsafe_redeclaration_of_std_safe_malloc",
        "extern fn malloc(size: usize) -> *mut u8;\npub fn main() -> i32 { let p = malloc(8); return 0; }",
        "Calling extern function 'malloc'",
    );
}

#[test]
fn test_c_abi_of_unsafe_fn_is_unsafe() {
    // The C entry point of an `unsafe export fn` keeps its preconditions.
    reject(
        "c_abi_unsafe_export",
        "export unsafe fn poke(p: *mut i32) { unsafe { *p = 1; } }
pub fn main() -> i32 { let f = @c_abi(poke); f(0 as *mut i32); return 0; }",
        "unsafe extern fn(*mut i32)",
    );
}

#[test]
fn test_export_fn_two_symbol_model() {
    let src = "\
export fn first_byte(p: *const u8) -> u8 {
    unsafe { return *p; }
}
pub fn main() -> i32 {
    let b: u8 = 7;
    return first_byte(&raw const b) as i32;
}
";
    let program = Compiler::compile_source(src).expect("export program should compile");
    // The exported symbol belongs to the C-ABI wrapper, which performs the entry null check...
    let wrapper = program
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("first_byte"))
        .expect("C-ABI wrapper carries the exported symbol");
    assert!(
        wrapper
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, crate::ir::Terminator::Unreachable)),
        "wrapper should trap on NULL"
    );
    // ...while the internal SlopLang-ABI body has no exported symbol and no null-check trap.
    let body = program
        .functions
        .iter()
        .find(|f| f.debug_name.as_deref() == Some("root::first_byte"))
        .expect("internal body");
    assert!(body.export.is_none());
    assert!(
        !body
            .blocks
            .iter()
            .any(|b| matches!(b.terminator, crate::ir::Terminator::Unreachable)),
        "internal body should not contain the C null check"
    );

    // SlopLang code may only use the SlopLang signature; the C ABI is reachable via `@c_abi`.
    let opt = "\
export fn maybe(ok: bool) -> ?i32 {
    if ok { return 1; }
    return null;
}
";
    reject(
        "call_with_c_abi_arguments",
        &format!(
            "{opt}pub fn main() -> i32 {{ let mut out: i32 = 0; let ok = maybe(true, &raw mut out); return out; }}"
        ),
        "must be called with its SlopLang signature",
    );
    accept(
        "c_abi_function_pointer",
        &format!(
            "{opt}pub fn main() -> i32 {{
    let f = @c_abi(maybe);
    let mut out: i32 = 0;
    let ok = f(true, &raw mut out);
    let v = maybe(true) orelse 0;
    return out + v;
}}"
        ),
    );
    reject(
        "c_abi_of_non_export",
        "fn helper() -> i32 { return 1; }\npub fn main() -> i32 { let f = @c_abi(helper); return 0; }",
        "requires an 'export fn'",
    );
}

#[test]
fn test_runtime_safety_traps() {
    // In-bounds accesses, range slices, and the edge cases of the checks run normally.
    assert_eq!(
        run_lli(
            "in_bounds",
            "fn at(a: &slice[i32], i: usize) -> i32 { return a[i]; }
fn tail(a: &slice[i32], lo: usize, hi: usize) -> usize { let s = a[lo..hi]; return s.len; }
pub fn main() -> i32 {
    let arr: array[i32; 4] = .[10, 20, 30, 2];
    let idx: usize = 3;
    let v = simd[i32; 4] { 1, 2, 3, 4 };
    if at(&arr, 1) != 20 { return 1; }
    if arr[idx] != 2 { return 2; }
    if v[idx] != 4 { return 3; }
    if tail(&arr, 1, 4) != 3 { return 4; }
    if tail(&arr, 4, 4) != 0 { return 5; }
    return 42;
}"
        ),
        Some(42)
    );
    // Each of these would be undefined behaviour without a check; they must trap instead.
    let traps = [
        (
            "array_index",
            "fn at(i: usize) -> i32 { let a: array[i32; 4] = .[1, 2, 3, 4]; return a[i]; }
pub fn main() -> i32 { return at(4); }",
        ),
        (
            "slice_index",
            "fn at(a: &slice[i32], i: usize) -> i32 { return a[i]; }
pub fn main() -> i32 { let arr: array[i32; 2] = .[1, 2]; return at(&arr, 2); }",
        ),
        (
            "slice_range_end",
            "fn sub(a: &slice[i32], hi: usize) -> usize { let s = a[0..hi]; return s.len; }
pub fn main() -> i32 { let arr: array[i32; 2] = .[1, 2]; return sub(&arr, 3) as i32; }",
        ),
        (
            "division_by_zero",
            "fn div(a: i32, b: i32) -> i32 { return a / b; }\npub fn main() -> i32 { return div(1, 0); }",
        ),
        (
            "remainder_by_zero",
            "fn rem(a: u32, b: u32) -> u32 { return a % b; }\npub fn main() -> i32 { return rem(1, 0) as i32; }",
        ),
        (
            "signed_min_div_neg_one",
            "fn div(a: i32, b: i32) -> i32 { return a / b; }\npub fn main() -> i32 { return div(-2147483648, -1); }",
        ),
        (
            "shift_by_width",
            "fn shl(a: i32, b: i32) -> i32 { return a << b; }\npub fn main() -> i32 { return shl(1, 32); }",
        ),
        (
            "shift_negative",
            "fn shr(a: i32, b: i32) -> i32 { return a >> b; }\npub fn main() -> i32 { return shr(1, -1); }",
        ),
        // Compound assignments are checked as their operators are.
        (
            "compound_shift_by_width",
            "fn shl(a: u8, b: u8) -> u8 { let mut x = a; x <<= b; return x; }\npub fn main() -> i32 { return shl(1, 8) as i32; }",
        ),
        (
            "compound_division_by_zero",
            "fn rem(a: i32, b: i32) -> i32 { let mut x = a; x %= b; return x; }\npub fn main() -> i32 { return rem(1, 0); }",
        ),
    ];
    for (name, src) in traps {
        assert_eq!(run_lli(name, src), Some(TRAP_EXIT), "[{name}] expected a trap");
    }

    // Float-to-integer casts saturate, and NaN converts to 0.
    assert_eq!(
        run_lli(
            "saturating_casts",
            "fn to_i32(x: f64) -> i32 { return x as i32; }
fn to_u8(x: f64) -> u8 { return x as u8; }
pub fn main() -> i32 {
    let zero: f64 = 0.0;
    if to_i32(100000000000.0) != 2147483647 { return 1; }
    if to_i32(-100000000000.0) != -2147483648 { return 2; }
    if to_u8(-5.0) != 0 { return 3; }
    if to_u8(300.0) != 255 { return 4; }
    if to_i32(zero / zero) != 0 { return 5; }
    return 42;
}"
        ),
        Some(42)
    );

    // Statically known indices are checked at compile time.
    reject(
        "constant_index_out_of_bounds",
        "pub fn main() -> i32 { let a: array[i32; 4] = .[1, 2, 3, 4]; return a[4]; }",
        "Index 4 is out of bounds for length 4",
    );
    reject(
        "constant_range_end_out_of_bounds",
        "pub fn main() -> i32 { let a: array[i32; 4] = .[1, 2, 3, 4]; let s = a[0..5]; return 0; }",
        "Slice end 5 is out of bounds for length 4",
    );
}

#[test]
fn test_wide_integer_constants_and_compile_time_arithmetic() {
    // Literals beyond `i128`, wide constant folding, and the VM agree with compiled code.
    let src = "const K: u256 = 1 << 200;
const W: u8 = 200 +% 100;
pub fn main() -> i32 {
    let digest: u256 = 0x9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08;
    let top = digest >> 248; // 0x9f = 159
    let m: u128 = 340282366920938463463374607431768211455;
    let low = (m -% 254) as u8; // 1
    let k = (K >> 199) as i32; // 2
    let neg: i8 = -128;
    return (top as i32) - 159 + (low as i32) + k + (W as i32) - 44 + 39 + (neg as i32) + 128;
}";
    assert_eq!(run_lli("wide_consts", src), Some(42));
    let mut program = Compiler::compile_source(src).expect("compiles");
    let main_fn = program
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    assert_eq!(
        crate::vm::Vm::eval(&mut program, main_fn, Vec::new()),
        Ok(crate::vm::Value::Int(42))
    );

    // Compile-time arithmetic follows the declared type's runtime rules.
    reject("const_overflow", "const X: u8 = 200 + 100;\npub fn main() -> i32 { return X as i32; }", "Compile-time integer overflow: 200 + 100 = 300 (in 'u8')");
    reject("const_div_zero", "const X: i32 = 1 / 0;\npub fn main() -> i32 { return X; }", "Compile-time division by zero");
    reject("const_min_div_neg_one", "const X: i8 = -128 / -1;\npub fn main() -> i32 { return X as i32; }", "Compile-time integer overflow");
    reject("const_shift_oob", "const X: u8 = 1 << 8;\npub fn main() -> i32 { return X as i32; }", "shift amount 8 is out of range");
    reject("literal_out_of_range", "pub fn main() -> i32 { let x: u8 = 300; return x as i32; }", "Integer literal 300 does not fit in 'u8'");
    reject("wide_literal_needs_wide_type", "pub fn main() -> i32 { let x = 340282366920938463463374607431768211455; return 0; }", "give it a wide integer type");
}

#[test]
fn test_vm_transmute_matches_compiled_layout() {
    let src = "alias PosixFd = i32 in 0..=2147483647;
struct P { a: u8, b: u32 }
pub fn main() -> i32 {
    let fd: ?PosixFd = null;
    let some: ?PosixFd = 7 as PosixFd;
    let p = P { a: 1, b: 2 };
    let f: f32 = 1.0;
    unsafe {
        let raw = @transmute(u64, p);
        let back = @transmute(P, raw);
        // -1 + 7 + 2 * 20 + 1 - 7 + (0x3f80_0000 >> 24 = 63) - 61 = 42
        return @transmute(i32, fd) + @transmute(i32, some) + ((raw >> 32) as i32) * 20
            + (back.a as i32) - 7 + ((@transmute(u32, f) >> 24) as i32) - 61;
    }
}";
    assert_eq!(run_lli("transmute_layout", src), Some(42));
    let mut program = Compiler::compile_source(src).expect("compiles");
    let main_fn = program
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    assert_eq!(
        crate::vm::Vm::eval(&mut program, main_fn, Vec::new()),
        Ok(crate::vm::Value::Int(42))
    );
}

#[test]
fn test_compile_time_functions_run_on_the_vm() {
    assert_eq!(
        run_lli(
            "comptime_vm",
            "fn fib(n: i32) -> i32 { if n < 2 { return n; } return fib(n - 1) + fib(n - 2); }
fn sum(n: i32) -> i32 { let mut s: i32 = 0; let mut i: i32 = 0; while i < n { s += i; i = i + 1; } return s; }
fn four() -> usize { return 4; }
fn Pick[n: i32]() -> type {
    let mut i: i32 = 0;
    while i < n { i = i + 1; if i == 2 { continue; } }
    if i == 3 { return u8; }
    return u64;
}
const F: i32 = fib(9);
const S: i32 = sum(4);
pub fn main() -> i32 {
    let a: array[i32; four()] = .[1, 2, 3, 4];
    // 34 + 6 + 4 - 3 + 1 = 42
    return F + S + (a.len as i32) - 3 + (@size_of(Pick[3]) as i32);
}"
        ),
        Some(42)
    );
    reject(
        "comptime_step_limit",
        "fn spin() -> i32 { let mut i: i32 = 0; while true { i = i +% 1; } return i; }\nconst X: i32 = spin();\npub fn main() -> i32 { return X; }",
        "exceeded step limit",
    );
    reject(
        "comptime_extern_call",
        "extern fn puts(s: *const u8) -> i32;\nfn f() -> i32 { unsafe { return puts(\"x\" as *const u8); } }\nconst X: i32 = f();\npub fn main() -> i32 { return X; }",
        "cannot call extern function",
    );
}

#[test]
fn test_sha256() {
    let hex = |data: &[u8]| crate::sha256::hex(&crate::sha256::digest(data));
    assert_eq!(hex(b""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855");
    assert_eq!(hex(b"abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad");
    assert_eq!(
        hex(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
    assert_eq!(hex(&vec![b'a'; 1_000_000]), "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0");
}

#[test]
fn test_vm_emulates_io_only_when_allowed() {
    // Compile-time code is sandboxed, whatever a test's own run of the VM allows.
    for (name, call) in [
        ("file", "if read_file(\"x\") == null { return 1; } return 2;"),
        ("socket", "if TcpListener::bind(\"127.0.0.1\", 0) == null { return 1; } return 2;"),
        ("output", "println(\"x\"); return 1;"),
    ] {
        assert_rejected(
            name,
            &format!("fn f() -> i32 {{ {call} }}\nconst N: i32 = f();\npub fn main() -> i32 {{ return N; }}"),
            "cannot call extern function",
        );
    }
    for (name, src, value) in [
        (
            "missing_file",
            "pub fn main() -> i32 { if read_file(\"/no/such/file\") == null { return 1; } return 2; }",
            1,
        ),
        (
            "nothing_listening",
            "pub fn main() -> i32 {
    let port = (TcpListener::bind(\"127.0.0.1\", 0) orelse unreachable).port();
    let fd = connect_to(\"127.0.0.1\", port) catch |e| { return 7; };
    return 1;
}",
            7,
        ),
        // Closing a listener closes what it had yet to accept.
        (
            "connection_never_accepted",
            "pub fn main() -> i32 {
    let listener = TcpListener::bind(\"127.0.0.1\", 0) orelse unreachable;
    let client = connect_to(\"127.0.0.1\", listener.port()) catch |e| { return 2; };
    return 1;
}",
            1,
        ),
        (
            "both_ways_on_one_socket",
            "pub fn main() -> i32 {
    let listener = TcpListener::bind(\"127.0.0.1\", 0) orelse unreachable;
    let client = connect_to(\"127.0.0.1\", listener.port()) catch |e| { return 1; };
    let server = listener.accept() catch |e| { return 2; };
    client.write_all(\"ping\") catch |e| { return 3; };
    server.write_all(\"pong!\") catch |e| { return 4; };
    let mut buf: array[u8; 8] = @default(array[u8; 8]);
    let a = server.read(&mut buf) catch |e| { return 5; };
    let b = client.read(&mut buf) catch |e| { return 6; };
    return (a * 10 + b) as i32;
}",
            45,
        ),
    ] {
        assert_runs(name, src, value);
    }
    // `errno` belongs to the OS thread, so fibers on one share it, which a VM must keep to:
    // one that failed and then parked would otherwise find its own again.
    assert_runs(
        "errno_is_per_thread",
        "extern fn __errno_location() -> *mut i32;
fn place() -> usize { return unsafe { __errno_location() } as usize; }
pub fn main() -> i32 {
    let here = place();
    let fiber = async(Fibers {}) place();
    let thread = async(Threads {}) place();
    return (fiber.await() == here) as i32 * 10 + (thread.await() != here) as i32;
}",
        11,
    );
    let mapping = |len: &str, body: &str| {
        format!(
            "extern fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
extern fn munmap(addr: *mut u8, len: usize) -> i32;
pub fn main() -> i32 {{ unsafe {{
    let m = mmap(0 as *mut u8, {len}, 3, 34, -1, 0);
    {body}
    let _rc = munmap(m, {len});
    return r;
}} }}"
        )
    };
    // A mapping costs nothing until used, as a fiber's stack never is: this one is 4 TB.
    let huge = mapping("4398046511104", "let r: i32 = 5;");
    let run = crate::tests::run_vm("huge_mapping", &huge).unwrap();
    assert_eq!((run.value, run.leaks), (5, 0));
    for (name, body, value) in [
        ("words", "let p = m as *mut u64; *(p + 1) = 9; let r = *(p + 1) as i32;", 9),
        ("bytes", "let p = m as *const u8 as *mut u8; *(p + 3) = 6; let r = *(p + 3) as i32;", 6),
    ] {
        assert_runs(name, &mapping("64", body), value);
    }
}

#[test]
fn test_string_keys() {
    let prelude = "static mut DROPS: i32 = 0;
pub struct P { x: i32, y: i32 }
impl Hash for P { fn hash(&self) -> u64 { return (self.x * 31 + self.y) as u64; } }
impl Eq for P { fn eq(&self, other: &Self) -> bool { return self.x == other.x && self.y == other.y; } }
pub opaque Name {
    s: String,
    pub fn new(s: &str) -> Self { return Self { s: String::from(s) }; }
    impl Hash { fn hash(&self) -> u64 { return self.s.len() as u64; } }
    impl Eq { fn eq(&self, other: &Self) -> bool { return self.s.as_str() == other.s.as_str(); } }
}
pub opaque Noisy {
    pub fn new() -> Self { return Self { }; }
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + 1; } } }
}
fn key(s: &str) -> String { return String::from(s); }
";
    for (name, body, value) in [
        ("lookup_by_str", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let _b = m.insert(key(\"b\"), 2); return *(m.get(\"b\") orelse unreachable);", 2),
        ("missing", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); return m.contains_key(\"z\") as i32;", 0),
        ("replaces", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let old = m.insert(key(\"a\"), 2); return (old orelse 0) * 10 + m.len() as i32;", 11),
        ("get_mut", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); if let ?v = m.get_mut(\"a\") { *v = 5; } return *(m.get(\"a\") orelse unreachable);", 5),
        ("remove", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let old = m.remove(\"a\"); return (old orelse 0) * 10 + m.len() as i32;", 10),
        ("reinsert_after_remove", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let _b = m.remove(\"a\"); let _c = m.insert(key(\"a\"), 3); return *(m.get(\"a\") orelse unreachable);", 3),
        ("grows", "let mut m = HashMap[String, i32]::new(); for i in 0..200 { let _a = m.insert(format(i), i); } return *(m.get(\"137\") orelse unreachable) + m.len() as i32 / 100;", 139),
        ("views_of_keys", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"abc\"), 1); let keys = m.keys(); return (*(keys.get(0) orelse unreachable)).len as i32;", 3),
        ("drain", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"abc\"), 1); let mut n: i32 = 0; m.drain(fn(k: String, v: i32) { n = n + k.len() as i32 + v; }); return n;", 4),
        // Keys of the types that were always allowed.
        ("integer", "let mut m = HashMap[i32, i32]::new(); let _a = m.insert(4, 5); return *(m.get(4) orelse unreachable);", 5),
        ("borrowed_str", "let s = String::from(\"hey\"); let mut m = HashMap[&str, i32]::new(); let _a = m.insert(s.as_str(), 5); return *(m.get(\"hey\") orelse unreachable);", 5),
        // A type of its own, by value if `copy` and by reference if not.
        ("copy_struct", "let mut m = HashMap[P, i32]::new(); let _a = m.insert(P { x: 1, y: 2 }, 7); return *(m.get(P { x: 1, y: 2 }) orelse unreachable);", 7),
        ("collision", "let mut m = HashMap[Name, i32]::new(); let _a = m.insert(Name::new(\"ab\"), 1); let _b = m.insert(Name::new(\"cd\"), 2); let n = Name::new(\"cd\"); return *(m.get(&n) orelse unreachable) + m.len() as i32 * 10;", 22),
        ("copy_collision", "let mut m = HashMap[P, i32]::new(); let _a = m.insert(P { x: 0, y: 31 }, 1); let _b = m.insert(P { x: 1, y: 0 }, 2); return m.len() as i32;", 2),
        // Keys are owned: a replaced, removed, or remaining one is dropped once.
        ("values_drop", "if true { let mut m = HashMap[String, Noisy]::new(); let _a = m.insert(key(\"a\"), Noisy::new()); } return unsafe { DROPS };", 1),
        ("send", "let m = Mutex[HashMap[String, i32]]::new(HashMap[String, i32]::new()); let t = spawn_scoped(fn() -> i32 { let mut g = m.lock(); let _o = g.get_mut().insert(key(\"a\"), 1); g.unlock(); return 0; }); let r = t.join(); let mut g = m.lock(); let n = g.get_mut().len() as i32; g.unlock(); return n + r;", 1),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "key_outlives_a_map",
        &format!("{prelude}pub fn main() -> i32 {{ let mut k: &str = \"x\"; if true {{ let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let keys = m.keys(); k = *(keys.get(0) orelse unreachable); }} return k.len as i32; }}"),
        "already borrowed",
    );
    assert_rejected(
        "key_needs_a_hash",
        "pub struct Q { x: i32 }\npub fn main() -> i32 { let mut m = HashMap[Q, i32]::new(); let _a = m.insert(Q { x: 1 }, 1); return 0; }",
        "",
    );
}

#[test]
fn test_sorting() {
    let prelude = "fn nums(items: array[i32; 5], n: usize) -> Vec[i32] { let mut v = Vec[i32]::new(); for i in 0..n { v.push(items[i]); } return v; }
fn digits(v: &Vec[i32]) -> i32 { let mut t: i32 = 0; for x in v.iter() { t = t * 10 + *x; } return t; }
struct Pair { key: i32, order: i32 }
static mut LIVE: i32 = 0;
pub opaque Tracked {
    n: i32,
    pub fn new(n: i32) -> Self { unsafe { LIVE = LIVE + 1; } return Self { n: n }; }
    pub fn n(&self) -> i32 { return self.n; }
    impl drop { fn drop(&mut self) { unsafe { LIVE = LIVE - 1; } } }
}
";
    for (name, body, value) in [
        ("numbers", "let mut v = nums(.[3, 1, 2, 0, 0], 3); v.sort(); return digits(&v) % 100;", 23),
        ("empty", "let mut v = Vec[i32]::new(); v.sort(); return v.len() as i32;", 0),
        ("one", "let mut v = nums(.[7, 0, 0, 0, 0], 1); v.sort(); return digits(&v);", 7),
        ("already_sorted", "let mut v = nums(.[1, 2, 3, 0, 0], 3); v.sort(); return digits(&v) % 100;", 23),
        ("reversed", "let mut v = nums(.[5, 4, 3, 2, 1], 5); v.sort(); return digits(&v) % 100;", 45),
        ("descending", "let mut v = nums(.[1, 3, 2, 0, 0], 3); v.sort_by(fn(a: &i32, b: &i32) -> bool { return *a > *b; }); return digits(&v) % 100;", 21),
        // Equal elements stay in their order.
        ("stable", "let mut v = Vec[Pair]::new(); for i in 0..9 { v.push(Pair { key: i % 2, order: i }); } v.sort_by(fn(a: &Pair, b: &Pair) -> bool { return a.key < b.key; }); let mut t: i32 = 0; for p in v.iter() { t = t * 2 + (p.order % 3); } return (v.get(0) orelse unreachable).order * 10 + (v.get(8) orelse unreachable).order;", 7),
        // What cannot be copied is moved, each once.
        ("strings", "let mut v = Vec[String]::new(); v.push(String::from(\"pear\")); v.push(String::from(\"apple\")); v.push(String::from(\"fig\")); v.sort_by(fn(a: &String, b: &String) -> bool { return a.as_str().str_before(b.as_str()); }); return (v.get(0) orelse unreachable).len() as i32 * 10 + (v.get(2) orelse unreachable).len() as i32;", 54),
        ("owned_values", "if true { let mut v = Vec[Tracked]::new(); for i in 0..17 { v.push(Tracked::new(17 - i)); } v.sort_by(fn(a: &Tracked, b: &Tracked) -> bool { return a.n() < b.n(); }); if (v.get(0) orelse unreachable).n() != 1 { return 99; } } return unsafe { LIVE };", 0),
        ("zero_sized", "let mut v = Vec[void]::new(); v.push(void); v.push(void); v.sort_by(fn(a: &void, b: &void) -> bool { return false; }); return v.len() as i32;", 2),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_string_helpers() {
    let prelude = "fn int_or(s: &str, d: i64) -> i32 { return (s.parse_int() orelse d) as i32; }
fn part(v: &Vec[&str], i: usize) -> i32 { return (*(v.get(i) orelse unreachable)).len as i32; }
";
    for (name, body, value) in [
        ("trim", "return \"  ab \\n\".trim().len as i32;", 2),
        ("trim_nothing", "return \"ab\".trim().len as i32;", 2),
        ("trim_all", "return \"   \".trim().len as i32;", 0),
        ("trim_empty", "return \"\".trim().len as i32;", 0),
        ("starts_with", "return \"hello\".starts_with(\"he\") as i32 * 10 + \"he\".starts_with(\"hello\") as i32;", 10),
        ("ends_with", "return \"hello\".ends_with(\"lo\") as i32 * 10 + \"lo\".ends_with(\"hello\") as i32;", 10),
        ("find", "return (\"abcd\".find_str(\"cd\") orelse 99) as i32;", 2),
        ("find_missing", "return (\"abcd\".find_str(\"x\") orelse 99) as i32;", 99),
        ("find_too_long", "return (\"ab\".find_str(\"abc\") orelse 99) as i32;", 99),
        ("find_empty", "return (\"ab\".find_str(\"\") orelse 99) as i32;", 0),
        ("split", "let p = \"a,bb,ccc\".split(\",\"); return p.len() as i32 * 10 + part(&p, 2);", 33),
        ("split_empty_parts", "let p = \"a,,b\".split(\",\"); return p.len() as i32 * 10 + part(&p, 1);", 30),
        ("split_at_the_ends", "let p = \",a,\".split(\",\"); return p.len() as i32;", 3),
        ("split_nothing", "return \"\".split(\",\").len() as i32;", 1),
        ("split_longer_separator", "let p = \"a::b\".split(\"::\"); return p.len() as i32 * 10 + part(&p, 1);", 21),
        ("words", "let p = \"  one two\\tthree\\n\".words(); return p.len() as i32 * 10 + part(&p, 2);", 35),
        ("no_words", "return \"   \".words().len() as i32;", 0),
        ("parse", "return int_or(\"42\", 0);", 42),
        ("parse_negative", "return int_or(\"-42\", 0) + 50;", 8),
        ("parse_plus", "return int_or(\"+7\", 0);", 7),
        ("parse_invalid", "return int_or(\"4x\", 9);", 9),
        ("parse_empty", "return int_or(\"\", 9);", 9),
        ("parse_sign_only", "return int_or(\"-\", 9);", 9),
        ("parse_largest", "return ((\"9223372036854775807\".parse_int() orelse 0) % 256) as i32;", 255),
        ("parse_smallest", "return ((\"-9223372036854775808\".parse_int() orelse 1) == -9223372036854775807 - 1) as i32;", 1),
        ("parse_overflow", "return int_or(\"9223372036854775808\", 9);", 9),
        ("before", "return \"a\".str_before(\"b\") as i32 * 100 + \"ab\".str_before(\"a\") as i32 * 10 + \"a\".str_before(\"ab\") as i32;", 101),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "part_outlives_its_string",
        "pub fn main() -> i32 { let mut t: &str = \"\"; if true { let s = String::from(\" a \"); t = s.as_str().trim(); } return t.len as i32; }",
        "already borrowed",
    );
}

#[test]
fn test_optimized_code_agrees_about_layout() {
    // An optional's payload is where `opt` and the code generator would differ without a target.
    let src = "pub struct S { a: ?u64, b: u64 }
fn make(n: u64) -> S { return S { a: n, b: n + 1 }; }
fn sum(s: &S) -> i32 { if let ?a = s.a { return (a + s.b) as i32; } return 0; }
fn sq(a: i32) -> i32 { return a * a; }
pub fn main() -> i32 {
    let mut all = Vec[S]::new();
    for i in 0..4 { all.push(make(i as u64)); }
    let t = async(Fibers { }) sq(2);
    return sum(all.get(3) orelse unreachable) + t.await();
}";
    let program = Compiler::compile_source(src).unwrap();
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, 222).unwrap();
    assert!(ir.contains("target triple"), "the module must name its target");
    let dir = std::env::temp_dir().join(format!("sloplang-opt-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (input, output) = (dir.join("in.ll"), dir.join("out.ll"));
    std::fs::write(&input, &ir).unwrap();
    let optimized = std::process::Command::new("opt")
        .args(["-O2", "-S"])
        .arg(&input)
        .arg("-o")
        .arg(&output)
        .output()
        .expect("opt");
    assert!(optimized.status.success(), "{}", String::from_utf8_lossy(&optimized.stderr));
    let code = crate::tests::lli(&std::fs::read_to_string(&output).unwrap()).status.code();
    std::fs::remove_dir_all(&dir).unwrap();
    assert_eq!(code, Some(11));
}

#[test]
fn test_packed_structs_cross_to_c() {
    // C sees a packed type as its backing integer in a struct of its own, with a shift, a mask,
    // and inline accessors for each field: a C struct member per field would have the padding
    // and alignment of C, not the packed layout.
    let lib = "export enum(u2) Mode { Off, Slow, Fast }
export packed struct Inner { lo: u2, hi: u2 }
export packed struct Flags { ready: bool, mode: Mode, delta: i5, count: u12, inner: Inner, tail: u8 }
export packed struct Pair { a: u8, b: u16 }
export fn pair_b(p: Pair) -> u16 { return p.b; }
export fn make_pair() -> Pair { return Pair { a: 1, b: 515 }; }
export fn score(f: Flags) -> i32 {
    let mut n = f.count as i32 * 1000 + f.delta as i32 * 10 + f.inner.hi as i32 * 4 + f.inner.lo as i32;
    if f.ready { n = n + 100000000; }
    if f.mode == .Fast { n = n + 10000000; }
    return n + f.tail as i32 * 0;
}
export fn make_flags() -> Flags {
    return Flags { ready: true, mode: .Slow, delta: -7, count: 4000, inner: Inner { lo: 3, hi: 1 }, tail: 200 };
}
";
    let (program, header) = Compiler::compile_source_with_c_header(lib).expect("compiles");
    assert!(header.contains("struct Pair {\n    uint32_t bits;\n};"), "{header}");
    assert!(header.contains("#define Flags_count_SHIFT 8"), "{header}");
    let ir = crate::llvm::LlvmLowering::lower(&program).unwrap();
    let c_main = r#"#include <stdio.h>
#include "lib.h"
#define CHECK(c) do { if (!(c)) { printf("failed line %d\n", __LINE__); return 1; } } while (0)
int main(void) {
    Pair p = Pair_make(1, 515);
    CHECK(pair_b(p) == 515);
    Pair q = make_pair();
    CHECK(Pair_get_a(q) == 1 && Pair_get_b(q) == 515);
    Flags f = Flags_make(true, Mode_Fast, -3, 1234, Inner_make(2, 1), 77);
    CHECK(score(f) == 100000000 + 10000000 + 1234 * 1000 - 30 + 4 + 2);
    Flags g = make_flags();
    CHECK(Flags_get_ready(g) && Flags_get_mode(g) == Mode_Slow && Flags_get_delta(g) == -7);
    CHECK(Flags_get_count(g) == 4000 && Flags_get_tail(g) == 200);
    CHECK(Inner_get_lo(Flags_get_inner(g)) == 3 && Inner_get_hi(Flags_get_inner(g)) == 1);
    Flags h = Flags_with_count(g, 9);
    CHECK(Flags_get_count(h) == 9 && Flags_get_delta(h) == -7 && Flags_get_tail(h) == 200);
    /* A value too wide for its field is cut to it, and leaves its neighbours alone. */
    Inner i = Inner_with_lo(Inner_make(0, 1), 7);
    CHECK(Inner_get_lo(i) == 3 && Inner_get_hi(i) == 1);
    Flags k = Flags_with_delta(Flags_make(false, Mode_Off, 0, 0, Inner_make(0, 0), 0), -1);
    CHECK(Flags_get_delta(k) == -1 && Flags_get_count(k) == 0 && Flags_get_mode(k) == Mode_Off);
    printf("ok\n");
    return 0;
}
"#;
    let out = crate::tests::link_with_c("packed_c", &ir, &header, c_main).run(&[]);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "ok\n");
    // The header is C++ too, as its `extern "C"` says.
    let dir = std::env::temp_dir().join(format!("sloplang_packed_cxx_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.h"), &header).unwrap();
    std::fs::write(dir.join("use.cpp"), "#include \"lib.h\"\nint use(Flags f) { return Inner_get_hi(Flags_get_inner(f)) + Flags_get_delta(f); }\n").unwrap();
    let cxx = std::process::Command::new("clang++")
        .args(["-std=c++17", "-Wall", "-Werror", "-pedantic-errors", "-c", "use.cpp", "-o", "use.o"])
        .current_dir(&dir)
        .output()
        .unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(cxx.status.success(), "{}", String::from_utf8_lossy(&cxx.stderr));
    // Bits that name no variant of an enum field are refused at the boundary.
    let bad = r#"#include "lib.h"
int main(void) { Flags f = Flags_make(false, Mode_Off, 0, 0, Inner_make(0, 0), 0); f.bits |= 3u << Flags_mode_SHIFT; return score(f) == 0 ? 0 : 5; }
"#;
    let out = crate::tests::link_with_c("packed_c_bad", &ir, &header, bad).run(&[]);
    assert!(!out.status.success() && out.status.code() != Some(5), "{out:?}");
    for (name, src, message) in [
        ("too_wide", "export packed struct W { a: u64, b: u1 }", "C has no integer that wide"),
        ("float_field", "export packed struct F { a: u8, b: f32 }", "packed"),
        ("enum_not_exported", "enum(u2) M { A, B }\nexport packed struct F { m: M, x: u6 }", "'export' enum or packed struct"),
    ] {
        assert_rejected(name, src, message);
    }
}

