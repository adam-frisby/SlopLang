use crate::lower::Compiler;
use super::{run_lli, TRAP_EXIT};

/// A `linear` opaque type shared by the tests below.
const LINEAR_TX: &str = "\
pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(move self) -> i32 { return self.id; }
}
";

fn accept(name: &str, src: &str) {
    if let Err(e) = Compiler::compile_source(src) {
        panic!("[{name}] expected to compile, got error: {e}");
    }
}

fn reject(name: &str, src: &str, expected: &str) {
    match Compiler::compile_source(src) {
        Ok(_) => panic!("[{name}] expected a compile error containing {expected:?}"),
        Err(e) => assert!(
            e.contains(expected),
            "[{name}] expected error containing {expected:?}, got: {e}"
        ),
    }
}

fn with_tx(body: &str) -> String {
    format!("{LINEAR_TX}\n{body}")
}

#[test]
fn test_owns_makes_containers_linear_for_linear_elements() {
    // Owning containers become linear when their element type is linear, so dropping them is rejected...
    reject(
        "box_linear_dropped",
        &with_tx("pub fn main() -> i32 { let b = Box[Tx]::new(Tx::new(1)); return 0; }"),
        "Linear value",
    );
    reject(
        "mutex_linear_dropped",
        &with_tx("pub fn main() -> i32 { let m = Mutex[Tx]::new(Tx::new(1)); return 0; }"),
        "Linear value",
    );
    reject(
        "channel_linear_dropped",
        &with_tx("pub fn main() -> i32 { let c = Channel[Tx]::new(); return 0; }"),
        "Linear value",
    );
    // ...while their consuming exits hand the elements back.
    accept(
        "box_into_inner",
        &with_tx(
            "pub fn main() -> i32 { let b = Box[Tx]::new(Tx::new(1)); return b.into_inner().commit(); }",
        ),
    );
    accept(
        "mutex_into_inner",
        &with_tx(
            "pub fn main() -> i32 { let m = Mutex[Tx]::new(Tx::new(1)); return m.into_inner().commit(); }",
        ),
    );
    accept(
        "channel_close_and_drain",
        &with_tx(
            "pub fn main() -> i32 {
    let c = Channel[Tx]::new();
    c.send(Tx::new(1));
    c.close_and_drain(fn(t: Tx) { let _x = t.commit(); });
    return 0;
}",
        ),
    );
    // Affine and copy elements keep implicit scope-exit drops.
    accept(
        "box_affine",
        "pub fn main() -> i32 { let b = Box[i32]::new(7); let c = Box[i32]::new(8); return *b.get() + c.into_inner(); }",
    );
    accept(
        "mutex_affine",
        "pub fn main() -> i32 { let m = Mutex[i32]::new(3); return m.with_lock(fn(v: &mut i32) -> i32 { return *v; }); }",
    );
}

#[test]
fn test_owns_declaration_errors_and_lint() {
    reject(
        "owns_unknown_param",
        "fn W[T] -> type { return opaque(owns U) { p: *mut T }; }
pub fn main() -> i32 { let x: ?*mut W[i32] = null; return 0; }",
        "'owns U' on opaque 'W' does not name a comptime type parameter",
    );
    reject(
        "owns_copy",
        "fn W[T] -> type { return opaque(copy, owns T) { p: *mut T }; }
pub fn main() -> i32 { return 0; }",
        "'opaque(copy, owns ...)' is invalid",
    );

    // An owning container (has a `drop` hook) holding `T` only behind a raw pointer is linted.
    let leaky = "\
fn Leaky[T] -> type {
    return opaque {
        ptr: *mut T,
        impl drop { fn drop(self: &mut Self) { unsafe { @dealloc(self.ptr); } } }
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let l = Leaky[i32]::new(1); return 0; }
";
    let (_, warnings) = Compiler::compile_package_with_warnings(&[("root", leaky)])
        .expect("Leaky[i32] should compile with a warning");
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("opaque 'Leaky'") && w.contains("use '*own T' if it owns these values")),
        "Expected raw-pointer ownership lint, got: {warnings:?}"
    );

    // Non-owning views (no `drop` hook) and declared owners are not linted; neither is std.
    let view = "\
fn View[T] -> type {
    return opaque {
        ptr: *const T,
        pub fn of(r: &T) -> Self { return Self { ptr: r as *const T }; }
    };
}
pub fn main() -> i32 {
    let x: i32 = 1;
    let v = View[i32]::of(&x);
    let b = Box[i32]::new(2);
    let m = Mutex[i32]::new(3);
    return 0;
}
";
    let (_, warnings) = Compiler::compile_package_with_warnings(&[("root", view)])
        .expect("View[i32] should compile");
    assert!(warnings.is_empty(), "Unexpected warnings: {warnings:?}");
}

#[test]
fn test_storing_linear_values_out_of_sight_requires_an_owner() {
    // A method that hands a linear value to storage the move checker cannot follow (a raw-pointer
    // write, or a copy followed by `@forget`) must belong to a linear type; otherwise the container
    // is affine and its scope-exit drop discards the value. A raw pointer owns nothing, so a type
    // holding only one stays affine. No `drop` hook is needed for the leak, so the lint for raw
    // pointers in owning containers does not catch these.
    const EXPECTED: &str = "but 'Holder' is not linear";
    reject(
        "raw_store_without_owns",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let h = Holder[Tx]::new(Tx::new(1)); return 0; }",
        ),
        EXPECTED,
    );
    // `uninit T` storage holds a `T`, so it makes the holder linear: the store is fine, and
    // dropping the holder is the error.
    reject(
        "uninit_field_makes_holder_linear",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque {
        slot: uninit T,
        pub fn new(v: T) -> Self { return Self { slot: uninit(v) }; }
    };
}
pub fn main() -> i32 { let h = Holder[Tx]::new(Tx::new(1)); return 0; }",
        ),
        "Linear value 'h' of type 'Holder[Tx]'",
    );
    reject(
        "copy_then_forget_without_owns",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe {
                @memcpy(p, &v as *const T, 1);
                @forget(v);
            }
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let h = Holder[Tx]::new(Tx::new(1)); return 0; }",
        ),
        EXPECTED,
    );
    // Closures lowered inside a method are checked as part of it.
    reject(
        "closure_store_without_owns",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            let put = move fn() { unsafe { *p = move v; } };
            put();
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let h = Holder[Tx]::new(Tx::new(1)); return 0; }",
        ),
        EXPECTED,
    );
    // A `move fn` that captures a linear value is linear, so storing it is checked like any other.
    reject(
        "linear_closure_stored_without_owns",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
    };
}
fn wrap[F](f: F) -> Holder[F] { return Holder[F]::new(move f); }
pub fn main() -> i32 {
    let t = Tx::new(1);
    let h = wrap(move fn() -> i32 { return t.commit(); });
    return 0;
}",
        ),
        "but 'Holder' is not linear",
    );

    // Even in a linear type, a raw pointer owns nothing: storing through one is only a refill.
    reject(
        "raw_store_with_declared_owns",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque(owns T) {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
        pub fn release(move self) {}
    };
}
pub fn main() -> i32 { Holder[Tx]::new(Tx::new(1)).release(); return 0; }",
        ),
        "store it through an owning pointer ('*own T')",
    );

    // An owning pointer makes `Holder[Tx]` linear, so the store is accepted and the value must come
    // back out through a consuming method.
    let owning = "fn Holder[T] -> type {
    return opaque {
        ptr: *own T,
        pub fn new(v: T) -> Self {
            let p: *own T = unsafe { @alloc(T, 1) as *own T };
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
        pub fn take(move self) -> T {
            unsafe {
                let v = move *self.ptr;
                @dealloc(self.ptr);
                return v;
            }
        }
    };
}
";
    accept(
        "own_store",
        &with_tx(&format!(
            "{owning}pub fn main() -> i32 {{ let h = Holder[Tx]::new(Tx::new(1)); return h.take().commit(); }}"
        )),
    );
    reject(
        "owning_holder_dropped",
        &with_tx(&format!(
            "{owning}pub fn main() -> i32 {{ let h = Holder[Tx]::new(Tx::new(1)); return 0; }}"
        )),
        "Linear value",
    );

    // The check runs per instantiation: a non-owning container of non-linear values is unaffected,
    // and free functions that refill a slot they emptied (`core::mem::replace`) still work.
    accept(
        "raw_store_non_linear",
        "fn Holder[T] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let h = Holder[i32]::new(1); return 0; }",
    );
    accept(
        "free_fn_replace",
        &with_tx(
            "pub fn main() -> i32 {
    let mut t = Tx::new(1);
    let old = core::mem::replace(&mut t, Tx::new(2));
    return old.commit() + t.commit();
}",
        ),
    );
}

#[test]
fn test_free_functions_store_linear_values_only_to_refill_slots() {
    // Outside a method of a linear type, a linear value stored behind a pointer or in `uninit`
    // storage must refill a slot the function moved a value out of on every path; otherwise a
    // non-owning container could delegate the store to a helper and lose the value.
    const EXPECTED: &str = "where the move checker cannot follow it";
    reject(
        "delegated_to_free_helper",
        &with_tx(
            "fn write_raw[T](p: *mut T, v: T) { unsafe { *p = move v; } }
fn Holder[T] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            write_raw(p, move v);
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let h = Holder[Tx]::new(Tx::new(1)); return 0; }",
        ),
        EXPECTED,
    );
    reject(
        "closure_in_free_fn",
        &with_tx(
            "pub fn main() -> i32 {
    let t = Tx::new(1);
    let p: *mut Tx = @alloc(Tx, 1);
    let put = move fn() { unsafe { *p = move t; } };
    put();
    return 0;
}",
        ),
        EXPECTED,
    );
    reject(
        "uninit_in_free_fn",
        &with_tx("pub fn main() -> i32 { let s: uninit Tx = uninit(Tx::new(1)); return 0; }"),
        EXPECTED,
    );
    reject(
        "refill_on_one_path_only",
        &with_tx(
            "fn put(p: *mut Tx, c: bool, v: Tx) -> i32 {
    let mut n = 0;
    unsafe {
        if c { let old = move *p; n = old.commit(); }
        *p = move v;
    }
    return n;
}
pub fn main() -> i32 { return 0; }",
        ),
        EXPECTED,
    );
    accept(
        "refill_after_move_out",
        &with_tx(
            "fn put(p: *mut Tx, v: Tx) -> Tx {
    unsafe {
        let old = move *p;
        *p = move v;
        return old;
    }
}
pub fn main() -> i32 { return 0; }",
        ),
    );
    accept(
        "swap",
        &with_tx(
            "pub fn main() -> i32 {
    let mut a = Tx::new(1);
    let mut b = Tx::new(2);
    core::mem::swap(&mut a, &mut b);
    return a.commit() + b.commit();
}",
        ),
    );

    // `spawn_scoped` hands its closure to `ScopedHandle`, a linear owner, so a closure that
    // captures a linear value still runs on another thread.
    assert_eq!(
        run_lli(
            "scoped_linear_closure",
            &with_tx(
                "pub fn main() -> i32 {
    let t = Tx::new(5);
    let h = spawn_scoped(move fn() -> i32 { return t.commit(); });
    return h.join();
}",
            ),
        ),
        Some(5)
    );
}

#[test]
fn test_match_scrutinee_is_dropped_or_consumed() {
    const UNION: &str = "union U { A(Tx), B(i32) }\n";
    // An arm that does not move the linear payload out leaves it unconsumed.
    reject(
        "wildcard_discards_linear",
        &with_tx(&format!(
            "{UNION}pub fn main() -> i32 {{ let u = U::A(Tx::new(1)); return match u {{ .B(n) => n, _ => 0 }}; }}"
        )),
        "Linear value 'match scrutinee'",
    );
    reject(
        "if_let_fallthrough_discards_linear",
        &with_tx(&format!(
            "{UNION}pub fn main() -> i32 {{ let u = U::A(Tx::new(1)); if let .B(n) = u {{ return n; }} return 0; }}"
        )),
        "Linear value 'match scrutinee'",
    );
    // Arms holding only `copy` payloads need no consumption.
    accept(
        "every_linear_payload_moved",
        &with_tx(&format!(
            "{UNION}pub fn main() -> i32 {{
    let u = U::A(Tx::new(1));
    let r = match u {{ .A(t) => t.commit(), .B(n) => n }};
    let v = U::B(2);
    return r + match v {{ .A(t) => t.commit(), _ => 0 }};
}}"
        )),
    );

    // An affine payload that no arm moves out is dropped, exactly once.
    let affine = "\
static mut DROPS: i32 = 0;
pub opaque Res {
    n: i32,
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + 1; } } }
    pub fn new() -> Self { return Self { n: 1 }; }
    pub fn take(move self) -> i32 { return self.n; }
}
union U { A(Res), B(i32) }
fn wildcard() -> i32 { let u = U::A(Res::new()); return match u { .B(n) => n, _ => 0 }; }
fn moved() -> i32 { let u = U::A(Res::new()); return match u { .A(r) => r.take(), _ => 0 }; }
pub fn main() -> i32 {
    let _a = wildcard();
    let _b = moved();
    return unsafe { DROPS };
}
";
    assert_eq!(run_lli("affine_wildcard_drop", affine), Some(2));
}

#[test]
fn test_consuming_self_must_move_out_linear_fields() {
    // A `move self` method may retire `self`, but not a linear value held inline in it.
    const EXPECTED: &str = "must be moved out before 'self' is retired";
    reject(
        "discards_field",
        &with_tx(
            "pub opaque(linear) Wrap {
    t: Tx,
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn discard(move self) -> i32 { return 0; }
}
pub fn main() -> i32 { let w = Wrap::new(Tx::new(1)); return w.discard(); }",
        ),
        EXPECTED,
    );
    reject(
        "consumes_on_one_path_only",
        &with_tx(
            "pub opaque(linear) Wrap {
    t: Tx,
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn maybe(move self, c: bool) -> i32 { if c { return self.t.commit(); } return 0; }
}
pub fn main() -> i32 { let w = Wrap::new(Tx::new(1)); return w.maybe(true); }",
        ),
        EXPECTED,
    );
    reject(
        "discards_nested_field",
        &with_tx(
            "pub struct P { t: Tx, n: i32 }
pub opaque(linear) Wrap {
    p: P,
    pub fn new(t: Tx) -> Self { return Self { p: P { t: t, n: 1 } }; }
    pub fn take_n(move self) -> i32 { return self.p.n; }
}
pub fn main() -> i32 { let w = Wrap::new(Tx::new(1)); return w.take_n(); }",
        ),
        EXPECTED,
    );
    // With a `drop` hook the field cannot be moved out at all, so no method can retire `self`.
    reject(
        "drop_hook_with_linear_field",
        &with_tx(
            "pub opaque(linear) Wrap {
    t: Tx,
    impl drop { fn drop(self: &mut Self) { } }
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn discard(move self) -> i32 { return 0; }
}
pub fn main() -> i32 { let w = Wrap::new(Tx::new(1)); return w.discard(); }",
        ),
        EXPECTED,
    );
    // Moving the field out, consuming it, or delegating `self` to another consuming method is fine.
    accept(
        "moves_or_delegates",
        &with_tx(
            "pub struct P { t: Tx, n: i32 }
pub opaque(linear) Wrap {
    t: Tx,
    p: P,
    pub fn new(a: Tx, b: Tx) -> Self { return Self { t: a, p: P { t: b, n: 1 } }; }
    pub fn split(move self) -> tuple { Tx, Tx } { let p = self.p; return { self.t, p.t }; }
    pub fn finish(move self) -> i32 { let p = self.p; return self.t.commit() + p.t.commit() + p.n; }
    pub fn delegate(move self) -> i32 { return self.finish(); }
}
pub fn main() -> i32 {
    let pair = Wrap::new(Tx::new(1), Tx::new(2)).split();
    let w = Wrap::new(Tx::new(3), Tx::new(4));
    return pair.0.commit() + pair.1.commit() + w.delegate();
}",
        ),
    );
}

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
        "pub struct S { n: i32, pub unsafe fn get(self: &Self) -> i32 { return self.n; } }
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
    const TRAIT: &str = "trait T { unsafe fn f(self: &Self) -> i32; }\n";
    reject(
        "impl_must_match",
        &format!("{TRAIT}pub struct S {{ n: i32, impl T {{ fn f(self: &Self) -> i32 {{ return self.n; }} }} }}
pub fn main() -> i32 {{ let s = S {{ n: 1 }}; return unsafe {{ s.f() }}; }}"),
        "is declared 'fn', but trait 'T' declares it 'unsafe fn'",
    );
    reject(
        "dyn_call",
        &format!("{TRAIT}pub struct S {{ n: i32, impl T {{ unsafe fn f(self: &Self) -> i32 {{ return self.n; }} }} }}
pub fn main() -> i32 {{ let s = S {{ n: 1 }}; let t: &T = &s; return t.f(); }}"),
        UNSAFE_CALL,
    );
    accept(
        "dyn_call_in_unsafe",
        &format!("{TRAIT}pub struct S {{ n: i32, impl T {{ unsafe fn f(self: &Self) -> i32 {{ return self.n; }} }} }}
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
fn test_pointer_kinds_own_ref_and_raw() {
    // Conversions: only a reference becomes a view safely; anything else that claims ownership or
    // a borrow needs `unsafe`, and never happens implicitly. Converting out to a raw pointer is safe.
    const ASSERTS: &str = "requires an 'unsafe { ... }' block";
    reject(
        "raw_to_own",
        "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 1); let o = p as *own i32; return 0; }",
        "asserts what the pointer owns",
    );
    reject(
        "raw_to_own_implicit",
        "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 1); let o: *own i32 = p; return 0; }",
        "cannot implicitly convert '*mut i32' to '*own i32'",
    );
    reject(
        "raw_to_view",
        "pub fn main() -> i32 { let x: i32 = 1; let v = (&x as *const i32) as *ref i32; return 0; }",
        ASSERTS,
    );
    accept(
        "ref_to_view_and_own_to_raw",
        "pub fn main() -> i32 {
    let x: i32 = 1;
    let v = &x as *ref i32;
    let w: *ref i32 = &x;
    let o: *own i32 = unsafe { @alloc(i32, 1) as *own i32 };
    let p: *mut i32 = o;
    unsafe { @dealloc(p); }
    return unsafe { *v + *w };
}",
    );

    // Only an `opaque` may own through a pointer, and a copyable one may not.
    reject(
        "struct_own_field",
        "pub struct S { p: *own i32 }\npub fn main() -> i32 { return 0; }",
        "only 'opaque' fields may own values",
    );
    reject(
        "copy_opaque_own_field",
        "pub opaque(copy) C { p: *own i32 }\npub fn main() -> i32 { return 0; }",
        "a copy would duplicate the values it owns",
    );
    // An opaque holding a linear value (here inline) is linear.
    reject(
        "inline_linear_field",
        &with_tx(
            "pub opaque W {
    t: Tx,
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn done(move self) -> i32 { return self.t.commit(); }
}
pub fn main() -> i32 { let w = W::new(Tx::new(1)); return 0; }",
        ),
        "Linear value 'w' of type 'W'",
    );

    // A view carries the borrow it was made from through every signature, so a cursor stays tied
    // to its buffer even when its pointer passes through a `usize`. A raw pointer would carry none;
    // `opaque(borrows T)` declares the same for a type that keeps one.
    let cursor = |field: &str, ptr: &str| {
        format!(
            "fn Cursor[T] -> type {{
    return opaque{decl} {{
        p: {field},
        pub unsafe fn at(p: {field}) -> Self {{ return Self {{ p: p }}; }}
        pub fn get(self: &Self) -> T where T: copy {{ unsafe {{ return *self.p; }} }}
    }};
}}
fn Buf[T] -> type {{
    return opaque {{
        ptr: *own T,
        pub fn new(v: T) -> Self {{
            let p: *own T = unsafe {{ @alloc(T, 1) as *own T }};
            unsafe {{ *p = move v; }}
            return Self {{ ptr: p }};
        }}
        pub fn cursor(self: &Self) -> Cursor[T] {{
            return unsafe {{ Cursor[T]::at((self.ptr as usize) as {ptr}) }};
        }}
        pub fn regrow(self: &mut Self) where T: copy {{
            let q: *own T = unsafe {{ @alloc(T, 1) as *own T }};
            unsafe {{ *q = *self.ptr; @dealloc(self.ptr); }}
            self.ptr = q;
        }}
    }};
}}
pub fn main() -> i32 {{ let mut b = Buf[i32]::new(7); let c = b.cursor(); b.regrow(); return c.get(); }}",
            decl = if field.starts_with("*ref") { "" } else { "(borrows T)" },
        )
    };
    const STILL_BORROWED: &str = "cannot borrow 'b' as mutable because 'b' is already borrowed";
    reject("view_cursor", &cursor("*ref T", "*ref T"), STILL_BORROWED);
    reject("declared_borrows_cursor", &cursor("*const T", "*const T"), STILL_BORROWED);

    // An owning container of references carries their borrows.
    reject(
        "box_of_ref_escapes",
        "fn mk() -> Box[&i32] { let x: i32 = 5; return Box[&i32]::new(&x); }
pub fn main() -> i32 { let b = mk(); return **b.get(); }",
        "goes out of scope while still borrowed",
    );
    assert_eq!(
        run_lli(
            "box_of_ref",
            "pub fn main() -> i32 { let x: i32 = 5; let b = Box[&i32]::new(&x); return *b.into_inner(); }",
        ),
        Some(5)
    );

    // `Vec::iter` / `iter_mut` are views: they borrow the vector, so it cannot grow under them.
    assert_eq!(
        run_lli(
            "vec_iter",
            "pub fn main() -> i32 {
    let mut v = Vec[i32]::new();
    v.push(1); v.push(2); v.push(3);
    for x in v.iter_mut() { *x = *x * 10; }
    let mut sum: i32 = 0;
    for x in v.iter() { sum += *x; }
    let empty = Vec[i32]::new();
    for x in empty.iter() { sum += *x; }
    return sum;
}",
        ),
        Some(60)
    );
    reject(
        "vec_iter_then_push",
        "pub fn main() -> i32 {
    let mut v = Vec[i32]::new();
    v.push(1);
    let mut it = v.iter();
    v.push(2);
    return *(it.next() orelse unreachable);
}",
        "already borrowed as immutable",
    );

    // Thread safety follows contents: owning containers are `send` when their elements are, a view
    // as `&T` is, and a raw pointer (the lock in a `MutexGuard`) is neither.
    assert_eq!(
        run_lli(
            "send_sync",
            "pub fn main() -> i32 {
    let mut r: i32 = 0;
    if @satisfies(Vec[i32], send) { r += 1; }
    if @satisfies(Box[i32], send) { r += 2; }
    if @satisfies(Iter[i32], send) { r += 4; }
    if @satisfies(MutexGuard[i32], send) { r += 8; }
    return r;
}",
        ),
        Some(7)
    );

    // Owning and view pointers do not cross the C boundary.
    reject(
        "extern_own_param",
        "extern fn f(p: *own i32);\npub fn main() -> i32 { return 0; }",
        "'*own i32' cannot cross the C boundary",
    );
    reject(
        "extern_view_return",
        "extern fn f() -> ?*ref i32;\npub fn main() -> i32 { return 0; }",
        "'?*ref i32' cannot cross the C boundary",
    );

    // `owns T` is only for contents no field shows.
    let redundant = "fn H[T] -> type {
    return opaque(owns T) { p: *own T, impl drop { fn drop(self: &mut Self) { } } };
}
pub fn main() -> i32 { let x: ?*mut H[i32] = null; return 0; }";
    let (_, warnings) = Compiler::compile_package_with_warnings(&[("root", redundant)])
        .expect("H[i32] should compile");
    assert!(
        warnings.iter().any(|w| w.contains("'owns T' on opaque 'H' is redundant")),
        "Expected redundant-owns lint, got: {warnings:?}"
    );
}

#[test]
fn test_thread_safety_declarations_and_cell_fields() {
    // Writing through a shared reference is allowed only into `cell` fields (or a type declaring
    // `unsafe sync`), so a type that looks immutable cannot race when shared.
    let counter = |decl: &str, field: &str, bump: &str| {
        format!(
            "pub opaque{decl} Counter {{
    {field}: u64,
    pub fn new() -> Self {{ return Self {{ n: 0 }}; }}
    pub fn bump(self: &Self) {{ unsafe {{ {bump} }} }}
    pub fn get(self: &Self) -> u64 {{ return self.n; }}
}}
"
        )
    };
    const CELL_BUMP: &str = "let p = &raw mut self.n; *p = *p + 1;";
    const SHARED: &str = "pub fn main() -> i32 {
    let c = Counter::new();
    let a = spawn_scoped(fn() -> i32 { c.bump(); return 0; });
    let b = spawn_scoped(fn() -> i32 { c.bump(); return 0; });
    let _x = a.join();
    let _y = b.join();
    return c.get() as i32;
}";
    reject(
        "cast_shared_to_mut",
        &format!(
            "{}{SHARED}",
            counter("", "n", "let p = self as *mut Self; (*p).n = (*p).n + 1;")
        ),
        "Cannot cast shared reference '&Counter' to '*mut Counter'",
    );
    reject(
        "raw_mut_to_non_cell",
        "pub opaque C {
    cell n: u64,
    m: u64,
    pub fn set(self: &Self) { unsafe { let p = &raw mut self.m; *p = 1; } }
}
pub fn main() -> i32 { return 0; }",
        "only a 'cell' field may change behind a shared reference",
    );
    // A `cell` field makes the type not `sync`: fine on one thread, rejected when shared.
    assert_eq!(
        run_lli(
            "cell_single_thread",
            &format!(
                "{}pub fn main() -> i32 {{ let c = Counter::new(); c.bump(); c.bump(); return c.get() as i32; }}",
                counter("", "cell n", CELL_BUMP)
            ),
        ),
        Some(2)
    );
    reject(
        "cell_shared_between_threads",
        &format!("{}{SHARED}", counter("", "cell n", CELL_BUMP)),
        "does not satisfy comptime constraint 'send'",
    );
    // `unsafe sync` asserts the type synchronizes its own state.
    accept(
        "cell_with_unsafe_sync",
        &format!("{}{SHARED}", counter("(unsafe sync)", "cell n", CELL_BUMP)),
    );
    reject(
        "struct_cell",
        "pub struct S { cell n: i32 }\npub fn main() -> i32 { return 0; }",
        "Only 'opaque' fields may be 'cell'",
    );

    // `unsafe send` and `unsafe sync` assert one trait each; `!send` / `!sync` withhold one safely.
    assert_eq!(
        run_lli(
            "declared_traits",
            "pub opaque(unsafe send) File { f: *mut u8 }
pub opaque(!send) Local { n: i32 }
pub opaque(!sync) Unshared { n: i32 }
pub fn main() -> i32 {
    let mut r: i32 = 0;
    if @satisfies(File, send) { r += 1; }
    if @satisfies(File, sync) { r += 2; }
    if @satisfies(Local, send) { r += 4; }
    if @satisfies(Local, sync) { r += 8; }
    if @satisfies(Unshared, send) { r += 16; }
    if @satisfies(Unshared, sync) { r += 32; }
    if @satisfies(Mutex[i32], send) && @satisfies(Mutex[i32], sync) { r += 64; }
    return r;
}",
        ),
        Some(1 + 8 + 16 + 64)
    );
    reject(
        "bare_send_modifier",
        "pub opaque(send) F { n: i32 }\npub fn main() -> i32 { return 0; }",
        "requires 'opaque(unsafe send)'",
    );
    reject(
        "assert_and_withhold",
        "pub opaque(unsafe send, !send) F { n: i32 }\npub fn main() -> i32 { return 0; }",
        "cannot both assert and withhold",
    );

    // `UnsafeSend` / `UnsafeSync` vouch for a single value; constructing one is `unsafe`.
    reject(
        "unsafe_send_new_outside_unsafe",
        "pub fn main() -> i32 { let mut x: i32 = 1; let p = UnsafeSend[*mut i32]::new(&raw mut x); return 0; }",
        "Calling 'unsafe fn' 'new'",
    );
    assert_eq!(
        run_lli(
            "unsafe_send_to_thread",
            "pub fn main() -> i32 {
    let mut x: i32 = 41;
    let p = unsafe { UnsafeSend[*mut i32]::new(&raw mut x) };
    let h = spawn_scoped(move fn() -> i32 { let q = *p.get(); unsafe { *q = *q + 1; } return 0; });
    let _r = h.join();
    return x;
}",
        ),
        Some(42)
    );
}

#[test]
fn test_atomics() {
    // Two threads incrementing one `cell` counter atomically lose no updates.
    assert_eq!(
        run_lli(
            "atomic_counter",
            "pub opaque(unsafe sync) Counter {
    cell n: u64,
    pub fn new() -> Self { return Self { n: 0 }; }
    pub fn bump(self: &Self) { unsafe { let _old = @atomic_add(&raw mut self.n, 1); } }
    pub fn get(self: &Self) -> u64 { return unsafe { @atomic_load(&raw mut self.n) }; }
}
pub fn main() -> i32 {
    let c = Counter::new();
    let a = spawn_scoped(fn() -> i32 { for i in 0..10000 { c.bump(); } return 0; });
    let b = spawn_scoped(fn() -> i32 { for i in 0..10000 { c.bump(); } return 0; });
    let _x = a.join();
    let _y = b.join();
    return (c.get() / 100) as i32;
}",
        ),
        Some(200)
    );
    // Every operation but `store` yields the previous value; `cas` stores only on a match.
    let ops = "{
    let mut x: u8 = 5;
    let p = &raw mut x;
    let a = unsafe { @atomic_cas(p, 5, 7) };
    let b = unsafe { @atomic_cas(p, 5, 9) };
    let c = unsafe { @atomic_swap(p, 250) };
    let d = unsafe { @atomic_add(p, 10) };
    unsafe { @atomic_store(p, 12); }
    let e = unsafe { @atomic_sub(p, 2) };
    let f = unsafe { @atomic_or(p, 1) };
    let g = unsafe { @atomic_xor(p, 3) };
    let h = unsafe { @atomic_and(p, 6) };
    return (a == 5 && b == 7 && c == 7 && d == 250 && e == 12 && f == 10 && g == 11 && h == 8 && x == 0) as i32;
}";
    assert_eq!(
        run_lli("atomic_ops", &format!("pub fn main() -> i32 {ops}")),
        Some(1)
    );
    // The compile-time VM runs them too (a `u8` wraps: 250 + 10 = 4).
    assert_eq!(
        run_lli(
            "atomic_comptime",
            &format!("fn check() -> i32 {ops}\nconst OK: i32 = check();\npub fn main() -> i32 {{ return OK; }}"),
        ),
        Some(1)
    );
    reject(
        "atomic_outside_unsafe",
        "pub fn main() -> i32 { let mut x: i32 = 0; return @atomic_load(&raw mut x); }",
        "requires an 'unsafe { ... }' block",
    );
    reject(
        "atomic_store_through_const",
        "pub fn main() -> i32 { let x: i32 = 0; unsafe { @atomic_store(&raw const x, 1); } return 0; }",
        "needs '*mut'",
    );
    reject(
        "atomic_non_integer",
        "pub fn main() -> i32 { let mut x: f64 = 0.0; unsafe { let _v = @atomic_load(&raw mut x); } return 0; }",
        "operates on 8-, 16-, 32-, or 64-bit integers",
    );
}

#[test]
fn test_borrows_contents_contracts() {
    // `borrows(*self)`: an iterator's items borrow the sequence, not the iterator, so two can be
    // held at once and an item can outlive its iterator.
    assert_eq!(
        run_lli(
            "items_held_together",
            "fn first(v: &Vec[i32]) -> &i32 { let mut it = v.iter(); return it.next() orelse unreachable; }
pub fn main() -> i32 {
    let mut v = Vec[i32]::new();
    v.push(3); v.push(4);
    let mut it = v.iter();
    let a = it.next() orelse unreachable;
    let b = it.next() orelse unreachable;
    return *a * 10 + *b + *first(&v);
}",
        ),
        Some(37)
    );
    // The sequence itself stays borrowed while an item lives.
    reject(
        "push_while_item_alive",
        "pub fn main() -> i32 {
    let mut v = Vec[i32]::new();
    v.push(3);
    let mut it = v.iter();
    let a = it.next() orelse unreachable;
    v.push(5);
    return *a;
}",
        "already borrowed as immutable",
    );
    // Depth: the inner reference outlives the outer one only with `borrows(*x)`.
    let unnest = |contract: &str| {
        format!(
            "fn unnest(x: &&i32) -> &i32 borrows({contract}) {{ return *x; }}
pub fn main() -> i32 {{ let v: i32 = 5; let mut r: &i32 = &v; if true {{ let tmp = &v; r = unnest(&tmp); }} return *r; }}"
        )
    };
    assert_eq!(run_lli("depth_contents", &unnest("*x")), Some(5));
    reject("depth_plain", &unnest("x"), "while still borrowed");
    // `*self` covers only borrows `self` holds: not its own fields, nor memory it owns.
    reject(
        "own_field_under_contents",
        "pub opaque S {
    n: i32,
    pub fn new() -> Self { return Self { n: 1 }; }
    pub fn bad(self: &Self) -> &i32 borrows(*self) { return &self.n; }
}
pub fn main() -> i32 { let s = S::new(); return *s.bad(); }",
        "not permitted by its contract borrows(*self)",
    );
    reject(
        "owned_memory_under_contents",
        "fn Holder[T] -> type {
    return opaque {
        p: *own T,
        pub fn new(v: T) -> Self {
            let p: *own T = unsafe { @alloc(T, 1) as *own T };
            unsafe { *p = move v; }
            return Self { p: p };
        }
        pub fn get(self: &Self) -> &T borrows(*self) { unsafe { return &*self.p; } }
    };
}
pub fn main() -> i32 { let h = Holder[i32]::new(1); return *h.get(); }",
        "not permitted by its contract borrows(*self)",
    );
    accept(
        "contents_in_fn_pointer_type",
        "fn unnest(x: &&i32) -> &i32 borrows(*x) { return *x; }
pub fn main() -> i32 { let f: fn(&&i32) -> &i32 borrows(*_1) = unnest; let v: i32 = 2; let r = &v; return *f(&r); }",
    );
}

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
    pub fn take_n(move self) -> i32 { return self.p.n; }
}
pub fn main() -> i32 { let w = Wrap::new(Tx::new(1)); return w.take_n(); }",
        ),
        "Linear field 'self.p.t' of type 'Tx'",
    );
}

#[test]
fn test_precise_drop_check() {
    const STILL_BORROWED: &str = "goes out of scope while still borrowed";
    // A container whose hook only drops or frees its elements (`unsafe impl drop(may_dangle T)`)
    // may be dropped after the data its elements borrow, since dropping an `&i32` reads nothing.
    assert_eq!(
        run_lli(
            "vec_dropped_after_referent",
            "pub fn main() -> i32 { let mut v = Vec[&i32]::new(); let x: i32 = 7; v.push(&x); return **(v.get(0) orelse unreachable); }",
        ),
        Some(7)
    );
    for (name, body) in [
        ("box", "let y: i32 = 0; let mut b = Box[&i32]::new(&y); let x: i32 = 1; b = Box[&i32]::new(&x);"),
        ("map", "let mut m = HashMap[i32, &i32]::new(); let x: i32 = 1; let _o = m.insert(1, &x);"),
        ("mutex", "let y: i32 = 0; let mut m = Mutex[&i32]::new(&y); let x: i32 = 1; m = Mutex[&i32]::new(&x);"),
        (
            "nested",
            "let mut outer = Vec[Vec[&i32]]::new(); let x: i32 = 1; let mut inner = Vec[&i32]::new(); inner.push(&x); outer.push(inner);",
        ),
    ] {
        accept(name, &format!("pub fn main() -> i32 {{ {body} return 0; }}"));
    }

    // Still rejected: elements whose own drop reads their borrow, a `may_dangle` type that also
    // holds a borrow directly, a hook that declares nothing, and any use after the referent dies.
    reject(
        "elements_read_their_borrow",
        "static mut SINK: i32 = 0;
pub opaque Peek {
    r: &i32,
    impl drop { fn drop(self: &mut Self) { unsafe { SINK = *self.r; } } }
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
}
pub fn main() -> i32 { let mut v = Vec[Peek]::new(); let x: i32 = 1; v.push(Peek::new(&x)); return 0; }",
        STILL_BORROWED,
    );
    reject(
        "direct_borrow_beside_contents",
        "fn C[T] -> type {
    return opaque {
        p: *own T,
        r: &i32,
        unsafe impl drop(may_dangle T) { fn drop(self: &mut Self) { unsafe { let _v = *self.r; @dealloc(self.p); } } }
        pub fn new(r: &i32) -> Self { return Self { p: unsafe { @alloc(T, 1) as *own T }, r: r }; }
    };
}
pub fn main() -> i32 { let y: i32 = 0; let mut c = C[i32]::new(&y); let x: i32 = 1; c = C[i32]::new(&x); return 0; }",
        STILL_BORROWED,
    );
    reject(
        "hook_without_may_dangle",
        "fn L[T] -> type {
    return opaque {
        p: *own T,
        impl drop { fn drop(self: &mut Self) { unsafe { @dealloc(self.p); } } }
        pub fn new(v: T) -> Self { let p: *own T = unsafe { @alloc(T, 1) as *own T }; unsafe { *p = move v; } return Self { p: p }; }
    };
}
pub fn main() -> i32 { let y: i32 = 0; let mut l = L[&i32]::new(&y); let x: i32 = 1; l = L[&i32]::new(&x); return 0; }",
        STILL_BORROWED,
    );
    reject(
        "use_after_referent_dies",
        "pub fn main() -> i32 { let mut v = Vec[&i32]::new(); if true { let x: i32 = 1; v.push(&x); } return v.len() as i32; }",
        STILL_BORROWED,
    );
    // A reference copied out through another keeps depending on what it refers to.
    reject(
        "copied_reference_keeps_referent",
        "pub fn main() -> i32 { let z: i32 = 0; let mut v: &i32 = &z; if true { let x: i32 = 1; let r = &x; let rr = &r; v = *rr; } return *v; }",
        STILL_BORROWED,
    );

    // The assertion is spelled `unsafe impl drop(may_dangle T)`.
    reject(
        "may_dangle_without_unsafe",
        "fn L[T] -> type { return opaque { p: *own T, impl drop(may_dangle T) { fn drop(self: &mut Self) { } } }; }\npub fn main() -> i32 { return 0; }",
        "write 'unsafe impl drop(may_dangle ...)'",
    );
    reject(
        "unsafe_without_may_dangle",
        "fn L[T] -> type { return opaque { p: *own T, unsafe impl drop { fn drop(self: &mut Self) { } } }; }\npub fn main() -> i32 { return 0; }",
        "'unsafe impl drop' asserts nothing",
    );

    // Dropping through a reference needs the referent alive, whatever the type: `v` here is
    // dropped at the end of its scope and again through `r`.
    reject(
        "drop_through_reference_after_referent",
        "pub fn main() -> i32 {
    let mut outer = Vec[&i32]::new();
    let mut r: &mut Vec[&i32] = &mut outer;
    if true { let mut v = Vec[&i32]::new(); r = &mut v; }
    @drop(r);
    return 0;
}",
        "already borrowed",
    );
    // `opaque(borrows U)` is a borrow held directly, which a `may_dangle T` hook may read.
    reject(
        "declared_borrow_beside_may_dangle",
        "fn C[T, U] -> type {
    return opaque(borrows U) {
        p: *own T,
        u: *const U,
        unsafe impl drop(may_dangle T) { fn drop(self: &mut Self) { unsafe { let _v = *self.u; @dealloc(self.p); } } }
        pub fn new(u: &U) -> Self { return Self { p: unsafe { @alloc(T, 1) as *own T }, u: u as *const U }; }
    };
}
pub fn main() -> i32 { let y: i32 = 0; let mut c = C[i32, i32]::new(&y); let x: i32 = 1; c = C[i32, i32]::new(&x); return 0; }",
        STILL_BORROWED,
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
fn test_linear_values_cannot_be_silently_overwritten() {
    reject(
        "overwrite_through_mut_ref",
        &with_tx(
            "fn clobber(r: &mut Tx) { *r = Tx::new(9); }
pub fn main() -> i32 { let mut t = Tx::new(1); clobber(&mut t); return t.commit(); }",
        ),
        "Cannot overwrite linear value",
    );
    reject(
        "overwrite_live_local_field",
        &with_tx(
            "struct Pair { a: Tx, b: i32 }
pub fn main() -> i32 { let mut p = Pair { a: Tx::new(1), b: 2 }; p.a = Tx::new(3); return p.a.commit(); }",
        ),
        "Linear value",
    );
    // Re-initializing a field after it was consumed is fine.
    accept(
        "reinit_consumed_field",
        &with_tx(
            "struct Pair { a: Tx, b: i32 }
pub fn main() -> i32 {
    let mut p = Pair { a: Tx::new(1), b: 2 };
    let x = p.a.commit();
    p.a = Tx::new(3);
    return x + p.a.commit();
}",
        ),
    );
    // `core::mem::replace` / `swap` are the sanctioned ways to replace a linear value in place.
    accept(
        "replace_linear",
        &with_tx(
            "fn upd(r: &mut Tx) -> i32 { let old = replace[Tx](r, Tx::new(9)); return old.commit(); }
pub fn main() -> i32 { let mut t = Tx::new(1); let a = upd(&mut t); return a + t.commit(); }",
        ),
    );
    accept(
        "swap_linear",
        &with_tx(
            "pub fn main() -> i32 {
    let mut a = Tx::new(1);
    let mut b = Tx::new(2);
    swap[Tx](&mut a, &mut b);
    return a.commit() + b.commit();
}",
        ),
    );
    // `error` types cannot carry linear payloads, so `catch` can never discard a linear value.
    reject(
        "linear_error_payload",
        &with_tx("pub error E { Bad: Tx }\npub fn main() -> i32 { return 0; }"),
        "cannot carry a linear payload",
    );
}

#[test]
fn test_every_pub_function_defines_its_borrow_contract() {
    let slot = "pub opaque Slot {
    r: &i32,
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
    pub fn get(self: &Self) -> &i32 { return self.r; }
";
    // A `pub` method that stores a parameter into `self` must declare the flow...
    reject(
        "pub_method_missing_flow",
        &format!(
            "{slot}    pub fn set(self: &mut Self, r: &i32) {{ self.r = r; }}
}}
pub fn main() -> i32 {{ let a: i32 = 1; let mut s = Slot::new(&a); return 0; }}"
        ),
        "Slot::set",
    );
    // ...and callers are then held to it.
    let declared = format!(
        "{slot}    pub fn set(self: &mut Self, r: &i32) borrows(self: r) {{ self.r = r; }}
}}
"
    );
    accept(
        "pub_method_declared_flow",
        &format!(
            "{declared}pub fn main() -> i32 {{ let a: i32 = 1; let mut s = Slot::new(&a); let b: i32 = 2; s.set(&b); return *s.get(); }}"
        ),
    );
    reject(
        "pub_method_declared_flow_dangling",
        &format!(
            "{declared}pub fn main() -> i32 {{
    let a: i32 = 1;
    let mut s = Slot::new(&a);
    if true {{ let b: i32 = 2; s.set(&b); }}
    return *s.get();
}}"
        ),
        "while still borrowed",
    );
    // Private functions keep inferred contracts.
    accept(
        "private_method_inferred",
        &format!(
            "{slot}    fn set(self: &mut Self, r: &i32) {{ self.r = r; }}
    pub fn put(self: &mut Self, r: &i32) borrows(self: r) {{ self.set(r); }}
}}
pub fn main() -> i32 {{ let a: i32 = 1; let mut s = Slot::new(&a); return *s.get(); }}"
        ),
    );

    // Generic `pub` functions: the clause matters only for instantiations whose types carry references.
    let store = "pub fn store[T](dst: &mut T, v: T) { unsafe { let p: *mut T = dst as *mut T; *p = v; } }\n";
    reject(
        "generic_pub_missing_flow",
        &format!(
            "{store}pub fn main() -> i32 {{ let a: i32 = 1; let mut r: &i32 = &a; let b: i32 = 2; store[&i32](&mut r, &b); return 0; }}"
        ),
        "root::store",
    );
    accept(
        "generic_pub_plain_instantiation",
        &format!("{store}pub fn main() -> i32 {{ let mut a: i32 = 1; store[i32](&mut a, 5); return a; }}"),
    );
    accept(
        "generic_pub_declared_flow",
        "pub fn store[T](dst: &mut T, v: T) borrows(dst: v) { unsafe { let p: *mut T = dst as *mut T; *p = v; } }
pub fn main() -> i32 { let a: i32 = 1; let mut r: &i32 = &a; let b: i32 = 2; store[&i32](&mut r, &b); return *r; }",
    );

    // A `pub(mod)` method is called only from its own module, so its contract is inferred.
    assert_eq!(
        run_lli(
            "pub_mod_inferred_contract",
            "struct S { v: i32, pub(mod) fn pick(self: &Self, b: &i32) -> &i32 { return b; } }
pub fn main() -> i32 { let s = S { v: 1 }; let b: i32 = 42; return *s.pick(&b); }",
        ),
        Some(42)
    );
}

#[test]
fn test_function_pointer_and_trait_method_contracts() {
    let slot = "struct Slot { r: &i32 }\nfn stash(dst: &mut Slot, x: &i32) { dst.r = x; }\n";
    // A function value is checked against the contract of the pointer type it is stored into.
    reject(
        "fn_value_flow_not_in_contract",
        &format!(
            "{slot}pub fn main() -> i32 {{ let a: i32 = 1; let mut s = Slot {{ r: &a }}; let f = stash; let b: i32 = 2; f(&mut s, &b); return *s.r; }}"
        ),
        "add 'borrows(_1: _2)'",
    );
    accept(
        "fn_value_flow_in_contract",
        &format!(
            "{slot}pub fn main() -> i32 {{
    let a: i32 = 1;
    let mut s = Slot {{ r: &a }};
    let f: fn(&mut Slot, &i32) borrows(_1: _2) = stash;
    let b: i32 = 2;
    f(&mut s, &b);
    return *s.r;
}}"
        ),
    );
    // Calls through the pointer enforce its contract at the call site.
    reject(
        "indirect_call_enforces_flow",
        &format!(
            "{slot}pub fn main() -> i32 {{
    let a: i32 = 1;
    let mut s = Slot {{ r: &a }};
    let f: fn(&mut Slot, &i32) borrows(_1: _2) = stash;
    if true {{ let b: i32 = 2; f(&mut s, &b); }}
    return *s.r;
}}"
        ),
        "while still borrowed",
    );
    // Return contracts on function types: elided for one reference parameter, explicit otherwise.
    accept(
        "fn_type_return_elided",
        "fn first(a: &i32) -> &i32 { return a; }
pub fn main() -> i32 { let f: fn(&i32) -> &i32 = first; let x: i32 = 3; return *f(&x); }",
    );
    reject(
        "fn_type_return_ambiguous",
        "fn pick(a: &i32, b: &i32) -> &i32 { return a; }
pub fn main() -> i32 { let f: fn(&i32, &i32) -> &i32 = pick; return 0; }",
        "add an explicit 'borrows(_N, ...)' contract",
    );
    reject(
        "fn_type_return_too_narrow",
        "fn pick(a: &i32, b: &i32) -> &i32 { return b; }
pub fn main() -> i32 { let f: fn(&i32, &i32) -> &i32 borrows(_1) = pick; return 0; }",
        "return value borrow from parameter '_2'",
    );

    // Trait methods carry contracts; an implementation that stores a parameter must match.
    // The impl inherits the trait method's contract, so its body is checked against it.
    let sink_impl = "struct S { r: &i32, impl Sink { fn put(self: &mut Self, r: &i32) { self.r = r; } } }\n";
    reject(
        "trait_method_flow_missing",
        &format!(
            "pub trait Sink {{ fn put(self: &mut Self, r: &i32); }}
{sink_impl}pub fn main() -> i32 {{ let a: i32 = 1; let mut s = S {{ r: &a }}; let d: &mut Sink = &mut s; return 0; }}"
        ),
        "<S as Sink>::put",
    );
    reject(
        "trait_object_call_enforces_flow",
        &format!(
            "pub trait Sink {{ fn put(self: &mut Self, r: &i32) borrows(self: r); }}
{sink_impl}pub fn main() -> i32 {{
    let a: i32 = 1;
    let mut s = S {{ r: &a }};
    if true {{ let b: i32 = 2; let d: &mut Sink = &mut s; d.put(&b); }}
    return *s.r;
}}"
        ),
        "while still borrowed",
    );
}

const HASH: &str = "\
pub trait Hash { fn hash(self: &Self) -> u64; }
fn h[T: Hash](x: &T) -> u64 { return x.hash(); }
";

fn with_hash(body: &str) -> String {
    format!("{HASH}\n{body}")
}

#[test]
fn test_traits_require_explicit_impl() {
    // Matching method names alone never make a type conform.
    reject(
        "duck_typing_rejected",
        &with_hash(
            "struct P { x: i32, pub fn hash(self: &Self) -> u64 { return 1; } }
pub fn main() -> i32 { let p = P { x: 1 }; return h(&p) as i32; }",
        ),
        "Type 'P' does not implement trait 'Hash'",
    );
    // Inline impls keep the body's private access and support static and dynamic dispatch.
    accept(
        "inline_impl",
        &with_hash(
            "opaque P {
    x: i32,
    pub fn new() -> Self { return Self { x: 3 }; }
    impl Hash { fn hash(self: &Self) -> u64 { return self.x as u64; } }
}
fn d(x: &Hash) -> u64 { return x.hash(); }
pub fn main() -> i32 { let p = P::new(); return (h(&p) + p.hash() + d(&p)) as i32; }",
        ),
    );
    // Module-level impls have no private access.
    reject(
        "module_impl_no_private_access",
        &with_hash(
            "opaque P { x: i32, pub fn new() -> Self { return Self { x: 3 }; } }
impl Hash for P { fn hash(self: &Self) -> u64 { return self.x as u64; } }
pub fn main() -> i32 { let p = P::new(); return h(&p) as i32; }",
        ),
        "Cannot access private field 'x' of opaque 'P'",
    );
    // Retroactive impls for builtin types (in the trait's module) and generic impls.
    accept(
        "generic_impl",
        &with_hash(
            "pub fn Pair[T] -> type { return struct { a: T, b: T }; }
impl Hash for i32 { fn hash(self: &Self) -> u64 { return *self as u64; } }
impl[T: Hash] Hash for Pair[T] {
    fn hash(self: &Self) -> u64 { return self.a.hash() + self.b.hash(); }
}
pub fn main() -> i32 { let p = Pair[i32] { a: 2, b: 3 }; return h(&p) as i32; }",
        ),
    );
    reject(
        "generic_impl_bound_unmet",
        &with_hash(
            "pub fn Pair[T] -> type { return struct { a: T, b: T }; }
impl[T: Hash] Hash for Pair[T] { fn hash(self: &Self) -> u64 { return self.a.hash(); } }
pub fn main() -> i32 { let p = Pair[bool] { a: true, b: false }; return h(&p) as i32; }",
        ),
        "does not implement trait 'Hash'",
    );
}

#[test]
fn test_trait_impl_coherence_and_signatures() {
    reject(
        "conflicting_impls",
        &with_hash(
            "struct P { x: i32, impl Hash { fn hash(self: &Self) -> u64 { return 1; } } }
impl Hash for P { fn hash(self: &Self) -> u64 { return 2; } }
pub fn main() -> i32 { let p = P { x: 1 }; return h(&p) as i32; }",
        ),
        "Conflicting implementations of trait 'Hash' for 'P'",
    );
    reject(
        "extra_impl_method",
        &with_hash(
            "struct P {
    x: i32,
    impl Hash {
        fn hash(self: &Self) -> u64 { return 1; }
        fn other(self: &Self) -> i32 { return 0; }
    }
}
pub fn main() -> i32 { let p = P { x: 1 }; return h(&p) as i32; }",
        ),
        "Method 'other' in 'impl Hash' in the body of 'P' is not declared by trait 'Hash'",
    );
    reject(
        "missing_impl_method",
        "pub trait Two { fn a(self: &Self) -> i32; fn b(self: &Self) -> i32; }
struct P { x: i32, impl Two { fn a(self: &Self) -> i32 { return 1; } } }
fn use2[T: Two](x: &T) -> i32 { return x.a(); }
pub fn main() -> i32 { let p = P { x: 1 }; return use2(&p); }",
        "is missing trait method 'b'",
    );
    reject(
        "impl_contract_differs",
        "pub trait Get { fn get(self: &Self, o: &i32) -> &i32 borrows(self); }
struct P { r: &i32, impl Get { fn get(self: &Self, o: &i32) -> &i32 borrows(o) { return o; } } }
fn u[T: Get](x: &T) -> i32 { let z: i32 = 0; return *x.get(&z); }
pub fn main() -> i32 { let a: i32 = 1; let p = P { r: &a }; return u(&p); }",
        "declares a borrows(...) contract that differs from trait 'Get'",
    );

    // Orphan rule: a module-level impl must live in the type's or the trait's module.
    let trait_mod = "pub trait Hash { fn hash(self: &Self) -> u64; }
pub fn h[T: Hash](x: &T) -> u64 { return x.hash(); }";
    let type_mod = "pub struct K { pub id: i32 }";
    let err = Compiler::compile_package(&[
        ("root::t", trait_mod),
        ("root::ty", type_mod),
        (
            "root",
            "import root::t::{Hash, h};
import root::ty::K;
impl Hash for K { fn hash(self: &Self) -> u64 { return 1; } }
pub fn main() -> i32 { let k = K { id: 1 }; return h(&k) as i32; }",
        ),
    ])
    .expect_err("impl in a third module should violate the orphan rule");
    assert!(err.contains("Orphan rule violation"), "Unexpected error: {err}");
    Compiler::compile_package(&[
        (
            "root::t",
            "import root::ty::K;
pub trait Hash { fn hash(self: &Self) -> u64; }
pub fn h[T: Hash](x: &T) -> u64 { return x.hash(); }
impl Hash for K { fn hash(self: &Self) -> u64 { return 1; } }",
        ),
        ("root::ty", type_mod),
        (
            "root",
            "import root::t::{Hash, h};
import root::ty::K;
pub fn main() -> i32 { let k = K { id: 1 }; return h(&k) as i32; }",
        ),
    ])
    .expect("impl in the trait's module should be accepted");
}

#[test]
fn test_trait_method_namespacing_and_traits_are_not_types() {
    let two = "pub trait Name { fn hash(self: &Self) -> u64; }
struct P {
    x: i32,
    impl Hash { fn hash(self: &Self) -> u64 { return 1; } }
    impl Name { fn hash(self: &Self) -> u64 { return 2; } }
}
";
    reject(
        "ambiguous_trait_method",
        &with_hash(&format!(
            "{two}pub fn main() -> i32 {{ let p = P {{ x: 1 }}; return p.hash() as i32; }}"
        )),
        "Ambiguous method 'hash' on 'P'",
    );
    accept(
        "qualified_trait_calls",
        &with_hash(&format!(
            "{two}pub fn main() -> i32 {{ let p = P {{ x: 1 }}; return (Hash::hash(&p) + Name::hash(&p)) as i32; }}"
        )),
    );
    // Inherent methods take priority over trait methods in method-call syntax.
    accept(
        "inherent_priority",
        &with_hash(
            "struct P {
    x: i32,
    pub fn hash(self: &Self) -> u64 { return 9; }
    impl Hash { fn hash(self: &Self) -> u64 { return 1; } }
}
pub fn main() -> i32 { let p = P { x: 1 }; return p.hash() as i32 + h(&p) as i32; }",
        ),
    );

    // Traits are a distinct kind: never accepted where a `type` is expected.
    reject(
        "trait_as_type_argument",
        &with_hash(
            "fn id[T](x: &T) -> i32 { return 1; }
struct P { x: i32 }
pub fn main() -> i32 { let p = P { x: 1 }; return id[Hash](&p); }",
        ),
        "Trait 'Hash' is not a type",
    );
    reject(
        "type_alias_for_trait",
        "type D = trait { fn d(self: &Self) -> i32; };\npub fn main() -> i32 { return 0; }",
        "write 'trait D ...'",
    );
    reject(
        "trait_equals_trait_literal",
        "trait D = trait { fn d(self: &Self) -> i32; };\npub fn main() -> i32 { return 0; }",
        "write 'trait D { ... }'",
    );
    accept(
        "trait_alias",
        "trait D { fn d(self: &Self) -> i32; }
struct P { x: i32, impl D { fn d(self: &Self) -> i32 { return 4; } } }
fn g[T: D](x: &T) -> i32 { return x.d(); }
pub fn main() -> i32 { let p = P { x: 1 }; return g(&p); }",
    );
}

#[test]
fn test_linear_values_in_threads_and_select() {
    // A losing `@select` send arm must hand its linear value back via `else |unsent|`.
    let prelude = "pub fn main() -> i32 {
    let a = Channel[Tx]::new();
    let b = Channel[i32]::new();
";
    let drain = "    a.close_and_drain(fn(t: Tx) { let _c = t.commit(); });
    return r;
}";
    reject(
        "select_linear_send_without_handler",
        &with_tx(&format!(
            "{prelude}    let r: i32 = @select {{
        a.send(Tx::new(1)) => 1,
        x = b.recv() => x,
        default => 0,
    }};
{drain}"
        )),
        "Linear value",
    );
    accept(
        "select_linear_send_with_handler",
        &with_tx(&format!(
            "{prelude}    let r: i32 = @select {{
        a.send(Tx::new(1)) else |unsent| {{ let _c = unsent.commit(); }} => 1,
        x = b.recv() => x,
        default => 0,
    }};
{drain}"
        )),
    );
    // Affine values from losing send arms are simply dropped.
    accept(
        "select_affine_send_dropped_on_loss",
        "opaque Tok {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    impl drop { fn drop(self: &mut Self) {} }
}
pub fn main() -> i32 {
    let a = Channel[Tok]::new();
    let b = Channel[i32]::new();
    let r: i32 = @select {
        a.send(Tok::new(1)) => 1,
        x = b.recv() => x,
        default => 0,
    };
    return r;
}",
    );

    // Detaching a thread would discard its result, so it is unavailable for linear results.
    reject(
        "detach_linear_result",
        &with_tx(
            "pub fn main() -> i32 {
    let jh = spawn(move fn() -> Tx { return Tx::new(1); });
    jh.detach();
    return 0;
}",
        ),
        "detach",
    );
    accept(
        "join_linear_result",
        &with_tx(
            "pub fn main() -> i32 {
    let jh = spawn(move fn() -> Tx { return Tx::new(1); });
    return jh.join().commit();
}",
        ),
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
            "fn at(a: &[i32], i: usize) -> i32 { return a[i]; }
fn tail(a: &[i32], lo: usize, hi: usize) -> usize { let s = a[lo..hi]; return s.len; }
pub fn main() -> i32 {
    let arr: [i32; 4] = { 10, 20, 30, 2 };
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
            "fn at(i: usize) -> i32 { let a: [i32; 4] = { 1, 2, 3, 4 }; return a[i]; }
pub fn main() -> i32 { return at(4); }",
        ),
        (
            "slice_index",
            "fn at(a: &[i32], i: usize) -> i32 { return a[i]; }
pub fn main() -> i32 { let arr: [i32; 2] = { 1, 2 }; return at(&arr, 2); }",
        ),
        (
            "slice_range_end",
            "fn sub(a: &[i32], hi: usize) -> usize { let s = a[0..hi]; return s.len; }
pub fn main() -> i32 { let arr: [i32; 2] = { 1, 2 }; return sub(&arr, 3) as i32; }",
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
        "pub fn main() -> i32 { let a: [i32; 4] = { 1, 2, 3, 4 }; return a[4]; }",
        "Index 4 is out of bounds for length 4",
    );
    reject(
        "constant_range_end_out_of_bounds",
        "pub fn main() -> i32 { let a: [i32; 4] = { 1, 2, 3, 4 }; let s = a[0..5]; return 0; }",
        "Slice end 5 is out of bounds for length 4",
    );
}

#[test]
fn test_overload_resolution_uses_subsumption() {
    // A strictly more specific constraint wins...
    assert_eq!(
        run_lli(
            "more_specific_wins",
            "pub trait A { fn a(self: &Self) -> i32; }
pub trait B { fn b(self: &Self) -> i32; }
struct P { x: i32, impl A { fn a(self: &Self) -> i32 { return 1; } } impl B { fn b(self: &Self) -> i32 { return 2; } } }
fn pick[T: integer](x: T) -> i32 { return 1; }
fn pick[T: signed](x: T) -> i32 { return 10; }
fn pick[T](x: T) -> i32 { return 100; }
fn tr[T: A](x: &T) -> i32 { return 1000; }
fn tr[T: A + B](x: &T) -> i32 { return 2000; }
pub fn main() -> i32 {
    let p = P { x: 0 };
    let a: i32 = 1;
    let b: u8 = 1;
    let c: bool = true;
    // 10 (signed) + 1 (integer) + 100 (type) + 2000 (A + B) = 2111, exit code 2111 % 256 = 63
    return pick(a) + pick(b) + pick(c) + tr(&p);
}"
        ),
        Some(63)
    );
    // ...while overlapping, incomparable constraints are ambiguous instead of ranked.
    reject(
        "send_vs_number",
        "fn foo[T: send](x: T) -> i32 { return 1; }
fn foo[T: number](x: T) -> i32 { return 2; }
pub fn main() -> i32 { let a: i32 = 42; return foo[i32](a); }",
        "Ambiguous call to overloaded 'foo'",
    );
    reject(
        "linear_vs_opaque_extension",
        &with_tx(
            "pub fn tag[S: opaque](self: &S) -> i32 { return 3; }
pub fn tag[L: linear](self: &L) -> i32 { return 4; }
pub fn main() -> i32 { let t = Tx::new(1); let k = t.tag(); return k + t.commit(); }",
        ),
        "Ambiguous extension method 'tag'",
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
    pub fn next(self: &mut Self) -> ?i32 {
        if self.n >= 5 { return null; }
        self.n = self.n + 1;
        return self.n;
    }
}
pub union Cell { Num: i32, Boxed: Box[i32], Empty }
pub fn main() -> i32 {
    let mut c = Ctr::new();
    let mut sum: i32 = 0;
    while let v = c.next() { sum = sum + v; }
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
    let arr: [u8; @size_of(u32)] = { 1, 2, 3, 4 };
    if @size_of(P) != 8 || @align_of(P) != 4 || N != 8 || arr.len != 4 { return 1; }
    let p = try_alloc[i32](4) orelse return 2;
    unsafe { *p = 7; @dealloc(p); }
    let huge: usize = 18446744073709551615;
    if let q = try_alloc[i64](huge) { return 3; }
    return 42;
}"
        ),
        Some(42)
    );
}

#[test]
fn test_instantiation_trace_in_diagnostics() {
    reject(
        "stage2_error_in_generic_fn",
        "fn call_it[T](x: T) -> i32 { return x.missing(); }
pub fn main() -> i32 { return call_it[i32](1); }",
        "in instantiation of root::call_it[T = i32]",
    );
    reject(
        "stage2_error_in_type_fn_method",
        "fn W[T] -> type {
    return opaque { v: T, pub fn new(v: T) -> Self { return Self { v: v }; } pub fn peek(self: &Self) -> i32 { return self.v.missing(); } };
}
pub fn main() -> i32 { let w = W[i32]::new(1); return w.peek(); }",
        "in instantiation of W[i32]::peek",
    );
    // Stage 3 diagnostics name the instantiation they occur in.
    reject(
        "stage3_error_names_instantiation",
        &with_tx(
            "fn ignore[T](x: T) -> i32 { return 0; }
pub fn main() -> i32 { return ignore[Tx](Tx::new(1)); }",
        ),
        "root::ignore[T = Tx]",
    );
    reject(
        "linear_type_label",
        &with_tx("pub fn main() -> i32 { let c = Channel[Tx]::new(); return 0; }"),
        "of type 'Channel[Tx]'",
    );
}

#[test]
fn test_optional_niche_layout() {
    assert_eq!(
        run_lli(
            "niche_layout",
            "pub fn NonZero[Int: integer] -> type { return Int in 1..=Int::MAX; }
alias PosixFd = i32 in 0..=2147483647;
alias Percent = u8 in 0..=100;
alias Digit = u8 in 0..=9 | 200..=255;
fn first(a: &i32) -> ?&i32 { return a; }
pub fn main() -> i32 {
    // Pointers and range types with an invalid bit pattern store `null` in it: no tag.
    if @size_of(?&i32) != 8 || @size_of(?*mut u8) != 8 || @size_of(?fn(i32) -> i32) != 8 { return 1; }
    if @size_of(?NonZero[u32]) != 4 || @size_of(?rune) != 4 || @size_of(?PosixFd) != 4 { return 2; }
    if @size_of(?Percent) != 1 || @size_of(?Digit) != 1 { return 3; }
    // Without a niche (every bit pattern of `i32` is valid) the optional keeps its tag.
    if @size_of(?i32) != 8 { return 4; }

    // The `null` value follows the documented priority: 0, then all-ones, then above the first range.
    let fd: ?PosixFd = null;
    let pct: ?Percent = null;
    let dig: ?Digit = null;
    let nz: ?NonZero[u32] = null;
    unsafe {
        if @transmute(i32, fd) != -1 { return 5; }
        if @transmute(u8, pct) != 255 { return 6; }
        if @transmute(u8, dig) != 10 { return 7; }
        if @transmute(u32, nz) != 0 { return 8; }
    }

    // Present values round-trip and are distinguished from `null`.
    let x: i32 = 40;
    let r = first(&x) orelse return 9;
    let some_fd: ?PosixFd = 3 as PosixFd;
    let fd_val = some_fd orelse return 10;
    let some_pct: ?Percent = 0 as Percent;
    if let p = some_pct { if p != 0 { return 11; } } else { return 12; }
    let no_fd: ?PosixFd = null;
    if let f = no_fd { return 13; }
    return *r + (fd_val as i32) - 1;
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
    impl drop { fn drop(self: &mut Self) { unsafe { *self.p = *self.p + 1; } } }
}
fn get(i: i32) -> ?i32 { if i < 3 { return i; } return null; }
opaque C { n: i32, pub fn new() -> Self { return Self { n: 0 }; } pub fn next(self: &mut Self) -> ?i32 { if self.n >= 6 { return null; } self.n = self.n + 1; return self.n; } }
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
    while let v = c.next() { if v % 2 == 1 { continue; } evens = evens + v; }
    if evens != 12 { return 4; }
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
        "break_skips_linear_consumption",
        &with_tx("pub fn main() -> i32 { while true { let t = Tx::new(1); break; } return 0; }"),
        "Linear value",
    );
}

#[test]
fn test_trait_methods_require_trait_in_scope() {
    let trait_mod = "pub trait Hash { fn hash(self: &Self) -> u64; }";
    let type_mod =
        "import root::t::Hash;\npub struct K { pub id: i32, impl Hash { fn hash(self: &Self) -> u64 { return 7; } } }";
    let err = Compiler::compile_package(&[
        ("root::t", trait_mod),
        ("root::ty", type_mod),
        ("root", "import root::ty::K;\npub fn main() -> i32 { let k = K { id: 1 }; return k.hash() as i32; }"),
    ])
    .expect_err("trait not in scope");
    assert!(
        err.contains("provided by trait 'Hash', which is not in scope; add 'import root::t::Hash;'"),
        "Unexpected error: {err}"
    );
    for root in [
        "import root::ty::K;\nimport root::t::Hash;\npub fn main() -> i32 { let k = K { id: 1 }; return k.hash() as i32; }",
        "import root::ty::K;\nimport root::t::*;\npub fn main() -> i32 { let k = K { id: 1 }; return k.hash() as i32; }",
        "import root::ty::K;\nimport root::t;\npub fn main() -> i32 { let k = K { id: 1 }; return t::Hash::hash(&k) as i32; }",
    ] {
        Compiler::compile_package(&[("root::t", trait_mod), ("root::ty", type_mod), ("root", root)])
            .unwrap_or_else(|e| panic!("expected to compile: {e}\n{root}"));
    }
}

#[test]
fn test_union_tags_linked_enums_and_variant_patterns() {
    assert_eq!(
        run_lli(
            "union_tags",
            "pub union(u16) Message { Ping: u64 = 1, Auth: i32 = 16, Disconnect = 65535 }
pub error(i16) MyErr { Bad: i32 = 10, Worse = -5 }
pub union Shape { Circle: i32, Square: i32, Empty }
fn kind(s: &Shape) -> Shape::Tag { return s.tag; }
fn step(i: i32) -> Shape { if i < 3 { return Shape::Circle(i); } return Shape::Empty; }
pub fn main() -> i32 {
    // Synthesized `T::Tag` enum and `.tag` on `union` and `error`.
    let sq = Shape::Square(3);
    match kind(&sq) { Shape::Tag::Square => {}, Shape::Tag::Circle => return 1, Shape::Tag::Empty => return 1, }
    let e = MyErr::Bad(99);
    if e.tag != MyErr::Tag::Bad || (MyErr::Tag::Worse as i16) != -5 { return 10; }
    // `union(u16)` with inline `= N`: `.tag` is `Message::Tag`, and the stored tag is the explicit value.
    let m = Message::Auth(5);
    let t: Message::Tag = m.tag;
    if t != Message::Tag::Auth { return 2; }
    let d = Message::Disconnect;
    if d.tag != Message::Tag::Disconnect { return 3; }
    let raw: [u16; 8] = unsafe { @transmute([u16; 8], d) };
    if raw[0] != 65535 { return 4; }
    let got: i32 = match m { Message::Auth(x) => x, Message::Ping(p) => 0, Message::Disconnect => 0, };
    if got != 5 { return 5; }
    // `if let` / `while let` with variant patterns.
    let s = Shape::Circle(40);
    let mut r: i32 = 0;
    if let Shape::Circle(x) = s { r = x; } else { return 6; }
    if let Shape::Square(y) = s { return 7; }
    let mut i: i32 = 0;
    let mut acc: i32 = 0;
    while let Shape::Circle(x) = step(i) { acc = acc + x; i = i + 1; }
    if acc != 3 { return 8; }
    // A user-declared union keeps its tag even when it looks like an optional.
    if @size_of(MaybeRef) != 16 { return 9; }
    return r + 2;
}
pub union MaybeRef { None, Some: &i32 }"
        ),
        Some(42)
    );
    reject(
        "linked_union_to_enum_rejected",
        "pub enum Op { A, B }\npub union(Op) M { A, B }\npub fn main() -> i32 { let m = M::A; return 0; }",
        "Union 'M' cannot link to enum 'Op'",
    );
    reject(
        "union_duplicate_variant_value",
        "pub union(u8) M { A = 5, B: i32 = 5 }\npub fn main() -> i32 { return 0; }",
        "Variants 'M::B' and 'M::A' of Union 'M' have the same value 5",
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
    reject("empty_tuple", "fn f() -> tuple {} { return {}; }\npub fn main() -> i32 { return 0; }", "use 'void'");

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
    impl drop { fn drop(self: &mut Self) { let x = *self.b.get(); } }
    pub fn take(move self) -> Box[i32] { return self.b; }
}
pub fn main() -> i32 { let o = O::new(); let b = o.take(); return 0; }",
        "because that type has a 'drop' hook",
    );
    accept(
        "move_out_of_plain_opaque",
        "opaque O { b: Box[i32], pub fn new() -> Self { return Self { b: Box[i32]::new(1) }; } pub fn take(move self) -> Box[i32] { return self.b; } }
pub fn main() -> i32 { let o = O::new(); let b = o.take(); return 0; }",
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
fn Pick[n: i32] -> type {
    let mut i: i32 = 0;
    while i < n { i = i + 1; if i == 2 { continue; } }
    if i == 3 { return u8; }
    return u64;
}
const F: i32 = fib(9);
const S: i32 = sum(4);
pub fn main() -> i32 {
    let a: [i32; four()] = { 1, 2, 3, 4 };
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
fn test_pattern_types_span_the_full_base_range() {
    // Full ranges carry no `!range` metadata (LLVM rejects a full range); ranges straddling the
    // signed midpoint and wrapping pieces must still produce valid metadata.
    assert_eq!(
        run_lli(
            "pattern_full_ranges",
            "alias FullU8 = u8 in 0..=255;
alias FullI8 = i8 in -128..=127;
alias FullU64 = u64 in 0..=u64::MAX;
alias Split = u8 in 0..=10 | 100..=200 | 250..=255;
alias Ends = i8 in -128..=-100 | 100..=127;
fn u(x: u8) -> FullU8 { return x as FullU8; }
fn s(x: u8) -> Split { return x as Split; }
fn e(x: i8) -> Ends { return x as Ends; }
pub fn main() -> i32 {
    let a: FullI8 = -128;
    let b: FullU64 = 18446744073709551615;
    // 255 - 150 + 0 - 128 + 127 + 63 - 128 + 3 = 42
    return (u(255) as i32) - (s(150) as i32) + (s(0) as i32) + (e(-128) as i32) + (e(127) as i32)
        + ((b >> 58) as i32) + (a as i32) + (@size_of(?FullU8) as i32) + 1;
}"
        ),
        Some(42)
    );
    assert_eq!(
        run_lli(
            "pattern_split_trap",
            "alias Split = u8 in 0..=10 | 250..=255;\nfn s(x: u8) -> Split { return x as Split; }\npub fn main() -> i32 { return s(100) as i32; }"
        ),
        Some(TRAP_EXIT)
    );
    // Bounds past `i128`: `u128::MAX`, `Int::MAX` of a `u256`, niche-optimized `?NonZero[u256]`,
    // checked casts, and compile-time evaluation through the VM.
    assert_eq!(
        run_lli(
            "pattern_wide_bounds",
            "alias Top = u128 in 340282366920938463463374607431768211400..=340282366920938463463374607431768211455;
pub fn NonZero[Int: integer] -> type { return Int in 1..=Int::MAX; }
fn top(x: u128) -> ?Top { return x as? Top; }
fn g(x: u256) -> u256 { let y: NonZero[u256] = x as NonZero[u256]; return y; }
const K: u256 = g(u256::MAX);
pub fn main() -> i32 {
    let m: Top = 340282366920938463463374607431768211455;
    let n: NonZero[u256] = 5;
    let mut r: i32 = (n as i32) + (@size_of(?NonZero[u256]) as i32) - 32;
    if top(5) == null { r = r + 10; }
    if top(340282366920938463463374607431768211455) != null { r = r + 1; }
    // 5 + 0 + 10 + 1 + 63 - 63 + 26 = 42
    return r + ((K >> 250) as i32) - ((m >> 122) as i32) + 26;
}"
        ),
        Some(42)
    );
    reject("pattern_bound_past_base", "alias S = u8 in 0..=256;\npub fn main() -> i32 { return 0; }", "does not fit in 'u8'");
    reject(
        "pattern_wide_literal_outside",
        "alias F = u128 in 1..=340282366920938463463374607431768211400;\npub fn main() -> i32 { let a: F = 340282366920938463463374607431768211455; return 0; }",
        "outside valid pattern ranges of 'u128 in 1..=340282366920938463463374607431768211400'",
    );
    // Arithmetic runs on the base type, so its result narrows back only explicitly.
    assert_eq!(
        run_lli(
            "pattern_arith_on_base",
            "alias P = u8 in 100..=200;
fn bump(p: P) -> P { return (p + 1) as P; }
pub fn main() -> i32 { let p: P = 150; let d = p - 108; if p < 3 { return 1; } return (d >> 1) as i32 + (bump(200) as i32); }"
        ),
        Some(TRAP_EXIT)
    );
    reject(
        "pattern_implicit_narrowing",
        "alias P = u8 in 100..=200;\nfn f(p: P) -> P { return p + 1; }\npub fn main() -> i32 { return 0; }",
        "Cannot implicitly narrow a runtime 'u8' to pattern type 'u8 in 100..=200'",
    );
    reject(
        "index_must_be_usize",
        "fn at(a: [i32; 4], i: u8) -> i32 { return a[i]; }\npub fn main() -> i32 { let arr: [i32; 4] = { 1, 2, 3, 42 }; return at(arr, 3); }",
        "Index must be 'usize', found 'u8'",
    );
}

#[test]
fn test_compile_package_from_directory() {
    let dir = std::env::temp_dir().join(format!("sloplang_pkg_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src/net")).unwrap();
    std::fs::write(
        dir.join("src/main.slop"),
        "import root::net::http::get;\npub fn main() -> i32 { return get(); }",
    )
    .unwrap();
    std::fs::write(dir.join("src/net/http.slop"), "pub fn get() -> i32 { return 42; }").unwrap();
    let modules = Compiler::load_package_dir(&dir).expect("load");
    let names: Vec<&str> = modules.iter().map(|(m, _)| m.as_str()).collect();
    assert_eq!(names, vec!["root", "root::net::http"]);
    Compiler::compile_package_dir(&dir).expect("package compiles");
    let _ = std::fs::remove_dir_all(&dir);
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
            "binop_mixed_widths",
            "pub fn main() -> i32 { let a: i32 = 1; let b: i64 = 2; let c = a + b; return 0; }",
            "cannot implicitly convert 'i64' to 'i32' (in '+')",
        ),
        (
            "binop_mixed_shift",
            "pub fn main() -> i32 { let a: u64 = 1; let b: u32 = 3; return (a << b) as i32; }",
            "cannot implicitly convert 'u32' to 'u64' (in '<<')",
        ),
    ] {
        reject(name, src, expected);
    }
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
    // the other operand of an operator, an index, or a return value; otherwise `i64` / `f64`.
    assert_eq!(
        run_lli(
            "literal_inference",
            "fn take_i32(x: i32) -> i32 { return x; }
fn take_f32(x: f32) -> f32 { return x; }
fn wide() -> u64 { let x = 7; return x; }
pub fn main() -> i32 {
    let a: [i32; 4] = { 10, 20, 3, 4 };
    let n: usize = 4;
    let mut i = 0;
    let mut s = 0;
    while i < n { s = s + a[i]; i = i + 1; }
    let b = 250;
    let wrapped: u8 = b +% 10;
    let half = 2.5;
    let big = 5000000000;
    // 37 + 4 + 2 + 7 + 1 - 9 = 42
    return take_i32(s) + (wrapped as i32) + (take_f32(half) as i32)
        + (wide() as i32) + ((big / 5000000000) as i32) - 9;
}"
        ),
        Some(42)
    );
    // A binding used before its first typed use in a way that needs a settled type (captured by a
    // closure, in a tuple, borrowed) still takes the type of that later use.
    assert_eq!(
        run_lli(
            "literal_inference_after_escape",
            "fn take(x: i32) -> i32 { return x; }
fn take_u8(x: u8) -> i32 { return x as i32; }
pub fn main() -> i32 {
    let mut c = 0;
    let g = fn() { c += 20; };
    g();
    let a = 20;
    let t = { a, 2 };
    return take(c) + take_u8(a) + (t.1 as i32);
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
        "fn f(x: u8) -> i32 { return x as i32; }\nfn g(x: i32) -> i32 { return x; }\npub fn main() -> i32 { let x = 5; return f(x) + g(x); }",
        "cannot implicitly convert 'u8' to 'i32'",
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
    pub fn next(self: &mut Self) -> ?i32 {
        if self.n >= 3 { return null; }
        self.n = self.n + 1;
        return self.n;
    }
}
fn sum(s: &[i32]) -> i32 { let mut t = 0; for x in s { t += x; } return t; }
pub fn main() -> i32 {
    let mut a: [i32; 4] = { 1, 2, 3, 4 };
    let mut r = 0;
    for i in 0..4 { r += a[i]; }                 // 10, `i` inferred as usize
    for ref mut x in a { *x = *x * 2; }          // a = { 2, 4, 6, 8 }
    for (x, i) in a { if i == 3 { r += x; } }    // 18
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
fn dm(a: i32, b: i32) -> tuple { i32, i32 } { return { a / b, a % b }; }
pub fn main() -> i32 {
    let { q, r } = dm(17, 5);                    // 3, 2
    let P { x, y: why, .. } = P { x: 30, y: 7, z: 0 };
    let t: tuple { i32, i32 } = { 0, 99 };
    let { a, _ } = t;
    return q + r + x + why + a;
}"
        ),
        Some(42)
    );
    for (name, src, expected) in [
        (
            "for_moves_noncopy",
            "opaque B { v: i32, pub fn new() -> Self { return Self { v: 1 }; } }\npub fn main() -> i32 { let a: [B; 1] = { B::new() }; for b in a { } return 0; }",
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
        ("element", "pub fn main() -> i32 { let a: [i32; 2] = { 1, 2 }; a[0] = 5; return a[0]; }"),
        ("borrow_mut", "pub fn main() -> i32 { let a = 1; let p = &mut a; *p = 2; return a; }"),
        ("param", "fn f(x: i32) -> i32 { x = x + 1; return x; }\npub fn main() -> i32 { return f(1); }"),
        ("loop_var", "pub fn main() -> i32 { for i in 0..3 { i = 5; } return 0; }"),
        ("for_ref_mut", "pub fn main() -> i32 { let a: [i32; 2] = { 1, 2 }; for ref mut x in a { *x = 0; } return 0; }"),
        ("capture", "pub fn main() -> i32 { let c = 0; let f = fn() { c += 1; }; f(); return c; }"),
        (
            "mut_self_method",
            "opaque C { n: i32, pub fn new() -> Self { return Self { n: 0 }; } pub fn inc(self: &mut Self) { self.n = self.n + 1; } }\npub fn main() -> i32 { let c = C::new(); c.inc(); return 0; }",
        ),
    ] {
        reject(name, src, "it is not declared 'mut'");
    }
    assert_eq!(
        run_lli(
            "mut_allowed",
            "struct P { x: i32 }
fn bump(mut x: i32) -> i32 { x += 1; return x; }
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
            "opaque(linear) Tx { id: i32, pub fn new(i: i32) -> Self { return Self { id: i }; } pub fn commit(move self) -> i32 { return self.id; } }\npub fn main() -> i32 { let pair: tuple { Tx, Tx } = { Tx::new(1), Tx::new(2) }; let { a, .. } = pair; return a.commit(); }",
            "Linear value '<destructured value>.1'",
        ),
    ] {
        reject(name, src, expected);
    }
}

#[test]
fn test_design_md_examples_compile() {
    // Every ```rust block in DESIGN.md compiles (with a trivial `main` added when it has none);
    // fragments and pseudo-code are fenced ```rust,ignore.
    let design = include_str!("../../DESIGN.md");
    let mut lines = design.lines().enumerate();
    let mut checked = 0;
    while let Some((i, line)) = lines.next() {
        if line.trim_start() != "```rust" {
            continue;
        }
        let indent = line.len() - line.trim_start().len();
        let mut block = String::new();
        for (_, l) in lines.by_ref() {
            if l.trim_start() == "```" {
                break;
            }
            block.push_str(l.get(indent..).unwrap_or(l.trim_start()));
            block.push('\n');
        }
        if !block.contains("fn main(") {
            block.push_str("pub fn main() -> i32 { return 0; }\n");
        }
        if let Err(e) = Compiler::compile_source(&block) {
            panic!("DESIGN.md example at line {} does not compile: {e}\n{block}", i + 1);
        }
        checked += 1;
    }
    assert!(checked >= 15, "only {checked} DESIGN.md examples found");
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
        "no enclosing loop is labelled 'nope'",
    );
}

#[test]
fn test_unused_generic_bodies_are_checked() {
    // A generic function a package never instantiates is tried with a representative of each
    // constraint; one that fails for a type its constraints allow is reported as a warning.
    let src = "
fn bad_field[T](a: T) -> i32 { return a.nonexistent; }
fn dup_any[T](a: T) -> tuple { T, T } { return { a, a }; }
fn good_add[T: integer](a: T, b: T) -> T { return a + b; }
fn dup_copy[T: copy](a: T) -> tuple { T, T } { return { a, a }; }
fn sized[n: usize]() -> usize { return n * 2; }
pub fn main() -> i32 { return 0; }
";
    let (_, warnings) =
        Compiler::compile_package_with_warnings(&[("root", src)]).expect("compiles");
    let flagged: Vec<&str> = ["bad_field", "dup_any", "good_add", "dup_copy", "sized"]
        .into_iter()
        .filter(|f| warnings.iter().any(|w| w.contains(&format!("'root::{f}'"))))
        .collect();
    assert_eq!(flagged, ["bad_field", "dup_any"], "{warnings:#?}");
    assert!(warnings.iter().any(|w| w.contains("Use of moved or uninitialized value 'a'")));
}

#[test]
fn test_type_functions_run_on_the_vm() {
    // A type function runs on the compile-time VM like any compile-time function; building a
    // type calls back into the compiler only on the path actually taken, so recursion that
    // stops at a base case terminates, and `type` locals can change in loops.
    let src = "
fn Nest[N: i32] -> type {
    if N == 0 { return i32; }
    return tuple { i32, Nest[N - 1] };
}
fn Wider[A, B] -> type {
    let mut t: type = A;
    if @size_of(B) > @size_of(A) { t = B; }
    return [t; 2];
}
fn Pair[A] -> type { return tuple { A, u8 }; }
fn Chain[n: i32] -> type {
    let mut t: type = u8;
    let mut i: i32 = 0;
    while i < n {
        t = Pair[t];
        i += 1;
    }
    return t;
}
pub fn main() -> i32 {
    let a: Nest[2] = { 1, { 2, 3 } };
    let w: Wider[u8, i64] = { 30, 2 };
    let c: Chain[2] = { { 1, 2 }, 3 };
    if @size_of(Wider[u8, i64]) != 16 || @size_of(Wider[i32, u16]) != 8 { return 1; }
    let inner = a.1;
    let c0 = c.0;
    return a.0 + inner.0 + inner.1 + (w[0] + w[1]) as i32 + (c0.0 + c0.1 + c.1) as i32 - 2;
}
";
    assert_eq!(run_lli("type_fns_on_vm", src), Some(42));

    // The VM's limits apply: a loop that never ends exhausts the step budget, and recursion
    // without a base case the nesting depth.
    for (body, want) in [
        ("let mut i: i32 = 0; while true { i += 1; } return u8;", "step limit"),
        ("return tuple { u8, Forever[N + 1] };", "recursed too deeply"),
    ] {
        let src = format!(
            "fn Forever[N: i32] -> type {{ {body} }}
pub fn main() -> i32 {{ let x: Forever[0] = uninit; return 0; }}"
        );
        let err = Compiler::compile_source(&src).err().unwrap_or_default();
        assert!(err.contains(want), "expected '{want}', got: {err}");
    }
}

#[test]
fn test_synthesized_structs_are_the_anonymous_struct() {
    // An anonymous struct is structural however it is written: `@Struct` with the same ordered
    // fields is the same type as `struct { ... }` (and `@Tuple` as `tuple { ... }`), and both
    // are named by their fields in diagnostics.
    let src = r#"
fn S() -> type { return @Struct(&[FieldSpec { name: "x", ty: i32 }]); }
fn T() -> type { return @Tuple(&[i32, u8]); }
pub fn main() -> i32 {
    let a: struct { x: i32 } = struct { x: i32 } { x: 40 };
    let b: S() = a;
    let c: tuple { i32, u8 } = { 1, 1 };
    let d: T() = c;
    return b.x + d.0 + (d.1 as i32);
}
"#;
    assert_eq!(run_lli("synthesized_struct_identity", src), Some(42));
    let err = Compiler::compile_source(
        "pub fn main() -> i32 { let a: struct { x: i32 } = struct { x: i32 } { x: 1 }; let b: i64 = a; return 0; }",
    )
    .unwrap_err();
    assert!(err.contains("'struct { x: i32 }'"), "{err}");
}

#[test]
fn test_named_structs_are_nominal_and_anonymous_structs_structural() {
    // A named struct (`struct N { ... }`, `type N = struct { ... }`, a struct literal returned by
    // a type function) is its own type; an anonymous struct is structural data and so cannot
    // carry methods or field defaults, which belong to a named struct. A tuple alias is an
    // alias.
    let distinct = [
        "struct A { x: i32 } struct B { x: i32 }
pub fn main() -> i32 { let a: A = A { x: 1 }; let b: B = a; return 0; }",
        "struct A { x: i32 }
pub fn main() -> i32 { let a: A = A { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
        "struct N { x: i32 }
pub fn main() -> i32 { let a: N = N { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
        "fn S[T] -> type { return struct { x: T }; }
pub fn main() -> i32 { let a: S[i32] = S[i32] { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
    ];
    for src in distinct {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains("Type mismatch"), "{src}\n{err}");
    }
    let same = "alias P = tuple { i32, i32 };
fn S[T] -> type { return @Struct(&[FieldSpec { name: \"x\", ty: T }]); }
pub fn main() -> i32 {
    let a: P = { 40, 1 };
    let b: tuple { i32, i32 } = a;
    let c: S[i32] = struct { x: i32 } { x: 1 };
    return b.0 + b.1 + c.x;
}";
    assert_eq!(run_lli("structural_identity", same), Some(42));
    for (src, want) in [
        (
            "pub fn main() -> i32 { let a = struct { x: i32, fn get(self: &Self) -> i32 { return self.x; } } { x: 1 }; return 0; }",
            "Anonymous struct cannot declare method 'get'",
        ),
        (
            "pub fn main() -> i32 { let a: struct { x: i32 = 3 } = uninit; return 0; }",
            "Anonymous struct cannot give field 'x' a default value",
        ),
    ] {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains(want), "expected '{want}', got: {err}");
    }
}

#[test]
fn test_type_declares_and_alias_names() {
    // `type N = ...` declares a new nominal type, so its right-hand side must be a declaration
    // (struct, opaque, enum, union, error, overlay); naming an existing or structural type takes
    // `alias`, and an alias never declares a new type.
    let src = "alias Pair = tuple { i32, i32 };
alias Small = u8 in 0..=100;
alias Point = struct { x: i32, y: i32 };
struct Named { x: i32, y: i32 }
pub fn main() -> i32 {
    let p: Pair = { 1, 2 };
    let q: tuple { i32, i32 } = p;
    let s: Small = 30;
    let a: Point = struct { x: i32, y: i32 } { x: 4, y: 5 };
    let n: Named = Named { x: 0, y: 0 };
    return q.0 + q.1 + (s as i32) + a.x + a.y + n.x;
}";
    assert_eq!(run_lli("alias_and_type", src), Some(42));
    for (src, want) in [
        ("type Pair = tuple { i32, i32 };", "write 'alias Pair = ...;'"),
        ("type Byte = u8;", "write 'alias Byte = ...;'"),
        ("alias Color = enum { Red, Green };", "write 'type Color = ...;'"),
        ("alias Box2 = opaque { v: i32 };", "write 'type Box2 = ...;'"),
        ("export alias Id = u32;", "'export alias Id' is not supported"),
    ] {
        let err = Compiler::compile_source(&format!("{src}\npub fn main() -> i32 {{ return 0; }}"))
            .unwrap_err();
        assert!(err.contains(want), "{src}: expected '{want}', got: {err}");
    }
    let err = Compiler::compile_source(
        "alias Point = struct { x: i32 }; struct Named { x: i32 }
pub fn main() -> i32 { let a: Point = struct { x: i32 } { x: 1 }; let b: Named = a; return 0; }",
    )
    .unwrap_err();
    assert!(err.contains("Type mismatch"), "{err}");
}

#[test]
fn test_distinct_type_declarations() {
    // A distinct type is declared `type Name = distinct T`; the former newtype spellings and a
    // distinct tuple or anonymous struct (whose fields it would hide, even through an alias)
    // are errors naming the right form.
    for (src, want) in [
        ("opaque Id = u64;", "write 'type Id = distinct ...;'"),
        ("type Id = opaque u64;", "write 'type Id = distinct ...;'"),
        ("type P = distinct struct { x: i32 };", "declare 'struct P { ... }'"),
        ("type P = distinct tuple { i32, i32 };", "wraps a tuple"),
        ("alias T = tuple { i32, i32 };\ntype P = distinct T;", "wraps a tuple"),
        ("alias S = struct { x: i32 };\ntype P = distinct S;", "wraps an anonymous struct"),
    ] {
        let err = Compiler::compile_source(&format!(
            "{src}\npub fn main() -> i32 {{ let p: {} = uninit; return 0; }}",
            if src.contains(" P ") { "P" } else { "Id" }
        ))
        .unwrap_err();
        assert!(err.contains(want), "{src}: expected '{want}', got: {err}");
    }
}

#[test]
fn test_method_visibility_levels() {
    // A private method is callable inside its type's block, a `pub(mod)` method anywhere in the
    // defining module (so cooperating types need not expose internals), a `pub` one everywhere.
    // `pub(mod)` applies only to methods, and `pub(pkg)` is gone (there are no packages).
    let lib = "pub opaque Guard {
    v: i32,
    pub(mod) fn create(v: i32) -> Self { return Self { v: v }; }
    pub fn get(self: &Self) -> i32 { return self.v; }
}
pub struct Lock {
    n: i32,
    fn secret(self: &Self) -> i32 { return self.n; }
    pub fn lock(self: &Self) -> Guard { return Guard::create(self.n); }
}
pub fn make() -> Guard { return Guard::create(42); }";
    let main_ok = "import root::lib::{Lock, make};
pub fn main() -> i32 { let l = Lock { n: 0 }; return make().get() + l.lock().get(); }";
    let prog = Compiler::compile_package(&[("root::lib", lib), ("root", main_ok)]).expect("compiles");
    let ir = crate::llvm::LlvmLowering::lower(&prog).unwrap();
    assert_eq!(super::lli(&ir).status.code(), Some(42));
    for (main, want) in [
        (
            "import root::lib::Guard;\npub fn main() -> i32 { return Guard::create(1).get(); }",
            "outside module 'root::lib': it is 'pub(mod)'",
        ),
        (
            "import root::lib::Lock;\npub fn main() -> i32 { let l = Lock { n: 1 }; return l.secret(); }",
            "Cannot call private method 'secret' of 'Lock' outside its block",
        ),
    ] {
        let err = Compiler::compile_package(&[("root::lib", lib), ("root", main)]).unwrap_err();
        assert!(err.contains(want), "expected '{want}', got: {err}");
    }
    // The standard library's cooperating types keep their internals module-only: user code can
    // neither forge a mutex guard nor rewrite a channel's wait node.
    for src in [
        "import std::sync::WaitNode;
pub fn main() -> i32 { let mut n = WaitNode::new(); n.deactivate(); return 0; }",
        "import std::sync::MutexGuard;
pub fn main() -> i32 { let g = MutexGuard[i32]::create(0 as *mut u8, 0 as *mut i32); g.unlock(); return 0; }",
    ] {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains("it is 'pub(mod)'"), "{src}\n{err}");
    }
    for (src, want) in [
        ("pub(mod) fn f() {}", "'pub(mod)' applies only to methods"),
        ("opaque O { pub(mod) x: i32 }", "'pub(mod)' applies only to methods"),
        ("pub(pkg) fn f() {}", "'pub(pkg)' was removed"),
    ] {
        let err = Compiler::compile_source(&format!("{src}\npub fn main() -> i32 {{ return 0; }}"))
            .unwrap_err();
        assert!(err.contains(want), "{src}: expected '{want}', got: {err}");
    }
}

#[test]
fn test_one_spelling_per_construct() {
    // `t.1.0` indexes twice; a call through a type is `Type::f(...)` (`.` is for values); each
    // kind of type has one declaration form; an export is written `export`, not `pub export`;
    // a struct literal is `Type { ... }`, not `Type.{ ... }`.
    let src = "struct P { x: i32, pub fn new(x: i32) -> Self { return Self { x: x }; } }
pub fn main() -> i32 {
    let t: tuple { i32, tuple { i32, i32 } } = { 1, { 2, 3 } };
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
error IoErr { NotFound, Denied: i32 }
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
    if let v = maybe { t += score(v); }
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
union Msg { Quit, Move: struct { dx: i32, dy: i32 } }
error E { Bad }
const ORIGIN: P = { x: 1, y: 1 };
fn make(x: i32) -> P { return { x: x, y: x + 1 }; }
fn sum(p: P) -> i32 { return p.x + p.y; }
fn checked(x: i32) -> E!P { if x < 0 { return .Bad; } return { x: x, y: 0 }; }
fn T() -> type { return @Struct(&[{ name: \"v\", ty: i32 }]); }
pub fn main() -> i32 {
    let a: P = { x: 2, y: 3 };
    let o: ?P = { x: 4, y: 0 };
    let anon = { u: 5, w: 6 };
    let same: struct { u: i64, w: i64 } = anon;
    let m: Msg = .Move({ dx: 1, dy: 1 });
    let t: T() = { v: 1 };
    let mut total = sum(a) + make(3).y + sum({ x: 1, y: 1 }) + sum(ORIGIN);
    total += (same.u + same.w) as i32;
    if let v = o { total += v.x; }
    if let .Move(d) = m { total += d.dx + d.dy; }
    let c = checked(7) catch |e| ORIGIN;
    return total + c.x + t.v - 17;
}";
    // 5 + 4 + 2 + 2 + 11 + 4 + 2 + 7 + 1 - 17 = 21
    assert_eq!(run_lli("record_literals", src), Some(21));
    // A literal naming a field the struct lacks (or one twice) is an error, in either form.
    for lit in ["{ x: 1, z: 2 }", "P { x: 1, z: 2 }", "P { x: 1, x: 2 }"] {
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
fn test_lifecycle_hooks_are_in_block_impls() {
    // Lifecycle hooks are built-in traits implemented in the type's own block (`impl drop`,
    // `impl clone`, `impl default`, `impl format`), conditional ones with `where` on the impl;
    // their names are not keywords, and the former hook form is an error naming the new one.
    let src = "opaque Counter {
    n: i32,
    impl default { fn default() -> Self { return Self { n: 40 }; } }
    impl clone { fn clone(self: &Self) -> Self { return Self { n: self.n + 1 }; } }
    impl drop { fn drop(self: &mut Self) { self.n = 0; } }
    pub fn get(self: &Self) -> i32 { return self.n; }
}
fn twice[T: clone](x: &T) -> T { return @clone(x); }
pub fn main() -> i32 {
    let clone: i32 = 1;
    let a: Counter = @default(Counter);
    let b = twice(&a);
    return b.get() + clone;
}";
    assert_eq!(run_lli("lifecycle_impls", src), Some(42));
    for (body, want) in [
        ("drop(self: &mut Self) { }", "Declare the 'drop' lifecycle hook as 'impl drop"),
        ("impl clone { fn copy(self: &Self) -> Self { return Self { n: 0 }; } }", "must contain exactly 'fn clone(...)'"),
        ("impl drop { fn drop() { } }", "'fn drop' takes 1 parameter(s)"),
    ] {
        let err = Compiler::compile_source(&format!(
            "opaque O {{ n: i32, {body} }}\npub fn main() -> i32 {{ return 0; }}"
        ))
        .unwrap_err();
        assert!(err.contains(want), "{body}\nexpected '{want}', got: {err}");
    }
    let err = Compiler::compile_source(
        "struct S { n: i32, impl drop { fn drop(self: &mut Self) { } } }\npub fn main() -> i32 { return 0; }",
    )
    .unwrap_err();
    assert!(err.contains("forbidden on transparent 'struct' types"), "{err}");
}

#[test]
fn test_errorcode_success_value_in_body() {
    // An `error` header holds only its C backing type; the success constant is the body
    // entry marked `ok`, so the body lists every constant of the emitted C enum. The former
    // header forms and the `errorcode` keyword are errors naming the new form, and a variant
    // may still be called `ok`.
    let src = "export error(u8) SmallErr { ok Success = 255, Low = 0, High = 200 }
error Plain { ok, NotOk }
export fn check(x: i32) -> SmallErr!void { if x < 0 { return .Low; } return; }
pub fn main() -> i32 { let p: Plain = .ok; return 42; }";
    let (_, header) = Compiler::compile_source_with_c_header(src).expect("compiles");
    assert!(header.contains("SmallErr_Success = 255"), "{header}");
    for src in [
        "export error(u8, Success = 255) E { Low = 0 }",
        "export error(Ok = 5) E { A = 6 }",
    ] {
        let err = Compiler::compile_source(&format!("{src}\npub fn main() -> i32 {{ return 0; }}"))
            .unwrap_err();
        assert!(err.contains("ok Success = 0"), "{src}\n{err}");
    }
    let err = Compiler::compile_source(
        "error E { ok A = 0, ok B = 1, C }\npub fn main() -> i32 { return 0; }",
    )
    .unwrap_err();
    assert!(err.contains("at most one 'ok'"), "{err}");
    let err = Compiler::compile_source(
        "errorcode E { A }\npub fn main() -> i32 { return 0; }",
    )
    .unwrap_err();
    assert!(err.contains("The 'errorcode' keyword has been unified into 'error'"), "{err}");
}

#[test]
fn test_type_literals_in_value_positions() {
    // A type literal is accepted wherever a value of type `type` is: on the right of an
    // assignment, as an initializer (including `*mut T` and anonymous declarations), and as an
    // argument. (`*mut` / `*const` can never begin a dereference.)
    let src = "fn Chain[n: i32] -> type {
    let mut t: type = u8;
    let mut i: i32 = 0;
    while i < n { t = tuple { t, u8 }; i += 1; }
    return t;
}
fn Ptr() -> type { let p: type = *mut u8; return p; }
fn Kind() -> type { let k: type = enum { A, B }; return k; }
pub fn main() -> i32 {
    let c: Chain[1] = { 40, 2 };
    let mut x: u8 = 0;
    let p: Ptr() = &mut x as *mut u8;
    let k: Kind() = .B;
    let a: i32 = 6;
    return (c.0 + c.1) as i32 + unsafe { *p } as i32 + (a * 0);
}";
    assert_eq!(run_lli("type_literal_values", src), Some(42));
}

#[test]
fn test_dot_variant_and_record_lit_corner_cases() {
    // 1. `.Variant` and `{ ... }` through `E!?T`, in `const`, and in struct default fields;
    //    embedded error subtype pattern `IoErr` alongside `.Leaf` in `match` on `error`.
    let src = "enum Color { Red = 1, Green = 2, Blue = 4 }
struct Point { x: i32, y: i32 = 10 }
struct Cfg { color: Color = .Green, pt: Point = { x: 5 } }
error IoErr { Disconnected }
error AppErr { IoErr, BadInput: i32 }

const C_BLUE: Color = .Blue;
const C_OPT: ?Color = .Red;
const C_CFG: Cfg = {};

fn pick_color(mode: i32) -> AppErr!?Color {
    if mode < 0 { return .BadInput(-mode); }
    if mode == 0 { return null; }
    return .Green;
}

fn pick_point(mode: i32) -> AppErr!?Point {
    if mode < 0 { return .Disconnected; }
    if mode == 0 { return null; }
    return { x: mode, y: 20 };
}

fn handle_err(e: AppErr) -> i32 {
    match e {
        .BadInput(code) => return code,
        IoErr => return 9,
    }
}

pub fn main() -> i32 {
    let c1 = (pick_color(1) catch |e| null) orelse .Red;
    let p1 = (pick_point(3) catch |e| null) orelse { x: 0, y: 0 };
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
            "error E {{ NotFound, Denied: i32 }}
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
        "pub fn main() -> i32 { let r = { a: 1, a: 2 }; return r.a; }",
        "const R = { a: 1, a: 2 };\npub fn main() -> i32 { return R.a; }",
        "fn check[r: struct { a: i32 }]() -> i32 { return r.a; }\npub fn main() -> i32 { return check[{ a: 1, a: 2 }](); }",
    ] {
        let err = Compiler::compile_source(code).unwrap_err();
        assert!(
            err.contains("Duplicate field 'a'") || err.contains("is given twice"),
            "code={code}, got: {err}"
        );
    }
}

#[test]
fn test_distinct_type_ownership_casts_and_reflection_corner_cases() {
    // 1. `distinct` over a struct, affine type with `drop`, raw pointer, and `@backing_type`;
    //    generic static method on a `distinct` type.
    let src = "static mut DROPS: i32 = 0;

opaque Tracked {
    v: i32,
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    impl drop {
        fn drop(self: &mut Self) {
            unsafe { DROPS += self.v; }
        }
    }
}

type DistinctTracked = distinct Tracked;
struct Pair { a: i32, b: i32 }
type DistinctPair = distinct Pair;
type RawPtr = distinct *mut i32;

type TaggedId = distinct i32 {
    pub fn from_val[T: integer](x: T) -> Self {
        return (x as i32) as Self;
    }
}

fn kind_fn() -> type {
    return enum { One, Two };
}

pub fn main() -> i32 {
    if @satisfies(DistinctTracked, copy) { return 1; }
    if !@satisfies(DistinctTracked, affine) { return 2; }
    if @satisfies(RawPtr, send) || @satisfies(RawPtr, sync) { return 3; }
    if @satisfies(DistinctPair, tuple) || @satisfies(DistinctPair, struct) { return 4; }
    if @backing_type(DistinctPair) != Pair { return 5; }
    if @backing_type(TaggedId) != i32 { return 6; }
    if @type_name(kind_fn()) != \"kind_fn\" { return 7; }
    if true {
        let dt: DistinctTracked = Tracked::new(12) as DistinctTracked;
    }
    let dp: DistinctPair = Pair { a: 10, b: 15 } as DistinctPair;
    let p_back: Pair = dp as Pair;
    let tid = TaggedId::from_val[i16](5);
    return unsafe { DROPS } + p_back.a + p_back.b + (tid as i32);
}";
    assert_eq!(run_lli("distinct_corner_cases", src), Some(42));

    // 2. `distinct` over a `linear` type must still be consumed.
    let err = Compiler::compile_source(
        "opaque(linear) Ticket {
    id: i32,
    pub fn new(id: i32) -> Self { return Self { id: id }; }
    pub fn consume(move self) -> i32 { return self.id; }
}
type MyTicket = distinct Ticket;
pub fn main() -> i32 {
    let t: MyTicket = Ticket::new(1) as MyTicket;
    return 0;
}",
    )
    .unwrap_err();
    assert!(err.contains("Linear value"), "Expected linear error, got: {err}");

    // 3. Invalid `as` casts involving `distinct` types are rejected.
    for bad in [
        "struct P { x: i32 }\ntype DP = distinct P;\npub fn main() -> i32 { let d: DP = P { x: 1 } as DP; return d as i32; }",
        "struct P { x: i32 }\nstruct Q { x: i32 }\ntype DP = distinct P;\npub fn main() -> i32 { let d: DP = P { x: 1 } as DP; let q: Q = d as Q; return q.x; }",
    ] {
        let err = Compiler::compile_source(bad).unwrap_err();
        assert!(err.contains("Cannot cast"), "bad={bad}, got: {err}");
    }

    // 4. Static method wrong argument count is rejected.
    let err = Compiler::compile_source(
        "struct Counter {
    v: i32,
    pub fn make(v: i32) -> Self { return Self { v: v }; }
}
pub fn main() -> i32 {
    let c = Counter::make(1, 2);
    return c.v;
}",
    )
    .unwrap_err();
    assert!(
        err.contains("Method 'Counter::make' expects 1 arguments, got 2"),
        "Unexpected error: {err}"
    );
}

#[test]
fn test_lifecycle_hook_and_errorcode_corner_cases() {
    // 1. Lifecycle hook placement and visibility diagnostics.
    for (src, want) in [
        (
            "opaque O { x: i32, pub impl drop { fn drop(self: &mut Self) {} } }\npub fn main() -> i32 { return 0; }",
            "'impl drop' takes no visibility modifier",
        ),
        (
            "opaque O { x: i32, impl drop { pub fn drop(self: &mut Self) {} } }\npub fn main() -> i32 { return 0; }",
            "'fn drop' inside 'impl drop' takes no visibility modifier",
        ),
        (
            "type D = distinct i32 { impl drop { fn drop(self: &mut Self) {} } }\npub fn main() -> i32 { return 0; }",
            "Lifecycle hook 'drop' is not permitted inside 'extern opaque' or 'distinct' type blocks",
        ),
        (
            "struct S { x: i32 }\nimpl drop for S { fn drop(self: &mut Self) {} }\npub fn main() -> i32 { return 0; }",
            "Lifecycle hook 'drop' must be declared as 'impl drop { fn drop(...) { ... } }' inside the type's own 'opaque { ... }' block",
        ),
    ] {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains(want), "src={src}\nwant={want}\ngot={err}");
    }

    // 2. `error` with `ok` entry in non-first position, `@backing_type(Status)`, and
    //    passing the `Ok` sentinel from C into a by-value unit `export error` parameter traps.
    let src = "export error(u8) Status {
    Busy = 10,
    ok Done = 200,
    Failed = 20,
}

export fn describe(s: Status) -> i32 {
    match s {
        .Busy => return 1,
        .Failed => return 2,
    }
}

export fn check_status(ok: bool) -> Status!void {
    if !ok { return .Failed; }
}

pub fn main() -> i32 {
    if @backing_type(Status) != u8 { return 1; }
    let fp = @c_abi(describe);
    let chk = @c_abi(check_status);
    if chk(true) != 200 || chk(false) != 20 { return 2; }
    return fp(.Failed) + 40;
}";
    assert_eq!(run_lli("errorcode_nonfirst_ok", src), Some(42));

    let trap_src = "export error(u8) Status {
    Busy = 10,
    ok Done = 200,
}
export fn describe(s: Status) -> i32 {
    match s {
        .Busy => return 1,
    }
}
pub fn main() -> i32 {
    let fp = @c_abi(describe);
    let bad: Status = unsafe { @transmute(Status, 200 as u8) };
    return fp(bad);
}";
    assert_eq!(
        run_lli("errorcode_ok_passed_as_param_traps", trap_src),
        Some(TRAP_EXIT),
        "Passing the C success code as a by-value unit error argument must trap"
    );
}

#[test]
fn test_comptime_parameters_in_brackets() {
    // Comptime parameters and arguments are written in brackets. A type function still returns
    // any kind of type; `f(x)` infers comptime arguments and `f[T](x)` gives them; `F[T]` with
    // one argument is a type-function call only when `F` names a function, so indexing a local
    // array (including an array of function pointers) is unchanged.
    let src = "fn Pick[N: usize] -> type {
    if N == 0 { return [u8; 2]; }
    if N == 1 { return struct { a: i32, b: i32 }; }
    return opaque {
        v: i32,
        pub fn new(v: i32) -> Self { return Self { v: v }; }
        pub fn get(self: &Self) -> i32 { return self.v; }
    };
}
fn Pair[T] -> type { return struct { first: T, second: T }; }
fn Grid[T, w: usize, h: usize] -> type { return [[T; w]; h]; }
fn id[T](v: T) -> T { return v; }
fn size[T]() -> usize { return @size_of(T); }
fn add1(x: i32) -> i32 { return x + 1; }
pub fn main() -> i32 {
    let a: Pick[0] = { 1, 2 };
    let b: Pick[1] = { a: 3, b: 4 };
    let c = Pick[2]::new(5);
    let p = Pair[i32] { first: 6, second: 7 };
    let t: type = Grid[u8, 2, 3];
    let fs: [fn(i32) -> i32; 1] = { add1 };
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
        "fn Pair[T] -> type { return struct { a: T }; }\npub fn main() -> i32 { let p: Pair(i32) = { a: 1 }; return 0; }",
        "Type function arguments go in brackets",
    );
    reject(
        "impl_in_parens",
        "trait Tr { fn f(self: &Self) -> i32; }\nfn W[T] -> type { return struct { x: T }; }\nimpl(comptime T: type) Tr for W[T] { fn f(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { return 0; }",
        "Generic 'impl' parameters go in brackets",
    );
}

#[test]
fn test_method_comptime_arguments_defaults_and_placeholders() {
    // Methods take bracketed comptime arguments too (`x.m[T](y)`, `Type::m[T](y)`), while
    // `s.fs[i](x)` still calls an element of a field. A comptime parameter may have a default,
    // which is used when the argument is neither given nor inferred; `_` asks for inference.
    // Defaults are filled before memoization, so `Table[i32]` and `Table[i32, 4]` are one type.
    let src = "fn add1(x: i32) -> i32 { return x + 1; }
struct Fns { fs: [fn(i32) -> i32; 1] }
struct Num {
    v: i32,
    pub fn conv[T: integer](self: &Self) -> T { return self.v as T; }
    pub fn scaled[T: integer, k: i32 = 2](self: &Self, x: T) -> i32 { return self.v * k + x as i32; }
    pub fn make[k: i32 = 5]() -> Num { return Num { v: k }; }
}
fn Table[T, n: usize = 4] -> type { return [T; n]; }
fn widen[D: integer, S: integer = u8](x: S) -> D { return x as D; }
fn pick[T, n: i32 = 7](x: T) -> i32 { return n; }
pub fn main() -> i32 {
    let f = Fns { fs: { add1 } };
    let n = Num { v: 3 };
    let a: i64 = n.conv[i64]();
    let t: Table[i32] = { 1, 2, 3, 4 };
    let u: Table[i32, 4] = t;
    let w: i64 = widen[i64, _](u.len as u16);
    return f.fs[0](1) + a as i32 + n.scaled(1) + n.scaled[i32, 10](0) + Num::make().v
        + Num::make[1]().v + u[3] + w as i32 + pick(true) + pick[_, 0](1) - 21;
}";
    assert_eq!(run_lli("method_brackets_defaults", src), Some(42));

    reject(
        "no_default_no_inference",
        "fn size[T, n: usize = 1]() -> usize { return @size_of(T) * n; }\npub fn main() -> i32 { return size[_]() as i32; }",
        "neither given nor inferable",
    );
    reject(
        "default_order",
        "fn F[T = i32, U] -> type { return T; }\npub fn main() -> i32 { return 0; }",
        "parameters after a defaulted one must also have defaults",
    );
    reject(
        "impl_default",
        "trait Tr { fn f(self: &Self) -> i32; }\nfn W[T] -> type { return struct { x: T }; }\nimpl[T = i32] Tr for W[T] { fn f(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { return 0; }",
        "cannot have a default",
    );
}

#[test]
fn test_design_md_soundness_audit_fixes() {
    // 1. `borrows(*x)` is rejected when reborrowing through a safe `&mut T` (since `x` retains
    //    exclusive access to the same referent unless `x` itself stays borrowed):
    reject(
        "borrows_contents_through_mut_ref_mut",
        "pub fn split_mut(x: &mut &mut i32) -> &mut i32 borrows(*x) { return &mut **x; }\npub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'x'",
    );
    reject(
        "borrows_contents_through_mut_ref_shared",
        "pub fn split_shared(x: &&mut i32) -> &i32 borrows(*x) { return &**x; }\npub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'x'",
    );

    // 2. `borrows(*self)` is rejected when taking a reference behind an `*own` or raw pointer:
    reject(
        "borrows_contents_through_own_ptr",
        "pub opaque OwnBox {
    p: *own i32,
    pub fn get(self: &Self) -> &i32 borrows(*self) { unsafe { return &*self.p; } }
}
pub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'self'",
    );
    reject(
        "borrows_contents_ref_to_own_ref_box",
        "pub opaque OwnRef {
    p: *own &i32,
    pub fn get(self: &Self) -> &&i32 borrows(*self) { unsafe { return &*self.p; } }
}
pub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'self'",
    );

    // 3. Reborrowing an iterator (`let r2 = &mut *r1`) and calling a `borrows(*self)` method
    //    cannot let the yielded element outlive the sequence borrowed by the iterator:
    reject(
        "reborrow_chain_borrows_contents_dangling",
        "pub opaque Iter {
    p: *ref i32,
    pub fn new(x: &i32) -> Self { return Self { p: x as *ref i32 }; }
    pub fn next(self: &mut Self) -> &i32 borrows(*self) { unsafe { return &*self.p; } }
}
pub fn main() -> i32 {
    let dummy: i32 = 0;
    let mut out: &i32 = &dummy;
    if true {
        let local: i32 = 99;
        let mut it = Iter::new(&local);
        let r1: &mut Iter = &mut it;
        let r2: &mut Iter = &mut *r1;
        out = r2.next();
    }
    return *out;
}",
        "goes out of scope while still borrowed",
    );

    // 4. Interprocedural summary inference tracks flows through local containers, reborrows,
    //    and references into by-value composite parameters:
    reject(
        "infer_flow_via_local_container",
        "struct Slot { r: &i32 }
fn indirect_stash(dst: &mut Slot, x: &i32) {
    let tmp = Slot { r: x };
    *dst = tmp;
}
pub fn main() -> i32 {
    let d: i32 = 0;
    let mut s = Slot { r: &d };
    if true {
        let short: i32 = 10;
        indirect_stash(&mut s, &short);
    }
    return *s.r;
}",
        "goes out of scope while still borrowed",
    );
    reject(
        "infer_flow_via_reborrow",
        "struct Slot { r: &i32 }
fn reborrow_stash(dst: &mut Slot, x: &i32) {
    let r: &mut Slot = &mut *dst;
    r.r = x;
}
pub fn main() -> i32 {
    let d: i32 = 0;
    let mut s = Slot { r: &d };
    if true {
        let short: i32 = 10;
        reborrow_stash(&mut s, &short);
    }
    return *s.r;
}",
        "goes out of scope while still borrowed",
    );
    reject(
        "infer_return_from_by_value_composite_param",
        "struct Wrap { r: &i32 }
fn extract(w: Wrap) -> &i32 {
    let p: &&i32 = &w.r;
    return *p;
}
pub fn main() -> i32 {
    let d: i32 = 0;
    let mut out: &i32 = &d;
    if true {
        let short: i32 = 10;
        let w = Wrap { r: &short };
        out = extract(w);
    }
    return *out;
}",
        "goes out of scope while still borrowed",
    );

    // 5. Escaping a borrow of a local stack variable or by-value parameter through a mutable
    //    reference parameter is rejected:
    reject(
        "escape_local_borrow_through_mut_param",
        "struct Slot { r: &i32 }
fn escape(out: &mut Slot) {
    let local: i32 = 42;
    out.r = &local;
}
pub fn main() -> i32 { return 0; }",
        "goes out of scope while still borrowed",
    );
    reject(
        "escape_by_val_param_borrow_through_mut_param",
        "struct Slot { r: &i32 }
fn escape_param(out: &mut Slot, val: i32) {
    out.r = &val;
}
pub fn main() -> i32 { return 0; }",
        "escapes through parameter",
    );

    // 6. `cell` field soundness:
    //    (a) Taking a safe `&` or `&mut` reference or slice to a `cell` field is rejected:
    reject(
        "safe_ref_to_cell_field",
        "pub opaque CellBox {
    cell v: i32,
    pub fn borrow_it(self: &Self) -> &i32 { return &self.v; }
}
pub fn main() -> i32 { return 0; }",
        "Cannot take a safe reference ('&' or '&mut') to 'cell' field 'CellBox.v'",
    );
    reject(
        "safe_slice_to_cell_field",
        "pub opaque CellArr {
    cell buf: [i32; 4],
    pub fn slice_it(self: &Self) -> &[i32] { return &self.buf[0..2]; }
}
pub fn main() -> i32 { return 0; }",
        "Cannot take a safe slice reference to 'cell' field 'CellArr.buf'",
    );
    //    (b) Casting `self: &Self` to `*mut Self` on an `opaque` that has a `cell` field (but NOT
    //        `unsafe sync`) is rejected so non-`cell` sibling fields cannot be mutated behind `&Self`:
    reject(
        "cast_shared_self_to_mut_ptr_with_only_cell_field",
        "pub opaque Mixed {
    cell count: i32,
    imm: i32,
    pub fn bad(self: &Self) {
        let p = self as *mut Self;
        unsafe { (*p).imm = 99; }
    }
}
pub fn main() -> i32 { return 0; }",
        "Cannot cast shared reference '&Mixed' to '*mut Mixed'",
    );

    // 7. `unsafe impl drop(may_dangle T)` soundness:
    //    (a) A type with `unsafe impl drop(may_dangle T)` that also holds a direct `&i32` field
    //        not covered by `T` cannot let that `&i32` dangle at drop:
    reject(
        "may_dangle_with_uncovered_ref_field",
        "fn BadBox[T] -> type {
    return opaque {
        val: T,
         spy: &i32,
        pub fn new(val: T, spy: &i32) -> Self { return Self { val: val, spy: spy }; }
        unsafe impl drop(may_dangle T) {
            fn drop(self: &mut Self) {
                let _ = *self.spy;
            }
        }
    };
}
pub fn main() -> i32 {
    let d: i32 = 1;
    let mut b = BadBox[i32]::new(0, &d);
    let short: i32 = 2;
    b = BadBox[i32]::new(0, &short);
    return 0;
}",
        "goes out of scope while still borrowed",
    );
    //    (b) Dropping a `may_dangle` field (`Vec[&i32]`) of an enclosing struct must not erase
    //        active loans held by a sibling field (`Peek`) whose drop reads its borrow:
    reject(
        "dangling_drop_ptr_does_not_erase_sibling_loan",
        "opaque Peek {
    r: &i32,
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
    impl drop {
        fn drop(self: &mut Self) {
            let _ = *self.r;
        }
    }
}
struct Both {
    v: Vec[&i32],
    p: Peek,
}
pub fn main() -> i32 {
    let d: i32 = 1;
    let mut b = Both { v: Vec[&i32]::new(), p: Peek::new(&d) };
    let short: i32 = 2;
    b.p = Peek::new(&short);
    return 0;
}",
        "goes out of scope while still borrowed",
    );

    // 8. `Channel[T]` borrow tracking across `send`, `try_send`, `recv`, and `@select`:
    reject(
        "channel_send_borrow_outlives_referent",
        "pub fn main() -> i32 {
    let ch = Channel[&i32]::new();
    let d: i32 = 0;
    let mut r: &i32 = &d;
    if true {
        let short: i32 = 42;
        ch.send(&short);
        r = ch.recv();
    }
    return *r;
}",
        "goes out of scope while still borrowed",
    );
    reject(
        "channel_select_send_recv_borrow_outlives_referent",
        "pub fn main() -> i32 {
    let ch = Channel[&i32]::new();
    let d: i32 = 0;
    let mut r: &i32 = &d;
    if true {
        let short: i32 = 42;
        let _ = @select {
            ch.send(&short) => 1,
        };
        r = @select {
            v = ch.recv() => v,
        };
    }
    return *r;
}",
        "goes out of scope while still borrowed",
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
    pub fn classify(self: &Self) -> i32 {
        return match *self {
            Self { code: 0, tag } => tag,
            { code: 1..=9, tag: 100 } => 50,
            { code, .. } => code,
        };
    }
}

opaque Tracked {
    v: i32,
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn val(self: &Self) -> i32 { return self.v; }
    impl drop {
        fn drop(self: &mut Self) {
            unsafe { DROPS += self.v; }
        }
    }
}

opaque(linear) Ticket {
    v: i32,
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn consume(move self) -> i32 { return self.v; }
}

union Event {
    Quit,
    Move: Point,
    Pair: tuple { i32, i32 },
    Bytes: [u8; 3],
}

error NetErr {
    Disconnected,
    Code: Point,
}

alias SmallScore = u8 in 0..=10;

const CONST_MATCH_VAL: i32 = match Point { x: 2, y: 7 } {
    Point { x: 0, y } => y,
    { x: 1 | 2, y } => y + 3,
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
        { x: 0, y } => y,
        .Some({ x, y }) => x + y,
    };
    // Exhaustive `?bool` without `_`
    let b = match ob {
        .None => 1,
        true => 2,
        false => 3,
    };
    // Exhaustive `NetErr!Point` without top-level `_`
    let c = match res {
        .Ok({ x: 0, y }) => y,
        .Ok({ x, y }) => x - y,
        .Err(.Disconnected) => -1,
        .Err(.Code({ x, y })) => x * y,
    };
    return a + b + c;
}

fn match_composites(p: Point, hdr: PackedHdr, tup: tuple { i32, i32, i32 }, flags: tuple { bool, bool }) -> i32 {
    let p_val = match p {
        Point { x: 0, y: 0 } => 0,
        Point { x, y: 0 } | Point { x: 0, y: x } => x,
        { x, y } => x + y,
    };
    let h_val = match hdr {
        PackedHdr { ver: 1, kind: 2, len } => len as i32,
        PackedHdr { ver, .. } => ver as i32,
    };
    let t_val = match tup {
        { 0, .., last } => last,
        (first, 10, last) => first + last,
        { a, b, c } => a + b + c,
    };
    // Multi-arm exhaustive tuple of bools without `_`
    let f_val = match flags {
        (true, true) => 4,
        (true, false) => 3,
        (false, _) => 1,
    };
    return p_val + h_val + t_val + f_val;
}

fn match_arrays_and_slices(arr: [i32; 4], sl: &[i32]) -> i32 {
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
        .Move({ x: 0, y }) => y,
        .Move({ x, y }) => x + y,
        .Pair((a, b)) => a * b,
        .Bytes([b'O', b'K', code]) => code as i32,
        .Bytes([head, ..]) => head as i32,
    };
    // Failed branches must not move affine or linear fields before the matching arm is chosen:
    let pair = { Tracked::new(5), 2 };
    let tr_val = match pair {
        { _t, 1 } => 100,
        { t, 2 } => t.val(),
        { _t, _ } => 0,
    };
    let lin_struct = { a: Ticket::new(4), b: 9 as i32 };
    let lin_val = match lin_struct {
        { a: t, b: 0 } => t.consume(),
        { a: t, b: n } => t.consume() + n,
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
    if match_composites(Point { x: 0, y: 8 }, hdr, { 3, 10, 4 }, { true, false }) != (8 + 11 + 7 + 3) {
        return 5;
    }
    let xs: [i32; 3] = { 4, 20, 6 };
    if match_arrays_and_slices({ 7, 1, 2, 99 }, &xs) != (7 + 10) {
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
    let ev_res = match_events_and_ownership(.Bytes({ b'O', b'K', 7 }));
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
    let xs: &[i32] = &[1, 2];
    return match xs {
        [a, ..] => a,
    };
}",
            "Non-exhaustive `match` on slice '&[i32]' requires a wildcard `_` or rest `..` arm",
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
    let p = { 1, 2 };
    return match p {
        { x, 0 } | { 0, y } => 1,
        _ => 0,
    };
}",
            "All alternatives of an `|` pattern must bind the same variables",
        ),
        (
            "duplicate_binding_in_pattern",
            "pub fn main() -> i32 {
    let p = { 1, 2 };
    return match p {
        { x, x } => x,
    };
}",
            "Identifier 'x' is bound more than once in the same pattern",
        ),
        (
            "multiple_rest_in_seq_pattern",
            "pub fn main() -> i32 {
    let xs: &[i32] = &[1, 2, 3];
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
fn test_opaque_affine_vs_bare_opaque_ownership() {
    // 1. `opaque(affine)` strictly asserts 0..1 uses (never linear):
    //    - holding a linear field inline, behind `*own T`, in `uninit T`, or via `owns T` is a compile error.
    reject(
        "opaque_affine_inline_linear_field",
        &with_tx(
            "pub opaque(affine) Bad {
    tx: Tx,
}
pub fn main() -> i32 { return 0; }",
        ),
        "Field 'tx' of 'opaque(affine) Bad' holds a linear value; 'opaque(affine)' types must be droppable without consumption (use 'opaque' or 'opaque(linear)')",
    );
    reject(
        "opaque_affine_generic_own_ptr_linear",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque(affine) {
        ptr: *own T,
    };
}
pub fn main() -> i32 {
    let _p: ?*mut Holder[Tx] = null;
    return 0;
}",
        ),
        "Field 'ptr' of 'opaque(affine) Holder' holds a linear value; 'opaque(affine)' types must be droppable without consumption (use 'opaque' or 'opaque(linear)')",
    );
    reject(
        "opaque_affine_owns_clause_linear",
        &with_tx(
            "fn Handle[T] -> type {
    return opaque(affine, owns T) {
        raw: *mut u8,
    };
}
pub fn main() -> i32 {
    let _p: ?*mut Handle[Tx] = null;
    return 0;
}",
        ),
        "'owns T' on 'opaque(affine) Handle' has linear type 'Tx'; 'opaque(affine)' types must be droppable without consumption (use 'opaque' or 'opaque(linear)')",
    );

    // 2. Bare `opaque` is affine by default (can be dropped for non-linear `T`) and upgrades to linear when holding `Tx`.
    accept(
        "opaque_affine_non_linear_ok",
        "fn Holder[T] -> type {
    return opaque(affine) {
        val: T,
        pub fn new(v: T) -> Self { return Self { val: move v }; }
    };
}
pub fn main() -> i32 {
    let _h = Holder[i32]::new(42);
    return 0;
}",
    );
    reject(
        "bare_opaque_upgrades_to_linear",
        &with_tx(
            "fn Holder[T] -> type {
    return opaque {
        val: T,
        pub fn new(v: T) -> Self { return Self { val: move v }; }
    };
}
pub fn main() -> i32 {
    let _h = Holder[Tx]::new(Tx::new(1));
    return 0;
}",
        ),
        "Linear value '_h' of type 'Holder[Tx]' must be explicitly consumed",
    );

    // 3. `packed opaque` is `copy` by default, whereas `packed opaque(affine)` stays strictly `affine` (move-only).
    accept(
        "packed_opaque_default_is_copy",
        "pub packed opaque Reg {
    bits: u32,
    pub fn new(b: u32) -> Self { return Self { bits: b }; }
    pub fn get(self: Self) -> u32 { return self.bits; }
}
pub fn main() -> i32 {
    let r = Reg::new(7);
    let a = r.get();
    let b = r.get();
    return (a + b - 14) as i32;
}",
    );
    reject(
        "packed_opaque_affine_is_move_only",
        "pub packed opaque(affine) Reg {
    bits: u32,
    pub fn new(b: u32) -> Self { return Self { bits: b }; }
    pub fn consume(move self) -> u32 { return self.bits; }
}
pub fn main() -> i32 {
    let r = Reg::new(7);
    let _a = r.consume();
    let _b = r.consume();
    return 0;
}",
        "Use of moved or uninitialized value 'r'",
    );
}

/// Runs `src` on the VM and natively, and checks both give `value` with nothing leaked.
fn assert_runs(name: &str, src: &str, value: i128) {
    let run = super::run_vm(name, src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    assert_eq!((run.value, run.leaks), (value, 0), "[{name}]");
    assert_eq!(run_lli(name, src), Some(value as i32), "[{name}]");
}

fn assert_rejected(name: &str, src: &str, what: &str) {
    let err = Compiler::compile_source(src).expect_err(name);
    assert!(err.contains(what), "[{name}] {err}");
}

const TX: &str = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(move self) -> i32 { return self.id; }
}
";

#[test]
fn test_deferred_initialization() {
    for (name, body, value) in [
        ("whole", "let mut x: i32; x = 4; return x;", 4),
        ("fields", "let mut r: tuple { i32, tuple { i32, i32 } }; r.0 = 1; r.1.0 = 2; r.1.1 = 3; let c = r; return c.0 + c.1.1;", 4),
        ("branches", "let mut x: i32; if false { x = 1; } else { x = 2; } return x;", 2),
        ("loop", "let mut t: i32 = 0; for i in 0..3 { let mut x: i32; x = i; t += x; } return t;", 3),
        // Whatever is initialized at a scope exit is dropped, once.
        ("early_return", "let mut r: tuple { Box[i32], Box[i32] }; r.0 = Box[i32]::new(1); if true { return 7; } r.1 = Box[i32]::new(2); return 0;", 7),
        ("overwrite", "let mut r: tuple { Box[i32], i32 }; r.0 = Box[i32]::new(1); r.0 = Box[i32]::new(2); r.1 = 3; let c = r; return c.1;", 3),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, body) in [
        ("read", "let mut x: i32; return x;"),
        ("partial", "let mut r: tuple { i32, i32 }; r.0 = 1; let c = r; return c.0;"),
        ("borrow", "let mut x: i32; let p = &x; return 0;"),
        ("borrow_mut", "let mut x: i32; let p = &mut x; *p = 1; return x;"),
        ("one_branch", "let mut x: i32; if true { x = 1; } return x;"),
        ("closure", "let mut x: i32; let f = fn() -> i32 { return x; }; return f();"),
        ("loop_body", "let mut x: i32; for i in 0..3 { x = i; } return x;"),
    ] {
        let src = format!("pub fn main() -> i32 {{ {body} }}");
        assert_rejected(name, &src, "moved or uninitialized");
    }
    for (name, body) in [
        ("lost", "let mut r: tuple { Tx, Tx }; r.0 = Tx::new(1); r.1 = Tx::new(2); return r.0.commit();"),
        ("partial", "let mut r: tuple { Tx, Tx }; r.0 = Tx::new(1); return 0;"),
        ("overwrite", "let mut r: tuple { Tx, Tx }; r.0 = Tx::new(1); r.0 = Tx::new(2); r.1 = Tx::new(2); return r.0.commit() + r.1.commit();"),
    ] {
        let src = format!("{TX}pub fn main() -> i32 {{ {body} }}");
        assert_rejected(name, &src, "must be explicitly consumed");
    }
    assert_rejected("immutable", "pub fn main() -> i32 { let x: i32; return 0; }", "let mut x: T;");
    assert_rejected("untyped", "pub fn main() -> i32 { let mut x; return 0; }", "let mut x: T;");
}

#[test]
fn test_tuple_concat_and_split() {
    assert_runs(
        "concat",
        "pub fn main() -> i32 {
    let a: tuple { i32, i32 } = { 1, 2 };
    let b: tuple { i32 } = { 3 };
    let c = tuple_concat(a, b);
    return c.0 * 100 + c.1 * 10 + c.2;
}",
        123,
    );
    let linear = "let a: tuple { Tx, i32 } = { Tx::new(1), 2 };
    let b: tuple { Tx } = { Tx::new(3) };
    let c = tuple_concat(a, b);";
    assert_runs(
        "concat_linear",
        &format!("{TX}pub fn main() -> i32 {{ {linear} return c.0.commit() + c.1 + c.2.commit(); }}"),
        6,
    );
    assert_rejected(
        "concat_linear_lost",
        &format!("{TX}pub fn main() -> i32 {{ {linear} return c.0.commit() + c.1; }}"),
        "must be explicitly consumed",
    );
    assert_runs(
        "split",
        &format!(
            "{TX}pub fn main() -> i32 {{
    let t: tuple {{ i32, Tx, i32 }} = {{ 1, Tx::new(2), 3 }};
    let parts = tuple_split[1, tuple {{ i32, Tx, i32 }}](t);
    return parts.0.0 * 100 + parts.1.0.commit() * 10 + parts.1.1;
}}"
        ),
        123,
    );
}

#[test]
fn test_field_paths() {
    let types = "pub struct In { a: i32, b: tuple { i32, i32 } }
pub struct Out { x: i32, i: In }
";
    let v = "let mut o: Out = Out { x: 1, i: In { a: 2, b: { 3, 4 } } };";
    for (name, body, value) in [
        ("read", "return @field(o, &[\"i\", \"b\", \"1\"]);", 4),
        ("bound", "comptime let p = &[\"i\", \"a\"]; @field(o, p) = 9; return o.i.a;", 9),
        ("indices", "let t: tuple { i32, tuple { i32, i32 } } = { 1, { 2, 3 } }; return @field(t, &[1, 1]);", 3),
        ("disjoint", "let a = &mut @field(o, &[\"i\", \"a\"]); let b = &mut @field(o, &[\"i\", \"b\", \"0\"]); *a = 5; *b = 6; return o.i.a + o.i.b.0;", 11),
        ("leaves", "let mut t: i32 = 0; comptime for p in @leaves(Out) { t = t * 2 + @field(o, p); } return t;", 26),
        ("leaves_write", "comptime for p in @leaves(Out) { @field(o, p) += 1; } return o.x + o.i.b.1;", 7),
        ("leaves_count", "comptime let l = @leaves(Out); return l.len as i32;", 4),
        ("tuple_names", "let t: tuple { i32, i32 } = { 4, 5 }; let mut s: i32 = 0; comptime for f in @fields(tuple { i32, i32 }) { s += @field(t, f.name); } return s;", 9),
        ("field_at", "return @size_of(FieldAt[Out, &[\"i\", \"b\"]]) as i32;", 8),
    ] {
        assert_runs(name, &format!("{types}pub fn main() -> i32 {{ {v} {body} }}"), value);
    }
    // Leaves stop at encapsulated types, and each linear leaf is consumed exactly once.
    assert_runs(
        "leaves_linear",
        &format!(
            "{TX}pub fn main() -> i32 {{
    let t: tuple {{ Tx, tuple {{ Tx, Tx }} }} = {{ Tx::new(1), {{ Tx::new(2), Tx::new(3) }} }};
    let mut s: i32 = 0;
    comptime for p in @leaves(tuple {{ Tx, tuple {{ Tx, Tx }} }}) {{ s += (move @field(t, p)).commit(); }}
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
    let two = "fn two[T, P: &[&str], Q: &[&str]](t: &mut T) -> tuple { &mut FieldAt[T, P], &mut FieldAt[T, Q] } borrows(t) {
    return { &mut @field(t, P), &mut @field(t, Q) };
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
fn test_type_function_returning_its_argument_labels() {
    // The instance label of `S` is `Id[S]`, whose argument is `S` again.
    assert_rejected(
        "identity",
        "pub struct S { a: i32 }
fn Id[T] -> type { return T; }
fn bad[T](x: &mut T) { let a = &mut *x; let b = &mut *x; *a = *b; }
pub fn main() -> i32 { let mut s = S { a: 1 }; bad[Id[S]](&mut s); return 0; }",
        "Borrow check error",
    );
}

#[test]
fn test_compile_error() {
    // Fires on the path a type function takes, and only there.
    let checked = "fn Checked[N: usize] -> type {
    if N > 2 {
        return @compile_error(\"Checked: \", N, \" is too big for \", i32);
    }
    return [i32; N];
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
    let generic = "fn only_ints[T](x: T) -> i32 {
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
            "pub fn main() -> i32 {{ let t: tuple {{ i32, i32 }} = {{ 1, 2 }}; let p = tuple_split[{n}, tuple {{ i32, i32 }}](t); return 0; }}"
        )
    };
    assert_rejected("split_none", &split(0), "TupleTake: cannot take 0 elements of tuple { i32, i32 }");
    assert_rejected("split_all", &split(2), "TupleSkip: skipping 2 elements of tuple { i32, i32 } leaves none");
    assert_rejected("split_past", &split(3), "TupleTake: cannot take 3 elements of tuple { i32, i32 }");
    assert_rejected(
        "field_at",
        "pub struct S { a: i32 }\npub fn main() -> i32 { return @size_of(FieldAt[S, &[\"zz\"]]) as i32; }",
        "FieldAt: S has no field zz",
    );
}

#[test]
fn test_type_labels_name_the_real_type() {
    // A type function returning an existing type does not rename it in diagnostics, and a tuple
    // keeps its structural name.
    let err = Compiler::compile_source(
        "pub struct S { a: i32 }
fn Id[T] -> type { return T; }
fn Pair[T] -> type { return tuple { T, T }; }
fn bad[T, U](x: &mut T, y: U) { let a = &mut *x; let b = &mut *x; *a = *b; }
pub fn main() -> i32 { let mut s = S { a: 1 }; let p: Pair[i32] = { 1, 2 }; bad[Id[S], Pair[i32]](&mut s, p); return 0; }",
    )
    .expect_err("double mutable borrow");
    assert!(err.contains("T = S, U = tuple { i32, i32 }"), "{err}");
    // A nominal instance keeps its instantiation.
    let err = Compiler::compile_source(
        "fn bad[T](x: &mut T) { let a = &mut *x; let b = &mut *x; *a = *b; }
pub fn main() -> i32 { let mut v = Box[i32]::new(1); bad[Box[i32]](&mut v); return 0; }",
    )
    .expect_err("double mutable borrow");
    assert!(err.contains("T = Box[i32]"), "{err}");
}

#[test]
fn test_conditional_move_into_a_call_clears_its_drop_flag() {
    let make = "fn make(n: i32) -> Box[i32] { return Box[i32]::new(n); }\nfn take(b: Box[i32]) -> i32 { return b.into_inner(); }\n";
    for (name, start, body, value) in [
        // Moved into a call on the path taken: dropping it again would be a double free.
        ("field_taken", 0, "let b: tuple { Box[i32], Box[i32] } = { make(6), make(7) }; if s < 21 { s = s + b.0.into_inner(); }", 6),
        ("field_not_taken", 30, "let b: tuple { Box[i32], Box[i32] } = { make(6), make(7) }; if s < 21 { s = s + b.0.into_inner(); }", 30),
        ("whole_taken", 0, "let b = make(6); if s < 21 { s = s + take(b); }", 6),
        ("whole_not_taken", 30, "let b = make(6); if s < 21 { s = s + take(b); }", 30),
        ("deferred_field", 0, "let mut b: tuple { Box[i32], Box[i32] }; b.0 = make(6); if s < 21 { s = s + b.0.into_inner(); }", 6),
        // Filled by a call on one path only.
        ("filled_taken", 0, "let mut b: Box[i32]; if s < 21 { b = make(1); }", 0),
        ("filled_not_taken", 30, "let mut b: Box[i32]; if s < 21 { b = make(1); }", 30),
        ("field_filled_taken", 0, "let mut b: tuple { Box[i32], i32 }; b.1 = 1; if s < 21 { b.0 = make(1); }", 0),
        ("field_filled_not_taken", 30, "let mut b: tuple { Box[i32], i32 }; b.1 = 1; if s < 21 { b.0 = make(1); }", 30),
        // Moved and refilled, on either path.
        ("refilled", 0, "let mut b = make(6); if s < 21 { s = s + take(b); b = make(2); } if s < 3 { s = s + take(b); }", 6),
    ] {
        let src = format!("{make}fn body(start: i32) -> i32 {{ let mut s: i32 = start; {body} return s; }}\npub fn main() -> i32 {{ return body({start}); }}");
        assert_runs(name, &src, value);
    }
}

#[test]
fn test_borrow_errors_name_source_places() {
    let types = "pub struct P { a: i32, b: i32 }\n";
    for (body, message) in [
        ("let mut x: i32 = 1; let a = &mut x; let b = &x; *a = 2; return *b;", "cannot borrow 'x' as immutable because 'x' is already borrowed as mutable"),
        ("let mut x: i32 = 1; let a = &x; x = 2; return *a;", "cannot mutate or move 'x' because it is currently borrowed"),
        ("let mut x: i32 = 1; let a = &mut x; let y = x; *a = 2; return y;", "cannot read 'x' because it is mutably borrowed"),
        ("let mut p = P { a: 1, b: 2 }; let a = &mut p.a; let b = &mut p.a; *a = 1; *b = 2; return 0;", "cannot borrow 'p.a' as mutable because 'p.a' is already borrowed as mutable"),
        ("let mut p = P { a: 1, b: 2 }; let a = &p; p.b = 3; return a.a;", "cannot mutate or move 'p.b' because it is currently borrowed via 'p'"),
        ("let mut t: tuple { i32, i32 } = { 1, 2 }; let a = &mut t.0; let b = &mut t; *a = 1; b.1 = 2; return 0;", "cannot borrow 't' as mutable because 't.0' is already borrowed as mutable"),
        ("let mut n: i32 = 1; let r = &mut n; let q = &mut *r; *r = 2; *q = 3; return 0;", "cannot mutate or move '*r' because it is currently borrowed"),
        ("let mut v = Vec[i32]::new(); v.push(1); let r = v.get(0) orelse unreachable; v.push(2); return *r;", "cannot borrow 'v' as mutable because 'v' is already borrowed as immutable"),
        ("let x: i32 = 0; let mut r: &i32 = &x; if true { let y: i32 = 1; r = &y; } return *r;", "'y' goes out of scope while still borrowed"),
    ] {
        let src = format!("{types}pub fn main() -> i32 {{ {body} }}");
        let err = Compiler::compile_source(&src).expect_err(body);
        assert!(err.contains(&format!("{message} (line 2)")), "[{body}] {err}");
    }
}

#[test]
fn test_borrow_and_move_errors_report_source_lines() {
    let tx = "pub opaque(linear) Tx {\n    id: i32,\n    pub fn new(i: i32) -> Self { return Self { id: i }; }\n    pub fn commit(move self) -> i32 { return self.id; }\n}\n";
    for (name, line, src) in [
        // After a call, whose continuation is a new IR block with no marker of its own.
        ("after_call", 5, "fn mk() -> i32 { return 1; }\npub fn main() -> i32 {\n    let mut x: i32 = mk();\n    let a = &x;\n    x = mk();\n    return *a;\n}".to_string()),
        ("in_branch", 6, "pub fn main() -> i32 {\n    let mut x: i32 = 1;\n    let a = &x;\n    let c = true;\n    if c {\n        x = 2;\n    }\n    return *a;\n}".to_string()),
        ("in_loop", 5, "pub fn main() -> i32 {\n    let mut v = Vec[i32]::new();\n    v.push(1);\n    for e in v.iter() {\n        v.push(*e);\n    }\n    return 0;\n}".to_string()),
        ("use_after_move", 4, "pub fn main() -> i32 {\n    let b = Box[i32]::new(1);\n    let c = b;\n    let d = b;\n    return c.into_inner() + d.into_inner();\n}".to_string()),
        ("after_a_branch", 6, "pub fn main() -> i32 {\n    let b = Box[i32]::new(1);\n    if true {\n        let c = b;\n    }\n    return b.into_inner();\n}".to_string()),
        // A statement over several lines reports its first.
        ("multi_line", 4, "pub fn main() -> i32 {\n    let mut x: i32 = 1;\n    let a = &mut x;\n    let y =\n        x;\n    *a = 2;\n    return y;\n}".to_string()),
        // A scope end reports the closing brace.
        ("scope_end", 7, "pub fn main() -> i32 {\n    let x: i32 = 0;\n    let mut r: &i32 = &x;\n    if true {\n        let y: i32 = 1;\n        r = &y;\n    }\n    return *r;\n}".to_string()),
        ("linear_lost", 8, format!("{tx}pub fn main() -> i32 {{\n    let t = Tx::new(1);\n    return 0;\n}}")),
    ] {
        let err = Compiler::compile_source(&src).expect_err(name);
        assert!(err.contains(&format!("(line {line})")), "[{name}] {err}");
    }
}

#[test]
fn test_assigning_through_a_reference_drops_the_old_value() {
    let setup = "fn set(r: &mut Box[i32], v: i32) { *r = Box[i32]::new(v); }\n";
    for (name, body, value) in [
        ("deref", "let mut b = Box[i32]::new(1); let r = &mut b; *r = Box[i32]::new(2); return b.into_inner();", 2),
        ("field", "let mut t: tuple { Box[i32], i32 } = { Box[i32]::new(1), 2 }; let r = &mut t; r.0 = Box[i32]::new(3); let c = t; return c.1 + c.0.into_inner();", 5),
        ("parameter", "let mut b = Box[i32]::new(1); set(&mut b, 4); set(&mut b, 5); return b.into_inner();", 5),
        ("get_mut", "let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); if let x = v.get_mut(0) { *x = Box[i32]::new(6); } return *(v.get(0) orelse unreachable).get();", 6),
        ("slice", "let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); if true { let sl = v.as_mut_slice(); sl[0] = Box[i32]::new(7); } return *(v.get(0) orelse unreachable).get();", 7),
        ("from_old", "let mut b = Box[i32]::new(1); let r = &mut b; let n = *r.get() + 7; *r = Box[i32]::new(n); return b.into_inner();", 8),
        ("string", "let mut a = String::from(\"abc\"); let r = &mut a; *r = String::from(\"z\"); return a.len() as i32;", 1),
    ] {
        assert_runs(name, &format!("{setup}pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_mutable_receiver_borrow_starts_after_the_arguments() {
    let types = "pub struct S { n: i32, v: Vec[i32] }
pub opaque C {
    n: i32,
    pub fn new() -> Self { return Self { n: 1 }; }
    pub fn get(self: &Self) -> i32 { return self.n; }
    pub fn add(self: &mut Self, x: i32) { self.n = self.n + x; }
    pub fn add_ref(self: &mut Self, x: &i32) { self.n = self.n + *x; }
    pub fn twice(self: &mut Self) { self.add(self.get()); }
}
pub opaque K {
    n: i32,
    pub fn new() -> Self { return Self { n: 1 }; }
    pub fn add_ref(self: &mut Self, x: &i32) { self.n = self.n + *x; }
    pub fn bad(self: &mut Self) { self.add_ref(&self.n); }
}
fn len_of(v: &Vec[i32]) -> i32 { return v.len() as i32; }
";
    let good = types.replace("    pub fn bad(self: &mut Self) { self.add_ref(&self.n); }\n", "");
    for (name, body, value) in [
        ("push_len", "let mut v = Vec[i32]::new(); v.push(v.len() as i32); v.push(v.len() as i32); return *(v.get(1) orelse unreachable);", 1),
        ("through_function", "let mut v = Vec[i32]::new(); v.push(7); v.push(len_of(&v)); return *(v.get(1) orelse unreachable);", 1),
        ("copied_element", "let mut v = Vec[i32]::new(); v.push(3); v.push(*(v.get(0) orelse unreachable) + 1); return *(v.get(1) orelse unreachable);", 4),
        ("field", "let mut s = S { n: 2, v: Vec[i32]::new() }; s.v.push(s.v.len() as i32 + s.n); return *(s.v.get(0) orelse unreachable);", 2),
        ("through_self", "let mut c = C::new(); c.twice(); c.twice(); return c.get();", 4),
        ("through_reference", "let mut c = C::new(); let r = &mut c; r.add(r.get()); return c.get();", 2),
        ("nested", "let mut c = C::new(); c.add(c.get() + c.get()); return c.get();", 3),
        ("map", "let mut m = HashMap[i32, i32]::new(); let _a = m.insert(m.len() as i32, 5); let _b = m.insert(m.len() as i32, 6); return *(m.get(1) orelse unreachable);", 6),
    ] {
        assert_runs(name, &format!("{good}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // The borrow still conflicts with anything an argument keeps, and with a move.
    assert_rejected(
        "kept_reference",
        &format!("{types}pub fn main() -> i32 {{ return 0; }}"),
        "already borrowed",
    );
    assert_rejected(
        "moved_by_argument",
        &format!(
            "{good}fn wrap(v: Vec[Box[i32]]) -> Box[i32] {{ return Box[i32]::new(v.len() as i32); }}
pub fn main() -> i32 {{ let mut v = Vec[Box[i32]]::new(); v.push(wrap(v)); return 0; }}"
        ),
        "moved or uninitialized",
    );
}

#[test]
fn test_small_language_fixes() {
    // Open-ended ranges, to the end or from the start.
    for (name, body, value) in [
        ("from", "let a: [i32; 4] = { 1, 2, 3, 4 }; let s: &[i32] = &a; let t = s[1..]; return t.len as i32 + t[0];", 5),
        ("to", "let a: [i32; 4] = { 1, 2, 3, 4 }; let s: &[i32] = &a; let t = s[..2]; return t.len as i32 * 10 + t[1];", 22),
        ("all", "let a: [i32; 4] = { 1, 2, 3, 4 }; let s: &[i32] = &a; let t = s[..]; return t.len as i32;", 4),
        ("str", "let s: &str = \"hello\"; return s[2..].len as i32;", 3),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "open_end_of_a_call",
        "fn mk(a: &[i32]) -> &[i32] { return a; }\npub fn main() -> i32 { let a: [i32; 2] = { 1, 2 }; let s: &[i32] = &a; let t = mk(s)[1..]; return 0; }",
        "write the end explicitly",
    );
    // A compile-time path can be sliced in place.
    assert_runs(
        "open_range_in_a_path",
        "pub struct S { a: tuple { i32, i32 } }
fn At[T, P: &[&str]] -> type {
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
        "pub trait Count { fn get(self: &Self) -> i32; fn add(self: &mut Self, x: i32); }
pub struct C { n: i32 }
impl Count for C {
    fn get(self: &Self) -> i32 { return self.n; }
    fn add(self: &mut Self, x: i32) { self.n = self.n + x; }
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
    impl drop { fn drop(self: &mut Self) { } }
    pub fn new() -> Self { let mut s: Self; s.n = 3; return s; }
}
pub fn main() -> i32 { let h = Hook::new(); return 0; }",
        "must be initialized whole",
    );
    // A broken contract names where its function starts.
    assert_rejected(
        "contract_line",
        "\n\nfn f(a: &i32, b: &i32) -> &i32 borrows(a) {\n    return b;\n}\npub fn main() -> i32 { return 0; }",
        "(function body at line 4)",
    );
}
