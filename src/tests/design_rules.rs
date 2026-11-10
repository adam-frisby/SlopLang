use crate::lower::Compiler;
use super::{run_lli, TRAP_EXIT, VmRun};

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
    if let u = c.send(Tx::new(1)) { let _c = u.commit(); }
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
            "fn Holder[T: ?linear] -> type {
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
            "fn Holder[T: ?linear] -> type {
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
            "fn Holder[T: ?linear] -> type {
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
            "fn Holder[T: ?linear] -> type {
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
            "fn Holder[T: ?linear] -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
    };
}
fn wrap[F: ?linear](f: F) -> Holder[F] { return Holder[F]::new(move f); }
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
            "fn Holder[T: ?linear] -> type {
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
    let owning = "fn Holder[T: ?linear] -> type {
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
            "fn write_raw[T: ?linear](p: *mut T, v: T) { unsafe { *p = move v; } }
fn Holder[T: ?linear] -> type {
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
        "fn Holder[T: ?linear] -> type {
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
        &with_tx("pub error E { Bad(Tx) }\npub fn main() -> i32 { return 0; }"),
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
            "pub fn tag[S: opaque + ?linear](self: &S) -> i32 { return 3; }
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
pub union Cell { Num(i32), Boxed(Box[i32]), Empty }
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
            "fn ignore[T: unchecked](x: T) -> i32 { return 0; }
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
            "pub union(u16) Message { Ping(u64) = 1, Auth(i32) = 16, Disconnect = 65535 }
pub error(i16) MyErr { Bad(i32) = 10, Worse = -5 }
pub union Shape { Circle(i32), Square(i32), Empty }
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
pub union MaybeRef { None, Some(&i32) }"
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
        "pub union(u8) M { A = 5, B(i32) = 5 }\npub fn main() -> i32 { return 0; }",
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
    let a: [i64; 4] = { 10, 20, 3, 4 };
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
    let t = { a, 2 };
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
        "no enclosing loop or block is labelled 'nope'",
    );
}

#[test]
fn test_generic_bodies_are_checked_against_their_bounds() {
    // A type parameter promises its bounds and nothing more. A generic is checked, whether or not
    // anything uses it, with an archetype for each type parameter: a type with exactly what the
    // bounds say. Duck typing is opt-in, as `[T: unchecked]`, and then checked only where used.
    let prelude = "trait Shape { fn area(self: &Self) -> i32; }
struct Square { side: i32, impl Shape { fn area(self: &Self) -> i32 { return self.side * self.side; } } }
";
    for (name, generic) in [
        ("plain", "fn twice[T](a: T) -> T { return a; }"),
        ("integer", "fn add[T: integer](a: T, b: T) -> T { return a + b; }"),
        ("copy", "fn dup[T: copy](a: T) -> tuple { T, T } { return { a, a }; }"),
        ("trait", "fn area_of[T: Shape](a: &T) -> i32 { return a.area(); }"),
        ("traits_and_copy", "fn both[T: Shape + copy](a: T) -> i32 { let b = a; return a.area() + b.area(); }"),
        ("default", "fn make[T: default]() -> T { return @default(T); }"),
        ("value", "fn sized[n: usize]() -> usize { return n * 2; }"),
        ("generic_type", "struct Wrap[T] { v: T, pub fn get(self: &Self) -> &T { return &self.v; } }"),
        ("generic_method_gated_on_the_type", "struct G[T] { v: T, pub fn with[U: copy](self: &Self, u: U) -> T where T: integer { let w = u; return self.v + self.v; } }"),
        ("where_gated", "struct W[T] { v: T, pub fn twice(self: &Self) -> T where T: integer { return self.v + self.v; } }"),
        ("generic_method", "struct S { x: i32, pub fn with[U: Shape](self: &Self, u: &U) -> i32 { return u.area() + self.x; } }"),
        ("generic_impl", "struct Box2[T] { v: T }\nimpl[T: Shape] Shape for Box2[T] { fn area(self: &Self) -> i32 { return self.v.area() * 2; } }"),
        ("duck_typed", "fn poke[T: unchecked](a: &T) -> i32 { return a.nonexistent(); }"),
    ] {
        let src = format!("{prelude}{generic}\npub fn main() -> i32 {{ return 0; }}");
        Compiler::compile_source(&src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    }
    for (name, generic, what) in [
        ("field", "fn bad_field[T](a: T) -> i32 { return a.nonexistent; }", "has no field 'nonexistent'"),
        ("method", "fn bad_method[T](a: &T) -> i32 { return a.area(); }", "has no method 'area'"),
        ("copy", "fn dup_any[T](a: T) -> tuple { T, T } { return { a, a }; }", "moved"),
        ("past_the_trait", "fn bad_shape[T: Shape](a: &T) -> i32 { return a.perimeter(); }", "has no method 'perimeter'"),
        ("operator", "fn add[T](a: T, b: T) -> T { return a + b; }", "T"),
        ("generic_type", "struct Bad[T] { v: T, pub fn get(self: &Self) -> i32 { return self.v.len(); } }", "has no method 'len'"),
        ("past_a_number", "fn bad_number[T: integer](a: T) -> i32 { return a.len(); }", "has no method 'len'"),
        // Members nothing checked until they were called: a method a `where` clause gates, a
        // generic method, an `impl` block (generic or not), and one inside a generic type.
        ("generic_method_gated_on_the_type", "struct G[T] { v: T, pub fn with[U](self: &Self, u: U) -> i32 where T: integer { return self.v.len(); } }", "Method 'G::with'"),
        ("where_gated", "struct W[T] { v: T, pub fn total(self: &Self) -> i32 where T: integer { return self.v.len(); } }", "Method 'W::total'"),
        ("generic_method", "struct S { x: i32, pub fn with[U](self: &Self, u: U) -> i32 { return u.area(); } }", "Method 'S::with'"),
        ("generic_impl", "struct Box2[T] { v: T }\nimpl[T] Shape for Box2[T] { fn area(self: &Self) -> i32 { return self.v.area(); } }", "has no method 'area'"),
        ("plain_impl", "struct Q { x: i32 }\nimpl Shape for Q { fn area(self: &Self) -> i32 { return self.y; } }", "has no field 'y'"),
        // An impl for a type declared elsewhere is checked as a block of its own.
        ("impl_for_a_builtin", "impl Shape for i64 { fn area(self: &Self) -> i32 { return self.y; } }", "'impl Shape for i64' does not compile"),
        // A borrow error in a method no one calls: of a generic type, a plain one, and an impl.
        ("moved_twice", "struct Mv[T] { s: String, v: T, fn take(self: Self) -> i32 { let a = move self.s; let b = move self.s; return 0; } }", "moved"),
        ("moved_twice_plain", "struct Mp { s: String, fn take(self: Self) -> i32 { let a = move self.s; let b = move self.s; return 0; } }", "moved"),
        ("moved_twice_in_impl", "impl Shape for u16 { fn area(self: &Self) -> i32 { let s = String::from(\"a\"); let a = move s; let b = move s; return 0; } }", "moved"),
        ("impl_in_a_generic_type", "struct In[T] { v: T, impl Shape { fn area(self: &Self) -> i32 { return self.v.area(); } } }", "'impl Shape' for 'In'"),
        // Each overload is checked as written, not the one its name would pick for an archetype.
        ("overload", "fn pick[T: integer](x: T) -> i32 { return x.len(); }\nfn pick[T: signed](x: T) -> i32 { return 1; }", "has no method 'len'"),
        ("not_send", "fn bad_send[T](x: T) -> i32 { let h = spawn(move fn() -> i32 { let y = move x; return 1; }); return h.join(); }", "send"),
    ] {
        let src = format!("{prelude}{generic}\npub fn main() -> i32 {{ return 0; }}");
        let err = Compiler::compile_source(&src).expect_err(name);
        assert!(err.contains(what), "[{name}] {err}");
    }
    // Used with a type that would do, it is still checked against its bounds.
    let used = format!("{prelude}fn bad_method[T](a: &T) -> i32 {{ return a.area(); }}\npub fn main() -> i32 {{ let s = Square {{ side: 2 }}; return bad_method(&s); }}");
    let err = Compiler::compile_source(&used).expect_err("used");
    assert!(err.contains("[T: unchecked]"), "{err}");
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
union Msg { Quit, Move(struct { dx: i32, dy: i32 }) }
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
    let same: struct { u: i32, w: i32 } = anon;
    let m: Msg = .Move({ dx: 1, dy: 1 });
    let t: T() = { v: 1 };
    let mut total = sum(a) + make(3).y + sum({ x: 1, y: 1 }) + sum(ORIGIN);
    total += same.u + same.w;
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
error AppErr { IoErr, BadInput(i32) }

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
        _ = ch.send(&short);
        r = (ch.recv() catch |e| unreachable);
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
    Move(Point),
    Pair(tuple { i32, i32 }),
    Bytes([u8; 3]),
}

error NetErr {
    Disconnected,
    Code(Point),
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
            "fn Holder[T: ?linear] -> type {
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
            "fn Handle[T: ?linear] -> type {
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
            "fn Holder[T: ?linear] -> type {
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
    let (run, native) = super::run_both(name, src);
    let run = run.unwrap_or_else(|e| panic!("[{name}] {e}"));
    assert_eq!((run.value, run.leaks), (value, 0), "[{name}]");
    assert_eq!(native, Some(value as i32), "[{name}]");
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
        assert!(err.contains(message) && err.contains(" (line 2, column "), "[{body}] {err}");
        // And where the borrow in the way was taken.
        assert!(err.contains("(borrowed on line 2, column "), "[{body}] {err}");
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
        assert!(err.contains(&format!("(line {line}, column ")), "[{name}] {err}");
    }
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
        ("move", "pub fn main() -> i32 {\n    let s = String::from(\"a\");\n    let t = move s;\n      let u = move s;\n    return 0;\n}", "'s' in root::main (fn0) (line 4, column 7)"),
        // Moves and borrows found in a call are placed at the call.
        ("move_into_a_call", "fn take(s: String) -> i32 { return s.len() as i32; }\npub fn main() -> i32 {\n    let s = String::from(\"a\");\n    let n = take(s) + take(s);\n    return n;\n}", ") (line 4, column 23)"),
        ("borrow_in_a_call", "fn grow(v: &mut Vec[i32], x: i32) -> i32 { return x; }\npub fn main() -> i32 {\n    let mut v = Vec[i32]::new();\n    let r = &v;\n    let k = 1 + grow(&mut v, 0) + v.len() as i32;\n    return r.len() as i32 + k;\n}", "cannot borrow 'v' as mutable because 'v' is already borrowed as immutable (borrowed on line 4, column 5) (line 5, column 17)"),
        ("parse", "pub fn main() -> i32 {\n    let x = 1 +;\n}", "Expected expression, found Semi (line 2, column 16)"),
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
        "(function body at line 4, column 5)",
    );
}

#[test]
fn test_static_trait_methods() {
    let shapes = "pub trait Shape {
    fn sides() -> i32;
    fn make(n: i32) -> Self;
    fn area(self: &Self) -> i32;
}
pub struct Square { w: i32 }
impl Shape for Square {
    fn sides() -> i32 { return 4; }
    fn make(n: i32) -> Self { return Square { w: n }; }
    fn area(self: &Self) -> i32 { return self.w * self.w; }
}
pub struct Tri { b: i32 }
impl Shape for Tri {
    fn sides() -> i32 { return 3; }
    fn make(n: i32) -> Self { return Tri { b: n }; }
    fn area(self: &Self) -> i32 { return self.b; }
}
fn describe[T: Shape](n: i32) -> i32 { let s = T::make(n); return T::sides() * 10 + s.area(); }
";
    for (name, body, value) in [
        ("on_a_type", "return Square::sides() + Tri::sides();", 7),
        ("self_return", "let s = Square::make(3); return s.area();", 9),
        ("generic", "return describe[Square](5);", 65),
        ("each_type", "return describe[Tri](5) - describe[Square](1) + 10;", 4),
    ] {
        assert_runs(name, &format!("{shapes}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "not_implemented",
        &format!("{shapes}pub struct Other {{ x: i32 }}\npub fn main() -> i32 {{ return Other::sides(); }}"),
        "has no method 'sides'",
    );
    assert_rejected(
        "bound_not_met",
        &format!("{shapes}pub struct Other {{ x: i32 }}\npub fn main() -> i32 {{ return describe[Other](1); }}"),
        "Shape",
    );
    assert_rejected(
        "not_object_safe",
        &format!("{shapes}pub fn main() -> i32 {{ let s = Square {{ w: 1 }}; let o: &Shape = &s; return 0; }}"),
        "not object-safe",
    );
    assert_rejected(
        "ambiguous",
        "pub trait A { fn id() -> i32; }
pub trait B { fn id() -> i32; }
pub struct S { x: i32 }
impl A for S { fn id() -> i32 { return 1; } }
impl B for S { fn id() -> i32 { return 2; } }
pub fn main() -> i32 { return S::id(); }",
        "ambiguous",
    );
    // An inherent method wins, as it does for receivers.
    assert_runs(
        "inherent_first",
        "pub trait A { fn id() -> i32; }
pub opaque S { x: i32, pub fn id() -> i32 { return 1; } }
impl A for S { fn id() -> i32 { return 2; } }
pub fn main() -> i32 { return S::id(); }",
        1,
    );
}

#[test]
fn test_thread_local_statics() {
    let decls = "thread_local static mut N: i32 = 5;
static mut SHARED: i32 = 0;
fn bump() -> i32 { unsafe { N = N + 1; return N; } }
pub struct P { a: i32, b: i32 }
thread_local static mut Q: P = P { a: 1, b: 2 };
";
    for (name, body, value) in [
        ("one_thread", "let a = bump(); let b = bump(); return a * 10 + b - 50;", 17),
        // Every thread starts from the initial value, and writes stay in its copy.
        ("threads_are_isolated", "let a = bump(); let t = spawn_scoped(fn() -> i32 { return bump() + bump(); }); let c = t.join(); return a * 10 + c - 13 + bump() - 7;", 60),
        ("field", "unsafe { Q.b = 7; } let t = spawn_scoped(fn() -> i32 { return unsafe { Q.b }; }); return t.join() * 10 + unsafe { Q.b };", 27),
        // A pointer keeps naming the copy of the thread that took it.
        ("pointer_to_another_copy", "unsafe { N = 40; let p = (&raw mut N as usize); let t = spawn_scoped(fn() -> i32 { unsafe { let q = p as *mut i32; *q = *q + 2; } return unsafe { N }; }); let x = t.join(); return N + x - 5; }", 42),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "needs_unsafe",
        "thread_local static mut N: i32 = 5;\npub fn main() -> i32 { return N; }",
        "unsafe",
    );
    assert_rejected(
        "needs_mut",
        "thread_local static N: i32 = 5;\npub fn main() -> i32 { return 0; }",
        "needs 'static mut'",
    );
    // Without `thread_local`, the same program is a data race.
    let racy = "static mut N: i32 = 5;
fn bump() -> i32 { unsafe { N = N + 1; return N; } }
pub fn main() -> i32 { let t = spawn_scoped(fn() -> i32 { return bump(); }); let a = bump(); return a + t.join(); }";
    let err = super::run_vm("shared_static", racy).expect_err("a shared static races");
    assert!(err.contains("data race"), "{err}");
    assert_eq!(
        super::run_vm(
            "thread_local_static",
            &racy.replacen("static mut", "thread_local static mut", 1)
        ),
        Ok(VmRun { value: 12, leaks: 0, output: String::new() })
    );
}

#[test]
fn test_taking_a_value_out_does_not_borrow_the_container() {
    let pool = "extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
pub struct Pool { x: i32 }
unsafe impl Allocator for Pool {
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 { return unsafe { malloc(bytes) }; }
    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return unsafe { realloc(ptr, bytes) }; }
    fn dealloc(self: &Self, ptr: *mut u8) { unsafe { free(ptr); } }
}
";
    for (name, body, value) in [
        ("pop_then_pop", "let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); v.push(&x); let a = v.pop(); let b = v.pop(); if let r = a { return *r; } return 0;", 1),
        ("pop_then_push", "let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); let a = v.pop(); v.push(&x); if let r = a { return *r; } return 0;", 1),
        ("insert_then_insert", "let x: i32 = 1; let mut m = HashMap[i32, &i32]::new(); let a = m.insert(1, &x); let b = m.insert(1, &x); if let r = b { return *r; } return 0;", 1),
        ("remove_then_insert", "let x: i32 = 1; let mut m = HashMap[i32, &i32]::new(); let a = m.insert(1, &x); let b = m.remove(1); let c = m.insert(2, &x); if let r = b { return *r; } return 0;", 1),
        ("stateful_insert", "let p = Pool { x: 1 }; let mut m = HashMap[i32, Box[i32, &Pool], &Pool]::new_in(&p); let a = m.insert(1, Box[i32, &Pool]::new_in(1, &p)); let b = m.insert(1, Box[i32, &Pool]::new_in(2, &p)); if let r = b { return r.into_inner(); } return 0;", 1),
        ("replace_then_write", "let x: i32 = 1; let y: i32 = 2; let mut r: &i32 = &x; let old = replace(&mut r, &y); r = &x; return *old;", 1),
    ] {
        assert_runs(name, &format!("{pool}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // What was taken out still holds what the container held.
    for (name, body) in [
        ("pop_outlives_referent", "let mut v = Vec[&i32]::new(); if true { let x: i32 = 1; v.push(&x); } let a = v.pop(); if let r = a { return *r; } return 0;"),
        ("taken_out_outlives_referent", "let mut a: ?&i32 = null; if true { let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); a = v.pop(); } if let r = a { return *r; } return 0;"),
        ("removed_outlives_referent", "let mut a: ?&i32 = null; if true { let x: i32 = 1; let mut m = HashMap[i32, &i32]::new(); let _o = m.insert(1, &x); a = m.remove(1); } if let r = a { return *r; } return 0;"),
        ("replaced_outlives_referent", "let y: i32 = 2; let mut old: &i32 = &y; if true { let x: i32 = 1; let mut r: &i32 = &x; old = replace(&mut r, &y); } return *old;"),
    ] {
        assert_rejected(name, &format!("pub fn main() -> i32 {{ {body} }}"), "goes out of scope while still borrowed");
    }
    // A reference into a container still borrows it, or it would dangle when the buffer moves.
    for (name, body) in [
        ("get_survives_push", "let mut v = Vec[i32]::new(); v.push(1); let r = v.get(0) orelse unreachable; v.push(2); return *r;"),
        ("get_of_refs_survives_push", "let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); let r = v.get(0) orelse unreachable; v.push(&x); return **r;"),
        ("map_get_survives_insert", "let mut m = HashMap[i32, i32]::new(); let _o = m.insert(1, 2); let r = m.get(1) orelse unreachable; let _p = m.insert(2, 3); return *r;"),
    ] {
        assert_rejected(name, &format!("pub fn main() -> i32 {{ {body} }}"), "already borrowed");
    }
    // A popped value that keeps its arena still cannot outlive it.
    assert_rejected(
        "popped_outlives_arena",
        &format!("{pool}pub fn main() -> i32 {{ let q = Pool {{ x: 1 }}; let mut a = Vec[Box[i32, &Pool], &Pool]::new_in(&q); if true {{ let p = Pool {{ x: 1 }}; let mut v = Vec[Box[i32, &Pool], &Pool]::new_in(&p); v.push(Box[i32, &Pool]::new_in(1, &p)); a = v; }} return 0; }}"),
        "goes out of scope while still borrowed",
    );
}

#[test]
fn test_cancel_scopes() {
    let tx = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(move self) -> i32 { return self.id; }
}
fn step() -> CancelError!i32 { try check_cancelled(); return 1; }
fn holds_tx() -> CancelError!i32 {
    let t = Tx::new(5);
    let r = step() catch |e| { let _x = t.commit(); return e; };
    return r + t.commit();
}
";
    for (name, body, value) in [
        ("no_scope_is_never_cancelled", "return step() catch |e| 9;", 1),
        ("not_cancelled", "let s = CancelScope::new(); return s.run(fn() -> i32 { return step() catch |e| 9; });", 1),
        ("cancelled", "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { return step() catch |e| 9; });", 9),
        ("restored_after_run", "let s = CancelScope::new(); s.cancel(); let a = s.run(fn() -> i32 { return step() catch |e| 9; }); return a + step() catch |e| 50;", 10),
        ("outer_cancels_inner", "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { let i = CancelScope::new(); return i.run(fn() -> i32 { return step() catch |e| 9; }); });", 9),
        ("inner_does_not_cancel_outer", "let s = CancelScope::new(); return s.run(fn() -> i32 { let i = CancelScope::new(); i.cancel(); let a = i.run(fn() -> i32 { return step() catch |e| 9; }); return a + step() catch |e| 50; });", 10),
        // The error path consumes a linear value, as cancellation must.
        ("linear_on_the_error_path", "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { return holds_tx() catch |e| 3; });", 3),
        // A scoped thread is inside its creator's scope, and cancelling reaches it.
        ("thread_inherits", "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { let t = spawn_scoped(fn() -> i32 { return step() catch |e| 9; }); return t.join(); });", 9),
        ("cancel_from_another_thread", "let s = CancelScope::new(); let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let x = t.join(); return x + s.run(fn() -> i32 { return step() catch |e| 9; });", 9),
        // A detached thread is not inside any scope.
        ("detached_is_a_root", "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { let t = spawn(move fn() -> i32 { return step() catch |e| 9; }); return t.join(); });", 1),
    ] {
        assert_runs(name, &format!("{tx}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "linear_lost_on_cancel",
        &format!("{tx}fn lost() -> CancelError!i32 {{ let t = Tx::new(5); try check_cancelled(); return t.commit(); }}\npub fn main() -> i32 {{ return 0; }}"),
        "must be explicitly consumed",
    );
}

#[test]
fn test_scoped_thread_closures_of_any_size() {
    let lets: String = (0..40).map(|i| format!("let a{i}: i32 = 1; ")).collect();
    let sum: Vec<String> = (0..40).map(|i| format!("a{i}")).collect();
    let src = format!(
        "pub fn main() -> i32 {{ {lets} let t = spawn_scoped(fn() -> i32 {{ return {}; }}); return t.join(); }}",
        sum.join(" + ")
    );
    assert_runs("large_capture", &src, 40);
}

#[test]
fn test_cancellable_waits() {
    let tx = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(move self) -> i32 { return self.id; }
}
";
    for (name, body, value) in [
        // Blocked with nothing to receive, until another thread cancels.
        ("recv_is_cancelled", "let s = CancelScope::new(); let c = Channel[i32]::new(); let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let r = s.run(fn() -> i32 { return c.recv() catch |e| 9; }); return r + t.join();", 9),
        ("send_is_cancelled_and_returns_the_value", "let s = CancelScope::new(); let c = Channel[i32]::with_capacity(1); let _a = c.send(1); let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let r = s.run(fn() -> i32 { if let v = c.send(7) { return v; } return 0; }); return r + t.join();", 7),
        ("linear_value_comes_back", "let s = CancelScope::new(); let c = Channel[Tx]::with_capacity(1); if let u = c.send(Tx::new(1)) { let _x = u.commit(); } let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let cr = &c; let f = Tx::new(8); let r = s.run(move fn() -> i32 { if let v = cr.send(f) { return v.commit(); } return 0; }); let _j = t.join(); c.close_and_drain(fn(u: Tx) { let _x = u.commit(); }); return r;", 8),
        // A value that is there wins over cancellation.
        ("value_beats_cancel", "let s = CancelScope::new(); let c = Channel[i32]::new(); let _a = c.send(4); s.cancel(); return s.run(fn() -> i32 { return c.recv() catch |e| 9; });", 4),
        ("nothing_there_when_cancelled", "let s = CancelScope::new(); let c = Channel[i32]::new(); s.cancel(); return s.run(fn() -> i32 { return c.recv() catch |e| 9; });", 9),
        // Without a scope, a blocking recv works as it did.
        ("no_scope", "let c = Channel[i32]::new(); let t = spawn_scoped(fn() -> i32 { let _a = c.send(3); return 0; }); let r = c.recv() catch |e| 9; return r + t.join();", 3),
        ("inner_scope_waits_for_outer", "let s = CancelScope::new(); let c = Channel[i32]::new(); let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let r = s.run(fn() -> i32 { let i = CancelScope::new(); return i.run(fn() -> i32 { return c.recv() catch |e| 9; }); }); return r + t.join();", 9),
    ] {
        assert_runs(name, &format!("{tx}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "unsent_linear_value_must_be_handled",
        &format!("{tx}pub fn main() -> i32 {{ let c = Channel[Tx]::with_capacity(1); c.send(Tx::new(1)); return 0; }}"),
        "must be explicitly consumed",
    );
}

#[test]
fn test_deadlines() {
    for (name, body, value) in [
        // Nothing arrives, and the scope ends itself.
        ("recv_times_out", "let s = CancelScope::with_timeout_ms(5); let c = Channel[i32]::new(); return s.run(fn() -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 1 }; });", 2),
        ("sleep_times_out", "let s = CancelScope::with_timeout_ms(5); return s.run(fn() -> i32 { let _a = sleep_ms(1000) catch |e| match e { .TimedOut => return 2, .Cancelled => return 1 }; return 0; });", 2),
        ("sleep_finishes_first", "let s = CancelScope::with_timeout_ms(1000); return s.run(fn() -> i32 { let _a = sleep_ms(2) catch |e| return 1; return 7; });", 7),
        ("sleep_without_a_scope", "let _a = sleep_ms(2) catch |e| return 1; return 7;", 7),
        // A value that arrived wins, even past the deadline.
        ("value_beats_deadline", "let s = CancelScope::with_timeout_ms(1); let c = Channel[i32]::new(); let _a = c.send(4); let _b = sleep_ms(3); return s.run(fn() -> i32 { return c.recv() catch |e| 9; });", 4),
        // The earliest deadline on the path applies, and an outer deadline reaches inner scopes.
        ("outer_deadline_reaches_inner", "let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let i = CancelScope::with_timeout_ms(100000); return i.run(fn() -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 1 }; }); });", 2),
        ("inner_deadline_spares_outer", "let s = CancelScope::new(); return s.run(fn() -> i32 { let i = CancelScope::with_timeout_ms(1); let c = Channel[i32]::new(); let a = i.run(fn() -> i32 { return c.recv() catch |e| 2; }); let _b = check_cancelled() catch |e| return 5; return a * 10; });", 20),
        // An explicit cancel is reported over a passed deadline.
        ("cancel_over_deadline", "let s = CancelScope::with_timeout_ms(1); let _a = sleep_ms(3); s.cancel(); return s.run(fn() -> i32 { let _b = check_cancelled() catch |e| match e { .TimedOut => return 2, .Cancelled => return 1 }; return 0; });", 1),
        // Zero means now, not never.
        ("zero_timeout", "let s = CancelScope::with_timeout_ms(0); return s.run(fn() -> i32 { let _b = check_cancelled() catch |e| return 2; return 7; });", 2),
        ("no_deadline_yet", "let s = CancelScope::with_timeout_ms(100000); return s.run(fn() -> i32 { let _b = check_cancelled() catch |e| return 1; return 7; });", 7),
        // A thread started inside a scope shares its deadline.
        ("thread_shares_deadline", "let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let t = spawn_scoped(fn() -> i32 { return c.recv() catch |e| 2; }); return t.join(); });", 2),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_move_closures_that_move_captures_out() {
    let total = "fn total(v: Vec[i32]) -> i32 { return v.len() as i32; }\n";
    let one = "let mut v = Vec[i32]::new(); v.push(1);";
    for (name, body, value) in [
        ("called_once", "let f = move fn() -> i32 { return total(v); }; return f();", 1),
        ("given_to_a_thread", "let t = spawn(move fn() -> i32 { return total(v); }); return t.join();", 1),
        // The environment still drops its capture.
        ("never_called", "let f = move fn() -> i32 { return total(v); }; return 3;", 3),
        // Only moving a capture out spends the closure.
        ("reading_is_reusable", "let f = move fn() -> i32 { return v.len() as i32; }; return f() + f();", 2),
        ("a_local_of_the_closure", "let f = move fn() -> i32 { let w = Vec[i32]::new(); return total(w) + 1; }; return f() + f();", 2),
    ] {
        assert_runs(name, &format!("{total}pub fn main() -> i32 {{ {one} {body} }}"), value);
    }
    assert_runs(
        "consuming_method",
        "pub struct T { v: Vec[i32], pub fn into_len(move self) -> i32 { return self.v.len() as i32; } }
pub fn main() -> i32 { let mut v = Vec[i32]::new(); v.push(1); let t = T { v: move v }; let f = move fn() -> i32 { return t.into_len(); }; return f(); }",
        1,
    );
    assert_rejected(
        "called_twice",
        &format!("{total}pub fn main() -> i32 {{ {one} let f = move fn() -> i32 {{ return total(v); }}; let a = f(); return a + f(); }}"),
        "Use of moved",
    );
    assert_rejected(
        "called_through_a_reference",
        &format!("{total}fn call[F: callable](f: &F) -> i32 {{ return f(); }}\npub fn main() -> i32 {{ {one} let f = move fn() -> i32 {{ return total(v); }}; return call(&f); }}"),
        "single-use closure",
    );
}

#[test]
fn test_spawn_returns_results_wider_than_a_pointer() {
    // The result used to overrun a pointer-sized slot on the joining stack, which only the
    // native run shows.
    assert_runs(
        "wide_result",
        "struct B { a: i64, b: i64, c: i64 }
fn work() -> i64 {
    let t = spawn(move fn() -> B { return B { a: 11, b: 22, c: 33 }; });
    let guard: [i64; 4] = { 7, 7, 7, 7 };
    let r = t.join();
    return r.a + r.b + r.c + guard[0] + guard[3];
}
pub fn main() -> i32 { return work() as i32; }",
        80,
    );
}

#[test]
fn test_async_tasks() {
    let prelude = "fn add(a: i32, b: i32) -> i32 { return a + b; }
fn sq(a: i32) -> i32 { return a * a; }
fn total(v: Vec[i32]) -> i32 { return v.len() as i32; }
fn peek(v: &Vec[i32]) -> i32 { return v.len() as i32; }
fn wait(c: &Channel[i32]) -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 7 }; }
fn nothing() { }
fn nested(a: i32) -> i32 { let t = async sq(a); return t.await() + 1; }
struct B { a: i64, b: i64, c: i64 }
fn wide(n: i64) -> B { return B { a: n, b: 2, c: 3 }; }
pub opaque(linear) Tx {
    n: i32,
    pub fn new(n: i32) -> Self { return Self { n: n }; }
    pub fn commit(move self) -> i32 { let n = self.n; unsafe { @forget(self); } return n; }
}
fn make_tx() -> Tx { return Tx::new(4); }
fn commit(t: Tx) -> i32 { return t.commit(); }
pub struct C {
    n: i32,
    pub fn get(self: &Self) -> i32 { return self.n; }
    pub fn bump(self: &mut Self) -> i32 { self.n = self.n + 1; return self.n; }
}
fn get[F: Future[i32] + ?linear](f: F) -> i32 { return f.await(); }
fn late() -> i32 { let _a = sleep_ms(5); let _b = check_cancelled() catch |e| return 9; return 0; }
fn escapes() -> Task[i32] { let s = CancelScope::new(); return s.run(fn() -> Task[i32] { return async late(); }); }
fn starts_late() -> Task[i32] { return async late(); }
";
    for (name, body, value) in [
        ("arguments", "let n = 3; let x = async add(n, 4); return x.await();", 7),
        ("two_tasks", "let x = async sq(3); let y = async sq(4); return x.await() + y.await();", 25),
        ("wide_result", "let t = async wide(9); let r = t.await(); return (r.a + r.c) as i32;", 12),
        ("no_result", "let t = async nothing(); t.await(); return 1;", 1),
        ("nested", "let t = async nested(2); return t.await();", 5),
        // Arguments move in, or stay borrowed.
        ("moved_argument", "let mut v = Vec[i32]::new(); v.push(1); let t = async total(v); return t.await();", 1),
        ("borrowed_argument", "let mut v = Vec[i32]::new(); v.push(1); let t = async peek(&v); let a = t.await(); v.push(2); return a + v.len() as i32;", 3),
        ("linear_argument", "let tx = Tx::new(6); let t = async commit(tx); return t.await();", 6),
        ("linear_receiver", "let tx = Tx::new(6); let t = async tx.commit(); return t.await();", 6),
        ("linear_result", "let t = async make_tx(); return t.await().commit();", 4),
        ("receiver_is_borrowed", "let mut c = C { n: 1 }; let t = async c.bump(); let a = t.await(); let u = async c.get(); return a * 10 + u.await();", 22),
        // Every handle is a future.
        ("generic_future", "let t = async sq(2); let j = spawn(move fn() -> i32 { return 3; }); let s = spawn_scoped(fn() -> i32 { return 5; }); return get(t) + get(j) + get(s);", 12),
        // Dropping a handle cancels the task and waits for it.
        ("dropped_task_is_cancelled", "let c = Channel[i32]::new(); let t = async wait(&c); return 3;", 3),
        ("cancel_returns_the_result", "let c = Channel[i32]::new(); let t = async wait(&c); return t.cancel();", 7),
        ("cancel_after_a_value", "let c = Channel[i32]::new(); let _s = c.send(5); let t = async wait(&c); let _a = sleep_ms(2); return t.cancel();", 5),
        // A task sits inside the scope it was started in.
        ("outer_cancel_reaches_a_task", "let s = CancelScope::new(); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let h = async wait(&c); s.cancel(); return h.await(); });", 7),
        ("outer_deadline_reaches_a_task", "let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let h = async wait(&c); return h.await(); });", 2),
        // A handle may leave its scope, but the scope waits for the task, which still reads it.
        ("scope_outlives_an_escaped_task", "return escapes().await();", 0),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // A task cannot hand back a handle it made: that would move the handle to another thread.
    assert_rejected(
        "task_returns_a_handle",
        &format!("{prelude}pub fn main() -> i32 {{ let t = async starts_late(); let child = t.await(); return child.await(); }}"),
        "Type 'Task' does not satisfy comptime constraint 'send'",
    );
    for (name, body, what) in [
        ("borrow_is_held", "let mut v = Vec[i32]::new(); let t = async peek(&v); v.push(1); return t.await();", "already borrowed"),
        ("receiver_borrow_is_held", "let mut c = C { n: 1 }; let t = async c.bump(); c.n = 3; return t.await();", "borrow"),
        ("linear_result_cannot_be_dropped", "let t = async make_tx(); return 1;", "must be explicitly consumed"),
        ("used_after_await", "let t = async sq(2); let a = t.await(); return a + t.await();", "Use of moved"),
        ("not_a_call", "let x = 1; let t = async x; return 0;", "'async' takes a call"),
        ("argument_not_send", "let mut x: i32 = 1; let p = &raw mut x; let t = async rawp(p); return t.await();", "does not satisfy comptime constraint 'send'"),
    ] {
        assert_rejected(
            name,
            &format!("{prelude}fn rawp(p: *mut i32) -> i32 {{ return 1; }}\npub fn main() -> i32 {{ {body} }}"),
            what,
        );
    }
    assert_rejected(
        "handle_outlives_a_borrow",
        "fn read(v: &i32) -> i32 { return *v; }
fn bad() -> Task[i32] { let x: i32 = 5; return async read(&x); }
pub fn main() -> i32 { return bad().await(); }",
        "goes out of scope while still borrowed",
    );
}

#[test]
fn test_race_detection_tells_fields_apart() {
    let shared = "pub opaque(unsafe sync) Pair {
    cell a: i32,
    cell b: i32,
    pub fn new() -> Self { return Self { a: 0, b: 0 }; }
    pub fn set_a(self: &Self) { unsafe { *(&raw mut self.a) = 1; } }
    pub fn get_b(self: &Self) -> i32 { return unsafe { *(&raw mut self.b) }; }
    pub fn get_a(self: &Self) -> i32 { return unsafe { *(&raw mut self.a) }; }
}
struct Point { x: i32, y: i32 }
";
    let run = |name: &str, body: &str| super::run_vm(name, &format!("{shared}pub fn main() -> i32 {{ {body} }}"));
    let other = "let p = Pair::new(); let t = spawn_scoped(fn() -> i32 { p.set_a(); return 0; }); let b = p.get_b(); return b + t.join();";
    assert_eq!(run("other_field", other).map(|r| r.value), Ok(0));
    let same = "let p = Pair::new(); let t = spawn_scoped(fn() -> i32 { p.set_a(); return 0; }); let a = p.get_a(); return a + t.join();";
    assert!(run("same_field", same).is_err_and(|e| e.contains("data race")));
    // A whole access meets every field.
    let whole = "let mut s = Point { x: 0, y: 0 }; let addr = &raw mut s as usize; let t = spawn_scoped(move fn() -> i32 { unsafe { (*(addr as *mut Point)).x = 1; } return 0; }); let c = unsafe { *(addr as *mut Point) }; return c.y + t.join();";
    assert!(run("whole_value", whole).is_err_and(|e| e.contains("data race")));
}

const COUNTING: &str = "static mut LIVE: i32 = 0;
static mut TOTAL: i32 = 0;
extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
";

#[test]
fn test_program_allocator() {
    let program = format!(
        "{COUNTING}pub struct Counted {{ }}
unsafe impl GlobalAllocator for Counted {{
    fn alloc(bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ LIVE = LIVE + 1; TOTAL = TOTAL + 1; return malloc(bytes); }} }}
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ return realloc(ptr, bytes); }} }}
    fn dealloc(ptr: *mut u8) {{ unsafe {{ LIVE = LIVE - 1; free(ptr); }} }}
}}
pub alias ProgramAllocator = Counted;
fn leak() -> *mut i32 {{ return unsafe {{ @alloc(i32, 1) as *mut i32 }}; }}
"
    );
    for (name, body, value) in [
        ("box", "if true { let b = Box[i32]::new(5); } return unsafe { TOTAL * 10 + LIVE };", 10),
        ("vec", "let mut v = Vec[i32]::new(); v.push(1); return unsafe { TOTAL * 10 + LIVE };", 11),
        ("string", "if true { let s = String::from(\"abc\"); } return unsafe { (TOTAL > 0) as i32 * 10 + LIVE };", 10),
        ("hash_map", "if true { let mut m = HashMap[i32, i32]::new(); let _o = m.insert(1, 2); } return unsafe { (TOTAL > 0) as i32 * 10 + LIVE };", 10),
        ("intrinsics", "let p = leak(); let n = unsafe { TOTAL }; unsafe { @dealloc(p); } return n;", 1),
        ("thread", "let t = spawn(move fn() -> i32 { let b = Box[i32]::new(5); return b.into_inner(); }); let r = t.join(); return r + unsafe { LIVE };", 5),
    ] {
        assert_runs(name, &format!("{program}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // Its own allocations go to the default, or it would call itself.
    assert_runs(
        "allocator_that_allocates",
        &format!(
            "{COUNTING}pub struct Own {{ }}
unsafe impl GlobalAllocator for Own {{
    fn alloc(bytes: usize, align: usize) -> *mut u8 {{ let scratch = unsafe {{ @alloc(i32, 1) as *mut i32 }}; unsafe {{ @dealloc(scratch); TOTAL = TOTAL + 1; return malloc(bytes); }} }}
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ return realloc(ptr, bytes); }} }}
    fn dealloc(ptr: *mut u8) {{ unsafe {{ free(ptr); }} }}
}}
pub alias ProgramAllocator = Own;
pub fn main() -> i32 {{ let b = Box[i32]::new(5); return b.into_inner() + unsafe {{ TOTAL }}; }}"
        ),
        6,
    );
    assert_rejected(
        "must_be_an_allocator",
        "pub struct Nope { }\npub alias ProgramAllocator = Nope;\npub fn main() -> i32 { let b = Box[i32]::new(5); return b.into_inner(); }",
        "needs a type implementing 'GlobalAllocator'",
    );
    // A program that names no allocator is unchanged.
    assert_runs("default", "pub fn main() -> i32 { let b = Box[i32]::new(5); return b.into_inner(); }", 5);
}

#[test]
fn test_container_allocators() {
    let prelude = format!(
        "{COUNTING}pub struct Counted {{ }}
unsafe impl Allocator for Counted {{
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ LIVE = LIVE + 1; TOTAL = TOTAL + 1; return malloc(bytes); }} }}
    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ return realloc(ptr, bytes); }} }}
    fn dealloc(self: &Self, ptr: *mut u8) {{ unsafe {{ LIVE = LIVE - 1; free(ptr); }} }}
}}
pub opaque Pool {{
    cell live: i32,
    cell total: i32,
    pub fn new() -> Self {{ return Self {{ live: 0, total: 0 }}; }}
    pub fn stats(self: &Self) -> i32 {{ return unsafe {{ *(&raw mut self.total) * 10 + *(&raw mut self.live) }}; }}
    pub fn note(self: &Self, d: i32) {{
        unsafe {{
            let p = &raw mut self.live;
            *p = *p + d;
            if d > 0 {{ let q = &raw mut self.total; *q = *q + 1; }}
        }}
    }}
}}
unsafe impl Allocator for Pool {{
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 {{ self.note(1); return unsafe {{ malloc(bytes) }}; }}
    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {{ return unsafe {{ realloc(ptr, bytes) }}; }}
    fn dealloc(self: &Self, ptr: *mut u8) {{ self.note(-1); unsafe {{ free(ptr); }} }}
}}
struct Held {{ v: Vec[i32, &Pool] }}
fn add(v: &mut Vec[i32, &Pool]) {{ v.push(1); }}
fn make(p: &Pool) -> Vec[i32, &Pool] borrows(p) {{ return Vec[i32, &Pool]::new_in(p); }}
fn wrap(v: Vec[i32, &Pool]) -> Held {{ return Held {{ v: move v }}; }}
fn put(m: &mut HashMap[i32, i32, &Pool]) {{ let _old = m.insert(1, 2); }}
fn plain_len(v: &Vec[i32]) -> i32 {{ return v.len() as i32; }}
fn any_len[T, A: Allocator + copy](v: &Vec[T, A]) -> i32 {{ return v.len() as i32; }}
fn sum[T: Allocator + copy](b: &Box[i32, T]) -> i32 {{ return *b.get(); }}
"
    );
    for (name, body, value) in [
        // Nothing is stored for an allocator with no state, and only what uses a pool holds one.
        ("box_size", "return (@size_of(Box[i32]) / 8 * 10 + @size_of(Box[i32, Counted]) / 8) as i32;", 11),
        ("vec_size", "return (@size_of(Vec[i32]) / 8 * 10 + @size_of(Vec[i32, Counted]) / 8) as i32;", 33),
        ("pool_size", "return (@size_of(Box[i32, &Pool]) / 8 * 10 + @size_of(Vec[i32, &Pool]) / 8) as i32;", 24),
        // A value is freed by its allocator.
        ("stateless", "if true { let b = Box[i32, Counted]::new(5); } return unsafe { TOTAL * 10 + LIVE };", 10),
        ("default_is_not_counted", "if true { let b = Box[i32]::new(5); } return unsafe { TOTAL };", 0),
        ("into_inner", "let b = Box[i32, Counted]::new(5); return b.into_inner() + unsafe { LIVE * 10 };", 5),
        ("vec_grows", "if true { let mut v = Vec[Box[i32, Counted], Counted]::new(); for i in 0..20 { v.push(Box[i32, Counted]::new(i)); } } return unsafe { LIVE };", 0),
        ("map_grows", "if true { let mut m = HashMap[i32, i32, Counted]::new(); for i in 0..40 { let _o = m.insert(i, i); } } return unsafe { (TOTAL > 3) as i32 * 10 + LIVE };", 10),
        ("clone_keeps_it", "if true { let mut v = Vec[i32, Counted]::new(); v.push(1); let w = @clone(&v); } return unsafe { TOTAL * 10 + LIVE };", 20),
        // A pool.
        ("instance", "let p = Pool::new(); if true { let b = Box[i32, &Pool]::new_in(5, &p); } return p.stats();", 10),
        ("instances_are_separate", "let p = Pool::new(); let q = Pool::new(); if true { let a = Box[i32, &Pool]::new_in(5, &p); let b = Box[i32, &Pool]::new_in(6, &q); let c = Box[i32, &Pool]::new_in(7, &q); } return p.stats() / 10 * 10 + q.stats() / 10;", 12),
        ("first_allocation_later", "let p = Pool::new(); let mut v = Vec[i32, &Pool]::new_in(&p); let n = p.stats(); v.push(1); return n * 100 + p.stats();", 11),
        ("with_capacity", "let p = Pool::new(); let v = Vec[i32, &Pool]::with_capacity_in(4, &p); return p.stats();", 11),
        ("clone_of_a_pool_vec", "let p = Pool::new(); let mut v = make(&p); v.push(1); let w = @clone(&v); return w.len() as i32 * 100 + p.stats();", 122),
        ("parameter", "let p = Pool::new(); let mut v = make(&p); add(&mut v); return v.len() as i32 * 100 + p.stats();", 111),
        ("struct_field", "let p = Pool::new(); let mut h = wrap(make(&p)); h.v.push(2); return h.v.len() as i32 * 100 + p.stats();", 111),
        ("map", "let p = Pool::new(); let mut m = HashMap[i32, i32, &Pool]::new_in(&p); put(&mut m); return m.len() as i32 * 100 + (p.stats() > 0) as i32;", 101),
        ("annotated_local", "let p = Pool::new(); let mut v: Vec[i32, &Pool] = make(&p); v.push(1); return v.len() as i32;", 1),
        // Generic code reaches every kind, and `Vec[T]` still means the default.
        ("generic", "let p = Pool::new(); let mut v = make(&p); v.push(1); let mut w = Vec[i32, Counted]::new(); w.push(1); w.push(2); let x = Vec[i32]::new(); return any_len(&v) * 100 + any_len(&w) * 10 + any_len(&x);", 120),
        ("generic_box", "let b = Box[i32, Counted]::new(7); return sum(&b);", 7),
        ("default_parameter", "let mut w = Vec[i32]::new(); w.push(1); return plain_len(&w);", 1),
        ("in_a_thread", "let b = Box[i32, Counted]::new(4); let t = spawn_scoped(fn() -> i32 { return *b.get(); }); return t.join();", 4),
        ("in_a_task", "let t = async vec_of_counted(); let v = t.await(); return v.len() as i32 * 10 + unsafe { LIVE };", 11),
    ] {
        assert_runs(
            name,
            &format!("{prelude}fn vec_of_counted() -> Vec[i32, Counted] {{ let mut v = Vec[i32, Counted]::new(); v.push(1); return v; }}\npub fn main() -> i32 {{ {body} }}"),
            value,
        );
    }
    for (name, items, body, what) in [
        ("no_default_for_a_pool", "", "let v = Vec[i32, &Pool]::new(); return 0;", "'A: default' is not satisfied"),
        ("plain_is_not_a_pool_vec", "", "let mut v = Vec[i32]::new(); add(&mut v); return 0;", "Type mismatch"),
        ("pool_vec_is_not_plain", "", "let p = Pool::new(); let v = make(&p); return plain_len(&v);", "Type mismatch"),
        ("default_pattern", "fn only_default[T](v: &Vec[T]) -> i32 { return 0; }", "let p = Pool::new(); let v = make(&p); return only_default(&v);", "No overload"),
        ("not_an_allocator", "", "let v = Vec[i32, i32]::new(); return 0;", "does not implement trait 'Storage'; add 'impl Storage { ... }' to the type's body or 'impl Storage for i32 { ... }' in the type's or the trait's module; or meet 'Allocator + copy', as every such type implements it"),
        ("outlives_the_pool", "fn bad() -> Vec[i32, &Pool] { let p = Pool::new(); return make(&p); }", "let v = bad(); return 0;", "goes out of scope while still borrowed"),
        ("in_a_struct", "fn bad() -> Held { let p = Pool::new(); return Held { v: make(&p) }; }", "let h = bad(); return 0;", "goes out of scope while still borrowed"),
        ("through_a_call", "fn bad() -> Held { let p = Pool::new(); return wrap(make(&p)); }", "let h = bad(); return 0;", "goes out of scope while still borrowed"),
        ("box_outlives_the_pool", "fn bad() -> Box[i32, &Pool] { let p = Pool::new(); return Box[i32, &Pool]::new_in(1, &p); }", "let v = bad(); return 0;", "goes out of scope while still borrowed"),
        ("drop_uses_the_pool", "", "let mut v: ?Vec[i32, &Pool] = null; if true { let p = Pool::new(); v = make(&p); } return 0;", "goes out of scope while still borrowed"),
        ("pool_dies_first", "", "let mut v: ?Vec[i32, &Pool] = null; let p = Pool::new(); v = make(&p); return 0;", "goes out of scope while still borrowed"),
        ("detached_thread", "", "let p = Pool::new(); let v = make(&p); let t = spawn(move fn() -> i32 { return v.len() as i32; }); return t.join();", "spawn"),
        ("detached_thread_nested", "", "let p = Pool::new(); let v = make(&p); let b = Box[Vec[i32, &Pool]]::new(move v); let t = spawn(move fn() -> i32 { return b.into_inner().len() as i32; }); return t.join();", "spawn"),
    ] {
        assert_rejected(name, &format!("{prelude}{items}\npub fn main() -> i32 {{ {body} }}"), what);
    }
}

#[test]
fn test_executors() {
    let prelude = "fn sq(a: i32) -> i32 { return a * a; }
fn wait(c: &Channel[i32]) -> i32 { return c.recv() catch |e| 7; }
fn produce(c: &Channel[i32]) -> i32 { let _s = c.send(9); return 0; }
fn nested(a: i32) -> i32 { let t = async(Inline { }) sq(a); return t.await() + 1; }
fn run_on[E: Executor + copy + send](e: E) -> i32 { let t = async(e) sq(3); return t.await(); }
fn starts_one(a: i32) -> i32 { let t = async sq(a); return t.await(); }
fn take(t: Task[i32]) -> i32 { return t.await(); }
pub struct Counting { }
static mut STARTED: i32 = 0;
impl Executor for Counting {
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
        unsafe { STARTED = STARTED + 1; }
        return Threads { }.start(entry, arg);
    }
    fn wait(self: &Self, id: u64) { Threads { }.wait(id); }
}
pub opaque(unsafe sync) Pool {
    cell started: i32,
    pub fn new() -> Self { return Self { started: 0 }; }
    pub fn count(self: &Self) -> i32 { return unsafe { *(&raw mut self.started) }; }
    pub fn note(self: &Self) { unsafe { let p = &raw mut self.started; *p = *p + 1; } }
}
impl Executor for Pool {
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 { self.note(); return null; }
    fn wait(self: &Self, id: u64) { }
}
";
    for (name, body, value) in [
        ("default_is_threads", "let t = async sq(3); return t.await();", 9),
        ("named_executor", "let t = async(Threads { }) sq(3); return t.await();", 9),
        ("runs_inline", "let t = async(Inline { }) sq(4); return t.await();", 16),
        // An inline task runs at once, so by the time it is awaited its work is done.
        ("inline_runs_before_returning", "let c = Channel[i32]::with_capacity(1); let t = async(Inline { }) produce(&c); let got = c.recv() catch |e| 0; return got + t.await();", 9),
        ("handle_is_dropped", "let t = async(Inline { }) sq(4); return 1;", 1),
        ("cancel_after_finishing", "let t = async(Inline { }) sq(4); return t.cancel();", 16),
        ("nested", "let t = async nested(2); return t.await();", 5),
        ("generic_executor", "return run_on(Inline { }) + run_on(Threads { });", 18),
        ("custom_executor", "let t = async(Counting { }) sq(2); return t.await() + unsafe { STARTED * 10 };", 14),
        // What a task on an executor starts runs there too, through any depth of calls.
        ("children_follow", "let t = async(Counting { }) starts_one(2); return t.await() + unsafe { STARTED * 10 };", 24),
        // A handle does not name its executor, so handles from any mix together.
        ("one_handle_type", "let a = take(async(Inline { }) sq(2)); let b = take(async sq(3)); return a + b;", 13),
        // An instance is only borrowed, by the handle.
        ("instance", "let p = Pool::new(); let t = async(&p) sq(2); let a = t.await(); let u = async(&p) sq(3); return a + u.await() + p.count() * 100;", 213),
        // A scope reaches an inline task too.
        ("caller_keeps_its_scope", "let s = CancelScope::new(); return s.run(fn() -> i32 { let t = async(Inline { }) sq(2); s.cancel(); let _a = check_cancelled() catch |e| return t.await() + 1; return 0; });", 5),
        ("scope", "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { let c = Channel[i32]::new(); let t = async(Inline { }) wait(&c); return t.await(); });", 7),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // Work that must overlap cannot be left to `async`: on the caller, this waits for itself. A
    // task's wait polls its scope, so it never blocks for good, and this ends at the step limit.
    let overlap = format!("{prelude}pub fn main() -> i32 {{ let c = Channel[i32]::new(); let t = async(Inline {{ }}) wait(&c); let _s = c.send(1); return t.await(); }}");
    let err = super::run_vm("needs_overlap", &overlap).expect_err("deadlock");
    assert!(err.contains("step limit"), "{err}");
    for (name, items, body, what) in [
        ("handle_outlives_the_executor", "fn bad() -> Task[i32] { let p = Pool::new(); return async(&p) sq(2); }", "return bad().await();", "goes out of scope while still borrowed"),
        ("not_an_executor", "", "let t = async(5) sq(2); return t.await();", "does not implement trait 'Executor'"),
        // A handle stays on the thread that made it, as a fiber's must be awaited there.
        ("moved_between_threads", "", "let t = async sq(3); let u = spawn_scoped(move fn() -> i32 { return t.await(); }); return u.join();", "does not satisfy comptime constraint 'send'"),
    ] {
        assert_rejected(name, &format!("{prelude}{items}\npub fn main() -> i32 {{ {body} }}"), what);
    }
    // A program can replace the default, for `async` and for `Task[R]`.
    let program = "pub alias ProgramExecutor = Inline;
fn sq(a: i32) -> i32 { return a * a; }
fn produce(c: &Channel[i32]) -> i32 { let _s = c.send(9); return 0; }
fn start() -> Task[i32] { return async sq(3); }
pub fn main() -> i32 {
    let c = Channel[i32]::with_capacity(1);
    let t = async produce(&c);
    let got = c.recv() catch |e| 0;
    return got + t.await() + start().await() + @size_of(Task[i32]) as i32 * 0;
}";
    assert_runs("program_executor", program, 18);
    assert_rejected(
        "program_executor_must_be_one",
        "pub struct Nope { }\npub alias ProgramExecutor = Nope;\nfn sq(a: i32) -> i32 { return a; }\npub fn main() -> i32 { let t = async sq(1); return t.await(); }",
        "does not implement trait 'Executor'",
    );
}

#[test]
fn test_fibers() {
    let prelude = "fn sq(a: i32) -> i32 { return a * a; }
fn int_of(o: ?i32) -> i32 { if let x = o { return x; } return -1; }
fn add_up(c: &Channel[i32], n: i32) -> i32 { let mut t: i32 = 0; for i in 0..n { t = t + (c.recv() catch |e| 0); } return t; }
fn feed(c: &Channel[i32], n: i32) -> i32 { for i in 0..n { let _s = c.send(i); } return n; }
fn wait(c: &Channel[i32]) -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 7 }; }
fn deep(c: &Channel[i32], n: i32) -> i32 { if n == 0 { return c.recv() catch |e| 0; } return deep(c, n - 1) + 1; }
trait Source { fn next(self: &Self) -> i32; }
pub struct Reader { c: Channel[i32], impl Source { fn next(self: &Self) -> i32 { return self.c.recv() catch |e| 0; } } }
fn through_object(s: &Source) -> i32 { return s.next(); }
fn through_pointer(f: fn(&Channel[i32]) -> i32, c: &Channel[i32]) -> i32 { return f(c); }
fn hold(m: &Mutex[i32], c: &Channel[i32]) -> i32 { let mut g = m.lock(); *g.get_mut() = 5; let _a = c.recv() catch |e| 0; *g.get_mut() = 6; g.unlock(); return 0; }
fn take(m: &Mutex[i32], c: &Channel[i32]) -> i32 { let _s = c.send(1); let mut g = m.lock(); let v = *g.get_mut(); g.unlock(); return v; }
fn late_read(c: &Channel[i32]) -> i32 { let _a = sleep_ms(5); return int_of(c.try_recv()) + 1; }
fn escapes() -> Task[i32] { let s = CancelScope::new(); return s.run(fn() -> Task[i32] { return async(Fibers { }) sq(3); }); }
fn picks(a: &Channel[i32], b: &Channel[i32]) -> i32 { return @select { v = a.recv() => 1, w = b.recv() => 2 }; }
fn cross(a: &Channel[i32], b: &Channel[i32]) -> i32 { let v = a.recv() catch |e| 0; let _s = b.send(v); return v; }
fn relock(m: &Mutex[i32]) -> i32 { let mut g = m.lock(); let v = *g.get_mut(); g.unlock(); return v; }
fn nested(a: i32) -> i32 { let t = async(Fibers { }) sq(a); return t.await() + 1; }
fn nap(ms: i64) -> i32 { let _a = sleep_ms(ms) catch |e| match e { .TimedOut => return 2, .Cancelled => return 1 }; return 0; }
fn scoped(c: &Channel[i32]) -> i32 { let s = CancelScope::new(); return s.run(fn() -> i32 { let a = c.recv() catch |e| 0; let _b = check_cancelled() catch |e| return 9; return a; }); }
fn cancels_itself(c: &Channel[i32]) -> i32 { let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { let _a = c.send(1); let _b = c.send(2); let _c = check_cancelled() catch |e| return 3; return 0; }); }
";
    for (name, body, value) in [
        ("one", "let t = async(Fibers { }) sq(3); return t.await();", 9),
        ("two", "let t = async(Fibers { }) sq(3); let u = async(Fibers { }) sq(4); return t.await() + u.await();", 25),
        // It does not start until something waits, unlike `Inline`.
        ("starts_on_a_wait", "let c = Channel[i32]::with_capacity(1); let t = async(Fibers { }) feed(&c, 1); let early = int_of(c.try_recv()); let got = t.await(); return (early + 1) * 10 + got;", 1),
        // Unlike `Inline`, tasks that need each other work, on one thread.
        ("rendezvous", "let c = Channel[i32]::with_capacity(1); let f = async(Fibers { }) feed(&c, 20); let a = async(Fibers { }) add_up(&c, 20); let n = f.await(); return a.await() + n;", 210),
        ("caller_takes_part", "let c = Channel[i32]::with_capacity(1); let f = async(Fibers { }) feed(&c, 3); let t = add_up(&c, 3); return t + f.await();", 6),
        // Suspending needs no change to what is on the stack.
        ("deep_stack", "let c = Channel[i32]::new(); let d = async(Fibers { }) deep(&c, 200); let _s = c.send(1); return d.await() - 200;", 1),
        ("through_a_function_pointer", "let c = Channel[i32]::new(); let t = async(Fibers { }) through_pointer(wait, &c); let _s = c.send(4); return t.await();", 4),
        ("through_a_trait_object", "let r = Reader { c: Channel[i32]::new() }; let t = async(Fibers { }) through_object(&r); let _s = r.c.send(4); return t.await();", 4),
        ("many", "let mut hs = Vec[Task[i32]]::new(); for i in 0..50 { hs.push(async(Fibers { }) sq(2)); } let mut t: i32 = 0; while let h = hs.pop() { t = t + h.await(); } return t / 4;", 50),
        ("nested", "let t = async(Fibers { }) nested(2); return t.await();", 5),
        // Waiting lets others in, and a held lock waits for its fiber.
        ("mutex_across_a_wait", "let m = Mutex[i32]::new(1); let c = Channel[i32]::new(); let h = async(Fibers { }) hold(&m, &c); let t = async(Fibers { }) take(&m, &c); let _a = h.await(); return t.await();", 6),
        // Cancelling, and each fiber's own scope.
        ("dropped_handle_cancels", "let c = Channel[i32]::new(); let t = async(Fibers { }) wait(&c); return 3;", 3),
        ("cancel_returns_the_result", "let c = Channel[i32]::new(); let t = async(Fibers { }) wait(&c); return t.cancel();", 7),
        ("deadline", "let s = CancelScope::with_timeout_ms(3); return s.run(fn() -> i32 { let t = async(Fibers { }) nap(1000); return t.await(); });", 2),
        ("sleep_finishes", "let t = async(Fibers { }) nap(2); return t.await() + 5;", 5),
        ("scopes_stay_with_their_fibers", "let c = Channel[i32]::with_capacity(4); let a = async(Fibers { }) scoped(&c); let b = async(Fibers { }) cancels_itself(&c); let x = b.await(); return a.await() * 10 + x;", 13),
        // `@select` waits like everything else.
        ("select_lets_others_run", "let a = Channel[i32]::new(); let b = Channel[i32]::new(); let t = async(Fibers { }) picks(&a, &b); let f = async(Fibers { }) feed(&b, 1); let _n = f.await(); return t.await();", 2),
        // A sleeper lets others run, and a scope that ends lets its tasks finish.
        ("sleep_lets_others_run", "let c = Channel[i32]::with_capacity(1); let a = async(Fibers { }) late_read(&c); let b = async(Fibers { }) feed(&c, 1); let _n = b.await(); return a.await();", 1),
        ("scope_end_lets_a_fiber_finish", "return escapes().await();", 9),
        // What cannot wake a fiber directly still reaches it: a deadline and a cancel from a thread.
        ("deadline_reaches_a_parked_fiber", "let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let t = async(Fibers { }) wait(&c); return t.await(); });", 2),
        ("cancel_from_a_thread", "let s = CancelScope::new(); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let t = async(Fibers { }) wait(&c); let u = spawn_scoped(fn() -> i32 { let _a = sleep_ms(2); s.cancel(); return 0; }); let r = t.await(); return r + u.join(); });", 7),
        ("two_sleepers", "let a = async(Fibers { }) nap(3); let b = async(Fibers { }) nap(1); return a.await() + b.await() + 4;", 4),
        // Real threads work alongside them.
        ("beside_a_thread", "let c = Channel[i32]::new(); let t = spawn_scoped(fn() -> i32 { let _s = c.send(5); return 0; }); let f = async(Fibers { }) wait(&c); let r = f.await(); return r + t.join();", 5),
        // Finished fibers leave nothing behind, and later ones start clean.
        ("reused_after_finishing", "let t = async(Fibers { }) sq(2); let a = t.await(); let u = async(Fibers { }) sq(3); return a + u.await();", 13),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_runs(
        "program_executor",
        "pub alias ProgramExecutor = Fibers;
fn feed(c: &Channel[i32]) -> i32 { let _a = c.send(1); let _b = c.send(2); return 0; }
fn take(c: &Channel[i32]) -> i32 { let a = c.recv() catch |e| 0; let b = c.recv() catch |e| 0; return a * 10 + b; }
pub fn main() -> i32 {
    let c = Channel[i32]::with_capacity(1);
    let f = async feed(&c);
    let t = async take(&c);
    let _d = f.await();
    return t.await();
}",
        12,
    );
    // A wake is direct: the rechecks that would hide a missing one take virtual time.
    for (name, body) in [
        ("channel", "let c = Channel[i32]::with_capacity(1); let f = async(Fibers { }) feed(&c, 20); let a = async(Fibers { }) add_up(&c, 20); let _n = f.await(); let _t = a.await();"),
        ("join", "let c = Channel[i32]::new(); let f = async(Fibers { }) feed(&c, 1); let a = async(Fibers { }) add_up(&c, 1); let _t = a.await(); let _n = f.await();"),
        ("select", "let a = Channel[i32]::new(); let b = Channel[i32]::new(); let t = async(Fibers { }) picks(&a, &b); let f = async(Fibers { }) feed(&b, 1); let _n = f.await(); let _t = t.await();"),
        ("mutex", "let m = Mutex[i32]::new(1); let c = Channel[i32]::new(); let h = async(Fibers { }) hold(&m, &c); let t = async(Fibers { }) take(&m, &c); let _a = h.await(); let _b = t.await();"),
        ("scope_end", "let _v = escapes().await();"),
        ("cancel", "let c = Channel[i32]::new(); let t = async(Fibers { }) wait(&c); let _y = std::sync::fiber_yield(); let _r = t.cancel();"),
    ] {
        // The first recheck is free, and would cover for a wake, so a task uses it up first.
        let src = format!("{prelude}pub fn main() -> i32 {{ let first = async(Fibers {{ }}) sq(1); let _f = first.await(); let start = now_ms(); {body} return (now_ms() - start) as i32 + 1; }}");
        let run = super::run_vm(name, &src).unwrap_or_else(|e| panic!("[{name}] {e}"));
        assert_eq!(run.value, 1, "[{name}] took virtual time");
    }
    // Fibers waiting for each other with nothing left to wake them are stopped, not left spinning.
    for (name, body) in [
        ("each_waits_for_the_other", "let a = Channel[i32]::new(); let b = Channel[i32]::new(); let x = async(Fibers { }) cross(&a, &b); let y = async(Fibers { }) cross(&b, &a); return x.await() + y.await();"),
        ("waiting_for_a_lock_held_by_the_waiter", "let m = Mutex[i32]::new(1); let c = Channel[i32]::new(); let x = async(Fibers { }) hold(&m, &c); let y = async(Fibers { }) relock(&m); let a = y.await(); return a + x.await();"),
    ] {
        let src = format!("{prelude}pub fn main() -> i32 {{ {body} }}");
        assert_eq!(run_lli(name, &src), Some(super::TRAP_EXIT), "[{name}]");
        assert!(super::run_vm(name, &src).is_err_and(|e| !e.contains("step limit")), "[{name}]");
    }
    // Two fibers handing a value back and forth switch stacks thousands of times, natively
    // with the backend's own switch.
    let ping = "fn ping(to: &Channel[i32], from: &Channel[i32], n: i32) -> i32 { let mut sum: i32 = 0; for i in 0..n { _ = to.send(i); let v = from.recv() catch return -1; sum = (sum + v) % 1000; } return sum; }
fn pong(from: &Channel[i32], to: &Channel[i32], n: i32) -> i32 { for i in 0..n { let v = from.recv() catch return -1; _ = to.send(v + 1); } return 0; }
pub fn main() -> i32 { let a = Channel[i32]::new(); let b = Channel[i32]::new(); let p = async(Fibers { }) ping(&a, &b, 300); let q = async(Fibers { }) pong(&a, &b, 300); let s = p.await(); return s + q.await(); }";
    assert_runs("ping_pong", ping, 150);
    // A call that blocks the thread while another fiber on it could run makes that fiber wait
    // unseen: the VM says so. Alone, it waits for nothing.
    let joins = "fn joins() -> i32 { let h = spawn(move fn() -> i32 { return 3; }); return h.join(); }\nfn other() -> i32 { return 4; }\n";
    let blocked = format!("{joins}pub fn main() -> i32 {{ let a = async(Fibers {{ }}) joins(); let b = async(Fibers {{ }}) other(); return a.await() + b.await(); }}");
    let err = super::run_vm("blocked", &blocked).map(|r| r.value).unwrap_err();
    assert!(err.contains("A fiber blocked its thread joining a thread while other fibers on it were ready to run"), "{err}");
    assert_eq!(run_lli("blocked_natively", &blocked), Some(7));
    assert_runs("alone", &format!("{joins}pub fn main() -> i32 {{ let a = async(Fibers {{ }}) joins(); return a.await(); }}"), 3);
    // A handle from another thread could not run its fiber, so it cannot be moved to one.
    let wrong_thread = format!("{prelude}pub fn main() -> i32 {{ let t = async(Fibers {{ }}) sq(2); let u = spawn_scoped(move fn() -> i32 {{ return t.await(); }}); return u.join(); }}");
    assert_rejected("wrong_thread", &wrong_thread, "does not satisfy comptime constraint 'send'");
}

#[test]
fn test_closure_returning_a_type_with_two_arguments() {
    assert_runs(
        "closure",
        "pub fn main() -> i32 { let f = fn() -> Vec[i32, Global] { return Vec[i32]::new(); }; return f().len() as i32 + 1; }",
        1,
    );
    assert_runs(
        "function_type",
        "fn make() -> Vec[i32, Global] { return Vec[i32]::new(); }\npub fn main() -> i32 { let f: fn() -> Vec[i32, Global] = make; return f().len() as i32 + 1; }",
        1,
    );
}

#[test]
fn test_a_fiber_overflowing_its_stack_faults() {
    // The guard page stops it. This overflows by a little, into the next fiber's stack below, so
    // without the guard it finishes normally, having written over that stack: about 500 frames fit.
    let src = "fn down(n: i32) -> i64 {
    let frame = @default([i64; 2048]);
    if n == 0 { return frame[0]; }
    return down(n - 1) + frame[2047] + 1;
}
fn idle() -> i64 { return 0; }
pub fn main() -> i32 {
    let t = async(Fibers { }) down(600);
    let u = async(Fibers { }) idle();
    let a = t.await();
    let b = u.await();
    return (a + b) as i32 + 1;
}";
    assert_eq!(run_lli("overflow", src), None);
}

#[test]
fn test_relaxed_atomics() {
    let src = "static mut N: u64 = 0;
pub fn main() -> i32 {
    let a = unsafe { @atomic_add_relaxed(&raw mut N, 3) };
    let b = unsafe { @atomic_sub_relaxed(&raw mut N, 1) };
    let c = unsafe { @atomic_load_relaxed(&raw mut N) };
    return (a * 100 + b * 10 + c) as i32;
}";
    assert_runs("arithmetic", src, 32);
    // Unlike the others, they order nothing, so a race around one is still a race.
    let racy = |op: &str| {
        format!(
            "static mut C: u64 = 0;
pub fn main() -> i32 {{
    let mut x: i32 = 0;
    let addr = &raw mut x as usize;
    let t = spawn_scoped(move fn() -> i32 {{ unsafe {{ *(addr as *mut i32) = 1; let _a = {op}(&raw mut C, 1); }} return 0; }});
    let _b = unsafe {{ {op}(&raw mut C, 1) }};
    let v = unsafe {{ *(addr as *mut i32) }};
    return v * 0 + t.join();
}}"
        )
    };
    let err = super::run_vm("relaxed", &racy("@atomic_add_relaxed")).expect_err("race");
    assert!(err.contains("data race"), "{err}");
}

#[test]
fn test_descriptors() {
    let prelude = "extern fn pipe(fds: *mut [i32; 2]) -> i32;
fn byte_of(s: &str) -> i32 { return s[0] as i32; }
fn read_one(fd: &Fd) -> i32 {
    let mut b: [u8; 1] = { 0 };
    let n = fd.read(&mut b) catch |e| match e { .Cancelled => return 100, .TimedOut => return 101, .Failed => return 102 };
    if n == 0 { return 0; }
    return b[0] as i32;
}
fn send_text(fd: &Fd, s: &str) -> i32 { let _a = fd.write_all(s) catch |e| return 1; return 0; }
fn count_all(fd: &Fd) -> i32 {
    let mut total: i32 = 0;
    let mut buf: [u8; 100] = @default([u8; 100]);
    while true {
        let n = fd.read(&mut buf) catch |e| return -1;
        if n == 0 { break; }
        total = total + n as i32;
    }
    return total;
}
fn big_write(fd: Fd, n: usize) -> i32 {
    let mut s = String::new();
    for i in 0..n { s.push_byte(120); }
    return send_text(&fd, s.as_str());
}
fn tick(c: &Channel[i32]) -> i32 { let _s = c.send(7); return 0; }
fn nap(ms: i64) -> i32 { let _a = sleep_ms(ms); return 0; }
fn one_then_other(a: &Fd, b: &Fd) -> i32 { let s = CancelScope::with_timeout_ms(1); let _x = s.run(fn() -> i32 { return read_one(a); }); return read_one(b); }
";
    for (name, body, value) in [
        ("round_trip", "let p = open_pipe() orelse return 90; let _a = send_text(&p.writer, \"A\"); return read_one(&p.reader);", 65),
        ("end_of_stream", "let p = open_pipe() orelse return 90; let r = p.reader; if true { let w = p.writer; } return read_one(&r);", 0),
        // A fiber waiting to read lets others run, and is woken by the data.
        ("reader_parks", "let p = open_pipe() orelse return 90; let t = async(Fibers { }) read_one(&p.reader); let u = async(Fibers { }) send_text(&p.writer, \"B\"); let _a = u.await(); return t.await();", 66),
        ("others_run_meanwhile", "let p = open_pipe() orelse return 90; let c = Channel[i32]::new(); let t = async(Fibers { }) read_one(&p.reader); let u = async(Fibers { }) tick(&c); let got = c.recv() catch |e| 0; let _a = send_text(&p.writer, \"A\"); let _b = u.await(); return t.await() - 65 + got;", 7),
        // More than a pipe holds: the writer waits for the reader, on one thread.
        ("a_write_bigger_than_the_pipe", "let p = open_pipe() orelse return 90; let r = p.reader; let w = async(Fibers { }) big_write(p.writer, 3000); let t = async(Fibers { }) count_all(&r); let _a = w.await(); return t.await() / 1000;", 3),
        // A watch must not outlive its fiber: this one is cancelled, then its pipe becomes ready.
        ("ready_after_its_fiber_is_gone", "let p = open_pipe() orelse return 90; let q = open_pipe() orelse return 91; let u = async(Fibers { }) read_one(&q.reader); let t = async(Fibers { }) read_one(&p.reader); let _a = sleep_ms(1); let r = t.cancel(); let _s = send_text(&p.writer, \"A\"); let _b = sleep_ms(2); let _t = send_text(&q.writer, \"B\"); return r - 100 + u.await();", 66),
        // Nor a watch outlive the fiber's wait on something else.
        ("ready_after_moving_on", "let p = open_pipe() orelse return 90; let q = open_pipe() orelse return 91; let _s = async(Fibers { }) nap(1); let t = async(Fibers { }) one_then_other(&p.reader, &q.reader); let _a = sleep_ms(3); let _b = send_text(&q.writer, \"B\"); let r = t.await(); let z = open_pipe() orelse return 92; let u = async(Fibers { }) read_one(&z.reader); let _c = send_text(&p.writer, \"A\"); let _d = sleep_ms(2); let _e = send_text(&z.writer, \"C\"); return r + u.await() - 67;", 66),
        // A descriptor from elsewhere keeps blocking, and is waited for first.
        ("borrowed_descriptor", "let mut ends: [i32; 2] = { 0, 0 }; if unsafe { pipe(&raw mut ends) } != 0 { return 90; } let r = Fd::from_raw(ends[0]); let w = Fd::from_raw(ends[1]); let t = async(Fibers { }) read_one(&r); let u = async(Fibers { }) send_text(&w, \"C\"); let _a = u.await(); return t.await();", 67),
        // Only one of these can be registered with `epoll`, and the sweep finds the other.
        ("two_readers_of_one_pipe", "let p = open_pipe() orelse return 90; let a = async(Fibers { }) read_one(&p.reader); let b = async(Fibers { }) read_one(&p.reader); let c = async(Fibers { }) send_text(&p.writer, \"AB\"); let _c = c.await(); return (a.await() + b.await()) - 130;", 1),
        // A thread cannot wake a fiber, but its data does.
        ("thread_wakes_a_fiber", "let p = open_pipe() orelse return 90; let r = p.reader; let w = p.writer; let t = async(Fibers { }) read_one(&r); let u = spawn_scoped(fn() -> i32 { return send_text(&w, \"D\"); }); let v = t.await(); return v + u.join();", 68),
        // Cancelling and deadlines reach a wait, under threads too.
        ("cancel_a_read", "let p = open_pipe() orelse return 90; let t = async(Fibers { }) read_one(&p.reader); return t.cancel();", 100),
        ("deadline_on_a_read", "let p = open_pipe() orelse return 90; let s = CancelScope::with_timeout_ms(3); return s.run(fn() -> i32 { let t = async(Fibers { }) read_one(&p.reader); return t.await(); });", 101),
        ("deadline_on_a_thread", "let p = open_pipe() orelse return 90; let s = CancelScope::with_timeout_ms(3); return s.run(fn() -> i32 { return read_one(&p.reader); });", 101),
        // With no reader left, a write is an error, not a signal.
        ("write_with_no_reader", "let p = open_pipe() orelse return 90; let w = p.writer; if true { let r = p.reader; } return send_text(&w, \"A\");", 1),
        ("between_threads", "let p = open_pipe() orelse return 90; let r = p.reader; let w = p.writer; let t = spawn_scoped(fn() -> i32 { return send_text(&w, \"C\"); }); let v = read_one(&r); return v + t.join();", 67),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // A signal can interrupt a read or write, which is then tried again.
    for (name, body, value) in [
        ("read", "let p = open_pipe() orelse return 90; let _a = send_text(&p.writer, \"A\"); return read_one(&p.reader);", 65),
        ("large_write", "let p = open_pipe() orelse return 90; let r = p.reader; let w = async(Fibers { }) big_write(p.writer, 3000); let t = async(Fibers { }) count_all(&r); let _a = w.await(); return t.await() / 1000;", 3),
    ] {
        let run = super::run_vm_interrupted(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"));
        assert_eq!(run.map(|r| r.value), Ok(value), "[{name}]");
    }
    // Readiness comes from `epoll` at once: the sweep that would hide a missing watch takes time.
    for (name, body) in [
        ("one_wait", "let p = open_pipe() orelse return 90; let t = async(Fibers { }) read_one(&p.reader); let u = async(Fibers { }) send_text(&p.writer, \"A\"); let _a = u.await(); let _b = t.await();"),
        ("waits_on_one_descriptor", "let p = open_pipe() orelse return 90; let c = Channel[i32]::new(); let t = async(Fibers { }) read_twice(&p.reader, &c); let u = async(Fibers { }) send_twice(&p.writer, &c); let _a = u.await(); let _b = t.await();"),
    ] {
        let src = format!("{prelude}fn read_twice(fd: &Fd, c: &Channel[i32]) -> i32 {{ let a = read_one(fd); let _s = c.send(1); return a + read_one(fd); }}\nfn send_twice(fd: &Fd, c: &Channel[i32]) -> i32 {{ let a = send_text(fd, \"A\"); let _r = c.recv() catch |e| 0; return a + send_text(fd, \"B\"); }}\npub fn main() -> i32 {{ let start = now_ms(); {body} return (now_ms() - start) as i32 + 1; }}");
        let run = super::run_vm(name, &src).unwrap_or_else(|e| panic!("[{name}] {e}"));
        assert!(run.value < 5, "[{name}] took {} ms of virtual time", run.value - 1);
    }
    // A real pipe holds 64 KiB, so this write has to wait for the reader.
    let big = format!("{prelude}pub fn main() -> i32 {{ let p = open_pipe() orelse return 90; let r = p.reader; let w = async(Fibers {{ }}) big_write(p.writer, 300000); let t = async(Fibers {{ }}) count_all(&r); let _a = w.await(); return t.await() / 10000; }}");
    assert_eq!(run_lli("native_big_write", &big), Some(30));
    // A waiter on a descriptor is not a deadlock, since the world outside can wake it.
    let parked = format!("{prelude}pub fn main() -> i32 {{ let p = open_pipe() orelse return 90; let t = async(Fibers {{ }}) read_one(&p.reader); return t.await(); }}");
    let err = super::run_vm("waiting_on_a_pipe", &parked).expect_err("never ends");
    assert!(err.contains("step limit"), "{err}");
    let twice = "pub fn main() -> i32 { let a = Fd::from_raw(40); return 0; }";
    assert!(super::run_vm("closing_what_is_not_open", twice).is_err_and(|e| e.contains("not open")));
    assert_rejected("descriptor_is_not_copy", &format!("{prelude}pub fn main() -> i32 {{ let f = Fd::from_raw(9); let g = f; let h = f; return 0; }}"), "moved");
}

#[test]
fn test_parsing_addresses() {
    let prelude = "fn ok(s: &str) -> i32 { if let a = parse_ipv4(s) { return (a & 255) as i32 + ((a >> 24) & 255) as i32; } return 0; }\n";
    for (name, text, value) in [
        ("loopback", "127.0.0.1", 128),
        ("edges", "255.0.0.0", 255),
        ("all_zero", "0.0.0.1", 1),
        ("three_parts", "1.2.3", 0),
        ("five_parts", "1.2.3.4.5", 0),
        ("too_big", "256.0.0.1", 0),
        ("empty_part", "1..3.4", 0),
        ("trailing_dot", "1.2.3.", 0),
        ("empty", "", 0),
        ("letters", "1.2.3.x", 0),
        ("too_many_digits", "0001.2.3.4", 0),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ return ok(\"{text}\"); }}"), value);
    }
}

#[test]
fn test_tcp_on_fibers() {
    let prelude = "fn echo(listener: &TcpListener) -> i32 {
    let conn = listener.accept() catch |e| return 1;
    let mut buf: [u8; 16] = @default([u8; 16]);
    let n = conn.read(&mut buf) catch |e| return 2;
    let _a = conn.write_all(\"pong\") catch |e| return 3;
    return n as i32;
}
fn client(port: u16) -> i32 {
    let conn = connect_to(\"127.0.0.1\", port) catch |e| return 90;
    let _a = conn.write_all(\"ping!\") catch |e| return 91;
    let mut buf: [u8; 16] = @default([u8; 16]);
    let n = conn.read(&mut buf) catch |e| return 92;
    return n as i32 * 10;
}
fn try_connect(port: u16) -> i32 {
    let conn = connect_to(\"127.0.0.1\", port) catch |e| match e { .Failed => return 7, .Cancelled => return 8, .TimedOut => return 9 };
    return 1;
}
fn wait_for_client(listener: &TcpListener) -> i32 {
    let conn = listener.accept() catch |e| match e { .Failed => return 3, .Cancelled => return 4, .TimedOut => return 5 };
    return 1;
}
extern fn fcntl(fd: i32, command: i32, arg: i32) -> i32;
fn closed_port() -> u16 { let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 0; return l.port(); }
";
    for (name, body, value) in [
        ("echo", "let listener = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let port = listener.port(); let server = async(Fibers { }) echo(&listener); let talk = async(Fibers { }) client(port); let a = talk.await(); return a + server.await();", 45),
        ("refused", "let t = async(Fibers { }) try_connect(closed_port()); return t.await();", 7),
        ("bad_host", "let c = connect_to(\"not.an.address\", 80) catch |e| return 7; return 1;", 7),
        ("bind_bad_host", "if let l = TcpListener::bind(\"nope\", 0) { return 1; } return 7;", 7),
        // Connecting is a wait like any other, and what it makes does not block.
        ("connect_cancelled", "let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 { return try_connect(l.port()); });", 8),
        ("stays_non_blocking", "let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let c = connect_to(\"127.0.0.1\", l.port()) catch |e| return 90; return (unsafe { fcntl(c.raw(), 3, 0) } & 2048) / 2048;", 1),
        // Only a wait can be stopped: a connection already made is not undone.
        ("accept_cancelled", "let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let t = async(Fibers { }) wait_for_client(&l); return t.cancel();", 4),
        ("accept_deadline", "let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let s = CancelScope::with_timeout_ms(5); return s.run(fn() -> i32 { let t = async(Fibers { }) wait_for_client(&l); return t.await(); });", 5),
    ] {
        assert_eq!(run_lli(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}")), Some(value), "[{name}]");
    }
}

#[test]
fn test_folding_leaves_run_time_values_alone() {
    let prelude = "const K: i32 = 9;
static mut G: i32 = 1;
static mut C: i32 = 0;
fn read_g() -> i32 { return unsafe { G }; }
fn counted() -> i32 { unsafe { C = C + 1; } return 9; }
fn pure(x: i32) -> i32 { return x * 3; }
fn Sized[T] -> i32 { return @size_of(T) as i32; }
extern fn getpid() -> i32;
fn id() -> i32 { return unsafe { getpid() }; }
";
    for (name, body, value) in [
        // A comparison with a constant must not run its other side at compile time.
        ("branch_on_a_static", "unsafe { G = 9; } if read_g() != K { return 1; } return 0;", 0),
        ("branch_equal", "unsafe { G = 9; } if read_g() == K { return 5; } return 0;", 5),
        ("value_of_a_comparison", "unsafe { G = 9; } let same = read_g() == K; return same as i32;", 1),
        ("reversed", "unsafe { G = 9; } if K != read_g() { return 1; } return 0;", 0),
        ("side_effect_happens", "let same = counted() == K; return same as i32 * 10 + unsafe { C };", 11),
        ("side_effect_in_a_branch", "if counted() != K { return 1; } return unsafe { C };", 1),
        ("logical", "unsafe { G = 9; } if read_g() == K && counted() == K { return unsafe { C } + 1; } return 0;", 2),
        // Pure code still folds.
        ("pure_call", "if pure(3) == K { return 4; } return 0;", 4),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // A branch on what can be known at compile time is still decided then: this is not compiled.
    assert_runs(
        "dead_branch",
        "fn pick[T: unchecked]() -> i32 { if T == i32 { return 1; } else { return @compile_error(\"not this one\"); } }\npub fn main() -> i32 { return pick[i32](); }",
        1,
    );
    assert_eq!(run_lli("extern_call", &format!("{prelude}pub fn main() -> i32 {{ if id() == K {{ return 1; }} return 2; }}")), Some(2));
}

#[test]
fn test_printing() {
    let run = |name: &str, body: &str| {
        let src = format!("pub struct P {{ x: i32 }}\npub fn main() -> i32 {{ {body} return 0; }}");
        let program = Compiler::compile_source(&src).unwrap_or_else(|e| panic!("[{name}] {e}"));
        let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, 222).unwrap();
        let out = crate::tests::lli(&ir);
        assert_eq!(out.status.code(), Some(0), "[{name}] {}", String::from_utf8_lossy(&out.stderr));
        (String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
    };
    for (name, body, stdout, stderr) in [
        ("integer", "let _n = println(5);", "5\n", ""),
        ("no_binding", "println(5);", "5\n", ""),
        ("variable", "let x: i32 = -12; println(x);", "-12\n", ""),
        ("string", "println(\"hi\");", "hi\n", ""),
        ("without_a_newline", "print(1); print(\"a\");", "1a", ""),
        ("print_str", "let _n = std::io::print_str(\"raw\");", "raw", ""),
        ("to_stderr", "eprint(7); eprintln(\"e\");", "", "7e\n"),
        ("owned_string", "let s = String::from(\"owned\"); println(s.as_str());", "owned\n", ""),
    ] {
        let (out, err) = run(name, body);
        assert_eq!((out.as_str(), err.as_str()), (stdout, stderr), "[{name}]");
    }
    // Nothing is cut off, however long it is.
    let long = "let mut s = String::new(); for i in 0..2000 { s.push_byte(120); }";
    for (name, body, fd_is_stdout, bytes) in [
        ("long_println", format!("{long} println(s.as_str());"), true, 2001),
        ("just_over_the_buffer", "let mut s = String::new(); for i in 0..512 { s.push_byte(120); } println(s.as_str());".to_string(), true, 513),
        ("exactly_the_buffer", "let mut s = String::new(); for i in 0..511 { s.push_byte(120); } println(s.as_str());".to_string(), true, 512),
        ("long_interpolation", format!("{long} let t = s.as_str(); print(f\"<{{t}}>\");"), true, 2002),
        ("long_eprintln", format!("{long} eprintln(s.as_str());"), false, 2001),
    ] {
        let (out, err) = run(name, &body);
        assert_eq!(if fd_is_stdout { out.len() } else { err.len() }, bytes, "[{name}]");
    }
    assert_runs(
        "format_is_whole",
        "pub fn main() -> i32 { let mut s = String::new(); for i in 0..2000 { s.push_byte(120); } let t = format(s.as_str()); return (t.len() / 100) as i32; }",
        20,
    );
}

#[test]
fn test_vec_swap() {
    for (name, body, value) in [
        ("boxes", "let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); v.push(Box[i32]::new(2)); v.swap(0, 1); return *(v.get(0) orelse unreachable).get() * 10 + *(v.get(1) orelse unreachable).get();", 21),
        ("same_index", "let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); v.swap(0, 0); return *(v.get(0) orelse unreachable).get();", 1),
        ("zero_sized", "let mut v = Vec[void]::new(); v.push(void); v.push(void); v.swap(0, 1); return v.len() as i32;", 2),
    ] {
        assert_runs(name, &format!("pub fn main() -> i32 {{ {body} }}"), value);
    }
    let out = "pub fn main() -> i32 { let mut v = Vec[i32]::new(); v.push(1); v.swap(0, 1); return 0; }";
    assert_eq!(run_lli("out_of_range", out), Some(super::TRAP_EXIT));
}

const KVSTORE: &str = include_str!("../../examples/kvstore.slop");
const WORDCOUNT: &str = include_str!("../../examples/wordcount.slop");
const SCRIPT: &str = include_str!("../../examples/script.slop");
const HTTPD: &str = include_str!("../../examples/httpd.slop");
const SERVE: &str = include_str!("../../examples/serve.slop");
const SCRIPT_OUT: &str = "line 8: division by zero
line 9: unbound variable
line 10: not a function
line 11: unexpected end
line 12: unexpected character 36
line 13: wrong arguments
14
144
-12
9
12
21
6 errors
";

/// An example compiled and run natively: its exit code and what it wrote.
fn example_natively(name: &str, src: &str) -> (Option<i32>, String) {
    let program = Compiler::compile_source(src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    native_output(&program)
}

fn native_output(program: &crate::ir::Program) -> (Option<i32>, String) {
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(program, 222).unwrap();
    let out = crate::tests::lli(&ir);
    (out.status.code(), String::from_utf8_lossy(&out.stdout).into_owned())
}

/// An example under the VM, for what it alone can see: races, leaks, and undefined behaviour.
fn example_checked(name: &str, src: &str, seed: Option<u64>) -> (i128, String) {
    let mut program = Compiler::compile_source(src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    let run = crate::tests::run_vm_long(&mut program, seed, 30_000_000)
        .unwrap_or_else(|e| panic!("[{name}, seed {seed:?}] {e}"));
    assert_eq!(run.leaks, 0, "[{name}, seed {seed:?}]");
    (run.value, run.output)
}

// Each example is a test of its own, so that they run in parallel.
#[test]
fn test_example_kvstore() {
    let (code, out) = example_natively("kvstore", KVSTORE);
    assert_eq!(code, Some(3), "{out}");
    // The clients run together, so they finish in any order.
    let mut lines: Vec<&str> = out.lines().collect();
    lines.sort();
    assert_eq!(lines, ["6 requests, 0 failures", "alpha = one", "beta = two", "gamma = three"]);
    for seed in [None, Some(1), Some(2), Some(3)] {
        let (value, out) = example_checked("kvstore", KVSTORE, seed);
        assert_eq!(value, 3);
        assert!(out.contains("6 requests, 0 failures"), "{out}");
    }
}

#[test]
fn test_example_httpd() {
    // The port it listens on differs each run.
    let without_port = |out: &str| -> String {
        out.lines().filter(|l| !l.starts_with("Port: ")).map(|l| format!("{l}\n")).collect()
    };
    let (code, out) = example_natively("httpd", HTTPD);
    assert_eq!(code, Some(0), "{out}");
    assert_eq!(without_port(&out), "4000 requests handled, 4000 hits, 0 failures\n");
    let small = HTTPD
        .replace("const CLIENTS: i32 = 200;", "const CLIENTS: i32 = 4;")
        .replace("const REQUESTS: i32 = 20;", "const REQUESTS: i32 = 5;");
    for seed in [None, Some(1), Some(2), Some(3)] {
        let (value, out) = example_checked("httpd", &small, seed);
        assert_eq!((value, without_port(&out).as_str()), (0, "20 requests handled, 20 hits, 0 failures\n"));
    }
}

#[test]
fn test_example_serve() {
    // Built natively and run on a port the system picks, it answers real connections until it
    // is stopped.
    let src = SERVE.replace("const PORT: u16 = 8080;", "const PORT: u16 = 0;");
    assert_ne!(src, SERVE, "the example declares PORT");
    let program = Compiler::compile_source(&src).unwrap_or_else(|e| panic!("{e}"));
    let ir = crate::llvm::LlvmLowering::lower(&program).unwrap();
    let bin = crate::tests::link_ir("serve", &ir);
    let mut child = std::process::Command::new(bin.path())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut first = String::new();
    std::io::BufRead::read_line(
        &mut std::io::BufReader::new(child.stdout.as_mut().unwrap()),
        &mut first,
    )
    .unwrap();
    let port: u16 = first
        .trim()
        .strip_prefix("listening on http://localhost:")
        .and_then(|p| p.strip_suffix('/'))
        .and_then(|p| p.parse().ok())
        .unwrap_or_else(|| panic!("{first}"));
    let get = |path: &str| -> String {
        use std::io::{Read, Write};
        let mut conn = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        conn.set_read_timeout(Some(std::time::Duration::from_secs(10))).unwrap();
        write!(conn, "GET {path} HTTP/1.1\r\nHost: localhost\r\n\r\n").unwrap();
        let mut reply = String::new();
        conn.read_to_string(&mut reply).unwrap();
        reply
    };
    let body = |reply: &str| reply.split_once("\r\n\r\n").map(|(_, b)| b.to_string()).unwrap_or_default();
    assert_eq!(body(&get("/hits/home")), "1\n");
    assert_eq!(body(&get("/hits/home")), "2\n");
    assert_eq!(body(&get("/hits/about")), "1\n");
    // More connections at once than it serves at a time.
    let threads: Vec<_> = (0..40).map(|_| std::thread::spawn(move || {
        use std::io::{Read, Write};
        let mut conn = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        conn.set_read_timeout(Some(std::time::Duration::from_secs(10))).unwrap();
        write!(conn, "GET /hits/load HTTP/1.1\r\n\r\n").unwrap();
        let mut reply = String::new();
        conn.read_to_string(&mut reply).unwrap();
    })).collect();
    for t in threads {
        t.join().unwrap();
    }
    assert_eq!(body(&get("/total")), "43\n");
    let missing = get("/nope");
    assert!(missing.starts_with("HTTP/1.1 404 Not Found"), "{missing}");
    assert!(get("/").contains("GET /hits/<name>"));
    child.kill().unwrap();
    let _ = child.wait();
}

#[test]
fn test_example_wordcount() {
    let (code, out) = example_natively("wordcount", WORDCOUNT);
    assert_eq!(code, Some(11), "{out}");
    assert!(out.starts_with(" 120 the\n"), "{out}");
    assert!(out.ends_with("500 words, 11 different\n"), "{out}");
    let (value, out) = example_checked("wordcount", WORDCOUNT, None);
    assert_eq!(value, 11);
    assert!(out.ends_with("500 words, 11 different\n"), "{out}");
}

#[test]
fn test_example_script() {
    let (code, out) = example_natively("script", SCRIPT);
    assert_eq!(code, Some(6), "{out}");
    assert_eq!(out, SCRIPT_OUT);
    let (value, out) = example_checked("script", SCRIPT, None);
    assert_eq!((value, out.as_str()), (6, SCRIPT_OUT));
}

/// The ledger package's modules, with its number of events replaced by `events`.
fn ledger_modules(events: &str) -> Vec<(String, String)> {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/ledger");
    Compiler::load_package_dir(&dir)
        .unwrap()
        .into_iter()
        .map(|(m, src)| (m, src.replace("const EVENTS: i32 = 3000;", events)))
        .collect()
}

fn compile_ledger(events: &str) -> crate::ir::Program {
    let modules = ledger_modules(events);
    let refs: Vec<(&str, &str)> = modules.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    Compiler::compile_package(&refs).unwrap_or_else(|e| panic!("[ledger] {e}"))
}

const REFLECT: &str = include_str!("../../examples/reflect.slop");

#[test]
fn test_example_reflect() {
    let expected = "{\"name\": \"ada\", \"age\": 36, \"active\": true, \"role\": \"Admin\", \"home\": {\"city\": \"london\", \"zip\": 1815}}
parsed: Member
changed: age
changed: home.city
{\"name\": \"ada\", \"age\": 40, \"active\": false, \"role\": \"Admin\", \"home\": {\"city\": \"london\", \"zip\": 1815}}
total of integer fields: 1851
User: 48 bytes
    0  16  name: &str
   16   4  age: i32
   20   1  active: bool
   21   1  role: Role
   24  24  home: Address
labels: london (1815), User
";
    let (code, out) = example_natively("reflect", REFLECT);
    assert_eq!((code, out.as_str()), (Some(2), expected));
    let (value, out) = example_checked("reflect", REFLECT, None);
    assert_eq!((value, out.as_str()), (2, expected));
}

#[test]
fn test_example_ledger() {
    // A package of modules.
    let (code, out) = native_output(&compile_ledger("const EVENTS: i32 = 3000;"));
    assert_eq!(code, Some(0), "{out}");
    assert_eq!(
        out,
        "account 28: 2039.87\naccount 20: 1967.79\naccount 40: 1964.26\n64 accounts, 14932 changes, 98 refused, 110882.87 held\n"
    );
}

#[test]
fn test_example_ledger_tests() {
    // Its test blocks pass, under the VM and natively.
    let ledger = ledger_modules("const EVENTS: i32 = 3000;");
    let refs: Vec<(&str, &str)> = ledger.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let outcomes = crate::testing::run_tests(&refs).unwrap();
    assert_eq!(outcomes.len(), 7);
    for o in &outcomes {
        assert_eq!(o.result, Ok(()), "[ledger test '{}']", o.name);
        assert_eq!(crate::testing::run_native(&refs, o.index), Ok(()), "[ledger test '{}', natively]", o.name);
    }
}

#[test]
fn test_example_ledger_schedules() {
    // Its numbers do not depend on how its workers interleave.
    let mut small = compile_ledger("const EVENTS: i32 = 150;");
    let (code, small_out) = native_output(&small);
    assert_eq!(code, Some(0), "{small_out}");
    for seed in [None, Some(1), Some(2), Some(3)] {
        let run = crate::tests::run_vm_long(&mut small, seed, 30_000_000)
            .unwrap_or_else(|e| panic!("[ledger, seed {seed:?}] {e}"));
        assert_eq!((run.value, run.leaks, run.output.as_str()), (0, 0, small_out.as_str()), "[ledger, seed {seed:?}]");
    }
}

#[test]
fn test_assert() {
    // `@assert(cond)` and `@assert(cond, "message")` trap unless `cond`, saying so with where
    // they are written: on stderr natively, as the error under the VM and at compile time.
    let src = "pub fn main() -> i32 {\n    let x: i32 = 3;\n    @assert(x == 3);\n    @assert(x == 4, \"x is four\");\n    return x;\n}";
    let err = super::run_vm("assert", src).unwrap_err();
    assert_eq!(err, "assertion failed: x is four (line 4, column 5)");
    let program = Compiler::compile_source(src).unwrap();
    let out = crate::tests::lli(&crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT).unwrap());
    assert_eq!(out.status.code(), Some(TRAP_EXIT));
    assert_eq!(String::from_utf8_lossy(&out.stderr), "assertion failed: x is four (line 4, column 5)\n");
    assert_runs("holds", "pub fn main() -> i32 { let x: i32 = 3; @assert(x == 3, \"three\"); return x; }", 3);
    for (name, src, message) in [
        ("at_compile_time", "fn f() -> i32 { @assert(1 == 2, \"never\"); return 1; }\nconst N: i32 = f();\npub fn main() -> i32 { return N; }", "assertion failed: never (line 1, column 17)"),
        // Without a message, the condition as written, on one line.
        ("unnamed", "fn f() -> i32 { @assert(1 + 1 == 3); return 1; }\nconst N: i32 = f();\npub fn main() -> i32 { return N; }", "assertion failed: 1 + 1 == 3 (line 1, column 17)"),
        ("over_lines", "fn f() -> i32 {\n    @assert(1 + 1\n        == 3);\n    return 1;\n}\nconst N: i32 = f();\npub fn main() -> i32 { return N; }", "assertion failed: 1 + 1 == 3 (line 2, column 5)"),
        ("not_a_bool", "pub fn main() -> i32 { @assert(1); return 0; }", "'@assert' takes a 'bool', found 'i32'"),
        ("message_is_a_literal", "pub fn main() -> i32 { let m = \"x\"; @assert(true, m); return 0; }", "the message is a string literal"),
    ] {
        assert_rejected(name, src, message);
    }
}

#[test]
fn test_test_blocks() {
    // `test "name" { ... }` blocks run one by one under the VM, which fails them on a trap, a
    // leak, or undefined behaviour; an ordinary build leaves them out.
    let root = "import root::util;
pub fn main() -> i32 { return 7; }
test \"passes\" { @assert(util::twice(2) == 4); println(\"hello from a test\"); }
test \"asserts\" { @assert(util::twice(2) == 5, \"twice two is five\"); }
test \"leaks\" { let b = Box[i32]::new(1); unsafe { @forget(b); } }
test \"overflows\" { let mut x: u8 = 255; x = x + 1; }
test \"dangles\" { let p: *mut i32 = unsafe { @raw_alloc(4) as *mut i32 }; unsafe { *p = 1; @dealloc(p); let v = *p; } }
";
    let util = "pub fn twice(n: i32) -> i32 { return n * 2; }
fn secret() -> i32 { return 9; }
test \"sees private items\" { @assert(secret() == 9); }
";
    let sources = [("root", root), ("root::util", util)];
    let outcomes = crate::testing::run_tests(&sources).unwrap();
    let results: Vec<(&str, &str, bool)> =
        outcomes.iter().map(|o| (o.module.as_str(), o.name.as_str(), o.result.is_ok())).collect();
    assert_eq!(
        results,
        [
            ("root", "passes", true),
            ("root", "asserts", false),
            ("root", "leaks", false),
            ("root", "overflows", false),
            ("root", "dangles", false),
            ("root::util", "sees private items", true),
        ]
    );
    assert_eq!(outcomes[0].output, "hello from a test\n");
    let why = |i: usize| outcomes[i].result.clone().unwrap_err();
    assert!(why(1).starts_with("assertion failed: twice two is five (line 4, column 18"), "{}", why(1));
    assert_eq!(why(2), "1 heap block(s) leaked");
    assert!(why(4).contains("Undefined behaviour"), "{}", why(4));
    let report = crate::testing::report(&outcomes);
    assert!(report.starts_with("test passes ... ok\ntest asserts ... FAILED: assertion failed"), "{report}");
    assert!(report.ends_with("test root::util: sees private items ... ok\n2 passed, 4 failed\n"), "{report}");

    // An ordinary build has no tests, and its `main` is the package's own.
    let program = Compiler::compile_package(&sources).unwrap();
    assert!(!program.functions.iter().any(|f| f.debug_name.as_deref().is_some_and(|n| n.contains("__slop_test"))));
    assert_eq!(super::run_vm_scheduled(&mut Compiler::compile_package(&sources).unwrap(), None).map(|r| r.value), Ok(7));
    // Natively, one test at a time: its own `main`, with the package's kept aside.
    let native = |index: usize| {
        let program = Compiler::compile_test_entry(&sources, index).unwrap();
        let out = crate::tests::lli(&crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT).unwrap());
        (out.status.code(), String::from_utf8_lossy(&out.stderr).into_owned())
    };
    assert_eq!(native(0).0, Some(0));
    assert_eq!(native(1), (Some(TRAP_EXIT), "assertion failed: twice two is five (line 4, column 18)\n".to_string()));
    assert_eq!(native(3).0, Some(TRAP_EXIT));
    assert_eq!(native(5).0, Some(0));
}

#[test]
fn test_slop_command() {
    // `slop run` and `slop test` on a file and on a package directory.
    let dir = std::env::temp_dir().join(format!("sloplang_cli_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("pkg/src")).unwrap();
    std::fs::write(
        dir.join("pkg/src/main.slop"),
        "import root::shapes;\npub fn main() -> i32 { println(\"area\"); return shapes::area(2, 3); }\ntest \"area\" { @assert(shapes::area(2, 3) == 6); }\ntest \"area of nothing\" { @assert(shapes::area(0, 3) == 1, \"zero by three\"); }\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("pkg/src/shapes.slop"),
        "pub fn area(w: i32, h: i32) -> i32 { return w * h; }\ntest \"squares\" { @assert(area(4, 4) == 16); }\n",
    )
    .unwrap();
    std::fs::write(dir.join("leaks.slop"), "pub fn main() -> i32 { let b = Box[i32]::new(1); unsafe { @forget(b); } return 0; }").unwrap();
    let slop = |args: &[&str]| {
        let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let code = crate::cli::main_with(&args, &mut out, &mut err);
        (code, String::from_utf8(out).unwrap(), String::from_utf8(err).unwrap())
    };
    let pkg = dir.join("pkg").to_string_lossy().into_owned();
    // `run`: what `main` wrote, and what it returned as the status.
    // `run` builds it natively; `run --vm` runs it under the VM. Both give its output and status.
    assert_eq!(slop(&["run", &pkg]), (6, "area\n".to_string(), String::new()));
    assert_eq!(slop(&["run", "--vm", &pkg]), (6, "area\n".to_string(), String::new()));
    // The program's stdout and stderr go to their own streams, as they are written.
    std::fs::write(dir.join("streams.slop"), "pub fn main() -> i32 { println(\"out\"); eprintln(\"err\"); return 3; }").unwrap();
    let streams = dir.join("streams.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["run", &streams]), (3, "out\n".to_string(), "err\n".to_string()));
    assert_eq!(slop(&["run", &streams, "--vm"]), (3, "out\n".to_string(), "err\n".to_string()));
    // A failed check traps natively, which `run` reports.
    std::fs::write(dir.join("traps.slop"), "fn at(a: &[i32], i: usize) -> i32 { return a[i]; }\npub fn main() -> i32 { let v: [i32; 2] = { 1, 2 }; println(\"before\"); return at(&v, 5); }").unwrap();
    let traps = dir.join("traps.slop").to_string_lossy().into_owned();
    let (code, output, error) = slop(&["run", &traps]);
    assert_eq!((code, output.as_str()), (crate::cli::FAILED, "before\n"));
    assert!(error.starts_with("error: the program trapped: a check failed"), "{error}");
    let leaks = dir.join("leaks.slop").to_string_lossy().into_owned();
    // Only the VM sees a leak.
    assert_eq!(slop(&["run", "--vm", &leaks]), (crate::cli::FAILED, String::new(), "error: 1 heap block(s) leaked\n".to_string()));
    assert_eq!(slop(&["run", &leaks]).0, 0);
    // `test`: every test, in module order, on however many threads.
    let report = "test area ... ok\ntest area of nothing ... FAILED: assertion failed: zero by three (line 4, column 26)\ntest root::shapes: squares ... ok\n2 passed, 1 failed\n";
    for jobs in ["1", "3"] {
        assert_eq!(slop(&["test", &pkg, "--jobs", jobs]), (1, report.to_string(), String::new()), "--jobs {jobs}");
    }
    assert_eq!(slop(&["test", &pkg, "--filter", "squares"]), (0, "test root::shapes: squares ... ok\n1 passed, 0 failed\n".to_string(), String::new()));
    assert_eq!(slop(&["test", &pkg, "--filter", "shapes: sq"]).0, 0);
    // Natively too: what passes under the VM must pass as compiled code.
    assert_eq!(slop(&["test", &pkg, "--native", "--jobs", "2"]), (1, report.to_string(), String::new()));
    let pkg_sources = Compiler::load_package_dir(&dir.join("pkg")).unwrap();
    let refs: Vec<(&str, &str)> = pkg_sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    assert_eq!(crate::testing::run_native(&refs, 0), Ok(()));
    assert_eq!(
        crate::testing::run_native(&refs, 1),
        Err("natively, trapped: assertion failed: zero by three (line 4, column 26)".to_string())
    );
    // `build`: an executable (with `clang`), or the LLVM IR.
    let exe = dir.join("shapes").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &pkg, "-o", &exe, "-O1"]), (0, format!("built {exe}\n"), String::new()));
    let ran = std::process::Command::new(&exe).output().unwrap();
    assert_eq!((ran.status.code(), String::from_utf8_lossy(&ran.stdout).into_owned()), (Some(6), "area\n".to_string()));
    let ll = dir.join("shapes.ll").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &pkg, "--emit", "ll", "-o", &ll]).0, 0);
    assert!(std::fs::read_to_string(&ll).unwrap().contains("define"), "LLVM IR");
    assert!(slop(&["build", &pkg, "--emit", "wasm"]).2.contains("expected 'exe', 'll', or 'h'"));
    // `--emit h`: the C declarations of what a package exports.
    std::fs::write(
        dir.join("exports.slop"),
        "export error ParseError { Empty }\nexport fn half(n: usize) -> ParseError!usize { if n == 0 { return .Empty; } return n / 2; }\n",
    )
    .unwrap();
    let exports = dir.join("exports.slop").to_string_lossy().into_owned();
    let h = dir.join("exports.h").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &exports, "--emit", "h", "-o", &h]), (0, format!("wrote {h}\n"), String::new()));
    let header = std::fs::read_to_string(&h).unwrap();
    assert!(header.contains("ParseError half(size_t n, /* out */ size_t* out_val);"), "{header}");
    assert!(header.contains("#ifndef SLOPLANG_EXPORT_H"), "{header}");
    let onto_a_directory = dir.join("pkg").to_string_lossy().into_owned();
    assert!(slop(&["build", &pkg, "-o", &onto_a_directory]).2.contains("is a directory; name the executable with '-o'"));
    // `new`: a package that runs, tests, and builds as it is.
    let fresh = dir.join("fresh").to_string_lossy().into_owned();
    assert_eq!(slop(&["new", &fresh]), (0, format!("created package 'fresh' in {fresh}\n"), String::new()));
    assert_eq!(slop(&["run", &fresh]), (0, "hello\n".to_string(), String::new()));
    assert_eq!(slop(&["test", &fresh]), (0, "test greets ... ok\n1 passed, 0 failed\n".to_string(), String::new()));
    assert!(slop(&["new", &fresh]).2.contains("exists already"));
    // `check`: everything `test` and `build` compile, tests included, running nothing; a library
    // needs no `main`. Warnings are printed, by every command.
    assert_eq!(slop(&["check", &pkg]), (0, "checked pkg (3 tests)\n".to_string(), String::new()));
    std::fs::write(dir.join("library.slop"), "pub fn area(w: i32, h: i32) -> i32 { return w * h; }\n").unwrap();
    let library = dir.join("library.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["check", &library]), (0, "checked library (0 tests)\n".to_string(), String::new()));
    assert_eq!(slop(&["run", &library]).2, "error: the package has no 'main'\n");
    std::fs::write(dir.join("bad_test.slop"), "pub fn main() -> i32 { return 0; }\ntest \"t\" { let x: bool = 5; }\n").unwrap();
    let bad_test = dir.join("bad_test.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["run", &bad_test]).0, 0, "run leaves tests out");
    let (code, _, err) = slop(&["check", &bad_test]);
    assert_eq!((code, err.as_str()), (crate::cli::FAILED, "error: Type mismatch: cannot implicitly convert 'i32' to 'bool' (line 2, column 12)\n"));
    std::fs::write(
        dir.join("warned.slop"),
        "opaque(owns T) Holder[T] { p: *own T }\npub fn main() -> i32 { let h: ?Holder[i32] = null; return 0; }\n",
    )
    .unwrap();
    let warned = dir.join("warned.slop").to_string_lossy().into_owned();
    let warning = "warning: 'owns T' on opaque 'Holder' is redundant: a field already holds 'T' behind '*own' or in 'uninit' storage\n";
    assert_eq!(slop(&["check", &warned]), (0, "checked warned (0 tests)\n".to_string(), warning.to_string()));
    assert_eq!(slop(&["run", &warned]), (0, String::new(), warning.to_string()));
    assert_eq!(slop(&["test", &warned]).2, warning);
    // A generic is linted where it is declared, used or not.
    std::fs::write(dir.join("unused.slop"), "opaque(owns T) Holder[T] { p: *own T }\npub fn main() -> i32 { return 0; }\n").unwrap();
    let unused = dir.join("unused.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["check", &unused]), (0, "checked unused (0 tests)\n".to_string(), warning.to_string()));
    // `check --all-targets`: for each C ABI the backend knows. Fibers switch stacks on x86-64
    // only, which a check on this machine alone would not show.
    assert_eq!(
        slop(&["check", &library, "--all-targets"]),
        (0, "checked library (0 tests) for x86_64-linux, aarch64-linux, aarch64-macos, riscv64-linux\n".to_string(), String::new())
    );
    std::fs::write(dir.join("fibers.slop"), "fn one() -> i32 { return 1; }\npub fn main() -> i32 { let t = async(Fibers { }) one(); return t.await(); }\n").unwrap();
    let fibers = dir.join("fibers.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["check", &fibers]).0, 0);
    assert_eq!(
        slop(&["check", "--all-targets", &fibers]),
        (
            crate::cli::FAILED,
            "checked fibers (0 tests) for x86_64-linux\n".to_string(),
            "error: for aarch64-linux: Fibers switch stacks only on x86-64\nerror: for aarch64-macos: Fibers switch stacks only on x86-64\nerror: for riscv64-linux: Fibers switch stacks only on x86-64\n".to_string()
        )
    );
    // A target its manifest refuses is not built for, and not an error.
    std::fs::create_dir_all(dir.join("linux_only/src")).unwrap();
    std::fs::write(dir.join("linux_only/src/main.slop"), "pub fn main() -> i32 { return 0; }\n").unwrap();
    std::fs::write(
        dir.join("linux_only/package.slop"),
        "import std::build::{Package, Target, Dependency};
pub fn package[target: Target]() -> Package {
    if target.os != Target::Os::Linux { @compile_error(\"Linux only\"); }
    return Package { name: \"linux_only\", version: { 1, 0, 0 }, root: \"src/main.slop\", no_std: false, deps: &[], system_libs: &[] };
}",
    )
    .unwrap();
    let linux_only = dir.join("linux_only").to_string_lossy().into_owned();
    assert_eq!(
        slop(&["check", &linux_only, "--all-targets"]),
        (0, "checked linux_only (0 tests) for x86_64-linux, aarch64-linux, riscv64-linux\nnot built for aarch64-macos\n".to_string(), String::new())
    );
    // `fmt`: what changes is rewritten; `--check` lists it and fails, changing nothing.
    std::fs::write(dir.join("messy.slop"), "pub fn main() -> i32 {\nlet x = 1;\n\t\treturn x;   \n}\n\n\n").unwrap();
    let messy = dir.join("messy.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["fmt", &messy, "--check"]), (1, format!("would format {messy}\n"), String::new()));
    assert_eq!(slop(&["fmt", &messy]), (0, format!("formatted {messy}\n"), String::new()));
    assert_eq!(std::fs::read_to_string(dir.join("messy.slop")).unwrap(), "pub fn main() -> i32 {\n    let x = 1;\n    return x;\n}\n");
    assert_eq!(slop(&["fmt", &messy, "--check"]), (0, String::new(), String::new()));
    assert_eq!(slop(&["fmt", &pkg, "--check"]).0, 0, "a package's files");
    // Wrong use says how to use it.
    let (code, _, err) = slop(&["build"]);
    assert_eq!(code, crate::cli::FAILED);
    assert!(err.starts_with("error: usage: slop new <dir>"), "{err}");
    assert!(slop(&["test", &pkg, "--jobs", "many"]).2.contains("'--jobs many' is not a count"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_slop_reads_package_manifests() {
    // A package's `package.slop`, evaluated for the host: its name names the executable, its
    // system libraries are linked, `no_std` compiles it freestanding, and what slop cannot do
    // yet (fetch dependencies) is an error.
    let dir = std::env::temp_dir().join(format!("sloplang_manifest_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let manifest = |name: &str, extra: &str| {
        format!("import std::build::{{Package, Target, Dependency}};
pub fn package[target: Target]() -> Package {{
    return Package {{ name: \"{name}\", version: {{ 0, 1, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[], system_libs: &[] {extra} }};
}}")
    };
    let make = |pkg: &str, manifest_src: String, main: &str| {
        std::fs::create_dir_all(dir.join(pkg).join("src")).unwrap();
        std::fs::write(dir.join(pkg).join("package.slop"), manifest_src).unwrap();
        std::fs::write(dir.join(pkg).join("src/main.slop"), main).unwrap();
        dir.join(pkg).to_string_lossy().into_owned()
    };
    let slop = |args: &[&str]| {
        let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let code = crate::cli::main_with(&args, &mut out, &mut err);
        (code, String::from_utf8(out).unwrap(), String::from_utf8(err).unwrap())
    };
    let main = "pub fn main() -> i32 { return 5; }\ntest \"five\" { @assert(main() == 5); }";
    let plain = make("plain", manifest("geometry", ""), main);
    // What is built is named after the package, not the directory.
    let package = crate::cli::load(&plain, "Debug").unwrap();
    assert_eq!((package.name.as_str(), package.no_std, package.system_libs.len()), ("geometry", false, 0));
    let exe = dir.join("geometry").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &plain, "-o", &exe]), (0, format!("built {exe}\n"), String::new()));
    assert_eq!(std::process::Command::new(&exe).status().unwrap().code(), Some(5));
    assert_eq!(slop(&["test", &plain]).0, 0);
    // Its system libraries reach the link: one that does not exist fails it.
    let libs = make("libs", manifest("linked", ", system_libs: &[\"slop_no_such_lib\"]").replace("system_libs: &[] ,", ""), main);
    assert_eq!(crate::cli::load(&libs, "Debug").unwrap().system_libs, ["slop_no_such_lib"]);
    let linked = dir.join("linked").to_string_lossy().into_owned();
    let (code, _, err) = slop(&["build", &libs, "-o", &linked]);
    assert_eq!(code, crate::cli::FAILED);
    assert!(err.contains("slop_no_such_lib"), "{err}");
    // `no_std`: freestanding, with `core` only.
    let free = make("free", manifest("free", "").replace("no_std: false", "no_std: true"), "pub fn main() -> i32 { return 3; }");
    assert_eq!(slop(&["run", &free]).0, 3);
    let needs_std = make("needs_std", manifest("needs_std", "").replace("no_std: false", "no_std: true"), "pub fn main() -> i32 { println(\"x\"); return 0; }");
    assert_eq!(slop(&["run", &needs_std]).0, crate::cli::FAILED);
    // A dependency that is not where its manifest says.
    let deps = make("deps", manifest("deps", "").replace("deps: &[]", "deps: &[Dependency { name: \"tls\", url: \"missing.tar\", sha256: 1_u256 }]"), main);
    assert!(slop(&["run", &deps]).2.contains("missing.tar"), "{:?}", slop(&["run", &deps]));
    let rooted = make("rooted", manifest("rooted", "").replace("src/main.slop", "lib/app.slop"), main);
    assert!(slop(&["run", &rooted]).2.contains("has root 'lib/app.slop'"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_zero_defaults_are_one_store() {
    // A default that is all zero bytes is one `zeroinitializer` store, not one per element.
    let src = "pub fn main() -> i32 { let mut buf: [u8; 4096] = @default([u8; 4096]); buf[7] = 3; return buf[7] as i32 + buf[4095] as i32; }";
    let program = Compiler::compile_source(src).unwrap();
    let ir = crate::llvm::LlvmLowering::lower(&program).unwrap();
    assert!(ir.contains("store [4096 x i8] zeroinitializer"), "{ir}");
    assert!(ir.lines().count() < 200, "{} lines", ir.lines().count());
    assert_runs("bytes", src, 3);
    for (name, body, value) in [
        ("nested", "let g: [[i32; 8]; 8] = @default([[i32; 8]; 8]); return g[7][7] + 1;", 1),
        ("tuple_of_floats", "let t: tuple { f64, bool, [i64; 3] } = @default(tuple { f64, bool, [i64; 3] }); if t.0 == 0.0 && !t.1 { return t.2[2] as i32 + 2; } return 9;", 2),
        // A field's own default keeps it from being all zeros.
        ("field_default", "let p: [P; 2] = @default([P; 2]); return p[1].x;", 5),
    ] {
        assert_runs(name, &format!("struct P {{ x: i32 = 5, y: i32 }}\npub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_linear_types_need_opting_in() {
    // A type parameter takes linear types only when its bound says `?linear`; a generic that
    // does not say so may drop what it is given. One that does is checked as if it were given a
    // linear type, so it is refused where it is written if it may drop one.
    let decls = format!("{TX}fn pass[T: ?linear](x: T) -> T {{ return x; }}
fn tag[T](x: T) -> tuple {{ i32, T }} {{ return {{ 1, x }}; }}
fn tag[T: ?linear](x: T) -> tuple {{ i32, T }} {{ return {{ 2, x }}; }}
trait Named {{ fn name(self: &Self) -> i32; }}
impl Named for Tx {{ fn name(self: &Self) -> i32 {{ return 7; }} }}
fn named[T: Named + ?linear](x: &T) -> i32 {{ return x.name(); }}
fn named_plain[T: Named](x: &T) -> i32 {{ return x.name(); }}
fn unasked[T: sync](x: &T) -> i32 {{ return 1; }}
fn Cell[T: ?linear] -> type {{ return opaque {{ v: T, pub fn new(v: T) -> Self {{ return Self {{ v: move v }}; }} pub fn take(move self) -> T {{ return self.v; }} }}; }}
");
    for (name, body, value) in [
        ("passed_through", "let t = pass(Tx::new(3)); return t.commit();", 3),
        ("not_linear_too", "let n: i32 = 4; return pass(n);", 4),
        // `[T]` is the more specific of the two, for a type that can be dropped.
        ("plain_preferred", "let n: i32 = 0; let { a, m } = tag(n); let { b, t } = tag(Tx::new(0)); return a * 10 + b + t.commit();", 12),
        // One that holds no `T` by value cannot drop one, so it takes linear types unasked.
        ("value_free", "let t = Tx::new(3); let k = unasked(&t); return k + t.commit();", 4),
        ("with_a_trait", "let t = Tx::new(0); return named(&t) + t.commit();", 7),
        ("a_type_function", "let c = Cell[Tx]::new(Tx::new(5)); let t = c.take(); return t.commit();", 5),
        ("in_std", "let mut v = Vec[Tx]::new(); v.push(Tx::new(6)); let mut n: i32 = 0; v.drain(fn(t: Tx) { n = n + t.commit(); }); return n;", 6),
        // An emptied vector of linear values is consumed by `finish`; inline storage too.
        ("finished", "let mut v = Vec[Tx]::new(); v.push(Tx::new(7)); let t = v.pop() orelse unreachable; v.finish(); return t.commit();", 7),
        ("inline_finished", "let mut v = ArrayVec[Tx, 2]::new(); v.push(Tx::new(8)); let t = v.pop() orelse unreachable; v.finish(); return t.commit();", 8),
        ("inline_drained", "let mut v = ArrayVec[Tx, 2]::new(); v.push(Tx::new(4)); v.push(Tx::new(5)); let mut n: i32 = 0; v.drain(fn(t: Tx) { n = n + t.commit(); }); return n;", 9),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // `finish` on a vector that is not empty would lose what it holds.
    let full = format!("{decls}pub fn main() -> i32 {{ let mut v = Vec[i32]::new(); v.push(1); v.finish(); return 0; }}");
    let err = super::run_vm("finish_full", &full).map(|r| r.value).unwrap_err();
    assert!(err.contains("Vec::finish on a vector that is not empty"), "{err}");
    let because = "Type 'Tx' is linear, and a type parameter takes linear types only when its bound says '?linear'";
    for (name, src, message) in [
        ("plain", "fn keep[T](x: T) -> T { return x; }\npub fn main() -> i32 { let t = keep(Tx::new(1)); return t.commit(); }", because),
        ("a_trait_alone", "pub fn main() -> i32 { let t = Tx::new(1); return named_plain(&t) + t.commit(); }", because),
        ("a_plain_type_function", "fn Plain[T] -> type { return opaque { v: T }; }\npub fn main() -> i32 { let p: ?*mut Plain[Tx] = null; return 0; }", because),
        // Saying `?linear` holds the body to it, used or not.
        ("drops_one", "fn lose[T: ?linear](x: T) -> i32 { return 1; }\npub fn main() -> i32 { return 0; }", "Generic 'root::lose' uses its type parameters beyond what their bounds promise: Linear value 'x' of type 'T' must be explicitly consumed"),
        // ... and is held to that: one that moves a `T` out of a pointer must consume it.
        ("value_free_drops_one", "fn lose[T](p: *mut T) -> i32 { unsafe { let v = move *p; } return 1; }\npub fn main() -> i32 { return 0; }", "Generic 'root::lose' uses its type parameters beyond what their bounds promise: Linear value 'v' of type 'T' must be explicitly consumed"),
    ] {
        assert_rejected(name, &format!("{decls}{src}"), message);
    }
}

#[test]
fn test_unsized_types_need_opting_in() {
    // An unsized type (bare `opaque`, an `extern opaque` handle) is taken by a type parameter only
    // when its bound says `?sized`; under it the generic check models `T` as unsized, so the body
    // may use a `T` only behind a pointer.
    let decls = "pub extern opaque Db;
fn same[T: ?sized](p: *const T) -> *const T { return p; }
fn tag[T: copy](p: &T) -> i32 { return 1; }
fn tag[T: ?sized](p: *const T) -> i32 { return 2; }
fn both[T: ?sized + ?linear](p: *const T) -> i32 { return 3; }
";
    let db = "let n: u8 = 0; let q = &n as *const u8 as *const Db;";
    for (name, body, value) in [
        ("a_handle", &*format!("{db} let r = same(q); return 1;"), 1),
        ("sized_too", "let n: i32 = 4; let r = same(&n as *const i32); return n;", 4),
        // `[T: copy]` is the more specific of the two, for a sized type.
        ("narrower_preferred", "let n: i32 = 0; return tag(&n);", 1),
        ("with_linear", &*format!("{db} return both(q);"), 3),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    let because = "Type 'Db' is unsized, and a type parameter takes unsized types only when its bound says '?sized'";
    for (name, src, message) in [
        ("plain", format!("fn keep[T](p: *const T) -> i32 {{ return 0; }}\npub fn main() -> i32 {{ {db} return keep(q); }}"), because),
        ("in_std", "pub fn main() -> i32 { let v = Vec[Db]::new(); return 0; }".to_string(), because),
        // Saying `?sized` holds the body to it, used or not.
        ("by_value", "fn hold[T: ?sized](x: T) -> i32 { return 0; }\npub fn main() -> i32 { return 0; }".to_string(), "Unsized type 'T' cannot be passed by value in parameter 'x' of 'hold'"),
        ("its_size", "fn size[T: ?sized]() -> usize { return @size_of(T); }\npub fn main() -> i32 { return 0; }".to_string(), "Cannot use unsized opaque type 'T' in '@size_of'"),
    ] {
        assert_rejected(name, &format!("{decls}{src}"), message);
    }
}

#[test]
fn test_tour() {
    // Each `slop` block in TOUR.md runs, under the VM and natively, and its `main` returns 0;
    // each `slop rejected` block is refused with what its first line, `// error: ...`, says.
    let tour = include_str!("../../TOUR.md");
    let mut blocks = 0;
    let mut lines = tour.lines().enumerate();
    while let Some((at, line)) = lines.next() {
        let Some(info) = line.strip_prefix("```slop") else { continue };
        let body: Vec<&str> = lines.by_ref().map(|(_, l)| l).take_while(|l| *l != "```").collect();
        let src = body.join("\n");
        let name = format!("TOUR.md line {}", at + 1);
        match info.trim() {
            "" => assert_runs(&name, &src, 0),
            "rejected" => {
                let what = body[0].strip_prefix("// error: ").unwrap_or_else(|| panic!("[{name}] starts with '// error: '"));
                assert_rejected(&name, &src, what);
            }
            other => panic!("[{name}] unknown block kind '{other}'"),
        }
        blocks += 1;
    }
    assert!(blocks >= 10, "{blocks} blocks");
}

#[test]
fn test_readme() {
    // Every `slop` block in README.md compiles and runs (or, for the C FFI library block without
    // `main`, compiles and emits the documented C header declarations).
    let readme = include_str!("../../README.md");
    let mut blocks = 0;
    let mut lines = readme.lines().enumerate();
    while let Some((at, line)) = lines.next() {
        let Some(info) = line.strip_prefix("```slop") else { continue };
        let body: Vec<&str> = lines.by_ref().map(|(_, l)| l).take_while(|l| *l != "```").collect();
        let src = body.join("\n");
        let name = format!("README.md line {}", at + 1);
        assert_eq!(info.trim(), "", "[{name}] unexpected block kind '{info}'");
        if src.contains("pub fn main()") {
            assert_runs(&name, &src, 0);
        } else {
            let (prog, header) = crate::lower::Compiler::compile_source_with_c_header(&src)
                .unwrap_or_else(|e| panic!("[{name}] failed to compile: {e}"));
            crate::llvm::LlvmLowering::lower(&prog)
                .unwrap_or_else(|e| panic!("[{name}] failed to lower to LLVM IR: {e}"));
            assert!(header.contains("bool digit_value(uint8_t c, /* out */ uint8_t* out_val);"), "{header}");
            assert!(header.contains("ParseError parse_u32(const uint8_t* s, size_t len, /* out */ uint32_t* out_val);"), "{header}");
        }
        blocks += 1;
    }
    assert!(blocks >= 10, "{blocks} blocks");
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
fn test_comptime_values_at_run_time() {
    // What `comptime for` binds is usable at run time: in a format string, and, for a list such
    // as a field path, as a static slice.
    let decls = "struct In { a: i32, b: i32 }\nstruct Out { x: i32, inner: In }
fn depth(path: &[&str]) -> usize { return path.len; }
fn names[T: struct]() -> String { let mut s = String::new(); comptime for f in @fields(T) { s.push_str(format(f\"{f.name}:{@size_of(f.ty)} \").as_str()); } return s; }
fn leaf_depths[T: struct]() -> usize { let mut n: usize = 0; comptime for p in @leaves(T) { n = n * 10 + depth(p); } return n; }
";
    for (name, body, value) in [
        ("in_a_format_string", "let s = names[Out](); if s.as_str() == \"x:4 inner:8 \" { return 1; } return 0;", 1),
        ("a_path_as_a_slice", "return leaf_depths[Out]() as i32;", 122),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_inference_through_optionals() {
    // A value that is not optional, given to a `?T` parameter, is a `T`, and infers `T` so.
    let decls = "fn opt[T](x: ?&T) -> i32 { if let r = x { return 4; } return 0; }\nfn wrap[T](x: ?T) -> i32 { if let v = x { return 6; } return 0; }\nfn named[T](label: &str, x: &T) -> i32 { return 7; }\n";
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
        ("same_element", "let a: [i32; 3] = zeroinit; let p = &a[1] as *const i32; let q = &a[1] as *const i32; if p == q { return 1; } return 2;", 1),
        ("ordered", "let a: [i32; 3] = zeroinit; let p = &a[0] as *const i32; let q = &a[2] as *const i32; if p != q && p < q && q >= p { return 1; } return 2;", 1),
        ("zero_sized", "let a: [void; 3] = zeroinit; let p = &a[0] as *const void; let q = &a[2] as *const void; if p == q { return 1; } return 2;", 1),
        ("separate", "let x: i32 = 1; let y: i32 = 2; let p = &x as *const i32; let q = &y as *const i32; if p != q { return 1; } return 2;", 1),
        ("moved_and_back", "let b = Box[i32]::new(1); let p = b.get() as *const i32; let q = p + 1; let ok = p == q - 1 && p < q; let n = b.into_inner(); if ok { return n; } return 2;", 1),
        // A vector of a zero-sized type holds no memory, and counts.
        ("vec_of_void", "let mut v = Vec[void]::new(); for i in 0..100 { v.push(void); } let mut n: i32 = 0; while let x = v.pop() { n = n + 1; } return n + @size_of([void; 1000]) as i32;", 100),
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
pub opaque Counter {{ n: i32, pub fn new() -> Self {{ return Self {{ n: 0 }}; }} pub fn bump(self: &mut Self) -> i32 discardable {{ self.n = self.n + 1; return self.n; }} }}
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
pub opaque Loud {{ n: i32, impl drop {{ fn drop(self: &mut Self) {{ unsafe {{ LOG = LOG * 10 + self.n; }} }} }} pub fn new(n: i32) -> Self {{ return Self {{ n: n }}; }} }}
fn log() -> i32 {{ return unsafe {{ LOG }}; }}
");
    for (name, body, value) in [
        ("dropped_at_once", "let _ = Loud::new(1); let k = Loud::new(2); return log();", 1),
        ("assigned", "_ = Loud::new(3); let k = Loud::new(2); return log();", 3),
        ("a_named_one_lives", "let _a = Loud::new(1); let k = Loud::new(2); return log();", 0),
        ("in_a_pattern", "let { a, _ } = { Loud::new(1), Loud::new(2) }; return log();", 2),
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
        ("linear_in_a_pattern", "let { t, _ } = { Tx::new(1), Tx::new(2) }; return t.commit();"),
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
fn test_callable_signatures() {
    // `callable(A, B) -> R` bounds a parameter to functions and closures called so, and its
    // generic is held to calling it so.
    let decls = "fn apply[F: callable(i32) -> i32](f: F) -> i32 { return f(3); }
fn best[T: copy, F: callable(&T, &T) -> bool](a: T, b: T, before: F) -> T { if before(&a, &b) { return a; } return b; }
fn dbl(x: i32) -> i32 { return x * 2; }
";
    for (name, body, value) in [
        ("a_function", "return apply(dbl);", 6),
        ("a_closure", "let k: i32 = 4; return apply(fn(x: i32) -> i32 { return x + k; });", 7),
        ("naming_another_parameter", "let a: i32 = 3; let b: i32 = 5; return best(a, b, fn(x: &i32, y: &i32) -> bool { return *x > *y; });", 5),
        ("std_sort_by", "let mut v = Vec[i32]::new(); v.push(2); v.push(9); v.push(4); v.sort_by(fn(a: &i32, b: &i32) -> bool { return *a > *b; }); return *(v.get(0) orelse unreachable);", 9),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, src, message) in [
        ("wrong_signature", "pub fn main() -> i32 { return apply(fn(x: i64) -> i32 { return 1; }); }", "Type 'fn(i64) -> i32' cannot be called as 'fn(i32) -> i32'"),
        ("beyond_the_signature", "fn bad[F: callable(i32) -> i32](f: F) -> i32 { return f(true); }\npub fn main() -> i32 { return 0; }", "Generic 'root::bad' uses its type parameters beyond"),
        ("std_sort_by_wrong", "pub fn main() -> i32 { let mut v = Vec[i32]::new(); v.sort_by(fn(a: &i32) -> bool { return true; }); return 0; }", "cannot be called as"),
        // A function pointer is called with as many arguments as it takes.
        ("too_many_arguments", "fn g(f: fn(i32) -> i32) -> i32 { return f(3, 4); }\npub fn main() -> i32 { return 0; }", "'f', of type 'fn(i32) -> i32', takes 1 argument(s), given 2"),
        ("too_few_arguments", "fn g(f: fn(i32, i32) -> i32) -> i32 { return f(3); }\npub fn main() -> i32 { return 0; }", "takes 2 argument(s), given 1"),
        ("closure_arity", "pub fn main() -> i32 { let c = fn(x: i32) -> i32 { return x; }; return c(1, 2); }", "argument"),
    ] {
        assert_rejected(name, &format!("{decls}{src}"), message);
    }
}

#[test]
fn test_trait_default_methods() {
    // A trait method with a body is what an implementation that leaves it out does, so a trait
    // can grow a method without breaking its implementors.
    let decls = "trait Shape { fn area(self: &Self) -> i32; fn twice(self: &Self) -> i32 { return self.area() * 2; } }
trait Greets { fn hello(self: &Self) -> i32 { return 1; } }
struct Sq { s: i32, pub fn name(self: &Self) -> i32 { return 5; } }
fn generic[T: Shape](x: &T) -> i32 { return x.twice(); }
fn through_object(s: &Shape) -> i32 { return s.twice(); }
";
    for (name, body, value) in [
        ("default", "impl Shape for Sq { fn area(self: &Self) -> i32 { return self.s * self.s; } }\npub fn main() -> i32 { let q = Sq { s: 3 }; return q.twice(); }", 18),
        ("overridden", "impl Shape for Sq { fn area(self: &Self) -> i32 { return 1; } fn twice(self: &Self) -> i32 { return 7; } }\npub fn main() -> i32 { let q = Sq { s: 3 }; return q.twice(); }", 7),
        ("generic_and_object", "impl Shape for Sq { fn area(self: &Self) -> i32 { return 4; } }\npub fn main() -> i32 { let q = Sq { s: 3 }; return generic(&q) + through_object(&q); }", 16),
        ("every_method_defaulted", "opaque B { impl Greets { } pub fn new() -> Self { return Self { }; } }\nfn greet[T: Greets](x: &T) -> i32 { return x.hello(); }\npub fn main() -> i32 { let b = B::new(); return greet(&b) + b.hello(); }", 2),
    ] {
        assert_runs(name, &format!("{decls}{body}"), value);
    }
    for (name, src, message) in [
        ("not_in_a_structural_trait", "trait(structural) Named { fn name(self: &Self) -> i32; fn tag(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { return 0; }", "a structural trait is met by the type's own methods"),
        ("required_still_required", "impl Shape for Sq { }\npub fn main() -> i32 { return 0; }", "is missing trait method 'area'"),
        // A default is checked where it is written, against what the trait promises.
        ("default_beyond_the_trait", "trait Bad { fn a(self: &Self) -> i32; fn b(self: &Self) -> i32 { return self.c(); } }\npub fn main() -> i32 { return 0; }", "Default method 'Bad::b'"),
    ] {
        assert_rejected(name, &format!("{decls}{src}"), message);
    }
}

#[test]
fn test_zeroinit() {
    // `zeroinit` types have all-zero bytes as a value; the `zeroinit` literal is that value, in
    // one store, and `Vec::zeroed` makes a vector of them.
    let src = "pub fn main() -> i32 { let b: [u8; 4096] = zeroinit; return b[4095] as i32; }";
    let ir = crate::llvm::LlvmLowering::lower(&Compiler::compile_source(src).unwrap()).unwrap();
    assert!(ir.contains("store [4096 x i8] zeroinitializer") && ir.lines().count() < 200);
    let decls = "opaque(unsafe zeroinit) Counter { n: u32, pub fn n(self: &Self) -> u32 { return self.n; } }
enum Level { Off = 0, On = 1 }
fn fill[T: zeroinit]() -> [T; 4] { return zeroinit; }
fn probe[T: unchecked]() -> i32 { if @satisfies(T, zeroinit) { return 1; } return 0; }
";
    for (name, body, value) in [
        ("scalars_and_arrays", "let b: [u8; 64] = zeroinit; let f: tuple { f64, bool, rune } = zeroinit; if f.0 == 0.0 && !f.1 { return b[63] as i32 + 1; } return 9;", 1),
        // Zero is `null` for an optional, and the variant of value 0 for an enum.
        ("null_and_enums", "let z: ?&i32 = zeroinit; let l: Level = zeroinit; if z == null && l == Level::Off { return 2; } return 9;", 2),
        ("an_opaque_that_says_so", "let c: Counter = zeroinit; return c.n() as i32 + 3;", 3),
        ("generic", "let a = fill[u16](); return a[3] as i32 + 4;", 4),
        ("vec_zeroed", "let v = Vec[i64]::zeroed(10); return v.len() as i32 + *(v.get(9) orelse unreachable) as i32;", 10),
        ("satisfies", "return probe[u8]() * 8 + probe[Counter]() * 4 + probe[&i32]() * 2 + probe[String]();", 12),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // Zeroed allocation: `calloc` for the default allocator; an allocator that writes no
    // `alloc_zeroed` gets the trait's (`alloc`, then zeros), as does a program allocator.
    let counted = "static mut ALLOCS: i32 = 0;
pub struct Counted { }
unsafe impl Allocator for Counted {
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 { unsafe { ALLOCS = ALLOCS + 1; } return @raw_alloc(bytes); }
    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return unsafe { @realloc(u8, ptr, bytes) }; }
    fn dealloc(self: &Self, ptr: *mut u8) { unsafe { @dealloc(ptr); } }
}
";
    for (name, src, value) in [
        ("raw_zeroed_bytes", "pub fn main() -> i32 { let p = @raw_alloc_zeroed(16); let b = unsafe { *(p + 3) }; unsafe { @dealloc(p); } return b as i32 + 1; }".to_string(), 1),
        ("an_allocator_default", format!("{counted}pub fn main() -> i32 {{ let v = Vec[i64, Counted]::zeroed(5); return *(v.get(4) orelse unreachable) as i32 + v.len() as i32 + unsafe {{ ALLOCS }} * 10; }}"), 15),
        ("a_program_allocator", "pub struct Mine { }
unsafe impl GlobalAllocator for Mine {
    fn alloc(bytes: usize, align: usize) -> *mut u8 { return @raw_alloc(bytes); }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return unsafe { @realloc(u8, ptr, bytes) }; }
    fn dealloc(ptr: *mut u8) { unsafe { @dealloc(ptr); } }
}
pub alias ProgramAllocator = Mine;
pub fn main() -> i32 { let v = Vec[u32]::zeroed(7); return *(v.get(6) orelse unreachable) as i32 + v.len() as i32; }".to_string(), 7),
    ] {
        assert_runs(name, &src, value);
    }
    for (name, src, message) in [
        ("a_reference", "pub fn main() -> i32 { let r: &i32 = zeroinit; return 0; }", "which '&i32' has none of (it is not 'zeroinit')"),
        ("an_opaque", "pub fn main() -> i32 { let s: String = zeroinit; return 0; }", "which 'String' has none of"),
        ("no_zero_variant", "enum E { A = 1, B = 2 }\npub fn main() -> i32 { let e: E = zeroinit; return 0; }", "which 'E' has none of"),
        ("a_pattern_type", "alias P = u8 in 1..=9;\npub fn main() -> i32 { let p: P = zeroinit; return 0; }", "has none of"),
        ("a_field_that_cannot", "opaque(unsafe zeroinit) Bad { r: &i32 }\npub fn main() -> i32 { return 0; }", "'opaque(unsafe zeroinit)' type 'Bad' has field 'r: &i32', which has no all-zero value"),
        ("unbounded_generic", "fn bad[T]() -> T { return zeroinit; }\npub fn main() -> i32 { return 0; }", "which 'T' has none of"),
        ("no_type_to_zero", "pub fn main() -> i32 { let x = zeroinit; return 0; }", "'zeroinit' needs a known type"),
    ] {
        assert_rejected(name, src, message);
    }
}

#[test]
fn test_marker_traits() {
    // A trait with no methods still has to be implemented: it promises what its documentation
    // says, and only an `impl` makes that promise.
    let decls = "trait Marker { }\nunsafe trait Trusted { }\nfn needs[T: Marker](x: &T) -> i32 { return 1; }\nfn passes_on[T: Marker](x: &T) -> i32 { return needs(x) + 1; }\nfn probe[T: unchecked]() -> i32 { if @satisfies(T, Marker) { return 1; } return 0; }\n";
    for (name, body, value) in [
        ("module_impl", "struct A { }\nimpl Marker for A { }\npub fn main() -> i32 { let a = A { }; return passes_on(&a); }", 2),
        ("in_the_body", "opaque B { impl Marker { } pub fn new() -> Self { return Self { }; } }\npub fn main() -> i32 { let b = B::new(); return needs(&b); }", 1),
        ("satisfies", "struct A { }\nimpl Marker for A { }\nstruct C { }\npub fn main() -> i32 { return probe[A]() * 10 + probe[C]() + probe[i32](); }", 10),
        ("unsafe_marker", "opaque B { unsafe impl Trusted { } pub fn new() -> Self { return Self { }; } }\nfn trusted[T: Trusted](x: &T) -> i32 { return 3; }\npub fn main() -> i32 { let b = B::new(); return trusted(&b); }", 3),
    ] {
        assert_runs(name, &format!("{decls}{body}"), value);
    }
    for (name, body, message) in [
        ("no_impl", "struct A { }\npub fn main() -> i32 { let a = A { }; return needs(&a); }", "Type 'A' does not implement trait 'Marker'"),
        ("unsafe_without_unsafe", "opaque B { impl Trusted { } pub fn new() -> Self { return Self { }; } }\nfn trusted[T: Trusted](x: &T) -> i32 { return 3; }\npub fn main() -> i32 { let b = B::new(); return trusted(&b); }", "write 'unsafe impl'"),
    ] {
        assert_rejected(name, &format!("{decls}{body}"), message);
    }
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
fn test_package_dependencies() {
    // A manifest's dependencies are fetched, checked against their SHA-256, unpacked into a
    // cache, and mounted under their names, with their own `root` meaning themselves.
    let dir = std::env::temp_dir().join(format!("sloplang_deps_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let write = |path: &str, text: &str| {
        let p = dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    let manifest = |name: &str, deps: &str, libs: &str| {
        format!("import std::build::{{Package, Target, Dependency}};
pub fn package[target: Target]() -> Package {{
    return Package {{ name: \"{name}\", version: {{ 1, 0, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[{deps}], system_libs: &[{libs}] }};
}}")
    };
    // The dependency, as its author wrote it: the root of its own build.
    write("shapes/package.slop", &manifest("shapes", "", "\"m\""));
    write("shapes/src/main.slop", "import root::util;\npub fn area(w: i32, h: i32) -> i32 { return util::mul(w, h); }\npub fn twice(x: i32) -> i32 { return root::util::mul(x, 2); }\ntest \"its own\" { @assert(area(2, 2) == 4); }\n");
    write("shapes/src/util.slop", "pub fn mul(a: i32, b: i32) -> i32 { return a * b; }\n");
    let tar = std::process::Command::new("tar").current_dir(&dir).args(["-cf", "shapes.tar", "shapes"]).status().unwrap();
    assert!(tar.success());
    let archive = std::fs::read(dir.join("shapes.tar")).unwrap();
    let hash = crate::sha256::hex(&crate::sha256::digest(&archive));
    let dep = |hash: &str| format!("Dependency {{ name: \"shapes\", url: \"../shapes.tar\", sha256: 0x{hash}_u256 }}");
    write("app/package.slop", &manifest("app", &dep(&hash), ""));
    write("app/src/main.slop", "import shapes;\npub fn main() -> i32 { return shapes::area(2, 3) + shapes::twice(1); }\n");
    let build = crate::packages::BuildFor {
        os: "Linux".to_string(),
        arch: "X86_64".to_string(),
        optimize: "Debug".to_string(),
        cache: dir.join("cache"),
    };
    let load = || crate::packages::load_package(&dir.join("app"), &build);
    let run = |pkg: &crate::packages::LoadedPackage| {
        let refs: Vec<(&str, &str)> = pkg.sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
        let mut program = Compiler::compile_package(&refs).unwrap_or_else(|e| panic!("{e}"));
        super::run_vm_scheduled(&mut program, None).map(|r| r.value)
    };
    let pkg = load().unwrap();
    let mut modules: Vec<&str> = pkg.sources.iter().map(|(m, _)| m.as_str()).collect();
    modules.sort();
    assert_eq!(modules, ["root", "shapes", "shapes::util"]);
    assert_eq!(pkg.system_libs, ["m"], "a dependency's libraries are linked too");
    assert_eq!(run(&pkg), Ok(8));
    // The dependency's tests stay its own: a build of the app runs none of them.
    let refs: Vec<(&str, &str)> = pkg.sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let outcomes = crate::testing::run_tests(&refs).unwrap();
    assert!(outcomes.is_empty(), "{outcomes:?}");
    // Fetched once: from the cache when the archive is gone.
    std::fs::remove_file(dir.join("shapes.tar")).unwrap();
    assert_eq!(run(&load().unwrap()), Ok(8));
    // Fetching writes the lock, and a build holds to it.
    let fetch = |targets: &[crate::packages::BuildFor]| crate::packages::fetch_package(&dir.join("app"), targets);
    let lock = fetch(std::slice::from_ref(&build)).unwrap().lock;
    let text = std::fs::read_to_string(&lock).unwrap();
    assert!(text.contains(&format!("\nshapes {hash} ../shapes.tar\n")), "{text}");
    assert_eq!(run(&load().unwrap()), Ok(8));
    let zeros = "0".repeat(64);
    std::fs::write(&lock, text.replace(&hash, &zeros)).unwrap();
    let err = load().unwrap_err();
    assert!(err.contains(&format!("has SHA-256 {hash}, but package.lock says {zeros}; run 'slop fetch'")), "{err}");
    std::fs::write(&lock, "# nothing\n").unwrap();
    assert!(load().unwrap_err().contains("dependency 'shapes' is not in package.lock"));
    std::fs::write(&lock, "shapes\n").unwrap();
    assert!(load().unwrap_err().contains("is not 'name sha256 url'"));
    // A fetch writes what the targets need and nothing else.
    std::fs::write(&lock, format!("other {} x.tar\n", "a".repeat(64))).unwrap();
    fetch(std::slice::from_ref(&build)).unwrap();
    let text = std::fs::read_to_string(&lock).unwrap();
    assert!(text.contains(&format!("shapes {hash} ")) && !text.contains("other "), "{text}");
    // A dependency only one target has is locked by a fetch for every target, and a target
    // the manifest refuses is skipped.
    let per_target = format!("import std::build::{{Package, Target, Dependency}};
pub fn package[target: Target]() -> Package {{
    if target.arch == Target::Arch::Wasm32 {{ @compile_error(\"no wasm\"); }}
    if target.os == Target::Os::Windows {{
        return Package {{ name: \"app\", version: {{ 1, 0, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[{}], system_libs: &[] }};
    }}
    return Package {{ name: \"app\", version: {{ 1, 0, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[], system_libs: &[] }};
}}", dep(&hash));
    write("app/package.slop", &per_target);
    let linux_only = fetch(std::slice::from_ref(&build)).unwrap();
    assert!(linux_only.deps.is_empty(), "{linux_only:?}");
    let every = fetch(&crate::packages::all_targets(&build.cache)).unwrap();
    assert_eq!(every.deps.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(), ["shapes"]);
    assert_eq!(every.refused, 20, "every OS and mode on Wasm32");
    std::fs::remove_file(&lock).unwrap();
    write("app/package.slop", &manifest("app", &dep(&hash), ""));
    // A hash that does not match what is downloaded is refused.
    std::fs::write(dir.join("shapes.tar"), &archive).unwrap();
    // The archive's hash differs from run to run (tar records times), so the last digit is
    // changed to one it is not.
    let last = if hash.ends_with('0') { '1' } else { '0' };
    let wrong = format!("{}{last}", &hash[..63]);
    write("app/package.slop", &manifest("app", &dep(&wrong), ""));
    let err = load().unwrap_err();
    assert!(err.contains(&format!("has SHA-256 {hash}, but the manifest says {wrong}")), "{err}");
    write("app/package.slop", &manifest("app", "Dependency { name: \"std\", url: \"x.tar\", sha256: 1_u256 }", ""));
    assert!(load().unwrap_err().contains("a dependency cannot be named 'std'"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_comptime_fields_and_associated_items() {
    // `const Name: T = value;` in an opaque is a compile-time field: a constant or a type of the type's
    // own, public, and known to its fields and methods (as `Self::Name` or `Name`). A trait asks
    // for one with `const Name: bound;`, and each implementation gives it.
    let k = "trait K { const Item: copy; fn get(self: &Self) -> Self::Item; }\nfn first[T: K](x: &T) -> T::Item { return x.get(); }\n";
    for (name, src, value) in [
        ("a_value", "opaque P { pub const N: usize = 4; pub fn n() -> usize { return Self::N + N; } }\npub fn main() -> i32 { return (P::N + P::n()) as i32; }", 12),
        ("a_type", "opaque P { pub const H: type = i32; v: Self::H, pub fn get(self: &Self) -> H { return self.v; } pub fn new() -> Self { return Self { v: 3 }; } }\npub fn main() -> i32 { let p = P::new(); let x: P::H = p.get(); return x; }", 3),
        ("from_parameters", "opaque P[T] { const H: type = ?T; v: Self::H, pub fn new() -> Self { return Self { v: null }; } pub fn has(self: &Self) -> bool { return self.v != null; } }\npub fn main() -> i32 { let p = P[i32]::new(); if p.has() { return 1; } return 2; }", 2),
        ("module_impl", "struct A { v: i64 }\nimpl K for A { const Item: copy = i64; fn get(self: &Self) -> i64 { return self.v; } }\npub fn main() -> i32 { let a = A { v: 5 }; return first(&a) as i32; }", 5),
        ("inline_impl", "opaque B { v: u8, impl K { const Item: type = u8; fn get(self: &Self) -> u8 { return self.v; } } pub fn new() -> Self { return Self { v: 6 }; } }\npub fn main() -> i32 { let b = B::new(); let x: B::Item = first(&b); return x as i32; }", 6),
        // `const` in a type is the same field, private unless `pub`.
        ("a_const", "opaque P { const N: usize = 2; const M: usize = 3; pub fn n() -> usize { return N * M; } }\npub fn main() -> i32 { return P::n() as i32; }", 6),
        ("blanket_impl", "trait Base { fn n(self: &Self) -> i32; }\nstruct C { }\nimpl Base for C { fn n(self: &Self) -> i32 { return 7; } }\nimpl[A: Base] K for A { const Item: type = i32; fn get(self: &Self) -> i32 { return self.n(); } }\npub fn main() -> i32 { let c = C { }; return first(&c); }", 7),
    ] {
        assert_runs(name, &format!("{k}{src}"), value);
    }
    for (name, src, message) in [
        ("item_missing", "struct A { }\nimpl K for A { fn get(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { }; return first(&a); }", "gives no 'const Item', which trait 'K' asks of each implementation"),
        ("item_misses_its_bound", "struct A { }\nimpl K for A { const Item: type = String; fn get(self: &Self) -> String { return String::new(); } }\npub fn main() -> i32 { let a = A { }; let s = first(&a); return 0; }", "'A::Item' does not meet its bound in trait 'K'"),
        ("not_an_item", "struct A { }\nimpl K for A { const Item: type = i32; const Other: type = i32; fn get(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { }; return first(&a); }", "'const Other' in 'impl K for A' in module 'root' is not an associated item of trait 'K'"),
        // Without a bound that gives it, a generic has no `T::Item`.
        ("not_promised", "fn f[S](x: S::Item) -> i32 { return 0; }\npub fn main() -> i32 { return 0; }", "Type 'S' has no associated type 'Item'"),
        ("valued_in_a_trait", "trait L { const Item: type = i32; }\npub fn main() -> i32 { return 0; }", "each implementation gives its value"),
        // Private unless `pub`, and a trait's item must be public.
        ("private_outside", "opaque P { const N: usize = 1; }\npub fn main() -> i32 { return P::N as i32; }", "private"),
        ("private_for_a_trait", "opaque B { const Item: type = i32; impl K { fn get(self: &Self) -> i32 { return 1; } } pub fn new() -> Self { return Self { }; } }\npub fn main() -> i32 { let b = B::new(); return first(&b); }", "but privately; write 'pub const Item'"),
        ("private_through_a_bound", "fn has[T: K](x: &T) -> i32 { return 1; }\nopaque B { const Item: type = i32; impl K { fn get(self: &Self) -> i32 { return 1; } } pub fn new() -> Self { return Self { }; } }\npub fn main() -> i32 { let b = B::new(); return has(&b); }", "but privately; write 'pub const Item'"),
        // A bound written on the value is checked where it is written, used or not.
        ("bound_where_written", "struct A { }\nimpl K for A { const Item: copy = String; fn get(self: &Self) -> String { return String::new(); } }\npub fn main() -> i32 { return 0; }", "'const Item: ... = String' in 'impl K for A' in module 'root' does not meet its bound: Type 'String' does not satisfy comptime constraint 'copy'"),
        // Brackets are for parameters; a field is a constant.
        ("bracketed", "opaque P { [N: usize = 1] }\npub fn main() -> i32 { return 0; }", "write 'const Name: T = value;'"),
        ("bracketed_in_a_trait", "trait L { [Item: copy] }\npub fn main() -> i32 { return 0; }", "'const Name: bound;'"),
        ("not_in_a_struct", "struct S { impl K { const Item: type = i32; fn get(self: &Self) -> i32 { return 1; } } }\npub fn main() -> i32 { return 0; }", "goes in an 'opaque' body or a module-level 'impl'"),
    ] {
        assert_rejected(name, &format!("{k}{src}"), message);
    }
}

#[test]
fn test_vec_storage() {
    // `Vec[T, A]` keeps its elements in a `Storage`: any allocator, or `Slots[T, N]` inside the
    // vector itself (`ArrayVec[T, N]`), which moves with it.
    let counting = "static mut GROWS: i32 = 0;
pub struct Counting { }
unsafe impl Storage for Counting {
    const Handle: type = *own u8;
    fn resolve(self: &Self, h: *own u8) -> *own u8 { return h; }
    fn grow(self: &mut Self, h: ?*own u8, keep: usize, bytes: usize, align: usize) -> ?*own u8 {
        unsafe { GROWS = GROWS + 1; }
        let g = Global { };
        let mut s: Global = g;
        return s.grow(h, keep, bytes, align);
    }
    fn release(self: &mut Self, h: *own u8) { let mut s = Global { }; s.release(h); }
    fn limit(self: &Self) -> usize { return 1024; }
    fn sibling(self: &Self) -> Self { return Counting { }; }
}
";
    for (name, body, value) in [
        ("array_vec", "let mut v = ArrayVec[Box[i32], 4]::new(); v.push(Box[i32]::new(3)); v.push(Box[i32]::new(4)); v.insert(0, Box[i32]::new(1)); let w = move v; let mut t: i32 = 0; for b in w.iter() { t = t * 10 + *b.get(); } return t;", 134),
        ("moved_and_cloned", "let mut v = ArrayVec[String, 3]::new(); v.push(String::from(\"b\")); v.push(String::from(\"aa\")); let w = @clone(&v); let x = v.remove(0) orelse unreachable; let moved = move v; return (w.len() * 100 + x.len() * 10 + moved.len()) as i32;", 211),
        ("slices_and_sorting", "let mut v = ArrayVec[i32, 5]::new(); v.push(3); v.push(1); v.push(2); v.sort(); let s = v.as_slice(); return s[0] * 100 + s[1] * 10 + s[2];", 123),
        // Growth stops at what the slots hold, not at the next doubling.
        ("five_slots", "let mut v = ArrayVec[i32, 5]::new(); for i in 0..5 { v.push(i); } return (v.capacity() * 10 + v.len()) as i32;", 55),
        ("drained", "let mut v = ArrayVec[Box[i32], 3]::new(); v.push(Box[i32]::new(2)); v.push(Box[i32]::new(5)); let mut t: i32 = 0; v.drain(fn(b: Box[i32]) { t = t + b.into_inner(); }); return t;", 7),
        // Inside a heap vector, the inline storage lives in a heap block.
        ("in_a_heap_vec", "let mut outer = Vec[ArrayVec[Box[i32], 2]]::new(); let mut a = ArrayVec[Box[i32], 2]::new(); a.push(Box[i32]::new(6)); outer.push(move a); let inner = outer.get_mut(0) orelse unreachable; inner.push(Box[i32]::new(7)); return *(inner.get(1) orelse unreachable).get() * 10 + *(inner.get(0) orelse unreachable).get();", 76),
        // Generic over the storage, and a storage of the program's own.
        ("generic_storage", "fn total[S: Storage](v: &Vec[i32, S]) -> i32 { let mut t: i32 = 0; for x in v.iter() { t = t + *x; } return t; }\nlet mut a = ArrayVec[i32, 2]::new(); a.push(1); let mut b = Vec[i32]::new(); b.push(2); let mut c = Vec[i32, Counting]::new_in(Counting { }); for i in 0..9 { c.push(i); } return total(&a) * 100 + total(&b) * 10 + unsafe { GROWS };", 123),
    ] {
        let (decls, main) = match body.split_once("\nlet ") {
            Some((d, rest)) => (d.to_string(), format!("let {rest}")),
            None => (String::new(), body.to_string()),
        };
        assert_runs(name, &format!("{counting}{decls}\npub fn main() -> i32 {{ {main} }}"), value);
    }
    // Past its slots, a push traps.
    let full = "pub fn main() -> i32 { let mut v = ArrayVec[i32, 2]::new(); v.push(1); v.push(2); v.push(3); return 0; }";
    assert_eq!(run_lli("full", full), Some(TRAP_EXIT));
    assert!(super::run_vm("full", full).is_err());
}

#[test]
fn test_blanket_impls() {
    // An impl for every type meeting a bound (`impl[A: K] L for A`), as std's for allocators.
    let decls = "trait K { fn k(self: &Self) -> i32; }\ntrait L { fn l(self: &Self) -> i32; }\nimpl[A: K] L for A { fn l(self: &Self) -> i32 { return self.k() + 1; } }\nstruct S { }\nimpl K for S { fn k(self: &Self) -> i32 { return 1; } }\n";
    assert_runs("direct", &format!("{decls}pub fn main() -> i32 {{ let s = S {{ }}; return s.l(); }}"), 2);
    assert_runs("through_a_bound", &format!("{decls}fn use_l[T: L](x: &T) -> i32 {{ return x.l(); }}\npub fn main() -> i32 {{ let s = S {{ }}; return use_l(&s); }}"), 2);
    // One whose bound is itself does not loop: the type has no impl.
    assert_rejected(
        "its_own_bound",
        "trait L { fn l(self: &Self) -> i32; }\nimpl[A: L] L for A { fn l(self: &Self) -> i32 { return 1; } }\nstruct S { }\npub fn main() -> i32 { let s = S { }; return s.l(); }",
        "no method 'l'",
    );
}

#[test]
fn test_payload_less_unions_and_enum_casts() {
    let decls = "union(u8) U { A = 0, B = 1 }\nenum(i8) E { Neg = -1, A = 0, B = 5 }\n";
    for (name, body, value) in [
        // A union without payloads compares by variant, under the VM as natively.
        ("union_eq", "let u: U = .B; let v: U = .A; if u == U::B && u != v { return 1; } return 0;", 1),
        // An enum holds only its variants' values, from an integer or from another enum.
        ("enum_cast", "let n: i32 = 5; let m: i64 = -1; let e = n as E; let f = m as E; return (e as i32) * 10 + (f as i32);", 49),
        ("enum_cast_const", "let e = 5 as E; return e as i32;", 5),
    ] {
        assert_runs(name, &format!("{decls}pub fn main() -> i32 {{ {body} }}"), value);
    }
    let trap = format!("{decls}fn bad(n: i32) -> E {{ return n as E; }}\npub fn main() -> i32 {{ let e = bad(7); return e as i32; }}");
    assert_eq!(run_lli("enum_cast_traps", &trap), Some(TRAP_EXIT));
    assert!(super::run_vm("enum_cast_traps", &trap).is_err());
    assert_rejected(
        "enum_cast_const_outside",
        &format!("{decls}pub fn main() -> i32 {{ let e = 7 as E; return 0; }}"),
        "7 is not a value of enum 'E', whose values are -1, 0, 5",
    );
}

#[test]
fn test_what_the_ledger_example_found() {
    // Each was found writing `examples/ledger`.
    for (name, src, value) in [
        // A type parameter inside a type call inside another (`T` in `Box[N[T]]`) is inferred.
        ("infer_nested", "struct N[T] { v: T }\nfn f[T: copy](a: &Box[N[T]]) -> T { return a.get().v; }\npub fn main() -> i32 { let b = Box[N[i32]]::new(N[i32] { v: 4 }); return f(&b); }", 4),
        ("infer_nested_optional", "struct N[T] { v: T }\nfn f[T: copy](a: &?Box[N[T]], x: T) -> T { if let ref b = *a { return b.get().v; } return x; }\npub fn main() -> i32 { let b: ?Box[N[i32]] = null; return f(&b, 5); }", 5),
        // A `&mut self` call's arguments are read before its borrow starts, places as well as
        // calls: `s.r(s.n)`, through a reference too.
        ("arg_reads_receiver", "struct S { n: u64, pub fn r(self: &mut Self, b: u64) -> u64 { self.n = b + 1; return self.n; } }\npub fn main() -> i32 { let mut s = S { n: 1 }; let a = s.r(s.n); let m = &mut s; return (a + m.r(m.n)) as i32; }", 5),
        // Storing into a container does not store into what the container already borrows.
        ("store_reaches_the_container", "fn eat(v: Vec[tuple { &Vec[i64], &i32 }]) -> i32 { return v.len() as i32; }\npub fn main() -> i32 { let a = Vec[i64]::new(); let mut b: i32 = 1; let mut keep = Vec[tuple { &Vec[i64], &i32 }]::new(); keep.push({ &a, &b }); keep.push({ &a, &b }); let n = eat(keep); b = 2; return n + b + a.len() as i32; }", 4),
        ("tasks_borrowing_an_array", "fn f(m: &[Vec[i64]; 2], w: u64) -> i32 { return 1; }\npub fn main() -> i32 { let m: [Vec[i64]; 2] = { Vec[i64]::new(), Vec[i64]::new() }; let pool = WorkerPool::new(2); let mut tasks = Vec[Task[i32]]::new(); tasks.push(async(&pool) f(&m, 1)); tasks.push(async(&pool) f(&m, 2)); let mut n = 0; while let t = tasks.pop() { n = n + t.await(); } return n; }", 2),
        // A field of what a trait method returns evaluates the call once.
        ("field_of_await", "struct P { a: i32 }\nfn g() -> P { return P { a: 3 }; }\npub fn main() -> i32 { let t = async g(); return t.await().a; }", 3),
        ("packed_field_of_a_call", "packed struct F { lo: u4, hi: u4 }\nfn mk() -> F { return F { lo: 2, hi: 5 }; }\npub fn main() -> i32 { return mk().hi as i32 + mk().bits as i32; }", 13),
        // `Vec::insert` and `Vec::remove` shift what follows, and drop what they should.
        ("vec_insert_remove", "pub fn main() -> i32 { let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); v.insert(0, Box[i32]::new(2)); v.insert(2, Box[i32]::new(3)); v.insert(1, Box[i32]::new(4)); let r = v.remove(0) orelse unreachable; if v.remove(9) != null { return 99; } return r.into_inner() * 100 + *(v.get(0) orelse unreachable).get() * 10 + *(v.get(2) orelse unreachable).get(); }", 243),
    ] {
        assert_runs(name, src, value);
    }
    for (name, src, message) in [
        ("arg_still_borrowing_receiver", "struct S { n: u64, pub fn k(self: &mut Self, r: &u64) -> u64 { return *r; } }\npub fn main() -> i32 { let mut s = S { n: 1 }; return s.k(&s.n) as i32; }", "already borrowed"),
        ("store_still_tracked", "pub fn main() -> i32 { let mut keep = Vec[&i32]::new(); if true { let x: i32 = 1; keep.push(&x); } return keep.len() as i32; }", "goes out of scope while still borrowed"),
    ] {
        assert_rejected(name, src, message);
    }
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
    let mut buf: [u8; 8] = @default([u8; 8]);
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
fn test_recursive_types() {
    for (name, src, value) in [
        (
            "pointer",
            "struct L { v: i32, next: *const L }
pub fn main() -> i32 { let a = L { v: 3, next: 0 as *const L }; let b = L { v: 4, next: &a as *const L };
    return unsafe { (*b.next).v }; }",
            3,
        ),
        (
            "boxed_list_walked",
            "struct L { v: i32, next: ?Box[L],
    pub fn sum(self: &Self) -> i32 { let mut s = self.v; if let ref n = self.next { s = s + n.get().sum(); } return s; }
    pub fn bump(self: &mut Self) { self.v = self.v + 1; if let ref mut n = self.next { n.get_mut().bump(); } }
}
fn walk(h: &L) -> i32 { let mut n = 0; let mut cur = h; while let ref next = cur.next { n = n + 1; cur = next.get(); } return n; }
pub fn main() -> i32 {
    let mut h = L { v: 1, next: null };
    let mut i = 2;
    while i <= 5 { h = L { v: i, next: Box[L]::new(move h) }; i = i + 1; }
    h.bump();
    return h.sum() * 10 + walk(&h);
}",
            204,
        ),
        (
            "tree_clones",
            "struct T { v: i32, kids: Vec[T] }
fn sum(t: &T) -> i32 { let mut s = t.v; for ref k in t.kids.as_slice() { s = s + sum(k); } return s; }
pub fn main() -> i32 {
    let mut a = T { v: 1, kids: Vec[T]::new() };
    a.kids.push(T { v: 2, kids: Vec[T]::new() });
    let b = @clone(&a);
    a.kids.push(T { v: 5, kids: Vec[T]::new() });
    return sum(&a) * 10 + sum(&b);
}",
            83,
        ),
        (
            "generic",
            "fn Tree[V] -> type { return struct { v: V, kids: Vec[Tree[V]],
    pub fn count(self: &Self) -> i32 { let mut n = 1; for ref k in self.kids.as_slice() { n = n + k.count(); } return n; } }; }
pub fn main() -> i32 {
    let mut a = Tree[i64] { v: 1, kids: Vec[Tree[i64]]::new() };
    a.kids.push(Tree[i64] { v: 2, kids: Vec[Tree[i64]]::new() });
    let mut s = Tree[String] { v: String::from(\"x\"), kids: Vec[Tree[String]]::new() };
    s.kids.push(Tree[String] { v: String::from(\"y\"), kids: Vec[Tree[String]]::new() });
    return a.count() + s.count();
}",
            4,
        ),
        (
            "mutual",
            "struct A { v: i32, bs: Vec[B],
    pub fn total(self: &Self) -> i32 { let mut s = self.v; for ref b in self.bs.as_slice() { s = s + b.total(); } return s; } }
struct B { w: i32, a: ?Box[A],
    pub fn total(self: &Self) -> i32 { let mut s = self.w; if let ref a = self.a { s = s + a.get().total(); } return s; } }
pub fn main() -> i32 {
    let inner = A { v: 3, bs: Vec[B]::new() };
    let mut a = A { v: 1, bs: Vec[B]::new() };
    a.bs.push(B { w: 2, a: Box[A]::new(move inner) });
    a.bs.push(B { w: 4, a: null });
    return a.total();
}",
            10,
        ),
        // Variants of every kind, so that the union's destructor must have an arm for each.
        (
            "union_drops_each_variant",
            "union J { Null, Num(i64), Str(String), Opt(?Box[J]), Arr(Vec[J]), Obj(HashMap[String, J]) }
fn depth(j: &J) -> i32 {
    match *j {
        J::Arr(ref v) => { let mut d = 0; for ref x in v.as_slice() { let k = depth(x); if k > d { d = k; } } return d + 1; }
        J::Opt(ref o) => { if let ref b = *o { return depth(b.get()) + 1; } return 1; }
        _ => { return 0; }
    }
}
pub fn main() -> i32 {
    let mut a = Vec[J]::new();
    a.push(J::Str(String::from(\"s\")));
    a.push(J::Opt(Box[J]::new(J::Str(String::from(\"t\")))));
    let mut o = HashMap[String, J]::new();
    let _old = o.insert(String::from(\"k\"), J::Arr(move a));
    let mut b = Vec[J]::new();
    b.push(J::Obj(move o));
    b.push(J::Num(1));
    b.push(J::Null);
    let mut c = Vec[J]::new();
    c.push(J::Str(String::from(\"u\")));
    c.push(J::Opt(Box[J]::new(J::Null)));
    b.push(J::Arr(move c));
    return depth(&J::Arr(move b));
}",
            3,
        ),
        (
            "fields_dropped",
            "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + 1; } } } }
struct L { d: D, next: ?Box[L] }
fn make() {
    let mut h = L { d: D::new(0), next: null };
    h = L { d: D::new(1), next: Box[L]::new(move h) };
    h = L { d: D::new(2), next: Box[L]::new(move h) };
}
pub fn main() -> i32 { make(); return unsafe { DROPS }; }",
            3,
        ),
        // A method of a finished type that names a type still being built must wait for it.
        (
            "method_names_unfinished_type",
            "struct Inner { x: i32, pub fn make(self: &Self) -> i32 { let o = Outer { i: Inner { x: 2 }, v: Vec[i32]::new(), n: 40 }; return o.n + o.i.x; } }
struct Outer { i: Inner, v: Vec[i32], n: i32 }
pub fn main() -> i32 { let i = Inner { x: 0 }; return i.make(); }",
            42,
        ),
        // Compile-time code run while a type is being built still has its callees.
        (
            "comptime_call_inside_a_type",
            "fn size() -> usize { let mut v = Vec[i32]::new(); v.push(1); v.push(2); v.push(3); return v.len(); }
struct S { a: [u8; size()], next: ?Box[S] }
pub fn main() -> i32 { return @size_of([u8; size()]) as i32; }",
            3,
        ),
        (
            "comptime_function_value_inside_a_type",
            "fn one() -> usize { return 1; }
fn size() -> usize { let f = one; return f() + 2; }
struct S { a: [u8; size()], next: ?Box[S] }
pub fn main() -> i32 { return @size_of([u8; size()]) as i32; }",
            3,
        ),
        // `B` names `A` without a type function, and it is unfinished until `A` is: `Which[B]`
        // has to wait to learn that `B` is linear, which picks its hook.
        (
            "cycle_finishes_together",
            "pub opaque(linear) Tx { id: i32, pub fn new(i: i32) -> Self { return Self { id: i }; } pub fn commit(move self) -> i32 { return self.id; } }
fn Which[T: ?linear] -> type { return opaque(copy) { p: *const T,
    pub fn make() -> Self { return Self { p: 0 as *const T }; }
    impl default where T: linear { fn default() -> Self { return Self { p: 8 as *const T }; } } }; }
struct A { w: Which[B], t: Tx }
struct B { a: A }
pub fn main() -> i32 { let w = @default(Which[B]); return 1; }",
            1,
        ),
        (
            "trait_object_argument",
            "trait T { fn f(self: &Self) -> i32; }
struct S { v: i32, impl T { fn f(self: &Self) -> i32 { return self.v; } } }
pub fn main() -> i32 { let s = S { v: 7 }; let mut x = Vec[&T]::new(); x.push(&s); let r = x.get(0) orelse unreachable; return r.f(); }",
            7,
        ),
    ] {
        assert_runs(name, src, value);
    }
    for (name, src, message) in [
        ("self", "struct L { v: i32, next: L }", "holds itself by value"),
        ("optional", "struct L { next: ?L }", "holds itself by value"),
        ("array", "struct L { next: [L; 2] }", "holds itself by value"),
        ("nested", "struct L { next: struct { a: i32, b: L } }", "holds itself by value"),
        ("mutual", "struct A { b: B }\nstruct B { a: A }", "holds itself by value"),
        ("union", "union U { A, B(U) }", "holds itself by value"),
        ("generic", "fn W[T] -> type { return struct { x: T }; }\nstruct L { w: W[L] }", "holds itself by value"),
        ("alias", "alias A = *const A;", "defined in terms of itself"),
        ("distinct", "type D = distinct *const D;", "defined in terms of itself"),
        ("packed", "packed struct L { x: u8, y: L }", "still being defined"),
        ("size_of", "struct L { b: [u8; @size_of(L)] }", "still being defined"),
        ("size_of_in_argument", "fn I[T] -> type { return struct { b: [u8; @size_of(T)] }; }\nstruct L { x: i32, w: I[L] }", "still being defined"),
        ("copy_holding_its_own_vec", "opaque(copy) Q { kids: Vec[Q] }", "non-copy type"),
        ("format_needs_a_hook", "struct L { v: i32, next: ?&L }\nfn show(l: &L) { println(f\"{l}\"); }", "cannot be formatted"),
        ("ever_larger", "fn G[T] -> type { return struct { x: T, n: *const G[*const T] }; }\nstruct S { g: G[i32] }", "nests more than"),
    ] {
        assert_rejected(name, &format!("{src}\npub fn main() -> i32 {{ return 0; }}"), message);
    }
}

#[test]
fn test_optional_owner_needs_no_tag() {
    let prelude = "struct Unit { }
struct Node { v: i32, next: ?Box[Node] }
struct Wrap { b: Box[i32] }
struct Late { n: u64, p: Box[u64],
    pub fn new(n: u64, v: u64) -> Self { return Self { n: n, p: Box[u64]::new(v) }; }
    pub fn sum(self: &Self) -> i32 { return (self.n + *self.p.get()) as i32; }
}
opaque Raw { p: *const u8 }
opaque Held { u: uninit *own u8 }
struct Beside { a: u64, o: ?Late, z: u8 }
struct Tagged { a: u64, o: ?i32 }
struct Deep { a: u64, l: Late }
struct Pad { a: u8, b: Box[u8] }
fn nothing() -> ?Late { return null; }
fn something(n: u64) -> ?Late { return Late::new(n, 2); }
fn use_late(o: ?Late) -> i32 { if let l = o { return l.sum(); } return 3; }
";
    for (name, body, value) in [
        ("box", "return @size_of(?Box[i32]) as i32;", 8),
        ("box_of_unit", "return @size_of(?Box[Unit]) as i32;", 8),
        ("wrapped", "return @size_of(?Wrap) as i32;", 8),
        ("list", "return @size_of(Node) as i32;", 16),
        ("after_a_field", "return @size_of(?Late) as i32;", 16),
        // Only a pointer that cannot be null makes a niche.
        ("nullable", "return @size_of(?Vec[i32]) as i32;", 32),
        ("raw", "return @size_of(?Raw) as i32;", 16),
        ("uninit", "return @size_of(?Held) as i32;", 16),
        ("twice", "return @size_of(??Box[i32]) as i32;", 16),
        ("unit_is_present", "let o: ?Box[Unit] = Box[Unit]::new(Unit { }); if o == null { return 0; } return 1;", 1),
        ("null_in_a_field", "return use_late(nothing());", 3),
        ("present_in_a_field", "return use_late(something(40));", 42),
        // A zero beside the pointer is a value, not `null`.
        ("zero_before_the_pointer", "return use_late(something(0));", 2),
        ("offset_inside", "let s = Beside { a: 1, o: something(7), z: 0 }; if let ref l = s.o { return (&l.p as *const Box[u64] as usize - &s as *const Beside as usize) as i32; } return 0;", 16),
        ("offset_after", "let s = Beside { a: 1, o: something(7), z: 0 }; return (&s.z as *const u8 as usize - &s as *const Beside as usize) as i32;", 24),
        ("offset_inside_a_tag", "let s = Tagged { a: 1, o: 7 }; if let ref v = s.o { return (v as *const i32 as usize - &s as *const Tagged as usize) as i32; } return 0;", 12),
        ("deep_in_a_field", "let o: ?Deep = Deep { a: 1, l: Late::new(0, 4) }; if let d = o { return d.l.sum(); } return 3;", 4),
        ("past_padding", "let bits: tuple { u64, u64 } = { 18446744073709551615, 0 }; let o = unsafe { @transmute(?Pad, bits) }; return (o == null) as i32;", 1),
        ("null_from_bits", "let bits: tuple { u64, u64 } = { 5, 0 }; let o = unsafe { @transmute(?Late, bits) }; return (o == null) as i32;", 1),
        ("reassigned", "let mut o = something(1); o = null; if o != null { return 0; } o = something(5); return use_late(move o);", 7),
        ("in_a_vec", "let mut v = Vec[?Box[i32]]::new(); v.push(null); v.push(Box[i32]::new(9)); let a = v.get(0) orelse unreachable; let b = v.get(1) orelse unreachable; return (*a == null) as i32 * 10 + (*b != null) as i32;", 11),
        ("taken", "let mut h = Node { v: 1, next: Box[Node]::new(Node { v: 2, next: null }) }; let n = core::mem::replace(&mut h.next, null); if h.next != null { return 0; } if let b = n { return b.get().v; } return 9;", 2),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_long_list_drops_in_a_loop() {
    // A type can still take itself apart, and then nothing is deferred.
    let src = "struct Node { v: i32, next: ?Box[Node] }
opaque List { head: ?Box[Node],
    pub fn new() -> Self { return Self { head: null }; }
    pub fn push(self: &mut Self, v: i32) {
        let old = core::mem::replace(&mut self.head, null);
        self.head = Box[Node]::new(Node { v: v, next: move old });
    }
    impl drop { fn drop(self: &mut Self) {
        let mut cur = core::mem::replace(&mut self.head, null);
        while let b = cur {
            let mut node = b.into_inner();
            cur = core::mem::replace(&mut node.next, null);
        }
    } }
}
fn work(n: i32) -> i32 { let mut l = List::new(); for i in 0..n { l.push(i); } return 7; }
pub fn main() -> i32 { let t = async(Fibers { }) work(1000000); return t.await(); }";
    assert_eq!(run_lli("long_list", src), Some(7));
    assert_runs("short_list", &src.replace("1000000", "50"), 7);
}

#[test]
fn test_recursive_boxes_drop_at_any_depth() {
    let list = "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + 1; } } } }
struct L { d: D, next: ?Box[L] }
fn make(n: i32) { let mut h = L { d: D::new(0), next: null }; for i in 1..n { h = L { d: D::new(i), next: Box[L]::new(move h) }; } }
fn work(n: i32) -> i32 { make(n); return unsafe { DROPS }; }
";
    let scaled = |src: &str, big: i32, small: i32, code: i32| {
        assert_eq!(run_lli("deep", &src.replace("NODES", &big.to_string())), Some(code));
        assert_runs("shallow", &src.replace("NODES", &small.to_string()), code as i128);
    };
    // Every node is dropped once, far past the limit and past a fiber's stack. Exit codes
    // being 8 bits, the count is compared here.
    let main = format!("{list}pub fn main() -> i32 {{ return (work(NODES) == NODES) as i32; }}");
    scaled(&main, 3000000, 400, 1);
    let fiber = format!("{list}pub fn main() -> i32 {{ let t = async(Fibers {{ }}) work(NODES); return (t.await() == NODES) as i32; }}");
    scaled(&fiber, 1000000, 400, 1);
    // Through a union, and around a cycle of two types.
    let shapes = "union E { Leaf, Neg(Box[E]) }
struct A { b: ?Box[B] }
struct B { a: ?Box[A] }
fn chain(n: i32) { let mut e = E::Leaf; for i in 0..n { e = E::Neg(Box[E]::new(move e)); } }
fn cycle(n: i32) { let mut a = A { b: null }; for i in 0..n { a = A { b: Box[B]::new(B { a: Box[A]::new(move a) }) }; } }
pub fn main() -> i32 { chain(NODES); cycle(NODES); return 1; }";
    scaled(shapes, 500000, 300, 1);
    // A drop that parks leaves its count with its fiber, and another's drops run meanwhile.
    let parking = "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(self: &mut Self) { if self.v % 50 == 0 { let _s = sleep_ms(0); } unsafe { DROPS = DROPS + 1; } } } }
struct L { d: D, next: ?Box[L] }
fn make(n: i32) -> i32 { let mut h = L { d: D::new(0), next: null }; for i in 1..n { h = L { d: D::new(i), next: Box[L]::new(move h) }; } return 1; }
pub fn main() -> i32 {
    let a = async(Fibers { }) make(NODES);
    let b = async(Fibers { }) make(NODES);
    let c = async(Fibers { }) make(NODES);
    let done = a.await() + b.await() + c.await();
    return (done == 3 && unsafe { DROPS } == 3 * NODES) as i32;
}";
    scaled(parking, 20000, 300, 1);
    // Up to the limit nothing changes: the head of a list goes first, then what follows it.
    let order = "static mut SEEN: i64 = 0;
opaque D { v: i64,
    pub fn new(v: i64) -> D { return D { v: v }; }
    impl drop { fn drop(self: &mut Self) { unsafe { SEEN = SEEN * 10 + self.v; } } } }
struct L { d: D, next: ?Box[L] }
fn make() { let mut h = L { d: D::new(3), next: null }; h = L { d: D::new(2), next: Box[L]::new(move h) }; h = L { d: D::new(1), next: Box[L]::new(move h) }; }
pub fn main() -> i32 { make(); return unsafe { SEEN } as i32; }";
    assert_runs("order", order, 123);
    // A box that cannot hold another pays nothing for this.
    let uses_queue = |src: &str| {
        let program = Compiler::compile_source(src).unwrap();
        program.functions.iter().any(|f| f.debug_name.as_deref().is_some_and(|n| n.contains("enter_drop")))
    };
    assert!(!uses_queue("struct P { b: Box[i32], v: Vec[Box[i32]] }\npub fn main() -> i32 { let p = P { b: Box[i32]::new(1), v: Vec[Box[i32]]::new() }; return 0; }"));
    assert!(uses_queue("struct L { next: ?Box[L] }\npub fn main() -> i32 { let l = L { next: null }; return 0; }"));
    assert!(uses_queue("struct L { kids: Vec[L], one: ?Box[L] }\npub fn main() -> i32 { let l = L { kids: Vec[L]::new(), one: null }; return 0; }"));
    // Asked of a finished type: only what a value owns counts, not what it points at.
    let recursive = "fn yes[T: recursive]() -> i32 { return 1; }
struct Tree { kids: Vec[Tree] }
struct Linked { p: *const Linked }
struct Plain { b: Box[i32] }
";
    assert_runs("owns_through_vec", &format!("{recursive}pub fn main() -> i32 {{ return yes[Tree](); }}"), 1);
    for (name, ty) in [("points_at_itself", "Linked"), ("plain", "Plain")] {
        assert_rejected(
            name,
            &format!("{recursive}pub fn main() -> i32 {{ return yes[{ty}](); }}"),
            "recursive",
        );
    }
    // A fiber recurses as deep as the main thread can: megabytes, at unoptimized frame sizes.
    assert_eq!(
        run_lli(
            "deep_recursion",
            "fn depth(n: i32, pad: [i64; 8]) -> i32 { if n == 0 { return pad[0] as i32; } let r = depth(n - 1, pad); return r + 1 - 1; }
pub fn main() -> i32 { let t = async(Fibers { }) depth(20000, @default([i64; 8])); return t.await() + 1; }"
        ),
        Some(1)
    );
}

#[test]
fn test_raw_pointers_hold_no_borrow() {
    let src = "struct W { a: i32, b: Vec[i32] }
fn f(w: &mut W, x: &i32) -> i32 { w.a = 1; return *x; }
pub fn main() -> i32 {
    let mut w = W { a: 0, b: Vec[i32]::new() };
    w.b.push(5);
    let p = (w.b.get(0) orelse unreachable) as *const i32;
    return f(&mut w, unsafe { &*p });
}";
    assert_runs("through_raw", src, 5);
    // A view is the pointer that does carry its borrow.
    assert_rejected(
        "through_view",
        "pub fn main() -> i32 {
    let mut x: i32 = 1;
    let v = unsafe { &x as *ref i32 };
    x = 2;
    return unsafe { *v };
}",
        "currently borrowed",
    );
    assert_rejected(
        "through_reference",
        "struct W { a: i32, b: Vec[i32] }
fn f(w: &mut W, x: &i32) -> i32 { w.a = 1; return *x; }
pub fn main() -> i32 {
    let mut w = W { a: 0, b: Vec[i32]::new() };
    w.b.push(5);
    let p = w.b.get(0) orelse unreachable;
    return f(&mut w, p);
}",
        "already borrowed",
    );
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
fn test_string_keys() {
    let prelude = "static mut DROPS: i32 = 0;
pub struct P { x: i32, y: i32 }
impl Hash for P { fn hash(self: &Self) -> u64 { return (self.x * 31 + self.y) as u64; } }
impl Eq for P { fn eq(self: &Self, other: &Self) -> bool { return self.x == other.x && self.y == other.y; } }
pub opaque Name {
    s: String,
    pub fn new(s: &str) -> Self { return Self { s: String::from(s) }; }
    impl Hash { fn hash(self: &Self) -> u64 { return self.s.len() as u64; } }
    impl Eq { fn eq(self: &Self, other: &Self) -> bool { return self.s.as_str() == other.s.as_str(); } }
}
pub opaque Noisy {
    pub fn new() -> Self { return Self { }; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + 1; } } }
}
fn key(s: &str) -> String { return String::from(s); }
";
    for (name, body, value) in [
        ("lookup_by_str", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let _b = m.insert(key(\"b\"), 2); return *(m.get(\"b\") orelse unreachable);", 2),
        ("missing", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); return m.contains_key(\"z\") as i32;", 0),
        ("replaces", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); let old = m.insert(key(\"a\"), 2); return (old orelse 0) * 10 + m.len() as i32;", 11),
        ("get_mut", "let mut m = HashMap[String, i32]::new(); let _a = m.insert(key(\"a\"), 1); if let v = m.get_mut(\"a\") { *v = 5; } return *(m.get(\"a\") orelse unreachable);", 5),
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
    let prelude = "fn nums(items: [i32; 5], n: usize) -> Vec[i32] { let mut v = Vec[i32]::new(); for i in 0..n { v.push(items[i]); } return v; }
fn digits(v: &Vec[i32]) -> i32 { let mut t: i32 = 0; for x in v.iter() { t = t * 10 + *x; } return t; }
struct Pair { key: i32, order: i32 }
static mut LIVE: i32 = 0;
pub opaque Tracked {
    n: i32,
    pub fn new(n: i32) -> Self { unsafe { LIVE = LIVE + 1; } return Self { n: n }; }
    pub fn n(self: &Self) -> i32 { return self.n; }
    impl drop { fn drop(self: &mut Self) { unsafe { LIVE = LIVE - 1; } } }
}
";
    for (name, body, value) in [
        ("numbers", "let mut v = nums({ 3, 1, 2, 0, 0 }, 3); v.sort(); return digits(&v) % 100;", 23),
        ("empty", "let mut v = Vec[i32]::new(); v.sort(); return v.len() as i32;", 0),
        ("one", "let mut v = nums({ 7, 0, 0, 0, 0 }, 1); v.sort(); return digits(&v);", 7),
        ("already_sorted", "let mut v = nums({ 1, 2, 3, 0, 0 }, 3); v.sort(); return digits(&v) % 100;", 23),
        ("reversed", "let mut v = nums({ 5, 4, 3, 2, 1 }, 5); v.sort(); return digits(&v) % 100;", 45),
        ("descending", "let mut v = nums({ 1, 3, 2, 0, 0 }, 3); v.sort_by(fn(a: &i32, b: &i32) -> bool { return *a > *b; }); return digits(&v) % 100;", 21),
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
fn test_temporaries_are_dropped() {
    let prelude = "static mut DROPS: i32 = 0;
pub opaque Noisy {
    n: i32,
    pub fn new(n: i32) -> Self { return Self { n: n }; }
    pub fn n(self: &Self) -> i32 { return self.n; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + 1; } } }
}
pub opaque Holder {
    r: &i32,
    pub fn new(r: &i32) -> Self borrows(r) { return Self { r: r }; }
    pub fn get(self: &Self) -> i32 { return *self.r; }
    impl drop { fn drop(self: &mut Self) { } }
}
fn mk() -> Vec[i32] { let mut v = Vec[i32]::new(); v.push(1); return v; }
fn len_of(v: &Vec[i32]) -> i32 { return v.len() as i32; }
fn n_of(x: &Noisy) -> i32 { return x.n(); }
fn drops() -> i32 { return unsafe { DROPS }; }
fn early(c: bool) -> i32 { let a = Noisy::new(1).n() + stop(c); return a; }
fn stop(c: bool) -> i32 { return c as i32; }
";
    for (name, body, value) in [
        ("chain_in_return", "return mk().len() as i32;", 1),
        ("chain_in_let", "let n = mk().len(); return n as i32;", 1),
        ("reference_argument", "return len_of(&mk());", 1),
        ("in_a_condition", "if mk().len() == 1 { return 1; } return 0;", 1),
        ("twice_in_one_expression", "let n = mk().len() + mk().len(); return n as i32;", 2),
        ("string", "return String::from(\"abc\").len() as i32;", 3),
        ("through_format", "let n = format(5).len(); return n as i32;", 1),
        ("unwrapped", "let n = *Box[i32]::new(4).get(); return n;", 4),
        // It lives to the end of the statement, and no longer.
        ("dropped_at_the_statement", "let a = Noisy::new(1).n(); let d = drops(); return a * 10 + d;", 11),
        ("live_in_its_statement", "let a = Noisy::new(1).n() + drops(); return a;", 1),
        ("each_time_round", "for i in 0..3 { let _a = Noisy::new(1).n(); } return drops();", 3),
        ("in_a_while_condition", "let mut i: i32 = 0; while Noisy::new(i).n() < 2 { i = i + 1; } return drops();", 3),
        ("on_the_path_taken", "let c = false; let a = c && Noisy::new(1).n() == 1; return drops();", 0),
        ("on_the_path_taken_too", "let c = true; let a = c && Noisy::new(1).n() == 1; return drops();", 1),
        // An early exit from the statement still drops it.
        ("before_a_return", "if true { let n = n_of(&Noisy::new(1)); if n == 1 { return drops(); } } return 9;", 1),
        // `let x = &value;` keeps it for as long as `x`.
        ("kept_by_a_reference", "if true { let x = &Noisy::new(7); let d = drops(); if x.n() != 7 || d != 0 { return 9; } } return drops();", 1),
        // A value moved out of a temporary is not dropped with it.
        ("moved_on", "let v = mk(); return v.len() as i32;", 1),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, body, what) in [
        ("reference_outlives_it", "let s = String::from(\"abc\").as_str(); return s.len as i32;", "borrowed"),
        ("element_outlives_it", "let r = mk().get(0); if let x = r { return *x; } return 0;", "borrowed"),
        ("linear_temporary", "let n = Tx::new(1).id(); return n;", "must be explicitly consumed"),
    ] {
        assert_rejected(
            name,
            &format!("{prelude}pub opaque(linear) Tx {{ n: i32, pub fn new(n: i32) -> Self {{ return Self {{ n: n }}; }} pub fn id(self: &Self) -> i32 {{ return self.n; }} }}\npub fn main() -> i32 {{ {body} }}"),
            what,
        );
    }
    // Ending with the statement, it no longer keeps what it borrows.
    assert_runs(
        "borrow_ends_with_it",
        &format!("{prelude}pub fn main() -> i32 {{ let mut x: i32 = 1; let a = Holder::new(&x).get(); x = 2; return a * 10 + x; }}"),
        12,
    );
}

#[test]
fn test_while_let_temporaries() {
    let prelude = "static mut DROPS: i32 = 0;
pub opaque Noisy {
    n: i32,
    pub fn new(n: i32) -> Self { return Self { n: n }; }
    pub fn value(self: &Self) -> ?i32 { if self.n > 0 { return self.n; } return null; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + 1; } } }
}
fn drops() -> i32 { return unsafe { DROPS }; }
";
    for (name, body, value) in [
        ("each_time_round", "let mut i: i32 = 3; while let n = Noisy::new(i).value() { i = i - n; } return drops();", 2),
        ("after_a_break", "while let n = Noisy::new(1).value() { break; } return drops();", 1),
        ("after_a_continue", "let mut i: i32 = 2; while let n = Noisy::new(i).value() { i = i - 1; continue; } return drops();", 3),
        ("after_a_return", "if true { let a = looped(); return a + drops(); } return 0;", 2),
        ("for_is_unchanged", "let mut t: i32 = 0; for x in 0..3 { t = t + x; } return t;", 3),
    ] {
        assert_runs(name, &format!("{prelude}fn looped() -> i32 {{ while let n = Noisy::new(1).value() {{ return n; }} return 0; }}\npub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_overwriting_a_reference_keeps_what_was_borrowed_through_it() {
    let prelude = "struct P { a: i32, b: i32 }
fn rd(x: &i32) -> i32 { return *x; }
fn pick(v: &Vec[P]) -> ?&P { return v.get(0); }
";
    let setup = "let mut v = Vec[P]::new(); v.push(P { a: 1, b: 2 });";
    for (name, body, value) in [
        ("task_per_item", "let mut t = Vec[Task[i32]]::new(); for i in 0..2 { let r = pick(&v) orelse unreachable; t.push(async rd(&r.b)); } let mut s: i32 = 0; while let x = t.pop() { s = s + x.await(); } return s;", 4),
        ("through_a_temporary", "let mut t = Vec[Task[i32]]::new(); for i in 0..2 { t.push(async rd(&(pick(&v) orelse unreachable).b)); } let mut s: i32 = 0; while let x = t.pop() { s = s + x.await(); } return s;", 4),
        ("reassigned", "let x: i32 = 1; let y: i32 = 2; let mut r = &x; let keep = &*r; r = &y; return *keep * 10 + *r;", 12),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {setup} {body} }}"), value);
    }
    for (name, body, what) in [
        // What the reference points to is still borrowed.
        ("target_is_held", "let mut x: i32 = 1; let r = &x; let keep = &*r; x = 2; return *keep;", "borrowed"),
        // A `&mut T` is unique, so a reborrow through it holds it.
        ("reborrow_holds_a_mut", "let mut x: i32 = 1; let r = &mut x; let keep = &mut *r; let moved = r; *keep = 2; return *moved;", "borrowed"),
        // The reference itself, not through it, cannot change.
        ("reference_to_the_reference", "let x: i32 = 1; let y: i32 = 2; let mut r = &x; let keep = &r; r = &y; return **keep;", "borrowed"),
    ] {
        assert_rejected(name, &format!("{prelude}pub fn main() -> i32 {{ {setup} {body} }}"), what);
    }
}

#[test]
fn test_optimized_code_agrees_about_layout() {
    // An optional's payload is where `opt` and the code generator would differ without a target.
    let src = "pub struct S { a: ?u64, b: u64 }
fn make(n: u64) -> S { return S { a: n, b: n + 1 }; }
fn sum(s: &S) -> i32 { if let a = s.a { return (a + s.b) as i32; } return 0; }
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

const WAKE_LIMIT_MS: i128 = 45;

#[test]
fn test_worker_pools() {
    let prelude = "fn sq(a: i32) -> i32 { return a * a; }
fn add_up(c: &Channel[i32], n: i32) -> i32 { let mut t: i32 = 0; for i in 0..n { t = t + (c.recv() catch |e| 0); } return t; }
fn feed(c: &Channel[i32], n: i32) -> i32 { for i in 0..n { let _s = c.send(i); } return n; }
fn wait(c: &Channel[i32]) -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 7 }; }
fn bump(m: &Mutex[i32], n: i32) -> i32 { for i in 0..n { let mut g = m.lock(); let v = g.get_mut(); *v = *v + 1; g.unlock(); } return 0; }
fn nap(ms: i64) -> i32 { let _a = sleep_ms(ms) catch |e| return 1; return 0; }
fn nested(p: &WorkerPool, a: i32) -> i32 { let t = async(p) sq(a); return t.await() + 1; }
fn owned(v: Vec[i32]) -> Vec[i32] { let mut w = move v; w.push(2); return w; }
";
    for (name, body, value) in [
        ("one_task", "let p = WorkerPool::new(2); let t = async(&p) sq(3); return t.await();", 9),
        ("many_tasks", "let p = WorkerPool::new(2); let mut ts = Vec[Task[i32]]::new(); for i in 0..6 { ts.push(async(&p) sq(2)); } let mut t: i32 = 0; while let h = ts.pop() { t = t + h.await(); } return t;", 24),
        ("one_worker", "let p = WorkerPool::new(1); let a = async(&p) sq(2); let b = async(&p) sq(3); return a.await() + b.await();", 13),
        ("one_after_another", "let p = WorkerPool::new(1); let a = async(&p) sq(2); let x = a.await(); let b = async(&p) sq(3); let y = b.await(); let c = async(&p) sq(4); return x + y + c.await();", 29),
        ("no_workers_runs_here", "let p = WorkerPool::new(0); let t = async(&p) sq(3); return t.await();", 9),
        ("no_tasks", "let p = WorkerPool::new(2); return p.workers() as i32;", 2),
        ("across_workers", "let p = WorkerPool::new(2); let c = Channel[i32]::with_capacity(1); let f = async(&p) feed(&c, 5); let a = async(&p) add_up(&c, 5); let n = f.await(); return a.await() + n;", 15),
        ("on_one_worker", "let p = WorkerPool::new(1); let c = Channel[i32]::with_capacity(1); let f = async(&p) feed(&c, 5); let a = async(&p) add_up(&c, 5); let n = f.await(); return a.await() + n;", 15),
        ("shared_lock", "let p = WorkerPool::new(2); let m = Mutex[i32]::new(0); let a = async(&p) bump(&m, 10); let b = async(&p) bump(&m, 10); let _x = a.await(); let _y = b.await(); let mut g = m.lock(); let v = *g.get_mut(); g.unlock(); return v;", 20),
        ("cancelled", "let p = WorkerPool::new(1); let c = Channel[i32]::new(); let t = async(&p) wait(&c); return t.cancel();", 7),
        ("dropped_handle", "let p = WorkerPool::new(1); let c = Channel[i32]::new(); let t = async(&p) wait(&c); return 3;", 3),
        ("deadline", "let p = WorkerPool::new(1); let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new(); return s.run(fn() -> i32 { let t = async(&p) wait(&c); return t.await(); });", 2),
        ("sleeping", "let p = WorkerPool::new(1); let a = async(&p) nap(2); let b = async(&p) nap(1); return a.await() + b.await() + 4;", 4),
        ("nested", "let p = WorkerPool::new(2); let t = async(&p) nested(&p, 2); return t.await();", 5),
        ("value_moves_through", "let p = WorkerPool::new(2); let mut v = Vec[i32]::new(); v.push(1); let t = async(&p) owned(v); return t.await().len() as i32;", 2),
        ("awaited_from_a_fiber", "let p = WorkerPool::new(1); let t = async(Fibers { }) nested(&p, 3); return t.await();", 10),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // More wakes at once than an inbox holds: the rest still happen.
    let burst = format!("{prelude}pub fn main() -> i32 {{ let p = WorkerPool::new(1); let mut cs = Vec[Channel[i32]]::new(); for i in 0..40 {{ cs.push(Channel[i32]::new()); }} let mut ts = Vec[Task[i32]]::new(); for i in 0..40 {{ ts.push(async(&p) wait(cs.get(i as usize) orelse unreachable)); }} let _a = sleep_ms(2); let start = now_ms(); for i in 0..40 {{ let _s = (cs.get(i as usize) orelse unreachable).send(1); }} let mut t: i32 = 0; while let h = ts.pop() {{ t = t + h.await(); }} if t != 40 {{ return 200; }} return (now_ms() - start) as i32; }}");
    let run = super::run_vm("burst", &burst).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(run.leaks, 0);
    assert!(run.value < 45, "the burst took {} ms of virtual time", run.value);
    // A wake reaches another worker at once: the sweep that would hide a lost one takes 50 ms.
    let pings = format!("{prelude}fn ping(a: &Channel[i32], b: &Channel[i32], n: i32) -> i32 {{ for i in 0..n {{ let _s = a.send(i); let _r = b.recv() catch |e| 0; }} return 0; }}
fn pong(a: &Channel[i32], b: &Channel[i32], n: i32) -> i32 {{ for i in 0..n {{ let r = a.recv() catch |e| 0; let _s = b.send(r); }} return 0; }}
fn guarded(m: &Mutex[i32], n: i32) -> i32 {{ for i in 0..n {{ let mut g = m.lock(); let v = g.get_mut(); *v = *v + 1; let _s = sleep_ms(1); g.unlock(); }} return 0; }}
pub fn main() -> i32 {{ let p = WorkerPool::new(2); let a = Channel[i32]::with_capacity(1); let b = Channel[i32]::with_capacity(1); let start = now_ms(); let x = async(&p) ping(&a, &b, 4); let y = async(&p) pong(&a, &b, 4); let _u = x.await(); let _v = y.await(); let m = Mutex[i32]::new(0); let c = async(&p) guarded(&m, 2); let d = async(&p) guarded(&m, 2); let _w = c.await(); let _z = d.await(); return (now_ms() - start) as i32; }}");
    let run = super::run_vm("pings", &pings).unwrap_or_else(|e| panic!("{e}"));
    assert!(run.value < WAKE_LIMIT_MS, "took {} ms of virtual time", run.value);
    let mut program = Compiler::compile_source(&pings).unwrap();
    for seed in 1..=6 {
        let run = super::run_vm_scheduled(&mut program, Some(seed)).unwrap_or_else(|e| panic!("seed {seed}: {e}"));
        assert!(run.value < WAKE_LIMIT_MS, "seed {seed} took {} ms of virtual time", run.value);
    }
    // The same programs under other interleavings, where the VM reports races and deadlocks.
    for body in [
        "let p = WorkerPool::new(2); let c = Channel[i32]::with_capacity(1); let f = async(&p) feed(&c, 3); let a = async(&p) add_up(&c, 3); let n = f.await(); return a.await() + n;",
        "let p = WorkerPool::new(2); let m = Mutex[i32]::new(0); let a = async(&p) bump(&m, 3); let b = async(&p) bump(&m, 3); let _x = a.await(); let _y = b.await(); let mut g = m.lock(); let v = *g.get_mut(); g.unlock(); return v + 0;",
        "let p = WorkerPool::new(2); let c = Channel[i32]::new(); let t = async(&p) wait(&c); return t.cancel() - 1;",
    ] {
        let mut program = Compiler::compile_source(&format!("{prelude}pub fn main() -> i32 {{ {body} }}")).unwrap();
        let mut values = Vec::new();
        for seed in 1..=8 {
            let run = super::run_vm_scheduled(&mut program, Some(seed)).unwrap_or_else(|e| panic!("seed {seed}: {e}"));
            assert_eq!(run.leaks, 0, "seed {seed}");
            values.push(run.value);
        }
        values.dedup();
        assert_eq!(values.len(), 1, "{values:?}");
    }
    // Under fibers alone neither could finish: each spins until it has seen the other.
    let together = "static mut A: u32 = 0;
static mut B: u32 = 0;
fn left() -> i32 { unsafe { @atomic_store(&raw mut A, 1); while @atomic_load(&raw mut B) == 0 { } } return 1; }
fn right() -> i32 { unsafe { @atomic_store(&raw mut B, 1); while @atomic_load(&raw mut A) == 0 { } } return 2; }
pub fn main() -> i32 { let p = WorkerPool::new(2); let a = async(&p) left(); let b = async(&p) right(); return a.await() + b.await(); }";
    assert_eq!(run_lli("really_parallel", together), Some(3));
    assert_rejected(
        "task_outlives_the_pool",
        &format!("{prelude}fn bad() -> Task[i32] {{ let p = WorkerPool::new(1); return async(&p) sq(2); }}\npub fn main() -> i32 {{ return bad().await(); }}"),
        "already borrowed",
    );
    assert_rejected(
        "argument_not_send",
        &format!("{prelude}fn use_it(p: *mut i32) -> i32 {{ return 1; }}\npub fn main() -> i32 {{ let w = WorkerPool::new(1); let mut x: i32 = 1; let r = &raw mut x; let t = async(&w) use_it(r); return t.await(); }}"),
        "does not satisfy comptime constraint 'send'",
    );
}

#[test]
fn test_atomic_stores_keep_to_their_width() {
    // Each store must leave the static after it alone, which a wider one would overwrite.
    for ty in ["u8", "u16", "u32", "u64", "i8", "i16", "i32"] {
        assert_runs(
            ty,
            &format!(
                "static mut A: [{ty}; 2] = {{ 9, 9 }};
pub fn main() -> i32 {{
    unsafe {{
        @atomic_store(&raw mut A[0], 1);
        return A[0] as i32 * 10 + A[1] as i32;
    }}
}}"
            ),
            19,
        );
    }
}

#[test]
fn test_wakes_between_workers_are_fast() {
    // Natively, as the VM's threads take turns: thousands of wakes between workers in a time that
    // only direct wakes can manage, since one that goes missing waits 1 to 50 ms for a look.
    let src = "fn ping(a: &Channel[i32], b: &Channel[i32], n: i32) -> i32 { for i in 0..n { let _s = a.send(i); let _r = b.recv() catch |e| 0; } return 0; }
fn pong(a: &Channel[i32], b: &Channel[i32], n: i32) -> i32 { for i in 0..n { let r = a.recv() catch |e| 0; let _s = b.send(r); } return 0; }
fn bump(m: &Mutex[i32], n: i32) -> i32 { for i in 0..n { let mut g = m.lock(); let v = g.get_mut(); *v = *v + 1; g.unlock(); } return 0; }
pub fn main() -> i32 {
    let p = WorkerPool::new(2);
    let a = Channel[i32]::with_capacity(1);
    let b = Channel[i32]::with_capacity(1);
    let start = now_ms();
    let x = async(&p) ping(&a, &b, 3000);
    let y = async(&p) pong(&a, &b, 3000);
    let _u = x.await();
    let _v = y.await();
    let m = Mutex[i32]::new(0);
    let mut ts = Vec[Task[i32]]::new();
    for i in 0..8 { ts.push(async(&p) bump(&m, 3000)); }
    while let t = ts.pop() { let _w = t.await(); }
    let mut g = m.lock();
    let total = *g.get_mut();
    g.unlock();
    if total != 24000 { return 2; }
    return (now_ms() - start > 1500) as i32;
}";
    assert_eq!(run_lli("fast_wakes", src), Some(0));
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
fn test_wakes_between_threads_are_not_missed() {
    // A fiber that waits for another thread joins its wait list before it lets go of the lock
    // (or, waiting for a lock, before trying it a last time), so a wake straight after cannot pass
    // it by. A wake that did would only cost a delay, until the periodic look for missed ones, so
    // the clock is stopped here and such a program would never finish. The seeds that catch a
    // wrong order are among those that keep one thread running long enough to fit in the window.
    for (name, src) in [
        // `Channel` waits on a condition.
        ("condition", "fn ping(a: &Channel[i32], b: &Channel[i32], n: i32) -> i64 {
    for i in 0..n { let _s = a.send(i); let _r = b.recv() catch |e| 0; }
    return 0;
}
fn pong(a: &Channel[i32], b: &Channel[i32], n: i32) -> i64 {
    for i in 0..n { let v = a.recv() catch |e| 0; let _s = b.send(v); }
    return 0;
}
pub fn main() -> i32 {
    let p = WorkerPool::new(2);
    let a = Channel[i32]::new();
    let b = Channel[i32]::new();
    let x = async(&p) ping(&a, &b, 20);
    let y = async(&p) pong(&a, &b, 20);
    return (x.await() + y.await()) as i32;
}"),
        // Each round, one task tries the lock just as the other lets go of it.
        ("lock", "fn holder(m: &Mutex[i32], c: &[Channel[i32]; 3], n: i32) -> i64 {
    for i in 0..n {
        let g = m.lock();
        let _held = c[0].send(i);
        let _trying = c[1].recv() catch |e| 0;
        g.unlock();
        let _done = c[2].recv() catch |e| 0;
    }
    return 0;
}
fn waiter(m: &Mutex[i32], c: &[Channel[i32]; 3], n: i32) -> i64 {
    for i in 0..n {
        let _held = c[0].recv() catch |e| 0;
        let _trying = c[1].send(i);
        let g = m.lock();
        g.unlock();
        let _done = c[2].send(i);
    }
    return 0;
}
pub fn main() -> i32 {
    let p = WorkerPool::new(2);
    let m = Mutex[i32]::new(0);
    let c: [Channel[i32]; 3] = { Channel[i32]::new(), Channel[i32]::new(), Channel[i32]::new() };
    let x = async(&p) holder(&m, &c, 20);
    let y = async(&p) waiter(&m, &c, 20);
    let w = x.await() + y.await();
    return w as i32;
}"),
    ] {
        let mut program = Compiler::compile_source(src).unwrap_or_else(|e| panic!("[{name}] {e}"));
        for seed in 1..=10 {
            let run = crate::tests::run_vm_frozen(&mut program, seed, 2_000_000)
                .unwrap_or_else(|e| panic!("[{name}, seed {seed}] {e}"));
            assert_eq!((run.value, run.leaks), (0, 0), "[{name}, seed {seed}]");
        }
    }
}

#[test]
fn test_arrays_drop_their_elements() {
    let prelude = "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + self.v; } } } }
struct W { a: [D; 2] }
union U { A, B([D; 2]) }
fn d(v: i32) -> D { return D::new(v); }
";
    for (name, body, value) in [
        ("plain", "if true { let a: [D; 2] = { d(1), d(2) }; }", 3),
        ("nested", "if true { let a: [[D; 2]; 2] = { { d(1), d(2) }, { d(4), d(8) } }; }", 15),
        ("in_a_struct", "if true { let s = W { a: { d(1), d(2) } }; }", 3),
        ("in_a_union", "if true { let u = U::B({ d(1), d(2) }); }", 3),
        ("in_an_optional", "if true { let o: ?[D; 2] = null; let a: [D; 2] = { d(1), d(2) }; let p: ?[D; 2] = move a; }", 3),
        ("moved_whole", "if true { let a: [D; 2] = { d(1), d(2) }; let b = move a; }", 3),
        ("moved_on_one_path", "if true { let a: [D; 2] = { d(1), d(2) }; if true { let b = move a; } }", 3),
        // Overwriting an element drops the one it replaces.
        ("overwritten", "if true { let mut a: [D; 2] = { d(1), d(2) }; a[0] = d(4); }", 7),
        ("overwritten_deep", "if true { let mut s = W { a: { d(1), d(2) } }; s.a[1] = d(4); }", 7),
        ("overwritten_through_a_reference", "if true { let mut a: [D; 2] = { d(1), d(2) }; let r = &mut a; r[1] = d(4); }", 7),
        ("replaced", "if true { let mut a: [D; 2] = { d(1), d(2) }; let x = core::mem::replace(&mut a[0], d(4)); }", 7),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} return unsafe {{ DROPS }}; }}"), value);
    }
    // Which element an index names is not known when checking moves, so none goes alone.
    for (name, body, message) in [
        ("move_by_index", "let a: [D; 2] = { d(1), d(2) }; let x = move a[0]; return 0;", "out of an array by index"),
        ("copy_by_index", "let a: [D; 2] = { d(1), d(2) }; let x = a[1]; return 0;", "out of an array by index"),
        ("write_into_moved", "let mut a: [D; 2] = { d(1), d(2) }; let b = move a; a[0] = d(4); return 0;", "moved or uninitialized"),
    ] {
        assert_rejected(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), message);
    }
}

#[test]
fn test_generic_type_declarations() {
    // `struct Pair[T] { ... }` is the type function `fn Pair[T] -> type { return struct { ... }; }`.
    let prelude = "struct Pair[T] { first: T, second: T,
    pub fn swapped(self: &Self) -> Self where T: copy { return Self { first: self.second, second: self.first }; } }
union Maybe[T] { None, Some(T) }
overlay Bits[T] { value: T, raw: u64 }
packed struct Flags[N: usize] { on: u1, rest: u7 }
static mut DROPS: i32 = 0;
opaque Guard[T, N: i32 = 3] { value: T,
    pub fn new(value: T) -> Self { return Self { value: value }; }
    pub fn weight(self: &Self) -> i32 { return N; }
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS = DROPS + N; } } } }
struct Tree[V] { value: V, kids: Vec[Tree[V]] }
trait Size { fn size(self: &Self) -> i32; }
impl[T] Size for Pair[T] { fn size(self: &Self) -> i32 { return 2; } }
fn count[V](t: &Tree[V]) -> i32 { let mut n = 1; for ref k in t.kids.as_slice() { n = n + count(k); } return n; }
fn unwrap_or(m: Maybe[i32], d: i32) -> i32 { match m { .Some(v) => { return v; } _ => { return d; } } }
fn first_of(p: Pair[i32]) -> i32 { return p.first; }
";
    for (name, body, value) in [
        ("fields", "let p = Pair[i32] { first: 1, second: 2 }; return p.first * 10 + p.second;", 12),
        ("method", "let o = Pair[i32] { first: 1, second: 2 }; let p = o.swapped(); return p.first * 10 + p.second;", 21),
        ("same_type_each_time", "return first_of(Pair[i32] { first: 4, second: 5 });", 4),
        ("union", "return unwrap_or(Maybe[i32]::Some(7), 0) * 10 + unwrap_or(.None, 3);", 73),
        ("overlay", "return @size_of(Bits[u8]) as i32;", 8),
        ("packed", "return @size_of(Flags[4]) as i32;", 1),
        ("default_parameter", "let g = Guard[i64]::new(1); return g.weight();", 3),
        ("given_parameter", "let g = Guard[i64, 5]::new(1); return g.weight();", 5),
        ("drop_hook", "if true { let a = Guard[i32]::new(1); let b = Guard[i32, 10]::new(2); } return unsafe { DROPS };", 13),
        ("recursive", "let mut t = Tree[i64] { value: 1, kids: Vec[Tree[i64]]::new() }; t.kids.push(Tree[i64] { value: 2, kids: Vec[Tree[i64]]::new() }); return count(&t);", 2),
        ("trait", "let p = Pair[u8] { first: 1, second: 2 }; return p.size();", 2),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // A value argument used to be rejected whenever the first type the compiler made was a trait.
    assert_runs(
        "value_parameter_after_a_trait",
        "trait Width { fn size(self: &Self) -> i32; }\nfn q[N: i32]() -> i32 { return N; }\npub fn main() -> i32 { return q[4](); }",
        4,
    );
    // The long form is the same type: either spelling names it.
    assert_runs(
        "long_form",
        "fn Wrap[T] -> type { return struct { v: T }; }
struct Same[T] { v: T }
fn get(w: Wrap[i32]) -> i32 { return w.v; }
pub fn main() -> i32 { return get(Wrap[i32] { v: 6 }) + @size_of(Same[i64]) as i32; }",
        14,
    );
    for (name, src, message) in [
        ("export", "export struct Pair[T] { a: T }\npub fn main() -> i32 { return 0; }", "cannot be exported"),
        ("constraint", "struct Num[T: integer] { v: T }\npub fn main() -> i32 { let n = Num[f64] { v: 1.0 }; return 0; }", "integer"),
        ("where_clause", "struct P[T] { a: T, pub fn get(self: &Self) -> T where T: copy { return self.a; } }\npub fn main() -> i32 { let p = P[String] { a: String::from(\"x\") }; let s = p.get(); return 0; }", "get"),
    ] {
        assert_rejected(name, src, message);
    }
}

#[test]
fn test_generic_paths() {
    let prelude = "union Maybe[T] { None, Some(T) }
struct Pair[T] { first: T, second: T, pub fn sum(self: &Self) -> T where T: integer { return self.first + self.second; } }
opaque K[T] { pub const N: i32 = 7; v: T }
fn unwrap(m: Maybe[i32]) -> i32 { match m { Maybe[i32]::Some(v) => { return v; } Maybe[i32]::None => { return -1; } } }
";
    for (name, body, value) in [
        ("unit_variant", "return unwrap(Maybe[i32]::None) + 2;", 1),
        ("variant", "return unwrap(Maybe[i32]::Some(5));", 5),
        ("if_let", "let m = Maybe[i32]::Some(3); if let Maybe[i32]::Some(v) = m { return v; } return 0;", 3),
        ("while_let", "let mut m = Maybe[i32]::Some(3); let mut n = 0; while let Maybe[i32]::Some(v) = m { n = n + v; m = Maybe[i32]::None; } return n;", 3),
        ("struct_pattern", "let p = Pair[i32] { first: 4, second: 2 }; match p { Pair[i32] { first, .. } => { return first; } }", 4),
        ("let_struct", "let p = Pair[i32] { first: 4, second: 2 }; let Pair[i32] { first, second: s } = p; return first * 10 + s;", 42),
        ("nested", "let m = Maybe[Pair[i32]]::Some(Pair[i32] { first: 1, second: 2 }); match m { Maybe[Pair[i32]]::Some(Pair[i32] { first, second }) => { return first * 10 + second; } _ => { return 0; } }", 12),
        ("or_pattern", "let m = Maybe[i32]::None; match m { Maybe[i32]::None | Maybe[i32]::Some(0) => { return 8; } _ => { return 0; } }", 8),
        ("const", "return K[u8]::N + K[i64]::N;", 14),
        // A literal can be the start of a longer expression.
        ("literal_method", "return Pair[i32] { first: 1, second: 2 }.sum();", 3),
        ("literal_field", "return Pair[i32] { first: 1, second: 2 }.second;", 2),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, src) in [
        ("other_union", "union A { X(i32), Y }\nunion B { X(i32), Y }\npub fn main() -> i32 { let a = A::X(1); match a { B::X(v) => { return v; } _ => { return 0; } } }"),
        ("other_enum", "enum A { X, Y }\nenum B { X, Y }\npub fn main() -> i32 { let a = A::X; match a { B::X => { return 1; } _ => { return 0; } } }"),
    ] {
        assert_rejected(name, src, "not the type of the value matched");
    }
    assert_rejected(
        "other_instance",
        &format!("{prelude}pub fn main() -> i32 {{ let m = Maybe[i32]::Some(3); match m {{ Maybe[u8]::Some(v) => {{ return 1; }} _ => {{ return 0; }} }} }}"),
        "not the type of the value matched",
    );
}

#[test]
fn test_generic_types_infer_their_arguments_in_static_calls() {
    let prelude = "struct H[T] {
    v: T,
    pub fn make(v: T) -> Self { return Self { v: v }; }
    pub fn get(h: &H[T]) -> &T borrows(h) { return &h.v; }
}
struct Q[T] { v: T, pub fn pair(a: T, b: T) -> Self { return Self { v: b }; } }
struct P[A, B] { a: A, b: B, pub fn of(a: A, b: B) -> Self { return Self { a: a, b: b }; } }
opaque E[T] { v: ?T, pub fn empty() -> Self { return Self { v: null }; } }
struct Num {
    v: i64,
    pub fn of[T: integer](x: T) -> Self { return Self { v: x as i64 }; }
    pub fn pair[A, B](a: A, b: B) -> tuple { A, B } { return { a, b }; }
    pub fn sized[T, N: usize = 4](x: T) -> usize { return N; }
    pub fn make[T]() -> i32 { return 0; }
}
struct W[T] { v: T, pub fn with[U](v: T, u: U) -> U { return u; } }
";
    for (name, body, value) in [
        ("value", "let k = H::make(7 as i32); return k.v;", 7),
        ("reference", "let x: i32 = 5; let h = H::make(&x); return *h.v;", 5),
        // `T` from `&H[T]`.
        ("through_a_reference", "let k = H::make(4 as i32); return *H::get(&k);", 4),
        // The literal takes the type the other argument gives `T`.
        ("literal_typed_by_another", "let y: i8 = 3; let m = Q::pair(1, y); return m.v as i32;", 3),
        ("two_parameters", "let p = P::of(true, 2 as u8); return p.b as i32;", 2),
        // A default fills what the arguments do not give (`Box`'s allocator).
        ("default", "let b = Box::new(6 as i32); return *b.get();", 6),
        ("same_as_brackets", "let a = H::make(1 as i32); let b: H[i32] = a; return b.v;", 1),
        // A static method's own parameters, from its arguments.
        ("method_parameter", "let n = Num::of(7 as u8); return n.v as i32;", 7),
        ("method_parameters", "let p = Num::pair(true, 3 as i16); return p.1 as i32;", 3),
        ("method_default", "return Num::sized(1 as u8) as i32;", 4),
        ("method_on_an_instance", "return W[i32]::with(1, 9 as u8) as i32;", 9),
        ("method_and_type", "return W::with(2 as i32, 5 as u16) as i32;", 5),
        ("method_brackets", "let n = Num::of[i32](4); return n.v as i32;", 4),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "nothing_to_infer_from",
        &format!("{prelude}pub fn main() -> i32 {{ let e = E::empty(); return 0; }}"),
        "Cannot infer 'T' of 'E' from the arguments of 'E::empty'; give it in brackets, 'E[...]::empty(...)'",
    );
    // Inside its own members, a generic type's bare name is the instance they belong to.
    assert_runs(
        "bare_name_inside",
        "struct B[T] { v: T, pub fn make(v: T) -> B { return B { v: v }; } pub fn other(self: &Self) -> B[u8] { return B[u8] { v: 1 }; } }
pub fn main() -> i32 { let b = B[i32]::make(4); return b.v + (b.other().v as i32); }",
        5,
    );
    assert_rejected(
        "bare_name_outside",
        "struct B[T] { v: T }\npub fn main() -> i32 { let b = B[i32] { v: 1 }; let c: B = b; return 0; }",
        "'B' is generic; give its arguments ('B[...]'), or write 'Self' inside its own methods",
    );
    // A member naming an ever deeper instance is refused, and quickly: each function that
    // names the type fails alike, and those count toward the compile's limit on errors.
    let started = std::time::Instant::now();
    assert_rejected(
        "nests_without_end",
        "struct N[T] { v: T, pub fn twice(self: &Self) -> N[N[T]] where T: copy { return N[N[T]] { v: Self { v: self.v } }; } }
pub fn main() -> i32 { let n = N[i32] { v: 4 }; return n.twice().v.v; }",
        "Instantiating 'N' nests it in itself without end",
    );
    assert!(started.elapsed() < std::time::Duration::from_secs(20), "{:?}", started.elapsed());
    // Two instances of one generic are told apart.
    assert_rejected(
        "instances_named",
        &format!("{prelude}pub fn main() -> i32 {{ let a = H::make(1 as i64); let h: H[i8] = a; return 0; }}"),
        "cannot implicitly convert 'H[i64]' to 'H[i8]'",
    );
    assert_rejected(
        "method_nothing_to_infer_from",
        &format!("{prelude}pub fn main() -> i32 {{ return Num::make(); }}"),
        "Cannot infer 'T' of 'Num::make' from its arguments; give it in brackets, 'Num::make[...](...)'",
    );
    assert_rejected(
        "outlived",
        &format!("{prelude}pub fn main() -> i32 {{ let y: i32 = 1; let mut h = H::make(&y); if true {{ let x: i32 = 5; h = H::make(&x); }} return *h.v; }}"),
        "'x' goes out of scope while still borrowed",
    );
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
        ("field", "let mut p: tuple { u32, u32 } = { 6, 0 }; p.0 <<= 4; p.0 |= 1; return p.0 as i32;", 97),
        ("element", "let mut a: [u16; 2] = { 255, 0 }; a[0] &= 15; a[1] ^= 3; return (a[0] + a[1]) as i32;", 18),
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
opaque E[T] { v: ?T, pub fn empty() -> Self { return Self { v: null }; } pub fn has(self: &Self) -> bool { return self.v != null; } }
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
fn test_std_owners_and_guards_share_their_accessors() {
    // `get` and `get_mut` on each type that owns or guards one value.
    assert_runs(
        "accessors",
        "pub fn main() -> i32 {
    let mut m = Mutex::new(3 as i32);
    *m.get_mut() += 1;
    let g = m.lock();
    let seen = *g.get();
    g.unlock();
    let mut s = unsafe { UnsafeSend[i32]::new(5) };
    *s.get_mut() += 1;
    let mut y = unsafe { UnsafeSync[i32]::new(7) };
    *y.get_mut() *= 2;
    let mut b = Box::new(1 as i32);
    *b.get_mut() = 2;
    return seen + *s.get() + *y.get() + *b.get();
}",
        26,
    );
    // `Mutex::get_mut` needs no lock because a `&mut Mutex` excludes every guard.
    assert_rejected(
        "get_mut_while_locked",
        "pub fn main() -> i32 { let mut m = Mutex::new(3 as i32); let g = m.lock(); let r = m.get_mut(); g.unlock(); return 0; }",
        "cannot borrow 'm' as mutable because 'm' is already borrowed as immutable",
    );
}

#[test]
fn test_union_and_error_payloads_are_spelled_alike() {
    assert_runs(
        "parentheses",
        "union Shape { Circle(i32), Pair(tuple { i32, i32 }), Empty }
error(i16) Fail { Bad(i32) = 10, Coords(struct { x: i32, y: i32 }) = 11, Worse = -5 }
fn fails(n: i32) -> Fail!i32 { if n > 0 { return Fail::Bad(n); } return 0; }
pub fn main() -> i32 {
    let s = Shape::Pair({ 2, 3 });
    let a = match s { Shape::Pair(p) => p.0 * p.1, Shape::Circle(r) => r, Shape::Empty => 0 };
    let b = fails(4) catch |e| match e { Fail::Bad(n) => n, _ => 0 };
    return a + b;
}",
        10,
    );
    for (name, src, what) in [
        ("union_colon", "union Shape { Circle: i32, Empty }\npub fn main() -> i32 { return 0; }", "A union variant's payload goes in parentheses: write 'Circle(T)', not 'Circle: T'"),
        ("error_colon", "error Fail { Bad: i32 }\npub fn main() -> i32 { return 0; }", "An error variant's payload goes in parentheses: write 'Bad(T)', not 'Bad: T'"),
    ] {
        assert_rejected(name, src, what);
    }
}

#[test]
fn test_optionals_print_as_some_or_null() {
    assert_runs(
        "formats",
        "struct P { a: ?i32, b: ?i32 }
union U { None, Some(i32) }
pub fn main() -> i32 {
    let x: ?i32 = 5;
    let n: ?i32 = null;
    let inner_null: ??i32 = n;
    let outer_null: ??i32 = null;
    let nested: ??i32 = x;
    let s: ?&str = \"null\";
    let text = format(f\"{x} {n} {nested} {inner_null} {outer_null} {s} {P { a: 1, b: null }} {U::Some(3)} {x:03}\");
    @assert(text.as_str() == \"some(5) null some(some(5)) some(null) null some(null) P { a: some(1), b: null } U::Some(3) some(005)\");
    return 0;
}",
        0,
    );
}

#[test]
fn test_results_print_as_ok_or_err() {
    assert_runs(
        "formats",
        "error E { Bad, Code(i32) }
fn f(n: i32) -> E!i32 { if n < 0 { return E::Code(n); } if n == 0 { return E::Bad; } return n; }
fn g() -> E!void { return; }
pub fn main() -> i32 {
    let nested: E!?i32 = 3;
    let text = format(f\"{f(5)} {f(-2)} {f(0)} {g()} {nested} {f(5):03}\");
    @assert(text.as_str() == \"ok(5) err(E::Code(-2)) err(E::Bad) ok() ok(some(3)) ok(005)\");
    return 0;
}",
        0,
    );
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
fn test_defer() {
    let prelude = "error E { Bad }
fn parse(n: i32) -> E!i32 { if n < 0 { return E::Bad; } return n; }
static mut LOG: i64 = 0;
fn note(d: i64) { unsafe { LOG = LOG * 10 + d; } }
fn log() -> i64 { return unsafe { LOG }; }
opaque(linear) Tx { id: i32, pub fn begin(id: i32) -> Self { return Self { id: id }; } pub fn commit(move self) -> i32 { note(9); return self.id; } }
";
    // Each program checks the order its deferred statements ran in, as digits of `log()`.
    for (name, body) in [
        // The end of the block, in the reverse of the order written, among the variables.
        ("order", "if true { defer note(1); defer note(2); note(3); } @assert(log() == 321); return 0;"),
        ("inner_block_first", "if true { defer note(1); if true { defer note(2); } note(3); } @assert(log() == 231); return 0;"),
        // Each way out runs it.
        ("return", "fn f(b: bool) -> i32 { defer note(1); if b { return 5; } note(2); return 6; }
pub fn main() -> i32 { let a = f(true); let b = f(false); @assert(a == 5 && b == 6 && log() == 121); return 0; }"),
        ("break_and_continue", "let mut n = 0; for i in 0..5 { defer n += 10; if i == 1 { continue; } if i == 3 { break; } n += 1; } @assert(n == 42); return 0;"),
        // A loop inside the deferred statement may be left.
        ("loop_inside", "let mut n = 0; if true { defer for i in 0..10 { if i == 3 { break; } n += 1; } } @assert(n == 3); return 0;"),
        // It sees what came before it, not what came after.
        ("shadowed", "let x = 1; let mut seen = 0; if true { defer seen = x; let x = 2; } @assert(seen == 1); return 0;"),
        ("block", "if true { defer { note(1); note(2); } note(3); } @assert(log() == 312); return 0;"),
        ("if", "let x = 2; if true { defer if x > 1 { note(7); } } @assert(log() == 7); return 0;"),
        // It consumes a linear value on every path.
        ("linear", "fn f(fail: bool) -> E!i32 { let tx = Tx::begin(4); defer _ = tx.commit(); if fail { return E::Bad; } return 1; }
pub fn main() -> i32 { let a = f(false) catch 0; let b = f(true) catch 2; @assert(a == 1 && b == 2 && log() == 99); return 0; }"),
    ] {
        let src = if body.starts_with("fn ") {
            format!("{prelude}{body}")
        } else {
            format!("{prelude}pub fn main() -> i32 {{ {body} }}")
        };
        assert_runs(name, &src, 0);
    }
    // A lock held across a `try`: the guard is unlocked whichever way the function returns.
    assert_runs(
        "guard_across_try",
        &format!("{prelude}fn add(m: &Mutex[i32], n: i32) -> E!i32 {{
    let mut g = m.lock();
    defer g.unlock();
    let v = try parse(n);
    *g.get_mut() += v;
    return *g.get();
}}
pub fn main() -> i32 {{
    let m = Mutex::new(1 as i32);
    let a = add(&m, 2) catch 0;
    let b = add(&m, -1) catch 50;
    let c = add(&m, 4) catch 0;
    return a + b + c;
}}"),
        60,
    );
    for (name, body, what) in [
        ("return", "defer return 1; return 0;", "'return' cannot be used in a 'defer' or 'errdefer'"),
        ("orelse_return", "let o: ?i32 = 3; defer { let v = o orelse return 0; } return 0;", "'return' cannot be used in a 'defer' or 'errdefer'"),
        ("break_out", "for i in 0..3 { defer break; } return 0;", "'break' cannot be used in a 'defer' or 'errdefer'"),
        ("continue_out", "for i in 0..3 { defer { continue; } } return 0;", "'continue' cannot be used in a 'defer' or 'errdefer'"),
        ("later_variable", "defer note(y); let y: i64 = 1; return 0;", "Cannot resolve value path 'y'"),
        ("unused_result", "defer parse(1); return 0;", "This discards an error union"),
        ("consumed_twice", "let m = Mutex::new(1 as i32); let g = m.lock(); defer g.unlock(); g.unlock(); return 0;", "Use of moved or uninitialized value 'g'"),
        ("defer_defer", "defer defer note(1); return 0;", "defers nothing more"),
    ] {
        assert_rejected(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), what);
    }
    assert_rejected(
        "try",
        &format!("{prelude}fn g() -> E!i32 {{ defer _ = try parse(1); return 0; }}\npub fn main() -> i32 {{ return g() catch 1; }}"),
        "'try' cannot be used in a 'defer' or 'errdefer'",
    );
    // `defer` is a word otherwise.
    assert_runs("a_variable", "pub fn main() -> i32 { let defer = 3; return defer - 3; }", 0);
}

#[test]
fn test_errdefer() {
    let prelude = "error E { Bad, Worse }
static mut LOG: i64 = 0;
fn note(d: i64) { unsafe { LOG = LOG * 10 + d; } }
fn log() -> i64 { return unsafe { LOG }; }
fn reset() { unsafe { LOG = 0; } }
opaque(linear) Tx {
    id: i32,
    pub fn begin(id: i32) -> Self { return Self { id: id }; }
    pub fn commit(move self) -> i32 { note(1); return self.id; }
    pub fn rollback(move self) { note(2); }
}
fn check(n: i32) -> E!i32 { if n < 0 { return E::Bad; } return n; }
fn inner(n: i32) -> E!i32 { if n == 13 { return E::Worse; } return n; }
/// Committed on success, rolled back on any error, whichever way it comes.
fn transfer(n: i32) -> E!i32 {
    let tx = Tx::begin(n);
    errdefer tx.rollback();
    let v = try check(n);
    if v == 7 {
        return E::Bad;
    }
    let w = inner(v) catch |e| return e;
    return tx.commit() + w - w;
}
/// An `E!T` returned as it is: which way is known at run time.
fn passthrough(r: E!i32) -> E!i32 {
    errdefer note(4);
    defer note(3);
    return r;
}
fn in_loop() -> E!i32 {
    let mut n = 0;
    for i in 0..3 {
        errdefer note(9);
        n += i;
    }
    return n;
}
";
    let body = "
    @assert((transfer(5) catch 0) == 5 && log() == 1);
    reset();
    @assert((transfer(-1) catch 0) == 0 && log() == 2);     // a failed `try`
    reset();
    @assert((transfer(7) catch 0) == 0 && log() == 2);      // `return E::Bad`
    reset();
    @assert((transfer(13) catch 0) == 0 && log() == 2);     // `catch |e| return e`
    reset();
    @assert((passthrough(1) catch 0) == 1 && log() == 3);
    reset();
    @assert((passthrough(E::Bad) catch 0) == 0 && log() == 34);
    reset();
    @assert((in_loop() catch 0) == 3 && log() == 0);        // the loop body ends normally
    return 0;";
    assert_runs("routes", &format!("{prelude}pub fn main() -> i32 {{{body}\n}}"), 0);
    for (name, src, what) in [
        ("not_fallible", "pub fn main() -> i32 { errdefer note(1); return 0; }", "'errdefer' runs when the function returns an error, which 'main' cannot"),
        ("optional", "fn f() -> ?i32 { errdefer note(1); return null; }\npub fn main() -> i32 { return f() orelse 0; }", "which 'f' cannot (it returns '?i32')"),
        // Checked where it is written, whether or not an error ever runs it.
        ("return", "fn f() -> E!i32 { errdefer return E::Bad; return 1; }\npub fn main() -> i32 { return f() catch 2; }", "'return' cannot be used in a 'defer' or 'errdefer'"),
        ("type", "fn f() -> E!i32 { errdefer { let x: bool = 5; } return 1; }\npub fn main() -> i32 { return f() catch 2; }", "cannot implicitly convert"),
        // A linear value still needs finishing on the paths that are not errors.
        ("success_unfinished", "fn f() -> E!i32 { let tx = Tx::begin(1); errdefer tx.rollback(); return 1; }\npub fn main() -> i32 { return f() catch 2; }", "Linear value 'tx' of type 'Tx' must be explicitly consumed"),
    ] {
        assert_rejected(name, &format!("{prelude}{src}"), what);
    }
    assert_runs("a_variable", "pub fn main() -> i32 { let errdefer = 1; return errdefer - 1; }", 0);
    // `errdefer |e|`: the error being returned, a copy, or a reference to one that is not `copy`.
    assert_runs(
        "named",
        "error E { Bad, Code(i32) }
error Owned { Msg(String) }
static mut SEEN: i32 = 0;
fn check(n: i32) -> E!i32 { if n < 0 { return E::Code(n); } return n; }
fn work(n: i32) -> E!i32 {
    errdefer |e| { match e { E::Bad => unsafe { SEEN = 1; }, E::Code(c) => unsafe { SEEN = c; } } }
    let v = try check(n);
    if v == 7 { return E::Bad; }
    return v;
}
fn owned(fail: bool) -> Owned!i32 {
    errdefer |e| { let text = format(f\"{e}\"); unsafe { SEEN = text.len() as i32; } }
    if fail { return Owned::Msg(String::from(\"disk full\")); }
    return 1;
}
pub fn main() -> i32 {
    @assert((work(3) catch 0) == 3 && unsafe { SEEN } == 0);
    @assert((work(-2) catch 0) == 0 && unsafe { SEEN } == -2);
    @assert((work(7) catch 0) == 0 && unsafe { SEEN } == 1);
    @assert((owned(true) catch 0) == 0 && unsafe { SEEN } == 21);   // \"Owned::Msg(disk full)\"
    return 0;
}",
        0,
    );
    assert_rejected(
        "named_in_defer",
        "pub fn main() -> i32 { defer |e| println(\"x\"); return 0; }",
        "'defer |e|' names an error, which only 'errdefer' has",
    );
}

#[test]
fn test_catch_drops_an_unnamed_error() {
    // An error caught without a name is dropped: here its `String`, which would otherwise leak.
    assert_runs(
        "unnamed",
        "error Owned { Msg(String) }
fn owned(fail: bool) -> Owned!i32 { if fail { return Owned::Msg(String::from(\"disk full\")); } return 1; }
pub fn main() -> i32 { let a = owned(true) catch 2; let b = owned(true) catch |_| 3; return a + b; }",
        5,
    );
}

#[test]
fn test_optional_relative_references() {
    // `?&rel T`: null, or an offset into the value, which survives moves; 0 is `null`, as no
    // field refers to itself, so it takes no more room than `&rel T`.
    assert_runs(
        "elem",
        "opaque MyOpaque {
    foo: i32,
    bar: i32,
    state: ?&rel i32,
    pub fn new() -> Self { return Self { foo: 1, bar: 2, state: null }; }
    pub fn pick(self: &mut Self, which: i32) {
        if which == 0 { self.state = null; } else if which == 1 { self.state = &rel self.foo; } else { self.state = &rel self.bar; }
    }
    pub fn get(self: &Self) -> ?i32 { let r = self.state orelse return null; return *r; }
    pub fn bump(self: &mut Self) { if let r = &mut self.state { *r += 10; } }
}
pub fn main() -> i32 {
    let mut m = MyOpaque::new();
    @assert(m.get() == null);
    m.pick(1);
    @assert((m.get() orelse 0) == 1);
    m.pick(2);
    m.bump();
    let moved = m;
    @assert((moved.get() orelse 0) == 12);
    let mut again = moved;
    again.pick(0);
    @assert(again.get() == null && @size_of(MyOpaque) == 16);
    return 0;
}",
        0,
    );
    assert_runs(
        "slices",
        "opaque W {
    buf: [u8; 6],
    text: ?&rel str,
    part: ?&rel [u8],
    pub fn new() -> Self { return Self { buf: b\"hello!\", text: null, part: &rel self.buf[1..3] }; }
    pub fn name(self: &mut Self) { self.text = &rel self.buf[0..5]; }
    pub fn text_len(self: &Self) -> usize { let t = self.text orelse return 0; return t.len; }
    pub fn part_first(self: &Self) -> u8 { let p = self.part orelse return 0; return p[0]; }
}
pub fn main() -> i32 {
    let mut w = W::new();
    @assert(w.text_len() == 0 && w.part_first() == 101);
    w.name();
    let moved = w;
    @assert(moved.text_len() == 5 && moved.part_first() == 101);
    return 0;
}",
        0,
    );
    for (name, src, what) in [
        ("outside_target", "opaque O { a: i32, s: ?&rel i32, pub fn set(self: &mut Self, x: &i32) { self.s = &rel *x; } }\npub fn main() -> i32 { return 0; }", "Co-Residence violation on 'O.s'"),
        ("wrong_type", "opaque O { a: i64, s: ?&rel i32, pub fn new() -> Self { return Self { a: 1, s: &rel self.a }; } }\npub fn main() -> i32 { let o = O::new(); return 0; }", "expected target of type i32, found i64"),
        ("not_a_reference", "opaque O { a: i32, s: ?&rel i32, pub fn new() -> Self { return Self { a: 1, s: 5 }; } }\npub fn main() -> i32 { let o = O::new(); return 0; }", "must be initialized or assigned with '&rel <place>' or 'null'"),
        ("in_struct", "struct S { a: i32, s: ?&rel i32 }\npub fn main() -> i32 { return 0; }", "only permitted in 'opaque' field declarations"),
        ("as_local", "pub fn main() -> i32 { let x: ?&rel i32 = null; return 0; }", "'?&rel' relative references are only permitted in 'opaque' field declarations"),
        // What it resolves to borrows the value, as `&rel T` does.
        ("borrow", "opaque O { a: i32, s: ?&rel i32,
  pub fn new() -> Self { return Self { a: 1, s: null }; }
  pub fn f(self: &mut Self) { self.s = &rel self.a; let r = &mut self.s; self.a = 5; if let x = r { *x = 2; } } }
pub fn main() -> i32 { let mut o = O::new(); o.f(); return 0; }", "cannot mutate or move 'self.a' because it is currently borrowed"),
    ] {
        assert_rejected(name, src, what);
    }
}

#[test]
fn test_byte_strings() {
    // `b"..."` is the `[u8; N]` of its bytes: escapes, ASCII only, no terminating zero.
    assert_runs(
        "arrays",
        "const MAGIC: [u8; 4] = b\"\\x7fELF\";
static GREETING: [u8; 5] = b\"hello\";
fn sum(bytes: &[u8]) -> i32 { let mut n = 0; for b in bytes { n += b as i32; } return n; }
pub fn main() -> i32 {
    let a: [u8; 4] = b\"blah\";
    let inferred = b\"ab\";
    let two: [u8; 2] = inferred;
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
        ("size", "let a: [u8; 8] = b\"blah\";", "cannot implicitly convert '[u8; 4]' to '[u8; 8]'"),
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
        "fn method(line: &[u8]) -> i32 {
    match line {
        b\"GET\" => { return 1; }
        b\"POST\" | b\"PUT\" => { return 2; }
        b\"\" => { return 3; }
        _ => { return 0; }
    }
}
pub fn main() -> i32 {
    let tag: [u8; 4] = b\"\\x7fELF\";
    @assert(match tag { b\"\\x7fELF\" => true, _ => false });
    @assert(method(&b\"GET\") == 1 && method(&b\"PUT\") == 2 && method(&b\"\") == 3 && method(&b\"GETS\") == 0);
    let buf: [u8; 8] = b\"GET /ok!\";
    if let b\"GET /ok!\" = buf { return 0; }
    return 9;
}",
        0,
    );
    assert_rejected(
        "pattern_length",
        "pub fn main() -> i32 { let t: [u8; 4] = b\"abcd\"; return match t { b\"abc\" => 1, _ => 0 }; }",
        "Array pattern has 3 element(s), but '[u8; 4]' has length 4",
    );
}

#[test]
fn test_reflection_needs_a_bound_that_promises_the_shape() {
    let prelude = "struct P { x: i32, y: i32 }
enum C { R, G }
";
    // A bound that says the parameter has fields (or variants), or `unchecked`.
    for (name, body, value) in [
        ("fields_struct", "fn n[T: struct]() -> usize { return @fields(T).len; }\npub fn main() -> i32 { return n[P]() as i32; }", 2),
        ("fields_aggregate_and_copy", "fn n[T: copy + aggregate]() -> usize { return @fields(T).len; }\npub fn main() -> i32 { return n[P]() as i32; }", 2),
        ("leaves_tuple", "fn n[T: tuple]() -> usize { let mut k: usize = 0; comptime for p in @leaves(T) { k += 1; } return k; }\npub fn main() -> i32 { return n[tuple { i32, tuple { u8, u8 } }]() as i32; }", 3),
        ("variants_enum", "fn n[T: enum]() -> usize { return @variants(T).len; }\npub fn main() -> i32 { return n[C]() as i32; }", 2),
        ("unchecked", "fn n[T: unchecked]() -> usize { return @fields(T).len; }\npub fn main() -> i32 { return n[P]() as i32; }", 2),
        // Reflecting over a named type, not the parameter, needs nothing.
        ("concrete", "fn n[T]() -> usize { return @fields(P).len; }\npub fn main() -> i32 { return n[i32]() as i32; }", 2),
        // A question any type answers.
        ("has_field", "fn n[T]() -> bool { return @has_field(T, \"x\"); }\npub fn main() -> i32 { return if n[P]() && !n[i32]() { 1 } else { 0 }; }", 1),
        ("method_with_bound", "struct W[T: struct] { v: T, pub fn count(self: &Self) -> usize { return @fields(T).len; } }\npub fn main() -> i32 { let w = W[P] { v: P { x: 1, y: 2 } }; return w.count() as i32; }", 2),
        // A function computing a type runs with real types, so it is not held to this.
        ("type_function", "fn First[T] -> type { comptime for f in @fields(T) { return f.ty; } return void; }\npub fn main() -> i32 { let x: First[P] = 2; return x; }", 2),
    ] {
        assert_runs(name, &format!("{prelude}{body}"), value);
    }
    // Refused where written, whether or not anything uses it.
    for (name, body, what) in [
        ("fields_plain", "fn n[T]() -> usize { return @fields(T).len; }", "Generic 'root::n' uses '@fields(T)', but 'T' is not bounded to a kind of type with fields"),
        ("leaves_copy", "fn n[T: copy]() -> usize { comptime for p in @leaves(T) { } return 0; }", "uses '@leaves(T)', but 'T' is not bounded to a kind of type with fields"),
        ("variants_struct", "fn n[T: struct]() -> usize { return @variants(T).len; }", "uses '@variants(T)', but 'T' is not bounded to a kind of type with variants"),
        ("fields_enum", "fn n[T: enum]() -> usize { return @fields(T).len; }", "uses '@fields(T)', but 'T' is not bounded to a kind of type with fields"),
        ("method", "struct W[T] { v: T, pub fn count(self: &Self) -> usize { return @fields(T).len; } }", "Method 'W::count' of generic type 'root::W' uses '@fields(T)'"),
        ("method_parameter", "struct W { v: i32, pub fn count[U](self: &Self) -> usize { return @fields(U).len; } }", "uses '@fields(U)'"),
    ] {
        assert_rejected(name, &format!("{prelude}{body}\npub fn main() -> i32 {{ return 0; }}"), what);
    }
    // `unchecked` checks each use, and says what is wrong there.
    assert_rejected(
        "unchecked_use",
        &format!("{prelude}fn n[T: unchecked]() -> usize {{ return @fields(T).len; }}\npub fn main() -> i32 {{ return n[i32]() as i32; }}"),
        "'@fields' expects a 'struct', 'tuple', or 'overlay' type, found 'i32'",
    );
}

#[test]
fn test_review_fixes_for_cancellation_and_cells() {
    // `try` on a `@select` whose arms give their own error: what is around a `@select` does not
    // make it wait for cancellation, so it gives what its arms do.
    assert_runs(
        "try_select_own_error",
        "error ParseError { Bad }
fn parse(v: i32) -> ParseError!i32 { if v < 0 { return .Bad; } return v * 2; }
fn first(a: &Channel[i32], b: &Channel[i32]) -> ParseError!i32 {
    return try @select { v = a.recv() => parse(v), w = b.recv() => parse(w) };
}
pub fn main() -> i32 {
    let a = Channel[i32]::new();
    let b = Channel[i32]::new();
    _ = a.send(4);
    return (first(&a, &b) catch 0) - 8;
}",
        0,
    );
    // Only `uncancelled { ... }` makes the guard, so guards cannot end out of order.
    assert_rejected(
        "uncancelled_guard_by_hand",
        "fn work() -> i32 { let g = Uncancelled::enter(); return 0; }\npub fn main() -> i32 { return work(); }",
        "Cannot call method 'enter' of 'Uncancelled' outside module 'std::sync'",
    );
    // A `const` is copied at each use, so one that changes through `&Self` is refused.
    for (name, decl) in [
        ("const_once_lock", "const C: OnceLock[i32] = OnceLock[i32]::new();"),
        ("const_mutex", "const C: Mutex[i32] = Mutex[i32]::new(0);"),
    ] {
        assert_rejected(
            name,
            &format!("{decl}\npub fn main() -> i32 {{ return 0; }}"),
            "a 'const' is copied at each use, so each would change its own copy; declare it 'static'",
        );
    }
    assert_runs(
        "static_once_lock",
        "static C: OnceLock[i32] = OnceLock[i32]::new();
static mut CALLS: i32 = 0;
fn three() -> i32 { unsafe { CALLS += 1; } return 3; }
fn f() -> i32 { return *C.get_or_init(three); }
pub fn main() -> i32 { let a = f() + f(); return a + unsafe { CALLS } * 10; }",
        16,
    );
    // What allocates cannot be made at compile time; a lazy static makes it when first used, and
    // what a static holds at the end is not a leak.
    assert_rejected(
        "static_vec",
        "static V: Vec[i32] = Vec[i32]::with_capacity(4);\npub fn main() -> i32 { return 0; }",
        "A constant or static of type 'Vec' cannot be made at compile time: it holds memory allocated as it was made",
    );
    assert_runs(
        "lazy_static_vec",
        "static V: LazyLock[Vec[i32]] = LazyLock[Vec[i32]]::new(fn() -> Vec[i32] { return Vec[i32]::with_capacity(4); });
pub fn main() -> i32 { return V.get().capacity() as i32; }",
        4,
    );
}

#[test]
fn test_generic_functions_as_values() {
    let prelude = "fn twice[T](x: T, f: fn(T) -> T) -> T { return f(f(x)); }
fn dbl[T: integer](x: T) -> T { return x + x; }
fn first[A, B](a: A, b: B) -> A { return a; }
fn d(x: i32) -> i32 { return x * 3; }
fn apply(f: fn(u8) -> u8, x: u8) -> u8 { return f(x); }
struct Ops { f: fn(i16) -> i16 }
";
    for (name, body, value) in [
        ("typed_binding", "let f: fn(i32) -> i32 = dbl[i32]; return f(5);", 10),
        ("inferred_binding", "let f = dbl[u8]; return f(4) as i32;", 8),
        ("two_arguments", "let f = first[i32, bool]; return f(9, false);", 9),
        ("passed", "return twice(1, dbl[i32]);", 4),
        // A literal before the function takes the type the function gives `T`.
        ("literal_first", "return twice(2, d);", 18),
        // The function-pointer type a generic is given to picks its instance.
        ("from_binding_type", "let f: fn(i32) -> i32 = dbl; return f(6);", 12),
        ("from_two_parameters", "let f: fn(i32, bool) -> i32 = first; return f(3, true);", 3),
        ("from_a_parameter", "return (apply(dbl, 5) as i32);", 10),
        ("from_a_field", "let o = Ops { f: dbl }; return (o.f)(4) as i32;", 8),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "bound_unmet",
        &format!("{prelude}pub fn main() -> i32 {{ let f = dbl[bool]; return 0; }}"),
        "Type 'bool' does not satisfy comptime constraint 'integer'",
    );
    assert_rejected(
        "no_instance_fits",
        &format!("{prelude}pub fn main() -> i32 {{ let f: fn(bool) -> bool = dbl; return 0; }}"),
        "No instance of generic 'dbl' has type 'fn(bool) -> bool'",
    );
}

#[test]
fn test_opaque_fields_drop_after_its_hook() {
    let prelude = "static mut LOG: i64 = 0;
opaque D { v: i64,
    pub fn new(v: i64) -> D { return D { v: v }; }
    impl drop { fn drop(self: &mut Self) { unsafe { LOG = LOG * 10 + self.v; } } } }
opaque Holder { a: D, n: i32, b: D, s: String,
    pub fn new() -> Self { return Self { a: D::new(2), n: 0, b: D::new(3), s: String::from(\"x\") }; }
    impl drop { fn drop(self: &mut Self) { unsafe { LOG = LOG * 10 + 1; } } } }
opaque Generic[T] { value: T,
    pub fn new(value: T) -> Self { return Self { value: value }; }
    impl drop { fn drop(self: &mut Self) { unsafe { LOG = LOG * 10 + 9; } } } }
opaque(linear) Owner { id: i32, d: D,
    pub fn new() -> Self { return Self { id: 5, d: D::new(4) }; }
    pub fn finish(move self) -> i32 { return self.id; }
    impl drop { fn drop(self: &mut Self) { unsafe { LOG = LOG * 10 + 1; } } } }
";
    for (name, body, value) in [
        // The hook first, then the fields in the order they are declared.
        ("in_order", "if true { let h = Holder::new(); } return unsafe { LOG } as i32;", 123),
        ("generic", "if true { let g = Generic[D]::new(D::new(4)); } return unsafe { LOG } as i32;", 94),
        // Retiring a linear owner runs its hook and drops its fields.
        ("linear_owner", "let o = Owner::new(); let id = o.finish(); return unsafe { LOG } as i32 * 10 + id;", 145),
        ("mutex", "if true { let m = Mutex[D]::new(D::new(7)); } return unsafe { LOG } as i32;", 7),
        ("box", "if true { let b = Box[D]::new(D::new(6)); } return unsafe { LOG } as i32;", 6),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
}

#[test]
fn test_generic_aliases() {
    // `alias Grid[T] = Vec[Vec[T]];` names a type that exists: `Grid[i32]` is `Vec[Vec[i32]]`.
    let prelude = "alias Grid[T] = Vec[Vec[T]];
alias Maybe[T] = ?T;
alias Table[V, K = String] = HashMap[K, V];
alias Small[T: integer] = [T; 2];
struct Tree[V] { value: V, kids: Grid[Tree[V]] }
fn rows(g: &Vec[Vec[i32]]) -> i32 { return g.len() as i32; }
fn first(m: ?i32) -> i32 { return m orelse 0; }
";
    for (name, body, value) in [
        ("same_type", "let mut g: Grid[i32] = Vec[Vec[i32]]::new(); g.push(Vec[i32]::new()); return rows(&g);", 1),
        ("optional", "let m: Maybe[i32] = 7; return first(m);", 7),
        ("default_parameter", "let mut t = Table[i32]::new(); let _o = t.insert(String::from(\"a\"), 3); return t.len() as i32;", 1),
        ("constrained", "let s: Small[u8] = { 1, 2 }; return (s[0] + s[1]) as i32;", 3),
        ("recursive", "let t = Tree[i32] { value: 1, kids: Grid[Tree[i32]]::new() }; return t.value + t.kids.len() as i32;", 1),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, src, message) in [
        ("anonymous_struct", "alias P[T] = struct { a: T };\npub fn main() -> i32 { return 0; }", "declare 'struct P[...]'"),
        ("constraint", "alias Small[T: integer] = [T; 2];\npub fn main() -> i32 { let s: Small[f64] = { 1.0, 2.0 }; return 0; }", "integer"),
    ] {
        assert_rejected(name, src, message);
    }
}

#[test]
fn test_type_functions_are_pure() {
    // A call is memoized, so a type may depend only on its arguments.
    for (name, src, message) in [
        (
            "mutable_static",
            "static mut WIDE: bool = false;\nfn Pick[T] -> type { if unsafe { WIDE } { return i64; } return T; }\npub fn main() -> i32 { let v: Pick[i32] = 1; return v; }",
            "mutable static",
        ),
        // Building a type inside it pauses the call; reading the static comes after.
        (
            "mutable_static_after_building_a_type",
            "static mut WIDE: bool = false;\nfn Pick[T] -> type { let inner = Vec[T]; if unsafe { WIDE } { return i64; } return inner; }\npub fn main() -> i32 { let v: Pick[i32] = Vec[i32]::new(); return v.len() as i32; }",
            "mutable static",
        ),
        (
            "output",
            "fn Noisy[T] -> type { println(\"hi\"); return T; }\npub fn main() -> i32 { let v: Noisy[i32] = 1; return v; }",
            "not constant",
        ),
    ] {
        assert_rejected(name, src, message);
    }
    // A type function can call one that builds a `Vec`, whose instantiation runs compile-time code
    // of its own; that used to lower `main`, which needed the type function, out of order.
    assert_runs(
        "calls_a_function_using_vec",
        "fn n() -> usize { let mut v = Vec[i32]::new(); v.push(1); return v.len(); }
fn Pick[T] -> type { if n() == 1 { return i64; } return T; }
pub fn main() -> i32 { return @size_of(Pick[i8]) as i32; }",
        8,
    );
    // A method reached only through a trait object's vtable is compiled for compile-time use too.
    assert_runs(
        "through_a_vtable",
        "trait Size { fn n(self: &Self) -> i32; }
struct A[T] { v: T, impl Size { fn n(self: &Self) -> i32 { return 6; } } }
fn ask(s: &Size) -> i32 { return s.n(); }
fn calc() -> i32 { let a = A[u16] { v: 1 }; return ask(&a); }
const N: i32 = calc();
pub fn main() -> i32 { return N; }",
        6,
    );
    // A function cannot need its own value to be compiled.
    assert_rejected(
        "needs_itself",
        "fn f() -> usize { let a: [u8; f()] = @default([u8; 1]); return 1; }\npub fn main() -> i32 { return f() as i32; }",
        "while it is itself being compiled",
    );
    // A constant static and the heap are fine.
    assert_runs(
        "constant_inputs",
        "static WIDE: bool = true;
fn count_up(n: i32) -> usize { let mut v = Vec[i32]::new(); for i in 0..n { v.push(i); } return v.len(); }
fn Pick[T] -> type { if WIDE && count_up(3) == 3 { return i64; } return T; }
pub fn main() -> i32 { return @size_of(Pick[i8]) as i32; }",
        8,
    );
}

#[test]
fn test_unsafe_traits() {
    // An `unsafe trait` makes promises the compiler cannot check, so its implementations say
    // `unsafe impl`, where their author takes them on.
    let prelude = "unsafe trait Trusted { fn get(self: &Self) -> i32; }
trait Plain { fn get(self: &Self) -> i32; }
";
    for (name, body, value) in [
        ("module", "struct A { v: i32 }\nunsafe impl Trusted for A { fn get(self: &Self) -> i32 { return self.v; } }\nfn use_it(t: &Trusted) -> i32 { return t.get(); }\npub fn main() -> i32 { let a = A { v: 4 }; return use_it(&a); }", 4),
        ("in_the_body", "struct A { v: i32, unsafe impl Trusted { fn get(self: &Self) -> i32 { return self.v; } } }\npub fn main() -> i32 { let a = A { v: 5 }; return a.get(); }", 5),
        ("generic", "struct A { v: i32 }\nstruct W[T] { t: T }\nunsafe impl Trusted for A { fn get(self: &Self) -> i32 { return self.v; } }\nunsafe impl[T: Trusted] Trusted for W[T] { fn get(self: &Self) -> i32 { return self.t.get() + 1; } }\npub fn main() -> i32 { let w = W[A] { t: A { v: 5 } }; return w.get(); }", 6),
        ("plain_stays_plain", "struct A { v: i32, impl Plain { fn get(self: &Self) -> i32 { return self.v; } } }\npub fn main() -> i32 { let a = A { v: 3 }; return a.get(); }", 3),
    ] {
        assert_runs(name, &format!("{prelude}{body}"), value);
    }
    for (name, body, message) in [
        ("module_without_unsafe", "struct A { v: i32 }\nimpl Trusted for A { fn get(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { v: 1 }; return a.get(); }", "write 'unsafe impl'"),
        ("body_without_unsafe", "struct A { v: i32, impl Trusted { fn get(self: &Self) -> i32 { return 1; } } }\npub fn main() -> i32 { let a = A { v: 1 }; return a.get(); }", "write 'unsafe impl'"),
        ("unsafe_for_nothing", "struct A { v: i32 }\nunsafe impl Plain for A { fn get(self: &Self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { v: 1 }; return a.get(); }", "asserts nothing"),
        // An allocator's memory is trusted by safe code, so implementing one is unsafe.
        ("allocator", "struct Bump { }\nimpl Allocator for Bump {\n    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 { return @raw_alloc(bytes); }\n    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return ptr; }\n    fn dealloc(self: &Self, ptr: *mut u8) { }\n}\npub fn main() -> i32 { let b = Box[i32, Bump]::new_in(1, Bump { }); return 0; }", "write 'unsafe impl'"),
    ] {
        assert_rejected(name, &format!("{prelude}{body}"), message);
    }
}

#[test]
fn test_structural_traits() {
    // A `trait(structural)` is met by any type with methods of its signatures, and by no `impl`:
    // the bound between naming a trait and `unchecked`.
    let prelude = "trait(structural) Keyed { fn key(self: &Self) -> u64; }
trait Named { fn key(self: &Self) -> u64; }
fn key_of[T: Keyed](x: &T) -> u64 { return x.key(); }
struct A { v: u64, pub fn key(self: &Self) -> u64 { return self.v; } }
struct P { fn hidden(self: &Self) -> i32 { return 1; } }
impl Named for i32 { fn key(self: &Self) -> u64 { return *self as u64 + 1; } }
trait(structural) Picks { fn pick(self: &Self, o: &i32) -> &i32 borrows(o); }
fn pick_of[T: Picks](x: &T, o: &i32) -> i32 { return *x.pick(o); }
";
    for (name, body, value) in [
        ("own_method", "pub fn main() -> i32 { let a = A { v: 7 }; return key_of(&a) as i32; }", 7),
        ("generic_type", "struct W[T] { t: T, pub fn key(self: &Self) -> u64 { return 2; } }\npub fn main() -> i32 { let w = W[i32] { t: 1 }; return key_of(&w) as i32; }", 2),
        // A nominal trait's method serves, so builtins can meet one through an `impl`.
        ("through_an_impl", "pub fn main() -> i32 { let n: i32 = 4; return key_of(&n) as i32; }", 5),
        ("trait_object", "fn dyn_key(k: &Keyed) -> u64 { return k.key(); }\npub fn main() -> i32 { let a = A { v: 9 }; return dyn_key(&a) as i32; }", 9),
        ("satisfies", "struct B { }\nfn probe[T: unchecked]() -> i32 { if @satisfies(T, Keyed) { return 1; } return 0; }\npub fn main() -> i32 { return probe[A]() * 10 + probe[B]() + probe[i32](); }", 11),
        ("has_method", "pub fn main() -> i32 { let a: i32 = if @has_method(A, \"key\") { 1 } else { 0 }; let b: i32 = if @has_method(&A, \"nope\") { 1 } else { 0 }; let c: i32 = if @has_method(P, \"hidden\") { 1 } else { 0 }; let d: i32 = if @has_method(i32, \"key\") { 1 } else { 0 }; return a * 8 + b * 4 + c * 2 + d; }", 9),
        ("same_borrows", "struct Q { pub fn pick(self: &Self, o: &i32) -> &i32 borrows(o) { return o; } }\npub fn main() -> i32 { let q = Q { }; let n: i32 = 6; return pick_of(&q, &n); }", 6),
    ] {
        assert_runs(name, &format!("{prelude}{body}"), value);
    }
    for (name, body, message) in [
        ("missing", "struct B { }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "it has no method 'key'"),
        ("private", "struct B { fn key(self: &Self) -> u64 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "is not 'pub'"),
        ("wrong_signature", "struct B { pub fn key(self: &Self) -> u32 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "different signature"),
        ("wrong_arity", "struct B { pub fn key(self: &Self, n: i32) -> u64 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "takes 2 parameters"),
        ("unsafe_method", "struct B { pub unsafe fn key(self: &Self) -> u64 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "is 'unsafe fn'"),
        ("different_borrows", "struct Q { v: i32, pub fn pick(self: &Self, o: &i32) -> &i32 borrows(self) { return &self.v; } }\npub fn main() -> i32 { let q = Q { v: 1 }; let n: i32 = 6; return pick_of(&q, &n); }", "different borrows(...) contract"),
        ("an_impl", "struct B { }\nimpl Keyed for B { fn key(self: &Self) -> u64 { return 1; } }\npub fn main() -> i32 { return 0; }", "write them as the type's own methods"),
        // The bound promises the trait's methods and nothing more.
        ("beyond_the_bound", "fn more[T: Keyed](x: &T) -> u64 { return x.size(); }\npub fn main() -> i32 { return 0; }", "has no method 'size'"),
    ] {
        assert_rejected(name, &format!("{prelude}{body}"), message);
    }
}

#[test]
fn test_nosuspend_blocks() {
    // `nosuspend { ... }` holds a block to not waiting: no fiber parks in it, and no thread blocks
    // on a lock, a condition, a join, a sleep, or a poll. The error shows the way it would.
    let prelude = "fn add(a: i32, b: i32) -> i32 { return a + b; }
fn locks(m: &Mutex[i32]) -> i32 { let g = m.lock(); g.unlock(); return 1; }
opaque Waits { m: Mutex[i32],
    pub fn new() -> Self { return Self { m: Mutex[i32]::new(0) }; }
    impl drop { fn drop(self: &mut Self) { let g = self.m.lock(); g.unlock(); } } }
";
    assert_runs(
        "computes",
        &format!("{prelude}pub fn main() -> i32 {{ let mut n = 0; nosuspend {{ let mut v = Vec[i32]::new(); v.push(add(1, 2)); n = *(v.get(0) orelse unreachable); let s = String::from(\"x\"); }} return n; }}"),
        3,
    );
    for (name, body, path) in [
        ("lock", "let m = Mutex[i32]::new(0); nosuspend { let g = m.lock(); g.unlock(); }", "Mutex[i32]::lock"),
        ("channel", "let c = Channel[i32]::new(); let _s = c.send(1); nosuspend { let v = c.recv() catch |e| 0; }", "Channel[i32]::recv"),
        ("sleep", "nosuspend { let _r = sleep_ms(1); }", "sleep_ms"),
        ("through_a_call", "let m = Mutex[i32]::new(0); nosuspend { let n = locks(&m); }", "root::locks -> "),
        ("function_value", "let f: fn(i32, i32) -> i32 = add; nosuspend { let n = f(1, 2); }", "a call through a function value"),
        ("a_drop", "let w = Waits::new(); nosuspend { let x = move w; }", "Waits"),
        // Each way of waiting alone: a fiber parking, and a thread blocking in C.
        ("parks", "nosuspend { let _y = std::sync::fiber_yield(); }", "std::sync::fiber_yield -> std::sync::switch_fiber"),
        ("blocks_in_c", "nosuspend { let _r = unsafe { usleep(10) }; }", "usleep"),
    ] {
        let src = format!("extern fn usleep(us: u32) -> i32;\n{prelude}pub fn main() -> i32 {{ {body} return 0; }}");
        assert_rejected(name, &src, path);
    }
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

#[test]
fn test_std_generics_meet_their_bounds() {
    // Compiling a program checks its own generics, not std's, which are the same every time.
    Compiler::check_std_generics().unwrap_or_else(|e| panic!("{e}"));
}

#[test]
fn test_operators_need_types_that_have_them() {
    // Arithmetic is for numbers, ordering for numbers, runes, pointers and enums, and equality
    // for those and other plain values; a struct or opaque has none of them.
    let prelude = "struct P { x: i32 }\nopaque O { x: i32, pub fn new() -> Self { return Self { x: 1 }; } }\nenum E { A, B }\npacked struct F { lo: u4, hi: u4 }\n";
    for (name, body, value) in [
        ("numbers", "let a: i32 = 2; let b: i32 = 3; return a * b + (a < b) as i32;", 7),
        ("enums", "let e = E::A; return (e == E::A) as i32 + (E::A < E::B) as i32;", 2),
        ("bools", "return (true & false == false) as i32;", 1),
        ("strings", "let s = \"ab\"; return (s == \"ab\") as i32;", 1),
        ("packed", "let a = F { lo: 1, hi: 2 }; let b = F { lo: 1, hi: 2 }; return (a == b) as i32 + (a != F { lo: 0, hi: 2 }) as i32;", 2),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, body, op) in [
        ("struct_add", "let a = P { x: 1 }; let b = P { x: 2 }; let c = a + b; return 0;", "'+' is not defined on 'P'"),
        ("opaque_eq", "let a = O::new(); let b = O::new(); return (a == b) as i32;", "'==' is not defined on 'O'"),
        ("struct_lt", "let a = P { x: 1 }; let b = P { x: 2 }; return (a < b) as i32;", "'<' is not defined on 'P'"),
        ("float_bits", "let a: f64 = 1.0; let b = a & a; return 0;", "'&' is not defined on 'f64'"),
        ("packed_lt", "let a = F { lo: 1, hi: 2 }; return (a < a) as i32;", "directly on packed type 'F'"),
    ] {
        assert_rejected(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), op);
    }
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
fn test_default_enum_backing_type_is_smallest_integer() {
    assert_runs(
        "smallest_backing",
        "enum Bit { Zero, One }
enum Three { A, B, C }
enum Five { A, B, C, D, E }
enum Signed { Neg = -2, Zero = 0, Pos = 1 }
export enum Exported { A, B, C }
packed struct Tiny { b: Bit, t: Three, f: Five }
pub fn main() -> i32 {
    @assert(@backing_type(Bit) == u1);
    @assert(@backing_type(Three) == u2);
    @assert(@backing_type(Five) == u3);
    @assert(@backing_type(Signed) == i2);
    @assert(@backing_type(Exported) == u32);
    @assert(Tiny.bits == 6 && @size_of(Tiny) == 1);
    return 0;
}",
        0,
    );
}

#[test]
fn test_uncancelled_select_cancellation_and_task_select() {
    let prelude = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(move self) -> i32 { return self.id; }
}
static mut CLEANED: i32 = 0;
fn fast_task(v: i32) -> i32 { return v; }
fn slow_task(v: i32) -> i32 {
    let _s = sleep_ms(1000) catch |e| {
        let _old = unsafe { @atomic_add(&raw mut CLEANED, v) };
        return -v;
    };
    return v;
}
fn fast_tx(v: i32) -> Tx { return Tx::new(v); }
fn slow_tx(v: i32) -> Tx {
    let _s = sleep_ms(1000) catch |e| {
        let _old = unsafe { @atomic_add(&raw mut CLEANED, v) };
        return Tx::new(v);
    };
    return Tx::new(v);
}
fn select_recv(c: &Channel[i32]) -> CancelError!i32 {
    return @select {
        x = c.recv() => x,
        e = check_cancelled() => e,
    };
}
";
    for (name, body, value) in [
        // `uncancelled { ... }` shields waits inside a cancelled or timed-out scope, and outer
        // cancellation resumes once the block ends.
        (
            "uncancelled_shields_waits_and_resumes",
            "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 {
                let c = Channel[i32]::with_capacity(1);
                let mut sum: i32 = 0;
                uncancelled {
                    check_cancelled() catch |e| return 90;
                    sleep_ms(1) catch |e| return 91;
                    if let u = c.send(4) { return 92; }
                    let v = c.recv() catch |e| return 93;
                    sum += v;
                }
                check_cancelled() catch |e| match e { .Cancelled => return sum + 10, .TimedOut => return sum + 20 };
                return 0;
            });",
            14,
        ),
        (
            "uncancelled_expr_and_timeout_shield",
            "let s = CancelScope::with_timeout_ms(0); return s.run(fn() -> i32 {
                let v: i32 = uncancelled {
                    sleep_ms(1) catch |e| return 90;
                    check_cancelled() catch |e| return 91;
                    5
                };
                check_cancelled() catch |e| match e { .Cancelled => return v + 10, .TimedOut => return v + 20 };
                return 0;
            });",
            25,
        ),
        (
            "uncancelled_inner_scope_still_cancels",
            "let s = CancelScope::new(); s.cancel(); return s.run(fn() -> i32 {
                return uncancelled {
                    let inner = CancelScope::new();
                    inner.cancel();
                    inner.run(fn() -> i32 {
                        check_cancelled() catch |e| return 7;
                        return 0;
                    })
                };
            });",
            7,
        ),
        (
            "uncancelled_linear_cleanup",
            "let s = CancelScope::new(); s.cancel();
            let c = Channel[Tx]::with_capacity(1);
            let r = s.run(fn() -> i32 {
                let tx = Tx::new(6);
                check_cancelled() catch |e| {
                    uncancelled {
                        if let u = c.send(move tx) { return u.commit() + 100; }
                        let got = c.recv() catch |err| return 90;
                        return got.commit();
                    }
                };
                return tx.commit();
            });
            c.close_and_drain(fn(u: Tx) { let _x = u.commit(); });
            return r;",
            6,
        ),
        // Cancellable `@select`: only through a `check_cancelled()` arm, whose error the
        // `@select` can give as its value.
        (
            "select_try_cancelled",
            "let s = CancelScope::new(); let c = Channel[i32]::new();
            return s.run(fn() -> i32 {
                let t = async(Fibers { }) select_recv(&c);
                s.cancel();
                return t.await() catch |e| match e { .Cancelled => 7, .TimedOut => 2 };
            });",
            7,
        ),
        (
            "select_catch_timed_out",
            "let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new();
            return s.run(fn() -> i32 {
                let r: CancelError!i32 = @select { x = c.recv() => x, e = check_cancelled() => e };
                return r catch |e| match e { .Cancelled => 7, .TimedOut => 2 };
            });",
            2,
        ),
        (
            "select_check_cancelled_arm_bound",
            "let s = CancelScope::with_timeout_ms(3); let c = Channel[i32]::new();
            return s.run(fn() -> i32 {
                return @select {
                    x = c.recv() => x,
                    e = check_cancelled() => match e { .Cancelled => 7, .TimedOut => 2 },
                };
            });",
            2,
        ),
        (
            "select_check_cancelled_arm_unbound",
            "let s = CancelScope::new(); s.cancel(); let c = Channel[i32]::new();
            return s.run(fn() -> i32 {
                return @select {
                    x = c.recv() => x,
                    check_cancelled() => 9,
                };
            });",
            9,
        ),
        (
            "select_ready_value_beats_cancel",
            "let s = CancelScope::new(); let c = Channel[i32]::with_capacity(1);
            let _ok = c.send(4); s.cancel();
            return s.run(fn() -> i32 {
                return @select {
                    x = c.recv() => x,
                    check_cancelled() => 9,
                };
            });",
            4,
        ),
        (
            "select_cancelled_settles_linear_send_arm",
            "let s = CancelScope::new();
            let full = Channel[Tx]::with_capacity(1);
            if let u = full.send(Tx::new(1)) { let _x = u.commit(); }
            let mut recovered: i32 = 0;
            let w = spawn_scoped(fn() -> i32 { let _d = sleep_ms(2); s.cancel(); return 0; });
            let r = s.run(fn() -> i32 {
                return @select {
                    full.send(Tx::new(8)) else |unsent| { recovered = unsent.commit(); } => 0,
                    check_cancelled() => 10,
                };
            });
            let _j = w.join();
            full.close_and_drain(fn(u: Tx) { let _x = u.commit(); });
            return r + recovered;",
            18,
        ),
        // `@select` over child tasks (`Task[R]`): winning task returns its value, losing task is
        // cancelled and awaited before `@select` finishes.
        (
            "select_task_fast_path_cancels_loser",
            "let a = async(Inline { }) fast_task(5);
            let b = async slow_task(30);
            let w = @select {
                x = a.await() => x,
                y = b.await() => y,
            };
            return w + unsafe { @atomic_load(&raw mut CLEANED) };",
            35,
        ),
        (
            "select_task_park_path_fibers",
            "let a = async(Fibers { }) slow_task(40);
            let b = async(Fibers { }) fast_task(6);
            let w = @select {
                x = a.await() => x,
                y = b.await() => y,
            };
            return w + unsafe { @atomic_load(&raw mut CLEANED) };",
            46,
        ),
        (
            "select_task_with_else_loser_handler",
            "let a = async(Fibers { }) slow_task(20);
            let b = async(Fibers { }) fast_task(4);
            let mut loser_val: i32 = 0;
            let w = @select {
                x = a.await() else |l| { loser_val = -l; } => x,
                y = b.await() => y,
            };
            return w + loser_val;",
            24,
        ),
        (
            "select_task_linear_result",
            "let a = async(Fibers { }) slow_tx(20);
            let b = async(Fibers { }) fast_tx(7);
            let mut loser_committed: i32 = 0;
            let w = @select {
                x = a.await() else |loser| { loser_committed = loser.commit(); } => x.commit(),
                y = b.await() else |loser| { loser_committed = loser.commit(); } => y.commit(),
            };
            return w + loser_committed;",
            27,
        ),
        (
            "select_task_cancelled_scope_cancels_all_tasks",
            "let s = CancelScope::new();
            return s.run(fn() -> i32 {
                let a = async(Fibers { }) slow_tx(11);
                let b = async(Fibers { }) slow_tx(22);
                let _c = async(Fibers { }) fast_task(0);
                s.cancel();
                let mut total: i32 = 0;
                let res = @select {
                    x = a.await() else |l| { total += l.commit(); } => x.commit(),
                    y = b.await() else |l| { total += l.commit(); } => y.commit(),
                    check_cancelled() => 100,
                };
                return res + total;
            });",
            133,
        ),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    assert_rejected(
        "select_linear_task_without_else_rejected",
        &format!(
            "{prelude}pub fn main() -> i32 {{
    let a = async fast_tx(1);
    let b = async fast_tx(2);
    return @select {{
        x = a.await() => x.commit(),
        y = b.await() else |l| {{ let _c = l.commit(); }} => y.commit(),
    }};
}}"
        ),
        "must be explicitly consumed",
    );
}

#[test]
fn test_once_cell_lazy_cell_once_lock_and_lazy_lock() {
    assert_runs(
        "once_cell_and_lazy_cell_lifecycle",
        "static mut DROPPED: i32 = 0;
static mut CLOSURE_DROPPED: i32 = 0;

pub opaque Tracked {
    v: i32,
    impl drop {
        fn drop(self: &mut Self) {
            unsafe { DROPPED += self.v; }
        }
    }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn val(self: &Self) -> i32 { return self.v; }
    pub fn add(self: &mut Self, d: i32) { self.v += d; }
}

pub opaque Guard {
    tag: i32,
    impl drop {
        fn drop(self: &mut Self) {
            unsafe { CLOSURE_DROPPED += self.tag; }
        }
    }
    pub fn new(tag: i32) -> Self { return Self { tag: tag }; }
    pub fn get(self: &Self) -> i32 { return self.tag; }
}

fn make_forty_two() -> i32 {
    return 42;
}

pub fn main() -> i32 {
    // 1. Uninitialized OnceCell does not drop T.
    if true {
        let _empty = OnceCell[Tracked]::new();
    }
    @assert(unsafe { DROPPED } == 0);

    // 2. Initialized OnceCell drops T once; rejected `set` value is returned and dropped.
    if true {
        let c = OnceCell[Tracked]::new();
        @assert(c.get() == null);
        if let rejected = c.set(Tracked::new(10)) {
            return 1;
        }
        if let rejected = c.set(Tracked::new(3)) {
            @assert(rejected.val() == 3);
        } else {
            return 2;
        }
        @assert(unsafe { DROPPED } == 3);
        @assert((c.get() orelse unreachable).val() == 10);
    }
    @assert(unsafe { DROPPED } == 13);

    // 3. `with_value`, `get_mut`, `take`, and `into_inner`.
    unsafe { DROPPED = 0; }
    if true {
        let mut c = OnceCell[Tracked]::with_value(Tracked::new(20));
        (c.get_mut() orelse unreachable).add(5);
        let taken = c.take() orelse unreachable;
        @assert(taken.val() == 25);
        @assert(c.get() == null);
    }
    @assert(unsafe { DROPPED } == 25);

    // 4. `get_or_init` runs only once.
    let mut calls: i32 = 0;
    let c2 = @default(OnceCell[i32]);
    let v1 = *c2.get_or_init(fn() -> i32 { calls += 1; return 77; });
    let v2 = *c2.get_or_init(fn() -> i32 { calls += 1; return 99; });
    @assert(v1 == 77 && v2 == 77 && calls == 1);
    @assert((c2.into_inner() orelse 0) == 77);

    // 5. LazyCell with function pointer default and with capturing closure.
    let l_fn = LazyCell[i32]::new(make_forty_two);
    @assert(!l_fn.is_initialized());
    @assert(*l_fn.get() == 42);
    @assert(l_fn.is_initialized());
    @assert((l_fn.into_inner() orelse 0) == 42);

    // Unforced LazyCell drops its captured closure and does not drop T.
    unsafe { DROPPED = 0; CLOSURE_DROPPED = 0; }
    if true {
        let g = Guard::new(7);
        let f = move fn() -> Tracked { return Tracked::new(g.get() * 10); };
        let _unforced = LazyCell[Tracked, @type_of(f)]::new(move f);
    }
    @assert(unsafe { CLOSURE_DROPPED } == 7 && unsafe { DROPPED } == 0);

    // Forced LazyCell drops its closure when forced and drops T when the cell drops.
    unsafe { DROPPED = 0; CLOSURE_DROPPED = 0; }
    if true {
        let g = Guard::new(4);
        let f = move fn() -> Tracked { return Tracked::new(g.get() * 10); };
        let mut forced = LazyCell[Tracked, @type_of(f)]::new(move f);
        @assert(forced.get().val() == 40);
        @assert(unsafe { CLOSURE_DROPPED } == 4 && unsafe { DROPPED } == 0);
        forced.get_mut().add(2);
    }
    @assert(unsafe { DROPPED } == 42);

    return 0;
}",
        0,
    );

    assert_runs(
        "static_once_lock_and_lazy_lock_with_threads_and_fibers",
        "static mut INIT_COUNT: i32 = 0;
static mut ONCE_INIT_COUNT: i32 = 0;
static mut STR_INIT_COUNT: i32 = 0;

fn compute_config() -> i32 {
    let _old = unsafe { @atomic_add(&raw mut INIT_COUNT, 1) };
    let _s = sleep_ms(3);
    return 123;
}

struct Pair {
    a: i32,
    b: i32,
}

fn compute_pair() -> Pair {
    let _old = unsafe { @atomic_add(&raw mut STR_INIT_COUNT, 1) };
    return Pair { a: 10, b: 32 };
}

static CONFIG: LazyLock[i32] = LazyLock[i32]::new(compute_config);
static PAIR: LazyLock[Pair] = LazyLock[Pair]::new(compute_pair);
static SHARED_ONCE: OnceLock[i32] = OnceLock[i32]::new();
static PRESET_ONCE: OnceLock[i32] = OnceLock[i32]::with_value(55);
static FIBER_LAZY: LazyLock[i32] = LazyLock[i32]::new(fn() -> i32 {
    let _s = sleep_ms(3);
    return 321;
});

fn fiber_reader() -> i32 {
    return *FIBER_LAZY.get();
}

pub fn main() -> i32 {
    @assert(!CONFIG.is_initialized());
    @assert(*(PRESET_ONCE.get() orelse unreachable) == 55);

    // Multi-threaded contention on `LazyLock` and `OnceLock`.
    let t1 = spawn_scoped(fn() -> i32 {
        let a = *CONFIG.get();
        let b = *SHARED_ONCE.get_or_init(fn() -> i32 {
            let _old = unsafe { @atomic_add(&raw mut ONCE_INIT_COUNT, 1) };
            let _s = sleep_ms(2);
            return 77;
        });
        return a + b;
    });
    let t2 = spawn_scoped(fn() -> i32 {
        let a = *CONFIG.get();
        let b = *SHARED_ONCE.get_or_init(fn() -> i32 {
            let _old = unsafe { @atomic_add(&raw mut ONCE_INIT_COUNT, 1) };
            return 88;
        });
        return a + b;
    });
    let r1 = t1.join();
    let r2 = t2.join();
    @assert(r1 == r2 && (r1 == 200 || r1 == 211));
    @assert(unsafe { @atomic_load(&raw mut INIT_COUNT) } == 1);
    @assert(unsafe { @atomic_load(&raw mut ONCE_INIT_COUNT) } == 1);
    @assert(CONFIG.is_initialized());

    // Static LazyLock[Pair] and scoped LazyLock[String] (verifying destructor cleanup).
    @assert(PAIR.get().a + PAIR.get().b == 42);
    @assert(unsafe { @atomic_load(&raw mut STR_INIT_COUNT) } == 1);
    let owned_lazy = LazyLock[String]::new(fn() -> String {
        return String::from(\"owned lazy\");
    });
    @assert(owned_lazy.get().as_str() == \"owned lazy\");

    // Fiber contention on the same OS thread.
    let f1 = async(Fibers { }) fiber_reader();
    let f2 = async(Fibers { }) fiber_reader();
    @assert(f1.await() + f2.await() == 642);

    return 0;
}",
        0,
    );

    // Reentrant initialization traps for OnceCell, LazyCell, OnceLock, and LazyLock.
    let reentrant_once_cell = "pub fn main() -> i32 {
    let c = OnceCell[i32]::new();
    return *c.get_or_init(fn() -> i32 {
        return *c.get_or_init(fn() -> i32 { return 1; });
    });
}";
    assert_eq!(run_lli("reentrant_once_cell", reentrant_once_cell), Some(TRAP_EXIT));

    let reentrant_once_lock = "static LOCK: OnceLock[i32] = OnceLock[i32]::new();
pub fn main() -> i32 {
    return *LOCK.get_or_init(fn() -> i32 {
        return *LOCK.get_or_init(fn() -> i32 { return 1; });
    });
}";
    assert_eq!(run_lli("reentrant_once_lock", reentrant_once_lock), Some(TRAP_EXIT));

    let reentrant_lazy_lock = "fn bad() -> i32 { return *LAZY.get(); }
static LAZY: LazyLock[i32] = LazyLock[i32]::new(bad);
pub fn main() -> i32 { return *LAZY.get(); }";
    assert_eq!(run_lli("reentrant_lazy_lock", reentrant_lazy_lock), Some(TRAP_EXIT));

    // Single-threaded `OnceCell` and `LazyCell` have `cell` fields without `unsafe sync`, so
    // placing them in a shared `static` is rejected.
    assert_rejected(
        "once_cell_in_static_rejected",
        "static C: OnceCell[i32] = OnceCell[i32]::new();\npub fn main() -> i32 { return 0; }",
        "sync",
    );
    assert_rejected(
        "lazy_cell_in_static_rejected",
        "fn init() -> i32 { return 1; }\nstatic L: LazyCell[i32] = LazyCell[i32]::new(init);\npub fn main() -> i32 { return 0; }",
        "sync",
    );
}



/// `v.clone()` is `@clone(v)` and `T::default()` is `@default(T)` for every type, `@default()`
/// takes its type from its context, and the hooks' names are reserved.
#[test]
fn test_clone_and_default_method_sugar() {
    const O: &str = "struct P { x: i32, y: i32 }
opaque O {
    v: i32,
    impl default { fn default() -> Self { return Self { v: 7 }; } }
    impl clone { fn clone(self: &Self) -> Self { return Self { v: self.v + 1 }; } }
    pub fn v(self: &Self) -> i32 { return self.v; }
}
struct W { o: O, n: i32 }
fn mk[T: default]() -> T { return T::default(); }
fn mk_inferred[T: default]() -> T { let t: T = @default(); return t; }
fn dup[T: clone](t: &T) -> T { return t.clone(); }
fn wrap() -> W { return W { o: @default(), n: @default() }; }
";
    assert_runs(
        "clone_and_default_sugar",
        &format!("{O}
pub fn main() -> i32 {{
    let o = O::default();
    let c = o.clone();
    let r = &o;
    let p = P::default();
    let s = String::from(\"ab\");
    let mut v = Vec[i32]::new();
    v.push(3);
    let n = s.clone().len() + v.clone().len();
    let w = wrap();
    let q: O = @default();
    @assert(o.v() == 7 && c.v() == 8 && r.clone().v() == 8 && p.x + p.y + i32::default() == 0);
    @assert(n == 3 && mk[i32]() == 0 && mk[O]().v() == 7 && mk_inferred[O]().v() == 7);
    @assert(dup(&o).v() == 8 && w.o.v() + w.n == 7 && q.v() == 7);
    return 42;
}}"),
        42,
    );
    assert_rejected(
        "default_with_no_type",
        "pub fn main() -> i32 { let x = @default(); return 0; }",
        "'@default()' takes its type from where it is used",
    );
    assert_rejected(
        "method_named_clone",
        "opaque B { v: i32, pub fn clone(self: &Self) -> Self { return Self { v: self.v }; } }
pub fn main() -> i32 { return 0; }",
        "'B' declares a method 'clone'",
    );
    assert_rejected(
        "trait_method_named_default",
        "trait Mk { fn default() -> i32; }
pub fn main() -> i32 { return 0; }",
        "'Mk' declares a method 'default'",
    );
    assert_rejected(
        "default_without_hook",
        "opaque N { v: i32 }
pub fn main() -> i32 { let n = N::default(); return 0; }",
        "does not implement a `default()` hook",
    );
}

/// `Rc` and `Weak`: shared values dropped with their last `Rc`, `Weak` back-references that
/// break cycles, uniqueness-gated mutation, and a long list dropped without deep recursion.
#[test]
fn test_rc_and_weak() {
    assert_runs(
        "rc_and_weak",
        "static mut DROPS: i32 = 0;
opaque Tracked {
    v: i32,
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS += 1; } } }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn v(self: &Self) -> i32 { return self.v; }
}
struct Node {
    v: i32,
    parent: Weak[Node],
    next: ?Rc[Node],
}
pub fn main() -> i32 {
    let a = Rc[Tracked]::new(Tracked::new(4));
    let b = a.clone();
    let w = b.downgrade();
    @assert(a.ptr_eq(&b) && a.strong_count() == 2 && a.weak_count() == 1);
    @assert((w.upgrade() orelse unreachable).get().v() == 4);
    let back = b.into_inner();
    @assert(back.is_none() && a.strong_count() == 1);
    { let gone = a; }
    @assert(unsafe { DROPS } == 1 && w.upgrade().is_none() && w.strong_count() == 0);
    let mut c = Rc[i32]::new(1);
    *(c.get_mut() orelse unreachable) += 1;
    let d = c.clone();
    @assert(c.get_mut().is_none());
    *c.make_mut() += 10;
    @assert(*c.get() == 12 && *d.get() == 2 && !c.ptr_eq(&d));
    @assert(d.unwrap_or_clone() == 2 && c.clone().unwrap_or_clone() == 12);
    let s = format(f\"{c} {Rc[i32]::default()}\");
    @assert(s.as_str() == \"12 0\" && Weak[i32]::new().upgrade().is_none());
    let root = Rc[Node]::new(Node { v: 1, parent: Weak[Node]::new(), next: null });
    let child = Node { v: 2, parent: root.downgrade(), next: null };
    @assert((child.parent.upgrade() orelse unreachable).get().v == 1);
    let mut list: ?Rc[Node] = null;
    for i in 0..1000 {
        list = Rc[Node]::new(Node { v: i, parent: Weak[Node]::new(), next: list });
    }
    return 42;
}",
        42,
    );
    // A cycle is never dropped, and the VM reports what it keeps.
    let cycle = super::run_vm(
        "rc_cycle_leaks",
        "struct Node { next: OnceCell[Rc[Node]] }
pub fn main() -> i32 {
    let a = Rc[Node]::new(Node { next: OnceCell[Rc[Node]]::new() });
    let b = Rc[Node]::new(Node { next: OnceCell[Rc[Node]]::new() });
    _ = a.get().next.set(b.clone());
    _ = b.get().next.set(a.clone());
    return 0;
}",
    )
    .unwrap();
    assert!(cycle.leaks > 0, "{}", cycle.leaks);
    assert_rejected(
        "rc_is_not_send",
        "pub fn main() -> i32 {
    let a = Rc[i32]::new(1);
    let h = spawn(move fn() -> i32 { return *a.get(); });
    return h.join();
}",
        "send",
    );
}

/// `Arc` and `WeakArc`: shared between threads, dropped with the last `Arc`, and refused for a
/// value that is not `sync`.
#[test]
fn test_arc_and_weak_arc() {
    assert_runs(
        "arc_and_weak_arc",
        "static mut DROPS: i32 = 0;
opaque Tracked {
    v: i32,
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS += 1; } } }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
}
pub fn main() -> i32 {
    let shared = Arc[Mutex[i32]]::new(Mutex[i32]::new(0));
    let mut handles = Vec[JoinHandle[i32]]::new();
    for i in 0..4 {
        let mine = shared.clone();
        let weak = shared.downgrade();
        handles.push(spawn(move fn() -> i32 {
            for k in 0..5 {
                let more = mine.clone();
                let mut g = more.get().lock();
                *g.get_mut() += 1;
                g.unlock();
                _ = weak.upgrade();
            }
            return 0;
        }));
    }
    while let h = handles.pop() {
        _ = h.join();
    }
    handles.finish();
    @assert(shared.strong_count() == 1 && shared.weak_count() == 0);
    let w = shared.downgrade();
    let m = shared.into_inner() orelse unreachable;
    @assert(w.upgrade().is_none() && m.into_inner() == 20);
    let t = Arc[Tracked]::new(Tracked::new(1));
    let u = t.clone();
    { let gone = t; }
    @assert(unsafe { DROPS } == 0);
    { let gone = u; }
    @assert(unsafe { DROPS } == 1);
    let mut n = Arc[i32]::new(3);
    let o = n.clone();
    *n.make_mut() += 1;
    @assert(*n.get() == 4 && *o.get() == 3 && n.get_mut().is_some());
    return 42;
}",
        42,
    );
    assert_rejected(
        "arc_needs_sync",
        "pub fn main() -> i32 { let a = Arc[Rc[i32]]::new(Rc[i32]::new(1)); return 0; }",
        "does not satisfy comptime constraint 'send' (for parameter 'T' in 'Arc')",
    );
}

/// A `where` gate asked about a type of an unfinished cycle is asked again once the cycle is
/// built: `Vec[Tree]` clones as `Tree` does, and a `Tree` holding a cell does not.
#[test]
fn test_where_gates_rechecked_after_type_cycles() {
    assert_runs(
        "cycle_gates",
        "struct Tree { v: i32, kids: Vec[Tree] }
struct Celled { kids: OnceCell[Vec[Celled]], shared: OnceCell[Rc[Celled]] }
pub fn main() -> i32 {
    let mut t = Tree { v: 1, kids: Vec[Tree]::new() };
    t.kids.push(Tree { v: 2, kids: Vec[Tree]::new() });
    let c = t.clone();
    let celled = Celled { kids: OnceCell[Vec[Celled]]::new(), shared: OnceCell[Rc[Celled]]::new() };
    return c.kids.len() as i32 + 41;
}",
        42,
    );
    assert_rejected(
        "cycle_gate_refused",
        "struct Celled { kids: OnceCell[Vec[Celled]] }
pub fn main() -> i32 { let v = Vec[Celled]::new(); let w = v.clone(); return 0; }",
        "does not implement `clone`",
    );
}

/// An `Rc` or `Arc` of a linear value is linear: `share` makes another, and each ends in
/// `into_inner`, of which exactly one gets the value.
#[test]
fn test_linear_rc_and_arc() {
    assert_runs(
        "linear_rc_and_arc",
        &format!("{TX}
pub fn main() -> i32 {{
    let a = Rc[Tx]::new(Tx::new(7));
    let b = a.share();
    let w = a.downgrade();
    @assert(a.strong_count() == 2);
    if let t = a.into_inner() {{ _ = t.commit(); unreachable; }}
    let tx = b.into_inner() orelse unreachable;
    if let r = w.upgrade() {{ unreachable; }}
    let x = Arc[Tx]::new(Tx::new(5));
    let y = x.share();
    if let t = y.into_inner() {{ _ = t.commit(); unreachable; }}
    let t2 = x.into_inner() orelse unreachable;
    return tx.commit() + t2.commit() + 30;
}}"),
        42,
    );
    assert_rejected(
        "linear_rc_must_be_consumed",
        &format!("{TX}
pub fn main() -> i32 {{ let a = Rc[Tx]::new(Tx::new(1)); return 0; }}"),
        "Linear value 'a' of type 'Rc[Tx, Global]' must be explicitly consumed",
    );
    assert_rejected(
        "linear_rc_does_not_clone",
        &format!("{TX}
pub fn main() -> i32 {{ let a = Rc[Tx]::new(Tx::new(1)); let b = a.clone(); return 0; }}"),
        "does not implement `clone`",
    );
}

/// `RcSlice`, `RcStr`, `ArcSlice`, and `ArcStr`: shared slices and text behind one pointer,
/// their elements dropped once, with the last reference.
#[test]
fn test_shared_slices_and_strings() {
    assert_runs(
        "shared_slices_and_strings",
        "static mut DROPS: i32 = 0;
opaque Tracked {
    v: i32,
    impl drop { fn drop(self: &mut Self) { unsafe { DROPS += 1; } } }
    impl clone { fn clone(self: &Self) -> Self { return Self { v: self.v }; } }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn v(self: &Self) -> i32 { return self.v; }
    pub fn set(self: &mut Self, v: i32) { self.v = v; }
}
pub fn main() -> i32 {
    let mut v = Vec[Tracked]::new();
    v.push(Tracked::new(1));
    v.push(Tracked::new(2));
    let mut s = RcSlice[Tracked]::from_vec(v);
    (s.get_mut() orelse unreachable)[0].set(10);
    let t = s.clone();
    @assert(s.get_mut().is_none() && t.len() == 2 && t.get()[0].v() + t.get()[1].v() == 12);
    { let gone = s; }
    @assert(unsafe { DROPS } == 0);
    { let gone = t; }
    @assert(unsafe { DROPS } == 2);
    let arr: [i32; 3] = { 4, 5, 6 };
    let nums = RcSlice[i32]::from_slice(&arr[0..3]);
    let none = RcSlice[i32]::default();
    let text = RcStr::from(\"hi\");
    let mut counts = HashMap[RcStr, i32]::new();
    _ = counts.insert(text.clone(), 3);
    let key = RcStr::from(\"hi\");
    let looked = format(f\"{nums} {none} {text} {*(counts.get(&key) orelse unreachable)}\");
    @assert(looked.as_str() == \"[4, 5, 6] [] hi 3\" && text.strong_count() == 2);
    let shared = ArcSlice[i32]::from_slice(&arr[0..3]);
    let name = ArcStr::from(\"pool\");
    let mut handles = Vec[JoinHandle[i32]]::new();
    for i in 0..3 as usize {
        let mine = shared.clone();
        let n = name.clone();
        handles.push(spawn(move fn() -> i32 { return mine.get()[i] + n.len() as i32; }));
    }
    let mut total = 0;
    while let h = handles.pop() {
        total += h.join();
    }
    handles.finish();
    @assert(total == 27 && shared.strong_count() == 1 && name.as_str() == \"pool\");
    return 42;
}",
        42,
    );
    assert_rejected(
        "arc_slice_needs_sync",
        "pub fn main() -> i32 { let v = Vec[Rc[i32]]::new(); let s = ArcSlice[Rc[i32]]::from_vec(v); return 0; }",
        "does not satisfy comptime constraint 'send' (for parameter 'T' in 'ArcSlice')",
    );
}
