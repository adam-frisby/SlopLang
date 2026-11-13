use super::*;

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
    if let ?u = c.send(Tx::new(1)) { let _c = u.commit(); }
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
        "fn W[T]() -> type { return opaque(owns U) { p: *mut T }; }
pub fn main() -> i32 { let x: ?*mut W[i32] = null; return 0; }",
        "'owns U' on opaque 'W' does not name a comptime type parameter",
    );
    reject(
        "owns_copy",
        "fn W[T]() -> type { return opaque(copy, owns T) { p: *mut T }; }
pub fn main() -> i32 { return 0; }",
        "'opaque(copy, owns ...)' is invalid",
    );

    // An owning container (has a `drop` hook) holding `T` only behind a raw pointer is linted.
    let leaky = "\
fn Leaky[T]() -> type {
    return opaque {
        ptr: *mut T,
        impl drop { fn drop(&mut self) { unsafe { @dealloc(self.ptr); } } }
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = v; }
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
fn View[T]() -> type {
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
            "fn Holder[T: ?linear]() -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = v; }
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
            "fn Holder[T: ?linear]() -> type {
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
            "fn Holder[T: ?linear]() -> type {
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
            "fn Holder[T: ?linear]() -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            let put = move fn() { unsafe { *p = v; } };
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
            "fn Holder[T: ?linear]() -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = v; }
            return Self { ptr: p };
        }
    };
}
fn wrap[F: ?linear](f: F) -> Holder[F] { return Holder[F]::new(f); }
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
            "fn Holder[T: ?linear]() -> type {
    return opaque(owns T) {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = v; }
            return Self { ptr: p };
        }
        pub fn release(self) {}
    };
}
pub fn main() -> i32 { Holder[Tx]::new(Tx::new(1)).release(); return 0; }",
        ),
        "store it through an owning pointer ('*own T')",
    );

    // An owning pointer makes `Holder[Tx]` linear, so the store is accepted and the value must come
    // back out through a consuming method.
    let owning = "fn Holder[T: ?linear]() -> type {
    return opaque {
        ptr: *own T,
        pub fn new(v: T) -> Self {
            let p: *own T = unsafe { @alloc(T, 1) as *own T };
            unsafe { *p = v; }
            return Self { ptr: p };
        }
        pub fn take(self) -> T {
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
        "fn Holder[T]() -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = v; }
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
            "fn write_raw[T: ?linear](p: *mut T, v: T) { unsafe { *p = v; } }
fn Holder[T: ?linear]() -> type {
    return opaque {
        ptr: *mut T,
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            write_raw(p, v);
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
    let put = move fn() { unsafe { *p = t; } };
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
        *p = v;
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
        *p = v;
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
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + 1; } } }
    pub fn new() -> Self { return Self { n: 1 }; }
    pub fn take(self) -> i32 { return self.n; }
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
    pub fn discard(self) -> i32 { return 0; }
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
    pub fn maybe(self, c: bool) -> i32 { if c { return self.t.commit(); } return 0; }
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
    pub fn take_n(self) -> i32 { return self.p.n; }
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
    impl drop { fn drop(&mut self) { } }
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn discard(self) -> i32 { return 0; }
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
    pub fn split(self) -> tuple { Tx, Tx } { let p = self.p; return .{ self.t, p.t }; }
    pub fn finish(self) -> i32 { let p = self.p; return self.t.commit() + p.t.commit() + p.n; }
    pub fn delegate(self) -> i32 { return self.finish(); }
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
    pub fn done(self) -> i32 { return self.t.commit(); }
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
            "fn Cursor[T]() -> type {{
    return opaque{decl} {{
        p: {field},
        pub unsafe fn at(p: {field}) -> Self {{ return Self {{ p: p }}; }}
        pub fn get(&self) -> T where T: copy {{ unsafe {{ return *self.p; }} }}
    }};
}}
fn Buf[T]() -> type {{
    return opaque {{
        ptr: *own T,
        pub fn new(v: T) -> Self {{
            let p: *own T = unsafe {{ @alloc(T, 1) as *own T }};
            unsafe {{ *p = v; }}
            return Self {{ ptr: p }};
        }}
        pub fn cursor(&self) -> Cursor[T] {{
            return unsafe {{ Cursor[T]::at((self.ptr as usize) as {ptr}) }};
        }}
        pub fn regrow(&mut self) where T: copy {{
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
    let redundant = "fn H[T]() -> type {
    return opaque(owns T) { p: *own T, impl drop { fn drop(&mut self) { } } };
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
    pub fn bad(&self) -> &i32 borrows(*self) { return &self.n; }
}
pub fn main() -> i32 { let s = S::new(); return *s.bad(); }",
        "not permitted by its contract borrows(*self)",
    );
    reject(
        "owned_memory_under_contents",
        "fn Holder[T: ?linear]() -> type {
    return opaque {
        p: *own T,
        pub fn new(v: T) -> Self {
            let p: *own T = unsafe { @alloc(T, 1) as *own T };
            unsafe { *p = v; }
            return Self { p: p };
        }
        pub fn get(&self) -> &T borrows(*self) { unsafe { return &*self.p; } }
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
    impl drop { fn drop(&mut self) { unsafe { SINK = *self.r; } } }
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
}
pub fn main() -> i32 { let mut v = Vec[Peek]::new(); let x: i32 = 1; v.push(Peek::new(&x)); return 0; }",
        STILL_BORROWED,
    );
    reject(
        "direct_borrow_beside_contents",
        "fn C[T]() -> type {
    return opaque {
        p: *own T,
        r: &i32,
        unsafe impl drop(may_dangle T) { fn drop(&mut self) { unsafe { let _v = *self.r; @dealloc(self.p); } } }
        pub fn new(r: &i32) -> Self { return Self { p: unsafe { @alloc(T, 1) as *own T }, r: r }; }
    };
}
pub fn main() -> i32 { let y: i32 = 0; let mut c = C[i32]::new(&y); let x: i32 = 1; c = C[i32]::new(&x); return 0; }",
        STILL_BORROWED,
    );
    reject(
        "hook_without_may_dangle",
        "fn L[T]() -> type {
    return opaque {
        p: *own T,
        impl drop { fn drop(&mut self) { unsafe { @dealloc(self.p); } } }
        pub fn new(v: T) -> Self { let p: *own T = unsafe { @alloc(T, 1) as *own T }; unsafe { *p = v; } return Self { p: p }; }
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
        "fn L[T]() -> type { return opaque { p: *own T, impl drop(may_dangle T) { fn drop(&mut self) { } } }; }\npub fn main() -> i32 { return 0; }",
        "write 'unsafe impl drop(may_dangle ...)'",
    );
    reject(
        "unsafe_without_may_dangle",
        "fn L[T]() -> type { return opaque { p: *own T, unsafe impl drop { fn drop(&mut self) { } } }; }\npub fn main() -> i32 { return 0; }",
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
        "fn C[T, U]() -> type {
    return opaque(borrows U) {
        p: *own T,
        u: *const U,
        unsafe impl drop(may_dangle T) { fn drop(&mut self) { unsafe { let _v = *self.u; @dealloc(self.p); } } }
        pub fn new(u: &U) -> Self { return Self { p: unsafe { @alloc(T, 1) as *own T }, u: u as *const U }; }
    };
}
pub fn main() -> i32 { let y: i32 = 0; let mut c = C[i32, i32]::new(&y); let x: i32 = 1; c = C[i32, i32]::new(&x); return 0; }",
        STILL_BORROWED,
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
            "fn Holder[T: ?linear]() -> type {
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
            "fn Handle[T: ?linear]() -> type {
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
        "fn Holder[T]() -> type {
    return opaque(affine) {
        val: T,
        pub fn new(v: T) -> Self { return Self { val: v }; }
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
            "fn Holder[T: ?linear]() -> type {
    return opaque {
        val: T,
        pub fn new(v: T) -> Self { return Self { val: v }; }
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
    pub fn get(self) -> u32 { return self.bits; }
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
    pub fn consume(self) -> u32 { return self.bits; }
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
fn test_conditional_move_into_a_call_clears_its_drop_flag() {
    let make = "fn make(n: i32) -> Box[i32] { return Box[i32]::new(n); }\nfn take(b: Box[i32]) -> i32 { return b.into_inner(); }\n";
    for (name, start, body, value) in [
        // Moved into a call on the path taken: dropping it again would be a double free.
        ("field_taken", 0, "let b: tuple { Box[i32], Box[i32] } = .{ make(6), make(7) }; if s < 21 { s = s + b.0.into_inner(); }", 6),
        ("field_not_taken", 30, "let b: tuple { Box[i32], Box[i32] } = .{ make(6), make(7) }; if s < 21 { s = s + b.0.into_inner(); }", 30),
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
fn test_assigning_through_a_reference_drops_the_old_value() {
    let setup = "fn set(r: &mut Box[i32], v: i32) { *r = Box[i32]::new(v); }\n";
    for (name, body, value) in [
        ("deref", "let mut b = Box[i32]::new(1); let r = &mut b; *r = Box[i32]::new(2); return b.into_inner();", 2),
        ("field", "let mut t: tuple { Box[i32], i32 } = .{ Box[i32]::new(1), 2 }; let r = &mut t; r.0 = Box[i32]::new(3); let c = t; return c.1 + c.0.into_inner();", 5),
        ("parameter", "let mut b = Box[i32]::new(1); set(&mut b, 4); set(&mut b, 5); return b.into_inner();", 5),
        ("get_mut", "let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); if let ?x = v.get_mut(0) { *x = Box[i32]::new(6); } return *(v.get(0) orelse unreachable).get();", 6),
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
    pub fn get(&self) -> i32 { return self.n; }
    pub fn add(&mut self, x: i32) { self.n = self.n + x; }
    pub fn add_ref(&mut self, x: &i32) { self.n = self.n + *x; }
    pub fn twice(&mut self) { self.add(self.get()); }
}
pub opaque K {
    n: i32,
    pub fn new() -> Self { return Self { n: 1 }; }
    pub fn add_ref(&mut self, x: &i32) { self.n = self.n + *x; }
    pub fn bad(&mut self) { self.add_ref(&self.n); }
}
fn len_of(v: &Vec[i32]) -> i32 { return v.len() as i32; }
";
    let good = types.replace("    pub fn bad(&mut self) { self.add_ref(&self.n); }\n", "");
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
fn test_taking_a_value_out_does_not_borrow_the_container() {
    let pool = "extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
pub struct Pool { x: i32 }
unsafe impl Allocator for Pool {
    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 { return unsafe { malloc(bytes) }; }
    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return unsafe { realloc(ptr, bytes) }; }
    fn dealloc(&self, ptr: *mut u8) { unsafe { free(ptr); } }
}
";
    for (name, body, value) in [
        ("pop_then_pop", "let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); v.push(&x); let a = v.pop(); let b = v.pop(); if let ?r = a { return *r; } return 0;", 1),
        ("pop_then_push", "let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); let a = v.pop(); v.push(&x); if let ?r = a { return *r; } return 0;", 1),
        ("insert_then_insert", "let x: i32 = 1; let mut m = HashMap[i32, &i32]::new(); let a = m.insert(1, &x); let b = m.insert(1, &x); if let ?r = b { return *r; } return 0;", 1),
        ("remove_then_insert", "let x: i32 = 1; let mut m = HashMap[i32, &i32]::new(); let a = m.insert(1, &x); let b = m.remove(1); let c = m.insert(2, &x); if let ?r = b { return *r; } return 0;", 1),
        ("stateful_insert", "let p = Pool { x: 1 }; let mut m = HashMap[i32, Box[i32, &Pool], &Pool]::new_in(&p); let a = m.insert(1, Box[i32, &Pool]::new_in(1, &p)); let b = m.insert(1, Box[i32, &Pool]::new_in(2, &p)); if let ?r = b { return r.into_inner(); } return 0;", 1),
        ("replace_then_write", "let x: i32 = 1; let y: i32 = 2; let mut r: &i32 = &x; let old = replace(&mut r, &y); r = &x; return *old;", 1),
    ] {
        assert_runs(name, &format!("{pool}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // What was taken out still holds what the container held.
    for (name, body) in [
        ("pop_outlives_referent", "let mut v = Vec[&i32]::new(); if true { let x: i32 = 1; v.push(&x); } let a = v.pop(); if let ?r = a { return *r; } return 0;"),
        ("taken_out_outlives_referent", "let mut a: ?&i32 = null; if true { let x: i32 = 1; let mut v = Vec[&i32]::new(); v.push(&x); a = v.pop(); } if let ?r = a { return *r; } return 0;"),
        ("removed_outlives_referent", "let mut a: ?&i32 = null; if true { let x: i32 = 1; let mut m = HashMap[i32, &i32]::new(); let _o = m.insert(1, &x); a = m.remove(1); } if let ?r = a { return *r; } return 0;"),
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
        "pub struct T { v: Vec[i32], pub fn into_len(self) -> i32 { return self.v.len() as i32; } }
pub fn main() -> i32 { let mut v = Vec[i32]::new(); v.push(1); let t = T { v: v }; let f = move fn() -> i32 { return t.into_len(); }; return f(); }",
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
fn test_zero_defaults_are_one_store() {
    // A default that is all zero bytes is one `zeroinitializer` store, not one per element.
    let src = "pub fn main() -> i32 { let mut buf: array[u8; 4096] = @default(array[u8; 4096]); buf[7] = 3; return buf[7] as i32 + buf[4095] as i32; }";
    let program = Compiler::compile_source(src).unwrap();
    let ir = crate::llvm::LlvmLowering::lower(&program).unwrap();
    assert!(ir.contains("store [4096 x i8] zeroinitializer"), "{ir}");
    assert!(ir.lines().count() < 200, "{} lines", ir.lines().count());
    assert_runs("bytes", src, 3);
    for (name, body, value) in [
        ("nested", "let g: array[array[i32; 8]; 8] = @default(array[array[i32; 8]; 8]); return g[7][7] + 1;", 1),
        ("tuple_of_floats", "let t: tuple { f64, bool, array[i64; 3] } = @default(tuple { f64, bool, array[i64; 3] }); if t.0 == 0.0 && !t.1 { return t.2[2] as i32 + 2; } return 9;", 2),
        // A field's own default keeps it from being all zeros.
        ("field_default", "let p: array[P; 2] = @default(array[P; 2]); return p[1].x;", 5),
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
fn tag[T](x: T) -> tuple {{ i32, T }} {{ return .{{ 1, x }}; }}
fn tag[T: ?linear](x: T) -> tuple {{ i32, T }} {{ return .{{ 2, x }}; }}
trait Named {{ fn name(&self) -> i32; }}
impl Named for Tx {{ fn name(&self) -> i32 {{ return 7; }} }}
fn named[T: Named + ?linear](x: &T) -> i32 {{ return x.name(); }}
fn named_plain[T: Named](x: &T) -> i32 {{ return x.name(); }}
fn unasked[T: sync](x: &T) -> i32 {{ return 1; }}
fn Cell[T: ?linear]() -> type {{ return opaque {{ v: T, pub fn new(v: T) -> Self {{ return Self {{ v: v }}; }} pub fn take(self) -> T {{ return self.v; }} }}; }}
");
    for (name, body, value) in [
        ("passed_through", "let t = pass(Tx::new(3)); return t.commit();", 3),
        ("not_linear_too", "let n: i32 = 4; return pass(n);", 4),
        // `[T]` is the more specific of the two, for a type that can be dropped.
        ("plain_preferred", "let n: i32 = 0; let .{ a, m } = tag(n); let .{ b, t } = tag(Tx::new(0)); return a * 10 + b + t.commit();", 12),
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
        ("a_plain_type_function", "fn Plain[T]() -> type { return opaque { v: T }; }\npub fn main() -> i32 { let p: ?*mut Plain[Tx] = null; return 0; }", because),
        // Saying `?linear` holds the body to it, used or not.
        ("drops_one", "fn lose[T: ?linear](x: T) -> i32 { return 1; }\npub fn main() -> i32 { return 0; }", "Generic 'root::lose' uses its type parameters beyond what their bounds promise: Linear value 'x' of type 'T' must be explicitly consumed"),
        // ... and is held to that: one that moves a `T` out of a pointer must consume it.
        ("value_free_drops_one", "fn lose[T](p: *mut T) -> i32 { unsafe { let v = move *p; } return 1; }\npub fn main() -> i32 { return 0; }", "Generic 'root::lose' uses its type parameters beyond what their bounds promise: Linear value 'v' of type 'T' must be explicitly consumed"),
    ] {
        assert_rejected(name, &format!("{decls}{src}"), message);
    }
}

#[test]
fn test_zeroinit() {
    // `zeroinit` types have all-zero bytes as a value; the `zeroinit` literal is that value, in
    // one store, and `Vec::zeroed` makes a vector of them.
    let src = "pub fn main() -> i32 { let b: array[u8; 4096] = zeroinit; return b[4095] as i32; }";
    let ir = crate::llvm::LlvmLowering::lower(&Compiler::compile_source(src).unwrap()).unwrap();
    assert!(ir.contains("store [4096 x i8] zeroinitializer") && ir.lines().count() < 200);
    let decls = "opaque(unsafe zeroinit) Counter { n: u32, pub fn n(&self) -> u32 { return self.n; } }
enum Level { Off = 0, On = 1 }
fn fill[T: zeroinit]() -> array[T; 4] { return zeroinit; }
fn probe[T: unchecked]() -> i32 { if @satisfies(T, zeroinit) { return 1; } return 0; }
";
    for (name, body, value) in [
        ("scalars_and_arrays", "let b: array[u8; 64] = zeroinit; let f: tuple { f64, bool, rune } = zeroinit; if f.0 == 0.0 && !f.1 { return b[63] as i32 + 1; } return 9;", 1),
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
    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 { unsafe { ALLOCS = ALLOCS + 1; } return @raw_alloc(bytes); }
    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return unsafe { @realloc(u8, ptr, bytes) }; }
    fn dealloc(&self, ptr: *mut u8) { unsafe { @dealloc(ptr); } }
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
fn test_optional_owner_needs_no_tag() {
    let prelude = "struct Unit { }
struct Node { v: i32, next: ?Box[Node] }
struct Wrap { b: Box[i32] }
struct Late { n: u64, p: Box[u64],
    pub fn new(n: u64, v: u64) -> Self { return Self { n: n, p: Box[u64]::new(v) }; }
    pub fn sum(&self) -> i32 { return (self.n + *self.p.get()) as i32; }
}
opaque Raw { p: *const u8 }
opaque Held { u: uninit *own u8 }
struct Beside { a: u64, o: ?Late, z: u8 }
struct Tagged { a: u64, o: ?i32 }
struct Deep { a: u64, l: Late }
struct Pad { a: u8, b: Box[u8] }
fn nothing() -> ?Late { return null; }
fn something(n: u64) -> ?Late { return Late::new(n, 2); }
fn use_late(o: ?Late) -> i32 { if let ?l = o { return l.sum(); } return 3; }
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
        ("offset_inside", "let s = Beside { a: 1, o: something(7), z: 0 }; if let ?ref l = s.o { return (&l.p as *const Box[u64] as usize - &s as *const Beside as usize) as i32; } return 0;", 16),
        ("offset_after", "let s = Beside { a: 1, o: something(7), z: 0 }; return (&s.z as *const u8 as usize - &s as *const Beside as usize) as i32;", 24),
        ("offset_inside_a_tag", "let s = Tagged { a: 1, o: 7 }; if let ?ref v = s.o { return (v as *const i32 as usize - &s as *const Tagged as usize) as i32; } return 0;", 12),
        ("deep_in_a_field", "let o: ?Deep = Deep { a: 1, l: Late::new(0, 4) }; if let ?d = o { return d.l.sum(); } return 3;", 4),
        ("past_padding", "let bits: tuple { u64, u64 } = .{ 18446744073709551615, 0 }; let o = unsafe { @transmute(?Pad, bits) }; return (o == null) as i32;", 1),
        ("null_from_bits", "let bits: tuple { u64, u64 } = .{ 5, 0 }; let o = unsafe { @transmute(?Late, bits) }; return (o == null) as i32;", 1),
        ("reassigned", "let mut o = something(1); o = null; if o != null { return 0; } o = something(5); return use_late(o);", 7),
        ("in_a_vec", "let mut v = Vec[?Box[i32]]::new(); v.push(null); v.push(Box[i32]::new(9)); let a = v.get(0) orelse unreachable; let b = v.get(1) orelse unreachable; return (*a == null) as i32 * 10 + (*b != null) as i32;", 11),
        ("taken", "let mut h = Node { v: 1, next: Box[Node]::new(Node { v: 2, next: null }) }; let n = core::mem::replace(&mut h.next, null); if h.next != null { return 0; } if let ?b = n { return b.get().v; } return 9;", 2),
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
    pub fn push(&mut self, v: i32) {
        let old = core::mem::replace(&mut self.head, null);
        self.head = Box[Node]::new(Node { v: v, next: old });
    }
    impl drop { fn drop(&mut self) {
        let mut cur = core::mem::replace(&mut self.head, null);
        while let ?b = cur {
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
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + 1; } } } }
struct L { d: D, next: ?Box[L] }
fn make(n: i32) { let mut h = L { d: D::new(0), next: null }; for i in 1..n { h = L { d: D::new(i), next: Box[L]::new(h) }; } }
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
fn chain(n: i32) { let mut e = E::Leaf; for i in 0..n { e = E::Neg(Box[E]::new(e)); } }
fn cycle(n: i32) { let mut a = A { b: null }; for i in 0..n { a = A { b: Box[B]::new(B { a: Box[A]::new(a) }) }; } }
pub fn main() -> i32 { chain(NODES); cycle(NODES); return 1; }";
    scaled(shapes, 500000, 300, 1);
    // A drop that parks leaves its count with its fiber, and another's drops run meanwhile.
    let parking = "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(&mut self) { if self.v % 50 == 0 { let _s = sleep_ms(0); } unsafe { DROPS = DROPS + 1; } } } }
struct L { d: D, next: ?Box[L] }
fn make(n: i32) -> i32 { let mut h = L { d: D::new(0), next: null }; for i in 1..n { h = L { d: D::new(i), next: Box[L]::new(h) }; } return 1; }
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
    impl drop { fn drop(&mut self) { unsafe { SEEN = SEEN * 10 + self.v; } } } }
struct L { d: D, next: ?Box[L] }
fn make() { let mut h = L { d: D::new(3), next: null }; h = L { d: D::new(2), next: Box[L]::new(h) }; h = L { d: D::new(1), next: Box[L]::new(h) }; }
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
            "fn depth(n: i32, pad: array[i64; 8]) -> i32 { if n == 0 { return pad[0] as i32; } let r = depth(n - 1, pad); return r + 1 - 1; }
pub fn main() -> i32 { let t = async(Fibers { }) depth(20000, @default(array[i64; 8])); return t.await() + 1; }"
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
fn test_temporaries_are_dropped() {
    let prelude = "static mut DROPS: i32 = 0;
pub opaque Noisy {
    n: i32,
    pub fn new(n: i32) -> Self { return Self { n: n }; }
    pub fn n(&self) -> i32 { return self.n; }
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + 1; } } }
}
pub opaque Holder {
    r: &i32,
    pub fn new(r: &i32) -> Self borrows(r) { return Self { r: r }; }
    pub fn get(&self) -> i32 { return *self.r; }
    impl drop { fn drop(&mut self) { } }
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
        ("element_outlives_it", "let r = mk().get(0); if let ?x = r { return *x; } return 0;", "borrowed"),
        ("linear_temporary", "let n = Tx::new(1).id(); return n;", "must be explicitly consumed"),
    ] {
        assert_rejected(
            name,
            &format!("{prelude}pub opaque(linear) Tx {{ n: i32, pub fn new(n: i32) -> Self {{ return Self {{ n: n }}; }} pub fn id(&self) -> i32 {{ return self.n; }} }}\npub fn main() -> i32 {{ {body} }}"),
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
    pub fn value(&self) -> ?i32 { if self.n > 0 { return self.n; } return null; }
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + 1; } } }
}
fn drops() -> i32 { return unsafe { DROPS }; }
";
    for (name, body, value) in [
        ("each_time_round", "let mut i: i32 = 3; while let ?n = Noisy::new(i).value() { i = i - n; } return drops();", 2),
        ("after_a_break", "while let ?n = Noisy::new(1).value() { break; } return drops();", 1),
        ("after_a_continue", "let mut i: i32 = 2; while let ?n = Noisy::new(i).value() { i = i - 1; continue; } return drops();", 3),
        ("after_a_return", "if true { let a = looped(); return a + drops(); } return 0;", 2),
        ("for_is_unchanged", "let mut t: i32 = 0; for x in 0..3 { t = t + x; } return t;", 3),
    ] {
        assert_runs(name, &format!("{prelude}fn looped() -> i32 {{ while let ?n = Noisy::new(1).value() {{ return n; }} return 0; }}\npub fn main() -> i32 {{ {body} }}"), value);
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
        ("task_per_item", "let mut t = Vec[Task[i32]]::new(); for i in 0..2 { let r = pick(&v) orelse unreachable; t.push(async rd(&r.b)); } let mut s: i32 = 0; while let ?x = t.pop() { s = s + x.await(); } return s;", 4),
        ("through_a_temporary", "let mut t = Vec[Task[i32]]::new(); for i in 0..2 { t.push(async rd(&(pick(&v) orelse unreachable).b)); } let mut s: i32 = 0; while let ?x = t.pop() { s = s + x.await(); } return s;", 4),
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
fn test_arrays_drop_their_elements() {
    let prelude = "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + self.v; } } } }
struct W { a: array[D; 2] }
union U { A, B(array[D; 2]) }
fn d(v: i32) -> D { return D::new(v); }
";
    for (name, body, value) in [
        ("plain", "if true { let a: array[D; 2] = [d(1), d(2)]; }", 3),
        ("nested", "if true { let a: array[array[D; 2]; 2] = [[d(1), d(2)], [d(4), d(8)]]; }", 15),
        ("in_a_struct", "if true { let s = W { a: [d(1), d(2)] }; }", 3),
        ("in_a_union", "if true { let u = U::B([d(1), d(2)]); }", 3),
        ("in_an_optional", "if true { let o: ?array[D; 2] = null; let a: array[D; 2] = [d(1), d(2)]; let p: ?array[D; 2] = a; }", 3),
        ("moved_whole", "if true { let a: array[D; 2] = [d(1), d(2)]; let b = a; }", 3),
        ("moved_on_one_path", "if true { let a: array[D; 2] = [d(1), d(2)]; if true { let b = a; } }", 3),
        // Overwriting an element drops the one it replaces.
        ("overwritten", "if true { let mut a: array[D; 2] = [d(1), d(2)]; a[0] = d(4); }", 7),
        ("overwritten_deep", "if true { let mut s = W { a: [d(1), d(2)] }; s.a[1] = d(4); }", 7),
        ("overwritten_through_a_reference", "if true { let mut a: array[D; 2] = [d(1), d(2)]; let r = &mut a; r[1] = d(4); }", 7),
        ("replaced", "if true { let mut a: array[D; 2] = [d(1), d(2)]; let x = core::mem::replace(&mut a[0], d(4)); }", 7),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} return unsafe {{ DROPS }}; }}"), value);
    }
    // Which element an index names is not known when checking moves, so none goes alone.
    for (name, body, message) in [
        ("move_by_index", "let a: array[D; 2] = [d(1), d(2)]; let x = a[0]; return 0;", "out of an array by index"),
        ("copy_by_index", "let a: array[D; 2] = [d(1), d(2)]; let x = a[1]; return 0;", "out of an array by index"),
        ("write_into_moved", "let mut a: array[D; 2] = [d(1), d(2)]; let b = a; a[0] = d(4); return 0;", "moved or uninitialized"),
    ] {
        assert_rejected(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), message);
    }
}

#[test]
fn test_defer() {
    let prelude = "error E { Bad }
fn parse(n: i32) -> E!i32 { if n < 0 { return E::Bad; } return n; }
static mut LOG: i64 = 0;
fn note(d: i64) { unsafe { LOG = LOG * 10 + d; } }
fn log() -> i64 { return unsafe { LOG }; }
opaque(linear) Tx { id: i32, pub fn begin(id: i32) -> Self { return Self { id: id }; } pub fn commit(self) -> i32 { note(9); return self.id; } }
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
    pub fn commit(self) -> i32 { note(1); return self.id; }
    pub fn rollback(self) { note(2); }
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
    pub fn pick(&mut self, which: i32) {
        if which == 0 { self.state = null; } else if which == 1 { self.state = &rel self.foo; } else { self.state = &rel self.bar; }
    }
    pub fn get(&self) -> ?i32 { let r = self.state orelse return null; return *r; }
    pub fn bump(&mut self) { if let ?r = &mut self.state { *r += 10; } }
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
    buf: array[u8; 6],
    text: ?&rel str,
    part: ?&rel [u8],
    pub fn new() -> Self { return Self { buf: b\"hello!\", text: null, part: &rel self.buf[1..3] }; }
    pub fn name(&mut self) { self.text = &rel self.buf[0..5]; }
    pub fn text_len(&self) -> usize { let t = self.text orelse return 0; return t.len; }
    pub fn part_first(&self) -> u8 { let p = self.part orelse return 0; return p[0]; }
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
        ("outside_target", "opaque O { a: i32, s: ?&rel i32, pub fn set(&mut self, x: &i32) { self.s = &rel *x; } }\npub fn main() -> i32 { return 0; }", "Co-Residence violation on 'O.s'"),
        ("wrong_type", "opaque O { a: i64, s: ?&rel i32, pub fn new() -> Self { return Self { a: 1, s: &rel self.a }; } }\npub fn main() -> i32 { let o = O::new(); return 0; }", "expected target of type i32, found i64"),
        ("not_a_reference", "opaque O { a: i32, s: ?&rel i32, pub fn new() -> Self { return Self { a: 1, s: 5 }; } }\npub fn main() -> i32 { let o = O::new(); return 0; }", "must be initialized or assigned with '&rel <place>' or 'null'"),
        ("in_struct", "struct S { a: i32, s: ?&rel i32 }\npub fn main() -> i32 { return 0; }", "only permitted in 'opaque' field declarations"),
        ("as_local", "pub fn main() -> i32 { let x: ?&rel i32 = null; return 0; }", "'?&rel' relative references are only permitted in 'opaque' field declarations"),
        // What it resolves to borrows the value, as `&rel T` does.
        ("borrow", "opaque O { a: i32, s: ?&rel i32,
  pub fn new() -> Self { return Self { a: 1, s: null }; }
  pub fn f(&mut self) { self.s = &rel self.a; let r = &mut self.s; self.a = 5; if let ?x = r { *x = 2; } } }
pub fn main() -> i32 { let mut o = O::new(); o.f(); return 0; }", "cannot mutate or move 'self.a' because it is currently borrowed"),
    ] {
        assert_rejected(name, src, what);
    }
}

#[test]
fn test_opaque_fields_drop_after_its_hook() {
    let prelude = "static mut LOG: i64 = 0;
opaque D { v: i64,
    pub fn new(v: i64) -> D { return D { v: v }; }
    impl drop { fn drop(&mut self) { unsafe { LOG = LOG * 10 + self.v; } } } }
opaque Holder { a: D, n: i32, b: D, s: String,
    pub fn new() -> Self { return Self { a: D::new(2), n: 0, b: D::new(3), s: String::from(\"x\") }; }
    impl drop { fn drop(&mut self) { unsafe { LOG = LOG * 10 + 1; } } } }
opaque Generic[T] { value: T,
    pub fn new(value: T) -> Self { return Self { value: value }; }
    impl drop { fn drop(&mut self) { unsafe { LOG = LOG * 10 + 9; } } } }
opaque(linear) Owner { id: i32, d: D,
    pub fn new() -> Self { return Self { id: 5, d: D::new(4) }; }
    pub fn finish(self) -> i32 { return self.id; }
    impl drop { fn drop(&mut self) { unsafe { LOG = LOG * 10 + 1; } } } }
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

/// `Rc` and `Weak`: shared values dropped with their last `Rc`, `Weak` back-references that
/// break cycles, uniqueness-gated mutation, and a long list dropped without deep recursion.
#[test]
fn test_rc_and_weak() {
    assert_runs(
        "rc_and_weak",
        "static mut DROPS: i32 = 0;
opaque Tracked {
    v: i32,
    impl drop { fn drop(&mut self) { unsafe { DROPS += 1; } } }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn v(&self) -> i32 { return self.v; }
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
    impl drop { fn drop(&mut self) { unsafe { DROPS += 1; } } }
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
    while let ?h = handles.pop() {
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
    if let ?t = a.into_inner() {{ _ = t.commit(); unreachable; }}
    let tx = b.into_inner() orelse unreachable;
    if let ?r = w.upgrade() {{ unreachable; }}
    let x = Arc[Tx]::new(Tx::new(5));
    let y = x.share();
    if let ?t = y.into_inner() {{ _ = t.commit(); unreachable; }}
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
    impl drop { fn drop(&mut self) { unsafe { DROPS += 1; } } }
    impl clone { fn clone(&self) -> Self { return Self { v: self.v }; } }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn v(&self) -> i32 { return self.v; }
    pub fn set(&mut self, v: i32) { self.v = v; }
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
    let arr: array[i32; 3] = [4, 5, 6];
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
    while let ?h = handles.pop() {
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

/// `clone` and `try_clone` copy optionals, unions, and arrays of what they copy, so a struct
/// holding a `?String` copies; and a `match` arm that retires its scrutinee (one whose variant
/// holds only `copy` values) leaves nothing to be dropped after it.
#[test]
fn test_copies_of_unions_and_arrays() {
    assert_runs("union_array_copies", "union Shape { Circle(String), Square(i32), Empty }
struct Card { name: ?String, tags: array[String; 2], shape: Shape }
pub fn main() -> i32 {
    let a: ?String = String::from(\"abc\");
    let b = a.clone();
    let none: ?String = null;
    let c = none.clone();
    let arr: array[String; 2] = [String::from(\"x\"), String::from(\"yz\")];
    let d = arr.clone();
    let card = Card { name: String::from(\"ada\"), tags: [String::from(\"p\"), String::from(\"qq\")], shape: .Circle(String::from(\"round\")) };
    let e = card.clone();
    let f = card.try_clone() catch |err| return 1;
    let g = arr.try_clone() catch |err| return 2;
    let h = none.try_clone() catch |err| return 3;
    let s2: Shape = .Square(4);
    let i = s2.try_clone() catch |err| return 4;
    let mut n: usize = 0;
    if let ?s = b { n += s.len(); }
    if let ?s = c { n += 100; }
    n += d[1].len() + g[0].len();
    if let ?s = e.name { n += s.len(); }
    if let ?s = f.name { n += s.len(); }
    if let ?s = h { n += 100; }
    n += f.tags[1].len();
    return n as i32 + 19 + match f.shape { .Circle(r) => r.len() as i32, .Square(k) => k, .Empty => 0 } + match i { .Square(k) => k, _ => 0 };
}
", 42);
    assert_runs(
        "match_retires_scrutinee",
        "union Shape { Circle(String), Square(i32), Empty }
pub fn main() -> i32 { let i: Shape = .Square(42); return match i { .Square(k) => k, _ => 0 }; }",
        42,
    );
}

/// `move` is written where it changes something: a closure that captures by value, a `&mut`
/// handed over, and a value taken out through a raw pointer. Elsewhere it is refused.
#[test]
fn test_move_is_written_where_it_changes_something() {
    assert_runs(
        "meaningful_moves",
        "fn take(s: String) -> i32 { return s.len() as i32; }
opaque O { s: String, pub fn new() -> Self { return Self { s: String::from(\"abc\") }; } pub fn into(self) -> String { return self.s; } }
pub fn main() -> i32 {
    let s = String::from(\"ab\");
    let f = move fn() -> i32 { return take(s); };
    let mut a: i32 = 20;
    let mut b: i32 = 10;
    let mut out = Vec[&mut i32]::new();
    let mut r: &mut i32 = &mut a;
    out.push(move r);
    r = &mut b;
    out.push(move r);
    let p: *mut String = unsafe { @alloc(String, 1) };
    unsafe { *p = String::from(\"xyz\"); }
    let t = unsafe { move *p };
    unsafe { @dealloc(p); }
    let mut sum = 0;
    for x in out.iter() { sum += **x; }
    return sum + f() + t.len() as i32 + O::new().into().len() as i32 + 4;
}",
        42,
    );
    let refused = [
        ("fn take(s: String) -> i32 { return 0; } pub fn main() -> i32 { let s = String::from(\"a\"); return take(move s); }", "'move' is implied here"),
        ("pub fn main() -> i32 { let n: i32 = 1; let m = move n; return m; }", "'move' of a 'copy' value ('i32') only forbids using it again"),
        ("fn f(move s: String) -> i32 { return 0; } pub fn main() -> i32 { return 0; }", "'move' on a parameter changes nothing"),
        ("opaque O { v: i32, pub fn f(move self) -> i32 { return self.v; } } pub fn main() -> i32 { return 0; }", "write 'self', which takes the value"),
        ("opaque O { v: i32, pub fn f(self: Self) -> i32 { return self.v; } } pub fn main() -> i32 { return 0; }", "Write 'self' for a receiver that takes the value, not 'self: Self'"),
        ("union U { A(String), B(i32) } pub fn main() -> i32 { let u: U = .B(1); return match u { .A(move s) => 0, .B(k) => k }; }", "'move' in a pattern changes nothing"),
        ("struct S { a: String } pub fn main() -> i32 { let a = String::from(\"x\"); let s = S { move a }; return 0; }", "'move' in a field shorthand changes nothing"),
        ("pub fn main() -> i32 { let p: *mut String = unsafe { @alloc(String, 1) }; unsafe { *p = String::from(\"x\"); } let t = unsafe { *p }; return 0; }", "write 'move' before it ('move *p')"),
    ];
    for (i, (src, what)) in refused.iter().enumerate() {
        assert_rejected(&format!("move_refused_{i}"), src, what);
    }
}

#[test]
fn test_borrows_name_what_can_be_borrowed() {
    assert_runs(
        "borrows_through_held",
        "struct H { r: &i32 }
fn first(h: H) -> &i32 borrows(h) { return h.r; }
fn pick[T](x: T, t: &i32) -> &i32 borrows(x, t) { return t; }
fn count(n: i32) -> gen i32 { for i in 0..n { yield i; } }
pub fn main() -> i32 {
    let x: i32 = 40;
    let y: i32 = 2;
    let mut sum = 0;
    for i in count(3) { sum += i; }
    return *first(H { r: &x }) + *pick(1, &y) + sum - 3;
}",
        42,
    );
    let refused = [
        ("fn f(s: String, t: &str) -> &str borrows(s, t) { return t; } pub fn main() -> i32 { return 0; }", "borrows(s) on 'f': 's' is of type 'String', which holds no borrows"),
        ("fn f(n: i32, t: &str) -> &str borrows(n, t) { return t; } pub fn main() -> i32 { return 0; }", "take '&i32'"),
        ("fn put(out: &mut ?&str, s: String) borrows(out: s) { } pub fn main() -> i32 { return 0; }", "borrows(out: s) on 'put'"),
        ("fn f(p: &i32) -> &i32 borrows(p, *p) { return p; } pub fn main() -> i32 { return 0; }", "'*p' is of type 'i32', which holds no borrows"),
        ("fn f(s: String) -> &str { return s.as_str(); } pub fn main() -> i32 { let r = f(String::from(\"a\")); return 0; }", "'s' is dropped while still borrowed"),
        ("struct S { a: String, n: i32 } fn f(s: S) -> &String { return &s.a; } pub fn main() -> i32 { return 0; }", "'s.a' is dropped while still borrowed"),
    ];
    for (i, (src, what)) in refused.iter().enumerate() {
        assert_rejected(&format!("borrows_refused_{i}"), src, what);
    }
}

