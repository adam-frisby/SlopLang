use crate::lower::Compiler;

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
        &with_tx("pub fn main() -> i32 { let b = Box(Tx)::new(Tx::new(1)); return 0; }"),
        "Linear value",
    );
    reject(
        "mutex_linear_dropped",
        &with_tx("pub fn main() -> i32 { let m = Mutex(Tx)::new(Tx::new(1)); return 0; }"),
        "Linear value",
    );
    reject(
        "channel_linear_dropped",
        &with_tx("pub fn main() -> i32 { let c = Channel(Tx)::new(); return 0; }"),
        "Linear value",
    );
    // ...while their consuming exits hand the elements back.
    accept(
        "box_into_inner",
        &with_tx(
            "pub fn main() -> i32 { let b = Box(Tx)::new(Tx::new(1)); return b.into_inner().commit(); }",
        ),
    );
    accept(
        "mutex_into_inner",
        &with_tx(
            "pub fn main() -> i32 { let m = Mutex(Tx)::new(Tx::new(1)); return m.into_inner().commit(); }",
        ),
    );
    accept(
        "channel_close_and_drain",
        &with_tx(
            "pub fn main() -> i32 {
    let c = Channel(Tx)::new();
    c.send(Tx::new(1));
    c.close_and_drain(fn(t: Tx) { let _x = t.commit(); });
    return 0;
}",
        ),
    );
    // Affine and copy elements keep implicit scope-exit drops.
    accept(
        "box_affine",
        "pub fn main() -> i32 { let b = Box(i32)::new(7); let c = Box(i32)::new(8); return *b.get() + c.into_inner(); }",
    );
    accept(
        "mutex_affine",
        "pub fn main() -> i32 { let m = Mutex(i32)::new(3); return m.with_lock(fn(v: &mut i32) -> i32 { return *v; }); }",
    );
}

#[test]
fn test_owns_declaration_errors_and_lint() {
    reject(
        "owns_unknown_param",
        "fn W(comptime T: type) -> type { return opaque(owns U) { p: *mut T }; }
pub fn main() -> i32 { let x: ?*mut W(i32) = null; return 0; }",
        "'owns(U)' on opaque 'W' does not name a comptime type parameter",
    );
    reject(
        "owns_copy",
        "fn W(comptime T: type) -> type { return opaque(copy, owns T) { p: *mut T }; }
pub fn main() -> i32 { return 0; }",
        "'opaque(copy, owns ...)' is invalid",
    );

    // An owning container (has a `drop` hook) hiding `T` behind a raw pointer without `owns T` is linted.
    let leaky = "\
fn Leaky(comptime T: type) -> type {
    return opaque {
        ptr: *mut T,
        drop(self: &mut Self) { unsafe { @dealloc(self.ptr); } }
        pub fn new(v: T) -> Self {
            let p: *mut T = @alloc(T, 1);
            unsafe { *p = move v; }
            return Self { ptr: p };
        }
    };
}
pub fn main() -> i32 { let l = Leaky(i32)::new(1); return 0; }
";
    let (_, warnings) = Compiler::compile_package_with_warnings(&[("root", leaky)])
        .expect("Leaky(i32) should compile with a warning");
    assert!(
        warnings
            .iter()
            .any(|w| w.contains("opaque 'Leaky'") && w.contains("does not declare 'owns(T)'")),
        "Expected missing-owns lint, got: {warnings:?}"
    );

    // Non-owning views (no `drop` hook) and declared owners are not linted; neither is std.
    let view = "\
fn View(comptime T: type) -> type {
    return opaque {
        ptr: *const T,
        pub fn of(r: &T) -> Self { return Self { ptr: r as *const T }; }
    };
}
pub fn main() -> i32 {
    let x: i32 = 1;
    let v = View(i32)::of(&x);
    let b = Box(i32)::new(2);
    let m = Mutex(i32)::new(3);
    return 0;
}
";
    let (_, warnings) = Compiler::compile_package_with_warnings(&[("root", view)])
        .expect("View(i32) should compile");
    assert!(warnings.is_empty(), "Unexpected warnings: {warnings:?}");
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
            "fn upd(r: &mut Tx) -> i32 { let old = replace(Tx, r, Tx::new(9)); return old.commit(); }
pub fn main() -> i32 { let mut t = Tx::new(1); let a = upd(&mut t); return a + t.commit(); }",
        ),
    );
    accept(
        "swap_linear",
        &with_tx(
            "pub fn main() -> i32 {
    let mut a = Tx::new(1);
    let mut b = Tx::new(2);
    swap(Tx, &mut a, &mut b);
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
    let store = "pub fn store(comptime T: type, dst: &mut T, v: T) { unsafe { let p: *mut T = dst as *mut T; *p = v; } }\n";
    reject(
        "generic_pub_missing_flow",
        &format!(
            "{store}pub fn main() -> i32 {{ let a: i32 = 1; let mut r: &i32 = &a; let b: i32 = 2; store(&i32, &mut r, &b); return 0; }}"
        ),
        "root::store",
    );
    accept(
        "generic_pub_plain_instantiation",
        &format!("{store}pub fn main() -> i32 {{ let mut a: i32 = 1; store(i32, &mut a, 5); return a; }}"),
    );
    accept(
        "generic_pub_declared_flow",
        "pub fn store(comptime T: type, dst: &mut T, v: T) borrows(dst: v) { unsafe { let p: *mut T = dst as *mut T; *p = v; } }
pub fn main() -> i32 { let a: i32 = 1; let mut r: &i32 = &a; let b: i32 = 2; store(&i32, &mut r, &b); return *r; }",
    );

    // `pub(pkg)` follows the same rules as `pub`.
    reject(
        "pub_pkg_ambiguous_return",
        "pub(pkg) fn pick(a: &i32, b: &i32) -> &i32 { return a; }\npub fn main() -> i32 { return 0; }",
        "add an explicit 'borrows(...)' contract",
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
fn h(comptime T: Hash, x: &T) -> u64 { return x.hash(); }
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
            "pub fn Pair(comptime T: type) -> type { return struct { a: T, b: T }; }
impl Hash for i32 { fn hash(self: &Self) -> u64 { return *self as u64; } }
impl(comptime T: Hash) Hash for Pair(T) {
    fn hash(self: &Self) -> u64 { return self.a.hash() + self.b.hash(); }
}
pub fn main() -> i32 { let p = Pair(i32) { a: 2, b: 3 }; return h(&p) as i32; }",
        ),
    );
    reject(
        "generic_impl_bound_unmet",
        &with_hash(
            "pub fn Pair(comptime T: type) -> type { return struct { a: T, b: T }; }
impl(comptime T: Hash) Hash for Pair(T) { fn hash(self: &Self) -> u64 { return self.a.hash(); } }
pub fn main() -> i32 { let p = Pair(bool) { a: true, b: false }; return h(&p) as i32; }",
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
fn use2(comptime T: Two, x: &T) -> i32 { return x.a(); }
pub fn main() -> i32 { let p = P { x: 1 }; return use2(&p); }",
        "is missing trait method 'b'",
    );
    reject(
        "impl_contract_differs",
        "pub trait Get { fn get(self: &Self, o: &i32) -> &i32 borrows(self); }
struct P { r: &i32, impl Get { fn get(self: &Self, o: &i32) -> &i32 borrows(o) { return o; } } }
fn u(comptime T: Get, x: &T) -> i32 { let z: i32 = 0; return *x.get(&z); }
pub fn main() -> i32 { let a: i32 = 1; let p = P { r: &a }; return u(&p); }",
        "declares a borrows(...) contract that differs from trait 'Get'",
    );

    // Orphan rule: a module-level impl must live in the type's or the trait's module.
    let trait_mod = "pub trait Hash { fn hash(self: &Self) -> u64; }
pub fn h(comptime T: Hash, x: &T) -> u64 { return x.hash(); }";
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
pub fn h(comptime T: Hash, x: &T) -> u64 { return x.hash(); }
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
            "fn id(comptime T: type, x: &T) -> i32 { return 1; }
struct P { x: i32 }
pub fn main() -> i32 { let p = P { x: 1 }; return id(Hash, &p); }",
        ),
        "Trait 'Hash' is not a type",
    );
    reject(
        "type_alias_for_trait",
        "type D = trait { fn d(self: &Self) -> i32; };\npub fn main() -> i32 { return 0; }",
        "declare the alias with 'trait D = trait { ... };'",
    );
    accept(
        "trait_alias",
        "trait D = trait { fn d(self: &Self) -> i32; };
struct P { x: i32, impl D { fn d(self: &Self) -> i32 { return 4; } } }
fn g(comptime T: D, x: &T) -> i32 { return x.d(); }
pub fn main() -> i32 { let p = P { x: 1 }; return g(&p); }",
    );
}

#[test]
fn test_linear_values_in_threads_and_select() {
    // A losing `@select` send arm must hand its linear value back via `else |unsent|`.
    let prelude = "pub fn main() -> i32 {
    let a = Channel(Tx)::new();
    let b = Channel(i32)::new();
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
    drop(self: &mut Self) {}
}
pub fn main() -> i32 {
    let a = Channel(Tok)::new();
    let b = Channel(i32)::new();
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
    // ...while the internal Lrrr-ABI body has no exported symbol and no null-check trap.
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

    // Lrrr code may only use the Lrrr signature; the C ABI is reachable via `@c_abi`.
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
        "must be called with its Lrrr signature",
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
