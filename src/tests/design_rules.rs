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
fn pick(comptime T: integer, x: T) -> i32 { return 1; }
fn pick(comptime T: signed, x: T) -> i32 { return 10; }
fn pick(comptime T: type, x: T) -> i32 { return 100; }
fn tr(comptime T: A, x: &T) -> i32 { return 1000; }
fn tr(comptime T: A + B, x: &T) -> i32 { return 2000; }
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
        "fn foo(comptime T: send, x: T) -> i32 { return 1; }
fn foo(comptime T: number, x: T) -> i32 { return 2; }
pub fn main() -> i32 { let a: i32 = 42; return foo(i32, a); }",
        "Ambiguous call to overloaded 'foo'",
    );
    reject(
        "linear_vs_opaque_extension",
        &with_tx(
            "pub fn tag(comptime S: opaque, self: &S) -> i32 { return 3; }
pub fn tag(comptime L: linear, self: &L) -> i32 { return 4; }
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
pub union Cell { Num: i32, Boxed: Box(i32), Empty }
pub fn main() -> i32 {
    let mut c = Ctr::new();
    let mut sum: i32 = 0;
    while let v = c.next() { sum = sum + v; }
    if sum != 15 { return 1; }

    let b = Cell::Boxed(Box(i32)::new(41));
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
    let p = try_alloc(i32, 4) orelse return 2;
    unsafe { *p = 7; @dealloc(p); }
    let huge: usize = 18446744073709551615;
    if let q = try_alloc(i64, huge) { return 3; }
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
        "fn call_it(comptime T: type, x: T) -> i32 { return x.missing(); }
pub fn main() -> i32 { return call_it(i32, 1); }",
        "in instantiation of root::call_it(T = i32)",
    );
    reject(
        "stage2_error_in_type_fn_method",
        "fn W(comptime T: type) -> type {
    return opaque { v: T, pub fn new(v: T) -> Self { return Self { v: v }; } pub fn peek(self: &Self) -> i32 { return self.v.missing(); } };
}
pub fn main() -> i32 { let w = W(i32)::new(1); return w.peek(); }",
        "in instantiation of W(i32)::peek",
    );
    // Stage 3 diagnostics name the instantiation they occur in.
    reject(
        "stage3_error_names_instantiation",
        &with_tx(
            "fn ignore(comptime T: type, x: T) -> i32 { return 0; }
pub fn main() -> i32 { return ignore(Tx, Tx::new(1)); }",
        ),
        "root::ignore(T = Tx)",
    );
    reject(
        "linear_type_label",
        &with_tx("pub fn main() -> i32 { let c = Channel(Tx)::new(); return 0; }"),
        "of type 'Channel(Tx)'",
    );
}

#[test]
fn test_optional_niche_layout() {
    assert_eq!(
        run_lli(
            "niche_layout",
            "pub fn NonZero(comptime Int: integer) -> type { return Int in 1..=Int::MAX; }
alias PosixFd = i32 in 0..=2147483647;
alias Percent = u8 in 0..=100;
alias Digit = u8 in 0..=9 | 200..=255;
fn first(a: &i32) -> ?&i32 { return a; }
pub fn main() -> i32 {
    // Pointers and range types with an invalid bit pattern store `null` in it: no tag.
    if @size_of(?&i32) != 8 || @size_of(?*mut u8) != 8 || @size_of(?fn(i32) -> i32) != 8 { return 1; }
    if @size_of(?NonZero(u32)) != 4 || @size_of(?rune) != 4 || @size_of(?PosixFd) != 4 { return 2; }
    if @size_of(?Percent) != 1 || @size_of(?Digit) != 1 { return 3; }
    // Without a niche (every bit pattern of `i32` is valid) the optional keeps its tag.
    if @size_of(?i32) != 8 { return 4; }

    // The `null` value follows the documented priority: 0, then all-ones, then above the first range.
    let fd: ?PosixFd = null;
    let pct: ?Percent = null;
    let dig: ?Digit = null;
    let nz: ?NonZero(u32) = null;
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
    drop(self: &mut Self) { unsafe { *self.p = *self.p + 1; } }
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
            "pub enum(u16) Opcode { Ping = 1, Auth = 16, Disconnect = 65535 }
pub union(Opcode) Message { Ping: u64, Auth: i32, Disconnect }
pub union Shape { Circle: i32, Square: i32, Empty }
fn kind(s: &Shape) -> Shape::Tag { return s.tag; }
fn step(i: i32) -> Shape { if i < 3 { return Shape::Circle(i); } return Shape::Empty; }
pub fn main() -> i32 {
    // Synthesized `T::Tag` enum and `.tag`.
    let sq = Shape::Square(3);
    match kind(&sq) { Shape::Tag::Square => {}, Shape::Tag::Circle => return 1, Shape::Tag::Empty => return 1, }
    // `union(Opcode)`: `.tag` is an `Opcode`, and the stored tag is Opcode's value.
    let m = Message::Auth(5);
    let t: Opcode = m.tag;
    if t != Opcode::Auth { return 2; }
    let d = Message::Disconnect;
    if d.tag != Opcode::Disconnect { return 3; }
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
        "linked_union_extra_variant",
        "pub enum Op { A, B }\npub union(Op) M { A, B, C }\npub fn main() -> i32 { let m = M::A; return 0; }",
        "variant 'C' is not a variant of linked enum 'Op'",
    );
    reject(
        "linked_union_missing_variant",
        "pub enum Op { A, B }\npub union(Op) M { A }\npub fn main() -> i32 { let m = M::A; return 0; }",
        "missing variant 'B' of linked enum 'Op'",
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
pub export enum Ffi { A, B }
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
    b: Box(i32),
    pub fn new() -> Self { return Self { b: Box(i32)::new(1) }; }
    drop(self: &mut Self) { let x = *self.b.get(); }
    pub fn take(move self) -> Box(i32) { return self.b; }
}
pub fn main() -> i32 { let o = O::new(); let b = o.take(); return 0; }",
        "because that type has a 'drop' hook",
    );
    accept(
        "move_out_of_plain_opaque",
        "opaque O { b: Box(i32), pub fn new() -> Self { return Self { b: Box(i32)::new(1) }; } pub fn take(move self) -> Box(i32) { return self.b; } }
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
fn Pick(comptime n: i32) -> type {
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
    return F + S + (a.len as i32) - 3 + (@size_of(Pick(3)) as i32);
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
    // Bounds past `i128`: `u128::MAX`, `Int::MAX` of a `u256`, niche-optimized `?NonZero(u256)`,
    // checked casts, and compile-time evaluation through the VM.
    assert_eq!(
        run_lli(
            "pattern_wide_bounds",
            "alias Top = u128 in 340282366920938463463374607431768211400..=340282366920938463463374607431768211455;
pub fn NonZero(comptime Int: integer) -> type { return Int in 1..=Int::MAX; }
fn top(x: u128) -> ?Top { return x as? Top; }
fn g(x: u256) -> u256 { let y: NonZero(u256) = x as NonZero(u256); return y; }
const K: u256 = g(u256::MAX);
pub fn main() -> i32 {
    let m: Top = 340282366920938463463374607431768211455;
    let n: NonZero(u256) = 5;
    let mut r: i32 = (n as i32) + (@size_of(?NonZero(u256)) as i32) - 32;
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
    let dir = std::env::temp_dir().join(format!("lrrr_pkg_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src/net")).unwrap();
    std::fs::write(
        dir.join("src/main.lrrr"),
        "import root::net::http::get;\npub fn main() -> i32 { return get(); }",
    )
    .unwrap();
    std::fs::write(dir.join("src/net/http.lrrr"), "pub fn get() -> i32 { return 42; }").unwrap();
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
    let s: &str = \"lrrr\";
    if s != \"lrrr\" || unsafe { q.a } != 1 || (next(43 as Id) as i64) != 42 || LOW != -128 {
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
fn bad_field(comptime T: type, a: T) -> i32 { return a.nonexistent; }
fn dup_any(comptime T: type, a: T) -> tuple { T, T } { return { a, a }; }
fn good_add(comptime T: integer, a: T, b: T) -> T { return a + b; }
fn dup_copy(comptime T: copy, a: T) -> tuple { T, T } { return { a, a }; }
fn sized(comptime n: usize) -> usize { return n * 2; }
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
fn Nest(comptime N: i32) -> type {
    if N == 0 { return i32; }
    return tuple { i32, Nest(N - 1) };
}
fn Wider(comptime A: type, comptime B: type) -> type {
    let mut t: type = A;
    if @size_of(B) > @size_of(A) { t = B; }
    return [t; 2];
}
fn Pair(comptime A: type) -> type { return tuple { A, u8 }; }
fn Chain(comptime n: i32) -> type {
    let mut t: type = u8;
    let mut i: i32 = 0;
    while i < n {
        t = Pair(t);
        i += 1;
    }
    return t;
}
pub fn main() -> i32 {
    let a: Nest(2) = { 1, { 2, 3 } };
    let w: Wider(u8, i64) = { 30, 2 };
    let c: Chain(2) = { { 1, 2 }, 3 };
    if @size_of(Wider(u8, i64)) != 16 || @size_of(Wider(i32, u16)) != 8 { return 1; }
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
        ("return tuple { u8, Forever(N + 1) };", "recursed too deeply"),
    ] {
        let src = format!(
            "fn Forever(comptime N: i32) -> type {{ {body} }}
pub fn main() -> i32 {{ let x: Forever(0) = uninit; return 0; }}"
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
        "type A = struct { x: i32 }; type B = struct { x: i32 };
pub fn main() -> i32 { let a: A = A { x: 1 }; let b: B = a; return 0; }",
        "type A = struct { x: i32 };
pub fn main() -> i32 { let a: A = A { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
        "struct N { x: i32 }
pub fn main() -> i32 { let a: N = N { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
        "fn S(comptime T: type) -> type { return struct { x: T }; }
pub fn main() -> i32 { let a: S(i32) = S(i32) { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
    ];
    for src in distinct {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains("Type mismatch"), "{src}\n{err}");
    }
    let same = "alias P = tuple { i32, i32 };
fn S(comptime T: type) -> type { return @Struct(&[FieldSpec { name: \"x\", ty: T }]); }
pub fn main() -> i32 {
    let a: P = { 40, 1 };
    let b: tuple { i32, i32 } = a;
    let c: S(i32) = struct { x: i32 } { x: 1 };
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
type Named = struct { x: i32, y: i32 };
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
        "alias Point = struct { x: i32 }; type Named = struct { x: i32 };
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
        ("type P = distinct struct { x: i32 };", "declare 'type P = struct { ... }'"),
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
