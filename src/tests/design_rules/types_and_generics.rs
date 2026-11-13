use super::*;

#[test]
fn test_every_pub_function_defines_its_borrow_contract() {
    let slot = "pub opaque Slot {
    r: &i32,
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
    pub fn get(&self) -> &i32 { return self.r; }
";
    // A `pub` method that stores a parameter into `self` must declare the flow...
    reject(
        "pub_method_missing_flow",
        &format!(
            "{slot}    pub fn set(&mut self, r: &i32) {{ self.r = r; }}
}}
pub fn main() -> i32 {{ let a: i32 = 1; let mut s = Slot::new(&a); return 0; }}"
        ),
        "Slot::set",
    );
    // ...and callers are then held to it.
    let declared = format!(
        "{slot}    pub fn set(&mut self, r: &i32) borrows(self: r) {{ self.r = r; }}
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
            "{slot}    fn set(&mut self, r: &i32) {{ self.r = r; }}
    pub fn put(&mut self, r: &i32) borrows(self: r) {{ self.set(r); }}
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
            "struct S { v: i32, pub(mod) fn pick(&self, b: &i32) -> &i32 { return b; } }
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
    let sink_impl = "struct S { r: &i32, impl Sink { fn put(&mut self, r: &i32) { self.r = r; } } }\n";
    reject(
        "trait_method_flow_missing",
        &format!(
            "pub trait Sink {{ fn put(&mut self, r: &i32); }}
{sink_impl}pub fn main() -> i32 {{ let a: i32 = 1; let mut s = S {{ r: &a }}; let d: &mut Sink = &mut s; return 0; }}"
        ),
        "<S as Sink>::put",
    );
    reject(
        "trait_object_call_enforces_flow",
        &format!(
            "pub trait Sink {{ fn put(&mut self, r: &i32) borrows(self: r); }}
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

#[test]
fn test_traits_require_explicit_impl() {
    // Matching method names alone never make a type conform.
    reject(
        "duck_typing_rejected",
        &with_hash(
            "struct P { x: i32, pub fn hash(&self) -> u64 { return 1; } }
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
    impl Hash { fn hash(&self) -> u64 { return self.x as u64; } }
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
impl Hash for P { fn hash(&self) -> u64 { return self.x as u64; } }
pub fn main() -> i32 { let p = P::new(); return h(&p) as i32; }",
        ),
        "Cannot access private field 'x' of opaque 'P'",
    );
    // Retroactive impls for builtin types (in the trait's module) and generic impls.
    accept(
        "generic_impl",
        &with_hash(
            "pub fn Pair[T]() -> type { return struct { a: T, b: T }; }
impl Hash for i32 { fn hash(&self) -> u64 { return *self as u64; } }
impl[T: Hash] Hash for Pair[T] {
    fn hash(&self) -> u64 { return self.a.hash() + self.b.hash(); }
}
pub fn main() -> i32 { let p = Pair[i32] { a: 2, b: 3 }; return h(&p) as i32; }",
        ),
    );
    reject(
        "generic_impl_bound_unmet",
        &with_hash(
            "pub fn Pair[T]() -> type { return struct { a: T, b: T }; }
impl[T: Hash] Hash for Pair[T] { fn hash(&self) -> u64 { return self.a.hash(); } }
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
            "struct P { x: i32, impl Hash { fn hash(&self) -> u64 { return 1; } } }
impl Hash for P { fn hash(&self) -> u64 { return 2; } }
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
        fn hash(&self) -> u64 { return 1; }
        fn other(&self) -> i32 { return 0; }
    }
}
pub fn main() -> i32 { let p = P { x: 1 }; return h(&p) as i32; }",
        ),
        "Method 'other' in 'impl Hash' in the body of 'P' is not declared by trait 'Hash'",
    );
    reject(
        "missing_impl_method",
        "pub trait Two { fn a(&self) -> i32; fn b(&self) -> i32; }
struct P { x: i32, impl Two { fn a(&self) -> i32 { return 1; } } }
fn use2[T: Two](x: &T) -> i32 { return x.a(); }
pub fn main() -> i32 { let p = P { x: 1 }; return use2(&p); }",
        "is missing trait method 'b'",
    );
    reject(
        "impl_contract_differs",
        "pub trait Get { fn get(&self, o: &i32) -> &i32 borrows(self); }
struct P { r: &i32, impl Get { fn get(&self, o: &i32) -> &i32 borrows(o) { return o; } } }
fn u[T: Get](x: &T) -> i32 { let z: i32 = 0; return *x.get(&z); }
pub fn main() -> i32 { let a: i32 = 1; let p = P { r: &a }; return u(&p); }",
        "declares a borrows(...) contract that differs from trait 'Get'",
    );

    // Orphan rule: a module-level impl must live in the type's or the trait's module.
    let trait_mod = "pub trait Hash { fn hash(&self) -> u64; }
pub fn h[T: Hash](x: &T) -> u64 { return x.hash(); }";
    let type_mod = "pub struct K { pub id: i32 }";
    let err = Compiler::compile_package(&[
        ("root::t", trait_mod),
        ("root::ty", type_mod),
        (
            "root",
            "import root::t::{Hash, h};
import root::ty::K;
impl Hash for K { fn hash(&self) -> u64 { return 1; } }
pub fn main() -> i32 { let k = K { id: 1 }; return h(&k) as i32; }",
        ),
    ])
    .expect_err("impl in a third module should violate the orphan rule");
    assert!(err.contains("Orphan rule violation"), "Unexpected error: {err}");
    Compiler::compile_package(&[
        (
            "root::t",
            "import root::ty::K;
pub trait Hash { fn hash(&self) -> u64; }
pub fn h[T: Hash](x: &T) -> u64 { return x.hash(); }
impl Hash for K { fn hash(&self) -> u64 { return 1; } }",
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
    let two = "pub trait Name { fn hash(&self) -> u64; }
struct P {
    x: i32,
    impl Hash { fn hash(&self) -> u64 { return 1; } }
    impl Name { fn hash(&self) -> u64 { return 2; } }
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
    pub fn hash(&self) -> u64 { return 9; }
    impl Hash { fn hash(&self) -> u64 { return 1; } }
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
        "type D = trait { fn d(&self) -> i32; };\npub fn main() -> i32 { return 0; }",
        "write 'trait D ...'",
    );
    reject(
        "trait_equals_trait_literal",
        "trait D = trait { fn d(&self) -> i32; };\npub fn main() -> i32 { return 0; }",
        "write 'trait D { ... }'",
    );
    accept(
        "trait_alias",
        "trait D { fn d(&self) -> i32; }
struct P { x: i32, impl D { fn d(&self) -> i32 { return 4; } } }
fn g[T: D](x: &T) -> i32 { return x.d(); }
pub fn main() -> i32 { let p = P { x: 1 }; return g(&p); }",
    );
}

#[test]
fn test_overload_resolution_uses_subsumption() {
    // A strictly more specific constraint wins...
    assert_eq!(
        run_lli(
            "more_specific_wins",
            "pub trait A { fn a(&self) -> i32; }
pub trait B { fn b(&self) -> i32; }
struct P { x: i32, impl A { fn a(&self) -> i32 { return 1; } } impl B { fn b(&self) -> i32 { return 2; } } }
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
fn test_instantiation_trace_in_diagnostics() {
    reject(
        "stage2_error_in_generic_fn",
        "fn call_it[T](x: T) -> i32 { return x.missing(); }
pub fn main() -> i32 { return call_it[i32](1); }",
        "in instantiation of root::call_it[T = i32]",
    );
    reject(
        "stage2_error_in_type_fn_method",
        "fn W[T]() -> type {
    return opaque { v: T, pub fn new(v: T) -> Self { return Self { v: v }; } pub fn peek(&self) -> i32 { return self.v.missing(); } };
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
            "pub fn NonZero[Int: integer]() -> type { return Int in 1..=Int::MAX; }
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
    if let ?p = some_pct { if p != 0 { return 11; } } else { return 12; }
    let no_fd: ?PosixFd = null;
    if let ?f = no_fd { return 13; }
    return *r + (fd_val as i32) - 1;
}"
        ),
        Some(42)
    );
}

#[test]
fn test_trait_methods_require_trait_in_scope() {
    let trait_mod = "pub trait Hash { fn hash(&self) -> u64; }";
    let type_mod =
        "import root::t::Hash;\npub struct K { pub id: i32, impl Hash { fn hash(&self) -> u64 { return 7; } } }";
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
    let raw: array[u16; 8] = unsafe { @transmute(array[u16; 8], d) };
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
pub fn NonZero[Int: integer]() -> type { return Int in 1..=Int::MAX; }
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
        "fn at(a: array[i32; 4], i: u8) -> i32 { return a[i]; }\npub fn main() -> i32 { let arr: array[i32; 4] = .[1, 2, 3, 42]; return at(arr, 3); }",
        "Index must be 'usize', found 'u8'",
    );
}

#[test]
fn test_generic_bodies_are_checked_against_their_bounds() {
    // A type parameter promises its bounds and nothing more. A generic is checked, whether or not
    // anything uses it, with an archetype for each type parameter: a type with exactly what the
    // bounds say. Duck typing is opt-in, as `[T: unchecked]`, and then checked only where used.
    let prelude = "trait Shape { fn area(&self) -> i32; }
struct Square { side: i32, impl Shape { fn area(&self) -> i32 { return self.side * self.side; } } }
";
    for (name, generic) in [
        ("plain", "fn twice[T](a: T) -> T { return a; }"),
        ("integer", "fn add[T: integer](a: T, b: T) -> T { return a + b; }"),
        ("copy", "fn dup[T: copy](a: T) -> tuple { T, T } { return .{ a, a }; }"),
        ("trait", "fn area_of[T: Shape](a: &T) -> i32 { return a.area(); }"),
        ("traits_and_copy", "fn both[T: Shape + copy](a: T) -> i32 { let b = a; return a.area() + b.area(); }"),
        ("default", "fn make[T: default]() -> T { return @default(T); }"),
        ("value", "fn sized[n: usize]() -> usize { return n * 2; }"),
        ("generic_type", "struct Wrap[T] { v: T, pub fn get(&self) -> &T { return &self.v; } }"),
        ("generic_method_gated_on_the_type", "struct G[T] { v: T, pub fn with[U: copy](&self, u: U) -> T where T: integer { let w = u; return self.v + self.v; } }"),
        ("where_gated", "struct W[T] { v: T, pub fn twice(&self) -> T where T: integer { return self.v + self.v; } }"),
        ("generic_method", "struct S { x: i32, pub fn with[U: Shape](&self, u: &U) -> i32 { return u.area() + self.x; } }"),
        ("generic_impl", "struct Box2[T] { v: T }\nimpl[T: Shape] Shape for Box2[T] { fn area(&self) -> i32 { return self.v.area() * 2; } }"),
        ("duck_typed", "fn poke[T: unchecked](a: &T) -> i32 { return a.nonexistent(); }"),
    ] {
        let src = format!("{prelude}{generic}\npub fn main() -> i32 {{ return 0; }}");
        Compiler::compile_source(&src).unwrap_or_else(|e| panic!("[{name}] {e}"));
    }
    for (name, generic, what) in [
        ("field", "fn bad_field[T](a: T) -> i32 { return a.nonexistent; }", "has no field 'nonexistent'"),
        ("method", "fn bad_method[T](a: &T) -> i32 { return a.area(); }", "has no method 'area'"),
        ("copy", "fn dup_any[T](a: T) -> tuple { T, T } { return .{ a, a }; }", "moved"),
        ("past_the_trait", "fn bad_shape[T: Shape](a: &T) -> i32 { return a.perimeter(); }", "has no method 'perimeter'"),
        ("operator", "fn add[T](a: T, b: T) -> T { return a + b; }", "T"),
        ("generic_type", "struct Bad[T] { v: T, pub fn get(&self) -> i32 { return self.v.len(); } }", "has no method 'len'"),
        ("past_a_number", "fn bad_number[T: integer](a: T) -> i32 { return a.len(); }", "has no method 'len'"),
        // Members nothing checked until they were called: a method a `where` clause gates, a
        // generic method, an `impl` block (generic or not), and one inside a generic type.
        ("generic_method_gated_on_the_type", "struct G[T] { v: T, pub fn with[U](&self, u: U) -> i32 where T: integer { return self.v.len(); } }", "Method 'G::with'"),
        ("where_gated", "struct W[T] { v: T, pub fn total(&self) -> i32 where T: integer { return self.v.len(); } }", "Method 'W::total'"),
        ("generic_method", "struct S { x: i32, pub fn with[U](&self, u: U) -> i32 { return u.area(); } }", "Method 'S::with'"),
        ("generic_impl", "struct Box2[T] { v: T }\nimpl[T] Shape for Box2[T] { fn area(&self) -> i32 { return self.v.area(); } }", "has no method 'area'"),
        ("plain_impl", "struct Q { x: i32 }\nimpl Shape for Q { fn area(&self) -> i32 { return self.y; } }", "has no field 'y'"),
        // An impl for a type declared elsewhere is checked as a block of its own.
        ("impl_for_a_builtin", "impl Shape for i64 { fn area(&self) -> i32 { return self.y; } }", "'impl Shape for i64' does not compile"),
        // A borrow error in a method no one calls: of a generic type, a plain one, and an impl.
        ("moved_twice", "struct Mv[T] { s: String, v: T, fn take(self) -> i32 { let a = self.s; let b = self.s; return 0; } }", "moved"),
        ("moved_twice_plain", "struct Mp { s: String, fn take(self) -> i32 { let a = self.s; let b = self.s; return 0; } }", "moved"),
        ("moved_twice_in_impl", "impl Shape for u16 { fn area(&self) -> i32 { let s = String::from(\"a\"); let a = s; let b = s; return 0; } }", "moved"),
        ("impl_in_a_generic_type", "struct In[T] { v: T, impl Shape { fn area(&self) -> i32 { return self.v.area(); } } }", "'impl Shape' for 'In'"),
        // Each overload is checked as written, not the one its name would pick for an archetype.
        ("overload", "fn pick[T: integer](x: T) -> i32 { return x.len(); }\nfn pick[T: signed](x: T) -> i32 { return 1; }", "has no method 'len'"),
        ("not_send", "fn bad_send[T](x: T) -> i32 { let h = spawn(move fn() -> i32 { let y = x; return 1; }); return h.join(); }", "send"),
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
fn Nest[N: i32]() -> type {
    if N == 0 { return i32; }
    return tuple { i32, Nest[N - 1] };
}
fn Wider[A, B]() -> type {
    let mut t: type = A;
    if @size_of(B) > @size_of(A) { t = B; }
    return array[t; 2];
}
fn Pair[A]() -> type { return tuple { A, u8 }; }
fn Chain[n: i32]() -> type {
    let mut t: type = u8;
    let mut i: i32 = 0;
    while i < n {
        t = Pair[t];
        i += 1;
    }
    return t;
}
pub fn main() -> i32 {
    let a: Nest[2] = .{ 1, .{ 2, 3 } };
    let w: Wider[u8, i64] = .[30, 2];
    let c: Chain[2] = .{ .{ 1, 2 }, 3 };
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
            "fn Forever[N: i32]() -> type {{ {body} }}
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
fn S() -> type { return @Struct(&.[FieldSpec { name: "x", ty: i32 }]); }
fn T() -> type { return @Tuple(&.[i32, u8]); }
pub fn main() -> i32 {
    let a: struct { x: i32 } = struct { x: i32 } { x: 40 };
    let b: S() = a;
    let c: tuple { i32, u8 } = .{ 1, 1 };
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
        "fn S[T]() -> type { return struct { x: T }; }
pub fn main() -> i32 { let a: S[i32] = S[i32] { x: 1 }; let b: struct { x: i32 } = a; return 0; }",
    ];
    for src in distinct {
        let err = Compiler::compile_source(src).unwrap_err();
        assert!(err.contains("Type mismatch"), "{src}\n{err}");
    }
    let same = "alias P = tuple { i32, i32 };
fn S[T]() -> type { return @Struct(&.[FieldSpec { name: \"x\", ty: T }]); }
pub fn main() -> i32 {
    let a: P = .{ 40, 1 };
    let b: tuple { i32, i32 } = a;
    let c: S[i32] = struct { x: i32 } { x: 1 };
    return b.0 + b.1 + c.x;
}";
    assert_eq!(run_lli("structural_identity", same), Some(42));
    for (src, want) in [
        (
            "pub fn main() -> i32 { let a = struct { x: i32, fn get(&self) -> i32 { return self.x; } } { x: 1 }; return 0; }",
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
    let p: Pair = .{ 1, 2 };
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
    pub fn get(&self) -> i32 { return self.v; }
}
pub struct Lock {
    n: i32,
    fn secret(&self) -> i32 { return self.n; }
    pub fn lock(&self) -> Guard { return Guard::create(self.n); }
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
fn test_lifecycle_hooks_are_in_block_impls() {
    // Lifecycle hooks are built-in traits implemented in the type's own block (`impl drop`,
    // `impl clone`, `impl default`, `impl format`), conditional ones with `where` on the impl;
    // their names are not keywords, and the former hook form is an error naming the new one.
    let src = "opaque Counter {
    n: i32,
    impl default { fn default() -> Self { return Self { n: 40 }; } }
    impl clone { fn clone(&self) -> Self { return Self { n: self.n + 1 }; } }
    impl drop { fn drop(&mut self) { self.n = 0; } }
    pub fn get(&self) -> i32 { return self.n; }
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
        ("drop(&mut self) { }", "Declare the 'drop' lifecycle hook as 'impl drop"),
        ("impl clone { fn copy(&self) -> Self { return Self { n: 0 }; } }", "must contain exactly 'fn clone(...)'"),
        ("impl drop { fn drop() { } }", "'fn drop' takes 1 parameter(s)"),
    ] {
        let err = Compiler::compile_source(&format!(
            "opaque O {{ n: i32, {body} }}\npub fn main() -> i32 {{ return 0; }}"
        ))
        .unwrap_err();
        assert!(err.contains(want), "{body}\nexpected '{want}', got: {err}");
    }
    let err = Compiler::compile_source(
        "struct S { n: i32, impl drop { fn drop(&mut self) { } } }\npub fn main() -> i32 { return 0; }",
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
    let src = "fn Chain[n: i32]() -> type {
    let mut t: type = u8;
    let mut i: i32 = 0;
    while i < n { t = tuple { t, u8 }; i += 1; }
    return t;
}
fn Ptr() -> type { let p: type = *mut u8; return p; }
fn Kind() -> type { let k: type = enum { A, B }; return k; }
pub fn main() -> i32 {
    let c: Chain[1] = .{ 40, 2 };
    let mut x: u8 = 0;
    let p: Ptr() = &mut x as *mut u8;
    let k: Kind() = .B;
    let a: i32 = 6;
    return (c.0 + c.1) as i32 + unsafe { *p } as i32 + (a * 0);
}";
    assert_eq!(run_lli("type_literal_values", src), Some(42));
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
        fn drop(&mut self) {
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
    pub fn consume(self) -> i32 { return self.id; }
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
            "opaque O { x: i32, pub impl drop { fn drop(&mut self) {} } }\npub fn main() -> i32 { return 0; }",
            "'impl drop' takes no visibility modifier",
        ),
        (
            "opaque O { x: i32, impl drop { pub fn drop(&mut self) {} } }\npub fn main() -> i32 { return 0; }",
            "'fn drop' inside 'impl drop' takes no visibility modifier",
        ),
        (
            "type D = distinct i32 { impl drop { fn drop(&mut self) {} } }\npub fn main() -> i32 { return 0; }",
            "Lifecycle hook 'drop' is not permitted inside 'extern opaque' or 'distinct' type blocks",
        ),
        (
            "struct S { x: i32 }\nimpl drop for S { fn drop(&mut self) {} }\npub fn main() -> i32 { return 0; }",
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
fn test_method_comptime_arguments_defaults_and_placeholders() {
    // Methods take bracketed comptime arguments too (`x.m[T](y)`, `Type::m[T](y)`), while
    // `s.fs[i](x)` still calls an element of a field. A comptime parameter may have a default,
    // which is used when the argument is neither given nor inferred; `_` asks for inference.
    // Defaults are filled before memoization, so `Table[i32]` and `Table[i32, 4]` are one type.
    let src = "fn add1(x: i32) -> i32 { return x + 1; }
struct Fns { fs: array[fn(i32) -> i32; 1] }
struct Num {
    v: i32,
    pub fn conv[T: integer](&self) -> T { return self.v as T; }
    pub fn scaled[T: integer, k: i32 = 2](&self, x: T) -> i32 { return self.v * k + x as i32; }
    pub fn make[k: i32 = 5]() -> Num { return Num { v: k }; }
}
fn Table[T, n: usize = 4]() -> type { return array[T; n]; }
fn widen[D: integer, S: integer = u8](x: S) -> D { return x as D; }
fn pick[T, n: i32 = 7](x: T) -> i32 { return n; }
pub fn main() -> i32 {
    let f = Fns { fs: .[add1] };
    let n = Num { v: 3 };
    let a: i64 = n.conv[i64]();
    let t: Table[i32] = .[1, 2, 3, 4];
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
        "fn F[T = i32, U]() -> type { return T; }\npub fn main() -> i32 { return 0; }",
        "parameters after a defaulted one must also have defaults",
    );
    reject(
        "impl_default",
        "trait Tr { fn f(&self) -> i32; }\nfn W[T]() -> type { return struct { x: T }; }\nimpl[T = i32] Tr for W[T] { fn f(&self) -> i32 { return 1; } }\npub fn main() -> i32 { return 0; }",
        "cannot have a default",
    );
}

#[test]
fn test_tuple_concat_and_split() {
    assert_runs(
        "concat",
        "pub fn main() -> i32 {
    let a: tuple { i32, i32 } = .{ 1, 2 };
    let b: tuple { i32 } = .{ 3 };
    let c = tuple_concat(a, b);
    return c.0 * 100 + c.1 * 10 + c.2;
}",
        123,
    );
    let linear = "let a: tuple { Tx, i32 } = .{ Tx::new(1), 2 };
    let b: tuple { Tx } = .{ Tx::new(3) };
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
    let t: tuple {{ i32, Tx, i32 }} = .{{ 1, Tx::new(2), 3 }};
    let parts = tuple_split[1, tuple {{ i32, Tx, i32 }}](t);
    return parts.0.0 * 100 + parts.1.0.commit() * 10 + parts.1.1;
}}"
        ),
        123,
    );
}

#[test]
fn test_type_function_returning_its_argument_labels() {
    // The instance label of `S` is `Id[S]`, whose argument is `S` again.
    assert_rejected(
        "identity",
        "pub struct S { a: i32 }
fn Id[T]() -> type { return T; }
fn bad[T](x: &mut T) { let a = &mut *x; let b = &mut *x; *a = *b; }
pub fn main() -> i32 { let mut s = S { a: 1 }; bad[Id[S]](&mut s); return 0; }",
        "Borrow check error",
    );
}

#[test]
fn test_type_labels_name_the_real_type() {
    // A type function returning an existing type does not rename it in diagnostics, and a tuple
    // keeps its structural name.
    let err = Compiler::compile_source(
        "pub struct S { a: i32 }
fn Id[T]() -> type { return T; }
fn Pair[T]() -> type { return tuple { T, T }; }
fn bad[T, U](x: &mut T, y: U) { let a = &mut *x; let b = &mut *x; *a = *b; }
pub fn main() -> i32 { let mut s = S { a: 1 }; let p: Pair[i32] = .{ 1, 2 }; bad[Id[S], Pair[i32]](&mut s, p); return 0; }",
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
fn test_borrow_errors_name_source_places() {
    let types = "pub struct P { a: i32, b: i32 }\n";
    for (body, message) in [
        ("let mut x: i32 = 1; let a = &mut x; let b = &x; *a = 2; return *b;", "cannot borrow 'x' as immutable because 'x' is already borrowed as mutable"),
        ("let mut x: i32 = 1; let a = &x; x = 2; return *a;", "cannot mutate or move 'x' because it is currently borrowed"),
        ("let mut x: i32 = 1; let a = &mut x; let y = x; *a = 2; return y;", "cannot read 'x' because it is mutably borrowed"),
        ("let mut p = P { a: 1, b: 2 }; let a = &mut p.a; let b = &mut p.a; *a = 1; *b = 2; return 0;", "cannot borrow 'p.a' as mutable because 'p.a' is already borrowed as mutable"),
        ("let mut p = P { a: 1, b: 2 }; let a = &p; p.b = 3; return a.a;", "cannot mutate or move 'p.b' because it is currently borrowed via 'p'"),
        ("let mut t: tuple { i32, i32 } = .{ 1, 2 }; let a = &mut t.0; let b = &mut t; *a = 1; b.1 = 2; return 0;", "cannot borrow 't' as mutable because 't.0' is already borrowed as mutable"),
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
    let tx = "pub opaque(linear) Tx {\n    id: i32,\n    pub fn new(i: i32) -> Self { return Self { id: i }; }\n    pub fn commit(self) -> i32 { return self.id; }\n}\n";
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
fn test_static_trait_methods() {
    let shapes = "pub trait Shape {
    fn sides() -> i32;
    fn make(n: i32) -> Self;
    fn area(&self) -> i32;
}
pub struct Square { w: i32 }
impl Shape for Square {
    fn sides() -> i32 { return 4; }
    fn make(n: i32) -> Self { return Square { w: n }; }
    fn area(&self) -> i32 { return self.w * self.w; }
}
pub struct Tri { b: i32 }
impl Shape for Tri {
    fn sides() -> i32 { return 3; }
    fn make(n: i32) -> Self { return Tri { b: n }; }
    fn area(&self) -> i32 { return self.b; }
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
    fn start(&self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
        unsafe { STARTED = STARTED + 1; }
        return Threads { }.start(entry, arg);
    }
    fn wait(&self, id: u64) { Threads { }.wait(id); }
}
pub opaque(unsafe sync) Pool {
    cell started: i32,
    pub fn new() -> Self { return Self { started: 0 }; }
    pub fn count(&self) -> i32 { return unsafe { *(&raw mut self.started) }; }
    pub fn note(&self) { unsafe { let p = &raw mut self.started; *p = *p + 1; } }
}
impl Executor for Pool {
    fn start(&self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 { self.note(); return null; }
    fn wait(&self, id: u64) { }
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
fn test_descriptors() {
    let prelude = "extern fn pipe(fds: *mut array[i32; 2]) -> i32;
fn byte_of(s: &str) -> i32 { return s[0] as i32; }
fn read_one(fd: &Fd) -> i32 {
    let mut b: array[u8; 1] = .[0];
    let n = fd.read(&mut b) catch |e| match e { .Cancelled => return 100, .TimedOut => return 101, .Failed => return 102 };
    if n == 0 { return 0; }
    return b[0] as i32;
}
fn send_text(fd: &Fd, s: &str) -> i32 { let _a = fd.write_all(s) catch |e| return 1; return 0; }
fn count_all(fd: &Fd) -> i32 {
    let mut total: i32 = 0;
    let mut buf: array[u8; 100] = @default(array[u8; 100]);
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
        ("borrowed_descriptor", "let mut ends: array[i32; 2] = .[0, 0]; if unsafe { pipe(&raw mut ends) } != 0 { return 90; } let r = Fd::from_raw(ends[0]); let w = Fd::from_raw(ends[1]); let t = async(Fibers { }) read_one(&r); let u = async(Fibers { }) send_text(&w, \"C\"); let _a = u.await(); return t.await();", 67),
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
    let prelude = "fn ok(s: &str) -> i32 { if let ?a = parse_ipv4(s) { return (a & 255) as i32 + ((a >> 24) & 255) as i32; } return 0; }\n";
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
fn test_folding_leaves_run_time_values_alone() {
    let prelude = "const K: i32 = 9;
static mut G: i32 = 1;
static mut C: i32 = 0;
fn read_g() -> i32 { return unsafe { G }; }
fn counted() -> i32 { unsafe { C = C + 1; } return 9; }
fn pure(x: i32) -> i32 { return x * 3; }
fn Sized[T]() -> i32 { return @size_of(T) as i32; }
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
fn test_comptime_values_at_run_time() {
    // What `comptime for` binds is usable at run time: in a format string, and, for a list such
    // as a field path, as a static slice.
    let decls = "struct In { a: i32, b: i32 }\nstruct Out { x: i32, inner: In }
fn depth(path: &slice[&str]) -> usize { return path.len; }
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
    let decls = "trait Shape { fn area(&self) -> i32; fn twice(&self) -> i32 { return self.area() * 2; } }
trait Greets { fn hello(&self) -> i32 { return 1; } }
struct Sq { s: i32, pub fn name(&self) -> i32 { return 5; } }
fn generic[T: Shape](x: &T) -> i32 { return x.twice(); }
fn through_object(s: &Shape) -> i32 { return s.twice(); }
";
    for (name, body, value) in [
        ("default", "impl Shape for Sq { fn area(&self) -> i32 { return self.s * self.s; } }\npub fn main() -> i32 { let q = Sq { s: 3 }; return q.twice(); }", 18),
        ("overridden", "impl Shape for Sq { fn area(&self) -> i32 { return 1; } fn twice(&self) -> i32 { return 7; } }\npub fn main() -> i32 { let q = Sq { s: 3 }; return q.twice(); }", 7),
        ("generic_and_object", "impl Shape for Sq { fn area(&self) -> i32 { return 4; } }\npub fn main() -> i32 { let q = Sq { s: 3 }; return generic(&q) + through_object(&q); }", 16),
        ("every_method_defaulted", "opaque B { impl Greets { } pub fn new() -> Self { return Self { }; } }\nfn greet[T: Greets](x: &T) -> i32 { return x.hello(); }\npub fn main() -> i32 { let b = B::new(); return greet(&b) + b.hello(); }", 2),
    ] {
        assert_runs(name, &format!("{decls}{body}"), value);
    }
    for (name, src, message) in [
        ("not_in_a_structural_trait", "trait(structural) Named { fn name(&self) -> i32; fn tag(&self) -> i32 { return 1; } }\npub fn main() -> i32 { return 0; }", "a structural trait is met by the type's own methods"),
        ("required_still_required", "impl Shape for Sq { }\npub fn main() -> i32 { return 0; }", "is missing trait method 'area'"),
        // A default is checked where it is written, against what the trait promises.
        ("default_beyond_the_trait", "trait Bad { fn a(&self) -> i32; fn b(&self) -> i32 { return self.c(); } }\npub fn main() -> i32 { return 0; }", "Default method 'Bad::b'"),
    ] {
        assert_rejected(name, &format!("{decls}{src}"), message);
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
fn test_comptime_fields_and_associated_items() {
    // `const Name: T = value;` in an opaque is a compile-time field: a constant or a type of the type's
    // own, public, and known to its fields and methods (as `Self::Name` or `Name`). A trait asks
    // for one with `const Name: bound;`, and each implementation gives it.
    let k = "trait K { const Item: copy; fn get(&self) -> Self::Item; }\nfn first[T: K](x: &T) -> T::Item { return x.get(); }\n";
    for (name, src, value) in [
        ("a_value", "opaque P { pub const N: usize = 4; pub fn n() -> usize { return Self::N + N; } }\npub fn main() -> i32 { return (P::N + P::n()) as i32; }", 12),
        ("a_type", "opaque P { pub const H: type = i32; v: Self::H, pub fn get(&self) -> H { return self.v; } pub fn new() -> Self { return Self { v: 3 }; } }\npub fn main() -> i32 { let p = P::new(); let x: P::H = p.get(); return x; }", 3),
        ("from_parameters", "opaque P[T] { const H: type = ?T; v: Self::H, pub fn new() -> Self { return Self { v: null }; } pub fn has(&self) -> bool { return self.v != null; } }\npub fn main() -> i32 { let p = P[i32]::new(); if p.has() { return 1; } return 2; }", 2),
        ("module_impl", "struct A { v: i64 }\nimpl K for A { const Item: copy = i64; fn get(&self) -> i64 { return self.v; } }\npub fn main() -> i32 { let a = A { v: 5 }; return first(&a) as i32; }", 5),
        ("inline_impl", "opaque B { v: u8, impl K { const Item: type = u8; fn get(&self) -> u8 { return self.v; } } pub fn new() -> Self { return Self { v: 6 }; } }\npub fn main() -> i32 { let b = B::new(); let x: B::Item = first(&b); return x as i32; }", 6),
        // `const` in a type is the same field, private unless `pub`.
        ("a_const", "opaque P { const N: usize = 2; const M: usize = 3; pub fn n() -> usize { return N * M; } }\npub fn main() -> i32 { return P::n() as i32; }", 6),
        ("blanket_impl", "trait Base { fn n(&self) -> i32; }\nstruct C { }\nimpl Base for C { fn n(&self) -> i32 { return 7; } }\nimpl[A: Base] K for A { const Item: type = i32; fn get(&self) -> i32 { return self.n(); } }\npub fn main() -> i32 { let c = C { }; return first(&c); }", 7),
    ] {
        assert_runs(name, &format!("{k}{src}"), value);
    }
    for (name, src, message) in [
        ("item_missing", "struct A { }\nimpl K for A { fn get(&self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { }; return first(&a); }", "gives no 'const Item', which trait 'K' asks of each implementation"),
        ("item_misses_its_bound", "struct A { }\nimpl K for A { const Item: type = String; fn get(&self) -> String { return String::new(); } }\npub fn main() -> i32 { let a = A { }; let s = first(&a); return 0; }", "'A::Item' does not meet its bound in trait 'K'"),
        ("not_an_item", "struct A { }\nimpl K for A { const Item: type = i32; const Other: type = i32; fn get(&self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { }; return first(&a); }", "'const Other' in 'impl K for A' in module 'root' is not an associated item of trait 'K'"),
        // Without a bound that gives it, a generic has no `T::Item`.
        ("not_promised", "fn f[S](x: S::Item) -> i32 { return 0; }\npub fn main() -> i32 { return 0; }", "Type 'S' has no associated type 'Item'"),
        ("valued_in_a_trait", "trait L { const Item: type = i32; }\npub fn main() -> i32 { return 0; }", "each implementation gives its value"),
        // Private unless `pub`, and a trait's item must be public.
        ("private_outside", "opaque P { const N: usize = 1; }\npub fn main() -> i32 { return P::N as i32; }", "private"),
        ("private_for_a_trait", "opaque B { const Item: type = i32; impl K { fn get(&self) -> i32 { return 1; } } pub fn new() -> Self { return Self { }; } }\npub fn main() -> i32 { let b = B::new(); return first(&b); }", "but privately; write 'pub const Item'"),
        ("private_through_a_bound", "fn has[T: K](x: &T) -> i32 { return 1; }\nopaque B { const Item: type = i32; impl K { fn get(&self) -> i32 { return 1; } } pub fn new() -> Self { return Self { }; } }\npub fn main() -> i32 { let b = B::new(); return has(&b); }", "but privately; write 'pub const Item'"),
        // A bound written on the value is checked where it is written, used or not.
        ("bound_where_written", "struct A { }\nimpl K for A { const Item: copy = String; fn get(&self) -> String { return String::new(); } }\npub fn main() -> i32 { return 0; }", "'const Item: ... = String' in 'impl K for A' in module 'root' does not meet its bound: Type 'String' does not satisfy comptime constraint 'copy'"),
        // Brackets are for parameters; a field is a constant.
        ("bracketed", "opaque P { [N: usize = 1] }\npub fn main() -> i32 { return 0; }", "write 'const Name: T = value;'"),
        ("bracketed_in_a_trait", "trait L { [Item: copy] }\npub fn main() -> i32 { return 0; }", "'const Name: bound;'"),
        ("not_in_a_struct", "struct S { impl K { const Item: type = i32; fn get(&self) -> i32 { return 1; } } }\npub fn main() -> i32 { return 0; }", "goes in an 'opaque' body or a module-level 'impl'"),
    ] {
        assert_rejected(name, &format!("{k}{src}"), message);
    }
}

#[test]
fn test_blanket_impls() {
    // An impl for every type meeting a bound (`impl[A: K] L for A`), as std's for allocators.
    let decls = "trait K { fn k(&self) -> i32; }\ntrait L { fn l(&self) -> i32; }\nimpl[A: K] L for A { fn l(&self) -> i32 { return self.k() + 1; } }\nstruct S { }\nimpl K for S { fn k(&self) -> i32 { return 1; } }\n";
    assert_runs("direct", &format!("{decls}pub fn main() -> i32 {{ let s = S {{ }}; return s.l(); }}"), 2);
    assert_runs("through_a_bound", &format!("{decls}fn use_l[T: L](x: &T) -> i32 {{ return x.l(); }}\npub fn main() -> i32 {{ let s = S {{ }}; return use_l(&s); }}"), 2);
    // One whose bound is itself does not loop: the type has no impl.
    assert_rejected(
        "its_own_bound",
        "trait L { fn l(&self) -> i32; }\nimpl[A: L] L for A { fn l(&self) -> i32 { return 1; } }\nstruct S { }\npub fn main() -> i32 { let s = S { }; return s.l(); }",
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
    pub fn sum(&self) -> i32 { let mut s = self.v; if let ?ref n = self.next { s = s + n.get().sum(); } return s; }
    pub fn bump(&mut self) { self.v = self.v + 1; if let ?ref mut n = self.next { n.get_mut().bump(); } }
}
fn walk(h: &L) -> i32 { let mut n = 0; let mut cur = h; while let ?ref next = cur.next { n = n + 1; cur = next.get(); } return n; }
pub fn main() -> i32 {
    let mut h = L { v: 1, next: null };
    let mut i = 2;
    while i <= 5 { h = L { v: i, next: Box[L]::new(h) }; i = i + 1; }
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
            "fn Tree[V]() -> type { return struct { v: V, kids: Vec[Tree[V]],
    pub fn count(&self) -> i32 { let mut n = 1; for ref k in self.kids.as_slice() { n = n + k.count(); } return n; } }; }
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
    pub fn total(&self) -> i32 { let mut s = self.v; for ref b in self.bs.as_slice() { s = s + b.total(); } return s; } }
struct B { w: i32, a: ?Box[A],
    pub fn total(&self) -> i32 { let mut s = self.w; if let ?ref a = self.a { s = s + a.get().total(); } return s; } }
pub fn main() -> i32 {
    let inner = A { v: 3, bs: Vec[B]::new() };
    let mut a = A { v: 1, bs: Vec[B]::new() };
    a.bs.push(B { w: 2, a: Box[A]::new(inner) });
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
        J::Opt(ref o) => { if let ?ref b = *o { return depth(b.get()) + 1; } return 1; }
        _ => { return 0; }
    }
}
pub fn main() -> i32 {
    let mut a = Vec[J]::new();
    a.push(J::Str(String::from(\"s\")));
    a.push(J::Opt(Box[J]::new(J::Str(String::from(\"t\")))));
    let mut o = HashMap[String, J]::new();
    let _old = o.insert(String::from(\"k\"), J::Arr(a));
    let mut b = Vec[J]::new();
    b.push(J::Obj(o));
    b.push(J::Num(1));
    b.push(J::Null);
    let mut c = Vec[J]::new();
    c.push(J::Str(String::from(\"u\")));
    c.push(J::Opt(Box[J]::new(J::Null)));
    b.push(J::Arr(c));
    return depth(&J::Arr(b));
}",
            3,
        ),
        (
            "fields_dropped",
            "static mut DROPS: i32 = 0;
opaque D { v: i32,
    pub fn new(v: i32) -> D { return D { v: v }; }
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + 1; } } } }
struct L { d: D, next: ?Box[L] }
fn make() {
    let mut h = L { d: D::new(0), next: null };
    h = L { d: D::new(1), next: Box[L]::new(h) };
    h = L { d: D::new(2), next: Box[L]::new(h) };
}
pub fn main() -> i32 { make(); return unsafe { DROPS }; }",
            3,
        ),
        // A method of a finished type that names a type still being built must wait for it.
        (
            "method_names_unfinished_type",
            "struct Inner { x: i32, pub fn make(&self) -> i32 { let o = Outer { i: Inner { x: 2 }, v: Vec[i32]::new(), n: 40 }; return o.n + o.i.x; } }
struct Outer { i: Inner, v: Vec[i32], n: i32 }
pub fn main() -> i32 { let i = Inner { x: 0 }; return i.make(); }",
            42,
        ),
        // Compile-time code run while a type is being built still has its callees.
        (
            "comptime_call_inside_a_type",
            "fn size() -> usize { let mut v = Vec[i32]::new(); v.push(1); v.push(2); v.push(3); return v.len(); }
struct S { a: array[u8; size()], next: ?Box[S] }
pub fn main() -> i32 { return @size_of(array[u8; size()]) as i32; }",
            3,
        ),
        (
            "comptime_function_value_inside_a_type",
            "fn one() -> usize { return 1; }
fn size() -> usize { let f = one; return f() + 2; }
struct S { a: array[u8; size()], next: ?Box[S] }
pub fn main() -> i32 { return @size_of(array[u8; size()]) as i32; }",
            3,
        ),
        // `B` names `A` without a type function, and it is unfinished until `A` is: `Which[B]`
        // has to wait to learn that `B` is linear, which picks its hook.
        (
            "cycle_finishes_together",
            "pub opaque(linear) Tx { id: i32, pub fn new(i: i32) -> Self { return Self { id: i }; } pub fn commit(self) -> i32 { return self.id; } }
fn Which[T: ?linear]() -> type { return opaque(copy) { p: *const T,
    pub fn make() -> Self { return Self { p: 0 as *const T }; }
    impl default where T: linear { fn default() -> Self { return Self { p: 8 as *const T }; } } }; }
struct A { w: Which[B], t: Tx }
struct B { a: A }
pub fn main() -> i32 { let w = @default(Which[B]); return 1; }",
            1,
        ),
        (
            "trait_object_argument",
            "trait T { fn f(&self) -> i32; }
struct S { v: i32, impl T { fn f(&self) -> i32 { return self.v; } } }
pub fn main() -> i32 { let s = S { v: 7 }; let mut x = Vec[&T]::new(); x.push(&s); let r = x.get(0) orelse unreachable; return r.f(); }",
            7,
        ),
    ] {
        assert_runs(name, src, value);
    }
    for (name, src, message) in [
        ("self", "struct L { v: i32, next: L }", "holds itself by value"),
        ("optional", "struct L { next: ?L }", "holds itself by value"),
        ("array", "struct L { next: array[L; 2] }", "holds itself by value"),
        ("nested", "struct L { next: struct { a: i32, b: L } }", "holds itself by value"),
        ("mutual", "struct A { b: B }\nstruct B { a: A }", "holds itself by value"),
        ("union", "union U { A, B(U) }", "holds itself by value"),
        ("generic", "fn W[T]() -> type { return struct { x: T }; }\nstruct L { w: W[L] }", "holds itself by value"),
        ("alias", "alias A = *const A;", "defined in terms of itself"),
        ("distinct", "type D = distinct *const D;", "defined in terms of itself"),
        ("packed", "packed struct L { x: u8, y: L }", "still being defined"),
        ("size_of", "struct L { b: array[u8; @size_of(L)] }", "still being defined"),
        ("size_of_in_argument", "fn I[T]() -> type { return struct { b: array[u8; @size_of(T)] }; }\nstruct L { x: i32, w: I[L] }", "still being defined"),
        ("copy_holding_its_own_vec", "opaque(copy) Q { kids: Vec[Q] }", "non-copy type"),
        ("format_needs_a_hook", "struct L { v: i32, next: ?&L }\nfn show(l: &L) { println(f\"{l}\"); }", "cannot be formatted"),
        ("ever_larger", "fn G[T]() -> type { return struct { x: T, n: *const G[*const T] }; }\nstruct S { g: G[i32] }", "nests more than"),
    ] {
        assert_rejected(name, &format!("{src}\npub fn main() -> i32 {{ return 0; }}"), message);
    }
}

#[test]
fn test_generic_type_declarations() {
    // `struct Pair[T] { ... }` is the type function `fn Pair[T]() -> type { return struct { ... }; }`.
    let prelude = "struct Pair[T] { first: T, second: T,
    pub fn swapped(&self) -> Self where T: copy { return Self { first: self.second, second: self.first }; } }
union Maybe[T] { None, Some(T) }
overlay Bits[T] { value: T, raw: u64 }
packed struct Flags[N: usize] { on: u1, rest: u7 }
static mut DROPS: i32 = 0;
opaque Guard[T, N: i32 = 3] { value: T,
    pub fn new(value: T) -> Self { return Self { value: value }; }
    pub fn weight(&self) -> i32 { return N; }
    impl drop { fn drop(&mut self) { unsafe { DROPS = DROPS + N; } } } }
struct Tree[V] { value: V, kids: Vec[Tree[V]] }
trait Size { fn size(&self) -> i32; }
impl[T] Size for Pair[T] { fn size(&self) -> i32 { return 2; } }
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
        "trait Width { fn size(&self) -> i32; }\nfn q[N: i32]() -> i32 { return N; }\npub fn main() -> i32 { return q[4](); }",
        4,
    );
    // The long form is the same type: either spelling names it.
    assert_runs(
        "long_form",
        "fn Wrap[T]() -> type { return struct { v: T }; }
struct Same[T] { v: T }
fn get(w: Wrap[i32]) -> i32 { return w.v; }
pub fn main() -> i32 { return get(Wrap[i32] { v: 6 }) + @size_of(Same[i64]) as i32; }",
        14,
    );
    for (name, src, message) in [
        ("export", "export struct Pair[T] { a: T }\npub fn main() -> i32 { return 0; }", "cannot be exported"),
        ("constraint", "struct Num[T: integer] { v: T }\npub fn main() -> i32 { let n = Num[f64] { v: 1.0 }; return 0; }", "integer"),
        ("where_clause", "struct P[T] { a: T, pub fn get(&self) -> T where T: copy { return self.a; } }\npub fn main() -> i32 { let p = P[String] { a: String::from(\"x\") }; let s = p.get(); return 0; }", "get"),
    ] {
        assert_rejected(name, src, message);
    }
}

#[test]
fn test_generic_paths() {
    let prelude = "union Maybe[T] { None, Some(T) }
struct Pair[T] { first: T, second: T, pub fn sum(&self) -> T where T: integer { return self.first + self.second; } }
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
    pub fn pair[A, B](a: A, b: B) -> tuple { A, B } { return .{ a, b }; }
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
        "struct B[T] { v: T, pub fn make(v: T) -> B { return B { v: v }; } pub fn other(&self) -> B[u8] { return B[u8] { v: 1 }; } }
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
        "struct N[T] { v: T, pub fn twice(&self) -> N[N[T]] where T: copy { return N[N[T]] { v: Self { v: self.v } }; } }
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
    let s = Shape::Pair(.{ 2, 3 });
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
        ("method_with_bound", "struct W[T: struct] { v: T, pub fn count(&self) -> usize { return @fields(T).len; } }\npub fn main() -> i32 { let w = W[P] { v: P { x: 1, y: 2 } }; return w.count() as i32; }", 2),
        // A function computing a type runs with real types, so it is not held to this.
        ("type_function", "fn First[T]() -> type { comptime for f in @fields(T) { return f.ty; } return void; }\npub fn main() -> i32 { let x: First[P] = 2; return x; }", 2),
    ] {
        assert_runs(name, &format!("{prelude}{body}"), value);
    }
    // Refused where written, whether or not anything uses it.
    for (name, body, what) in [
        ("fields_plain", "fn n[T]() -> usize { return @fields(T).len; }", "Generic 'root::n' uses '@fields(T)', but 'T' is not bounded to a kind of type with fields"),
        ("leaves_copy", "fn n[T: copy]() -> usize { comptime for p in @leaves(T) { } return 0; }", "uses '@leaves(T)', but 'T' is not bounded to a kind of type with fields"),
        ("variants_struct", "fn n[T: struct]() -> usize { return @variants(T).len; }", "uses '@variants(T)', but 'T' is not bounded to a kind of type with variants"),
        ("fields_enum", "fn n[T: enum]() -> usize { return @fields(T).len; }", "uses '@fields(T)', but 'T' is not bounded to a kind of type with fields"),
        ("method", "struct W[T] { v: T, pub fn count(&self) -> usize { return @fields(T).len; } }", "Method 'W::count' of generic type 'root::W' uses '@fields(T)'"),
        ("method_parameter", "struct W { v: i32, pub fn count[U](&self) -> usize { return @fields(U).len; } }", "uses '@fields(U)'"),
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
fn test_generic_aliases() {
    // `alias Grid[T] = Vec[Vec[T]];` names a type that exists: `Grid[i32]` is `Vec[Vec[i32]]`.
    let prelude = "alias Grid[T] = Vec[Vec[T]];
alias Maybe[T] = ?T;
alias Table[V, K = String] = HashMap[K, V];
alias Small[T: integer] = array[T; 2];
struct Tree[V] { value: V, kids: Grid[Tree[V]] }
fn rows(g: &Vec[Vec[i32]]) -> i32 { return g.len() as i32; }
fn first(m: ?i32) -> i32 { return m orelse 0; }
";
    for (name, body, value) in [
        ("same_type", "let mut g: Grid[i32] = Vec[Vec[i32]]::new(); g.push(Vec[i32]::new()); return rows(&g);", 1),
        ("optional", "let m: Maybe[i32] = 7; return first(m);", 7),
        ("default_parameter", "let mut t = Table[i32]::new(); let _o = t.insert(String::from(\"a\"), 3); return t.len() as i32;", 1),
        ("constrained", "let s: Small[u8] = .[1, 2]; return (s[0] + s[1]) as i32;", 3),
        ("recursive", "let t = Tree[i32] { value: 1, kids: Grid[Tree[i32]]::new() }; return t.value + t.kids.len() as i32;", 1),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    for (name, src, message) in [
        ("anonymous_struct", "alias P[T] = struct { a: T };\npub fn main() -> i32 { return 0; }", "declare 'struct P[...]'"),
        ("constraint", "alias Small[T: integer] = array[T; 2];\npub fn main() -> i32 { let s: Small[f64] = .{ 1.0, 2.0 }; return 0; }", "integer"),
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
            "static mut WIDE: bool = false;\nfn Pick[T]() -> type { if unsafe { WIDE } { return i64; } return T; }\npub fn main() -> i32 { let v: Pick[i32] = 1; return v; }",
            "mutable static",
        ),
        // Building a type inside it pauses the call; reading the static comes after.
        (
            "mutable_static_after_building_a_type",
            "static mut WIDE: bool = false;\nfn Pick[T]() -> type { let inner = Vec[T]; if unsafe { WIDE } { return i64; } return inner; }\npub fn main() -> i32 { let v: Pick[i32] = Vec[i32]::new(); return v.len() as i32; }",
            "mutable static",
        ),
        (
            "output",
            "fn Noisy[T]() -> type { println(\"hi\"); return T; }\npub fn main() -> i32 { let v: Noisy[i32] = 1; return v; }",
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
fn Pick[T]() -> type { if n() == 1 { return i64; } return T; }
pub fn main() -> i32 { return @size_of(Pick[i8]) as i32; }",
        8,
    );
    // A method reached only through a trait object's vtable is compiled for compile-time use too.
    assert_runs(
        "through_a_vtable",
        "trait Size { fn n(&self) -> i32; }
struct A[T] { v: T, impl Size { fn n(&self) -> i32 { return 6; } } }
fn ask(s: &Size) -> i32 { return s.n(); }
fn calc() -> i32 { let a = A[u16] { v: 1 }; return ask(&a); }
const N: i32 = calc();
pub fn main() -> i32 { return N; }",
        6,
    );
    // A function cannot need its own value to be compiled.
    assert_rejected(
        "needs_itself",
        "fn f() -> usize { let a: array[u8; f()] = @default(array[u8; 1]); return 1; }\npub fn main() -> i32 { return f() as i32; }",
        "while it is itself being compiled",
    );
    // A constant static and the heap are fine.
    assert_runs(
        "constant_inputs",
        "static WIDE: bool = true;
fn count_up(n: i32) -> usize { let mut v = Vec[i32]::new(); for i in 0..n { v.push(i); } return v.len(); }
fn Pick[T]() -> type { if WIDE && count_up(3) == 3 { return i64; } return T; }
pub fn main() -> i32 { return @size_of(Pick[i8]) as i32; }",
        8,
    );
}

#[test]
fn test_unsafe_traits() {
    // An `unsafe trait` makes promises the compiler cannot check, so its implementations say
    // `unsafe impl`, where their author takes them on.
    let prelude = "unsafe trait Trusted { fn get(&self) -> i32; }
trait Plain { fn get(&self) -> i32; }
";
    for (name, body, value) in [
        ("module", "struct A { v: i32 }\nunsafe impl Trusted for A { fn get(&self) -> i32 { return self.v; } }\nfn use_it(t: &Trusted) -> i32 { return t.get(); }\npub fn main() -> i32 { let a = A { v: 4 }; return use_it(&a); }", 4),
        ("in_the_body", "struct A { v: i32, unsafe impl Trusted { fn get(&self) -> i32 { return self.v; } } }\npub fn main() -> i32 { let a = A { v: 5 }; return a.get(); }", 5),
        ("generic", "struct A { v: i32 }\nstruct W[T] { t: T }\nunsafe impl Trusted for A { fn get(&self) -> i32 { return self.v; } }\nunsafe impl[T: Trusted] Trusted for W[T] { fn get(&self) -> i32 { return self.t.get() + 1; } }\npub fn main() -> i32 { let w = W[A] { t: A { v: 5 } }; return w.get(); }", 6),
        ("plain_stays_plain", "struct A { v: i32, impl Plain { fn get(&self) -> i32 { return self.v; } } }\npub fn main() -> i32 { let a = A { v: 3 }; return a.get(); }", 3),
    ] {
        assert_runs(name, &format!("{prelude}{body}"), value);
    }
    for (name, body, message) in [
        ("module_without_unsafe", "struct A { v: i32 }\nimpl Trusted for A { fn get(&self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { v: 1 }; return a.get(); }", "write 'unsafe impl'"),
        ("body_without_unsafe", "struct A { v: i32, impl Trusted { fn get(&self) -> i32 { return 1; } } }\npub fn main() -> i32 { let a = A { v: 1 }; return a.get(); }", "write 'unsafe impl'"),
        ("unsafe_for_nothing", "struct A { v: i32 }\nunsafe impl Plain for A { fn get(&self) -> i32 { return 1; } }\npub fn main() -> i32 { let a = A { v: 1 }; return a.get(); }", "asserts nothing"),
        // An allocator's memory is trusted by safe code, so implementing one is unsafe.
        ("allocator", "struct Bump { }\nimpl Allocator for Bump {\n    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 { return @raw_alloc(bytes); }\n    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return ptr; }\n    fn dealloc(&self, ptr: *mut u8) { }\n}\npub fn main() -> i32 { let b = Box[i32, Bump]::new_in(1, Bump { }); return 0; }", "write 'unsafe impl'"),
    ] {
        assert_rejected(name, &format!("{prelude}{body}"), message);
    }
}

#[test]
fn test_structural_traits() {
    // A `trait(structural)` is met by any type with methods of its signatures, and by no `impl`:
    // the bound between naming a trait and `unchecked`.
    let prelude = "trait(structural) Keyed { fn key(&self) -> u64; }
trait Named { fn key(&self) -> u64; }
fn key_of[T: Keyed](x: &T) -> u64 { return x.key(); }
struct A { v: u64, pub fn key(&self) -> u64 { return self.v; } }
struct P { fn hidden(&self) -> i32 { return 1; } }
impl Named for i32 { fn key(&self) -> u64 { return *self as u64 + 1; } }
trait(structural) Picks { fn pick(&self, o: &i32) -> &i32 borrows(o); }
fn pick_of[T: Picks](x: &T, o: &i32) -> i32 { return *x.pick(o); }
";
    for (name, body, value) in [
        ("own_method", "pub fn main() -> i32 { let a = A { v: 7 }; return key_of(&a) as i32; }", 7),
        ("generic_type", "struct W[T] { t: T, pub fn key(&self) -> u64 { return 2; } }\npub fn main() -> i32 { let w = W[i32] { t: 1 }; return key_of(&w) as i32; }", 2),
        // A nominal trait's method serves, so builtins can meet one through an `impl`.
        ("through_an_impl", "pub fn main() -> i32 { let n: i32 = 4; return key_of(&n) as i32; }", 5),
        ("trait_object", "fn dyn_key(k: &Keyed) -> u64 { return k.key(); }\npub fn main() -> i32 { let a = A { v: 9 }; return dyn_key(&a) as i32; }", 9),
        ("satisfies", "struct B { }\nfn probe[T: unchecked]() -> i32 { if @satisfies(T, Keyed) { return 1; } return 0; }\npub fn main() -> i32 { return probe[A]() * 10 + probe[B]() + probe[i32](); }", 11),
        ("has_method", "pub fn main() -> i32 { let a: i32 = if @has_method(A, \"key\") { 1 } else { 0 }; let b: i32 = if @has_method(&A, \"nope\") { 1 } else { 0 }; let c: i32 = if @has_method(P, \"hidden\") { 1 } else { 0 }; let d: i32 = if @has_method(i32, \"key\") { 1 } else { 0 }; return a * 8 + b * 4 + c * 2 + d; }", 9),
        ("same_borrows", "struct Q { pub fn pick(&self, o: &i32) -> &i32 borrows(o) { return o; } }\npub fn main() -> i32 { let q = Q { }; let n: i32 = 6; return pick_of(&q, &n); }", 6),
    ] {
        assert_runs(name, &format!("{prelude}{body}"), value);
    }
    for (name, body, message) in [
        ("missing", "struct B { }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "it has no method 'key'"),
        ("private", "struct B { fn key(&self) -> u64 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "is not 'pub'"),
        ("wrong_signature", "struct B { pub fn key(&self) -> u32 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "different signature"),
        ("wrong_arity", "struct B { pub fn key(&self, n: i32) -> u64 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "takes 2 parameters"),
        ("unsafe_method", "struct B { pub unsafe fn key(&self) -> u64 { return 1; } }\npub fn main() -> i32 { let b = B { }; return key_of(&b) as i32; }", "is 'unsafe fn'"),
        ("different_borrows", "struct Q { v: i32, pub fn pick(&self, o: &i32) -> &i32 borrows(self) { return &self.v; } }\npub fn main() -> i32 { let q = Q { v: 1 }; let n: i32 = 6; return pick_of(&q, &n); }", "different borrows(...) contract"),
        ("an_impl", "struct B { }\nimpl Keyed for B { fn key(&self) -> u64 { return 1; } }\npub fn main() -> i32 { return 0; }", "write them as the type's own methods"),
        // The bound promises the trait's methods and nothing more.
        ("beyond_the_bound", "fn more[T: Keyed](x: &T) -> u64 { return x.size(); }\npub fn main() -> i32 { return 0; }", "has no method 'size'"),
    ] {
        assert_rejected(name, &format!("{prelude}{body}"), message);
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

/// `v.clone()` is `@clone(v)` and `T::default()` is `@default(T)` for every type, `@default()`
/// takes its type from its context, and the hooks' names are reserved.
#[test]
fn test_clone_and_default_method_sugar() {
    const O: &str = "struct P { x: i32, y: i32 }
opaque O {
    v: i32,
    impl default { fn default() -> Self { return Self { v: 7 }; } }
    impl clone { fn clone(&self) -> Self { return Self { v: self.v + 1 }; } }
    pub fn v(&self) -> i32 { return self.v; }
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
        "opaque B { v: i32, pub fn clone(&self) -> Self { return Self { v: self.v }; } }
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

#[test]
fn test_generic_trait_and_error_headers() {
    assert_runs(
        "generic_trait_and_error_headers_positive",
        "pub trait Convert[Dst] {
    fn convert(&self) -> Dst;
}

trait(structural) HasScale[T] {
    fn scale(&self, factor: T) -> T;
}

unsafe trait TrustedTag[T] {
    fn tag_val(&self) -> T;
}

trait ConvertBoth[A, B] = Convert[A] + Convert[B];

pub error ParseErr[Ctx] {
    Bad(Ctx),
    Empty,
}

struct Meter {
    n: i32,
    pub fn scale(&self, factor: i32) -> i32 {
        return self.n * factor;
    }
}

impl Convert[i32] for Meter {
    fn convert(&self) -> i32 { return self.n; }
}

impl Convert[i64] for Meter {
    fn convert(&self) -> i64 { return (self.n * 2) as i64; }
}

unsafe impl TrustedTag[i32] for Meter {
    fn tag_val(&self) -> i32 { return self.n + 1; }
}

fn sum_both[T: ConvertBoth[i32, i64]](v: &T) -> i32 {
    let a: i32 = Convert[i32]::convert(v);
    let b: i64 = Convert[i64]::convert(v);
    return a + (b as i32);
}

fn apply_scale[S: HasScale[i32]](s: &S, f: i32) -> i32 {
    return s.scale(f);
}

fn parse_pos(x: i32) -> ParseErr[i32]!i32 {
    if x < 0 {
        return .Bad(-x);
    }
    if x == 0 {
        return .Empty;
    }
    return x;
}

pub fn main() -> i32 {
    let m = Meter { n: 5 };
    let r1 = sum_both(&m);
    let r2 = apply_scale(&m, 3);
    let r3 = m.tag_val();
    let ok_v = parse_pos(4) catch 0;
    let err_v = parse_pos(-2) catch |e| match e {
        .Bad(c) => c,
        .Empty => 0,
    };
    // 15 + 15 + 6 + 4 + 2 = 42
    return r1 + r2 + r3 + ok_v + err_v;
}",
        42,
    );

    assert_rejected(
        "unsafe_generic_trait_requires_unsafe_impl",
        "unsafe trait Trusted[T] {}
struct S { x: i32 }
impl Trusted[i32] for S {}
pub fn main() -> i32 { return 0; }",
        "unsafe",
    );
}

#[test]
fn test_const_and_comptime_let_bindings() {
    assert_runs(
        "const_and_comptime_let_positive",
        "struct Sample { a: i32, b: i64, c: u8 }

pub fn main() -> i32 {
    const N: usize = 4;
    let outer_arr: array[i32; N] = .[5; N];
    let inner_sum = {
        const N: usize = 2;
        let inner_arr: array[i32; N] = .[3; N];
        inner_arr[0] + inner_arr[1]
    };
    let check_outer: array[i32; N] = outer_arr;

    comptime let mut field_count: usize = 0;
    comptime let mut byte_sum: usize = 0;
    comptime for f in @fields(Sample) {
        field_count += 1;
        byte_sum = byte_sum + @size_of(f.ty);
    }
    let sized_buf: array[u8; field_count] = .[1; field_count];

    // 20 + 6 + 3 + 13 = 42
    return check_outer[0] * 4 + inner_sum + (sized_buf.len as i32) + (byte_sum as i32);
}",
        42,
    );

    assert_rejected(
        "const_mut_rejected",
        "pub fn main() -> i32 { const mut X = 1; return X; }",
        "'const mut' is invalid",
    );
    assert_rejected(
        "bare_module_comptime_rejected",
        "comptime X: i32 = 1;
pub fn main() -> i32 { return X; }",
        "const",
    );
    assert_rejected(
        "bare_local_comptime_rejected",
        "pub fn main() -> i32 { comptime X = 1; return X; }",
        "comptime let",
    );
    assert_rejected(
        "immutable_comptime_let_mutation_rejected",
        "pub fn main() -> i32 { comptime let x = 1; x = 2; return x; }",
        "Cannot mutate",
    );
    assert_rejected(
        "local_const_runtime_init_rejected",
        "fn id(v: i32) -> i32 { return v; }
pub fn main() -> i32 { let r = id(3); const C = r; return C; }",
        "compile-time",
    );
}

