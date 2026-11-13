use super::*;

#[test]
fn test_container_allocators() {
    let prelude = format!(
        "{COUNTING}pub struct Counted {{ }}
unsafe impl Allocator for Counted {{
    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ LIVE = LIVE + 1; TOTAL = TOTAL + 1; return malloc(bytes); }} }}
    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {{ unsafe {{ return realloc(ptr, bytes); }} }}
    fn dealloc(&self, ptr: *mut u8) {{ unsafe {{ LIVE = LIVE - 1; free(ptr); }} }}
}}
pub opaque Pool {{
    cell live: i32,
    cell total: i32,
    pub fn new() -> Self {{ return Self {{ live: 0, total: 0 }}; }}
    pub fn stats(&self) -> i32 {{ return unsafe {{ *(&raw mut self.total) * 10 + *(&raw mut self.live) }}; }}
    pub fn note(&self, d: i32) {{
        unsafe {{
            let p = &raw mut self.live;
            *p = *p + d;
            if d > 0 {{ let q = &raw mut self.total; *q = *q + 1; }}
        }}
    }}
}}
unsafe impl Allocator for Pool {{
    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 {{ self.note(1); return unsafe {{ malloc(bytes) }}; }}
    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {{ return unsafe {{ realloc(ptr, bytes) }}; }}
    fn dealloc(&self, ptr: *mut u8) {{ self.note(-1); unsafe {{ free(ptr); }} }}
}}
struct Held {{ v: Vec[i32, &Pool] }}
fn add(v: &mut Vec[i32, &Pool]) {{ v.push(1); }}
fn make(p: &Pool) -> Vec[i32, &Pool] borrows(p) {{ return Vec[i32, &Pool]::new_in(p); }}
fn wrap(v: Vec[i32, &Pool]) -> Held {{ return Held {{ v: v }}; }}
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
        ("detached_thread_nested", "", "let p = Pool::new(); let v = make(&p); let b = Box[Vec[i32, &Pool]]::new(v); let t = spawn(move fn() -> i32 { return b.into_inner().len() as i32; }); return t.join();", "spawn"),
    ] {
        assert_rejected(name, &format!("{prelude}{items}\npub fn main() -> i32 {{ {body} }}"), what);
    }
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

#[test]
fn test_vec_storage() {
    // `Vec[T, A]` keeps its elements in a `Storage`: any allocator, or `Slots[T, N]` inside the
    // vector itself (`ArrayVec[T, N]`), which moves with it.
    let counting = "static mut GROWS: i32 = 0;
pub struct Counting { }
unsafe impl Storage for Counting {
    const Handle: type = *own u8;
    fn resolve(&self, h: *own u8) -> *own u8 { return h; }
    fn grow(&mut self, h: ?*own u8, keep: usize, bytes: usize, align: usize) -> ?*own u8 {
        unsafe { GROWS = GROWS + 1; }
        let g = Global { };
        let mut s: Global = g;
        return s.grow(h, keep, bytes, align);
    }
    fn release(&mut self, h: *own u8) { let mut s = Global { }; s.release(h); }
    fn limit(&self) -> usize { return 1024; }
    fn sibling(&self) -> Self { return Counting { }; }
}
";
    for (name, body, value) in [
        ("array_vec", "let mut v = ArrayVec[Box[i32], 4]::new(); v.push(Box[i32]::new(3)); v.push(Box[i32]::new(4)); v.insert(0, Box[i32]::new(1)); let w = v; let mut t: i32 = 0; for b in w.iter() { t = t * 10 + *b.get(); } return t;", 134),
        ("moved_and_cloned", "let mut v = ArrayVec[String, 3]::new(); v.push(String::from(\"b\")); v.push(String::from(\"aa\")); let w = @clone(&v); let x = v.remove(0) orelse unreachable; let moved = v; return (w.len() * 100 + x.len() * 10 + moved.len()) as i32;", 211),
        ("slices_and_sorting", "let mut v = ArrayVec[i32, 5]::new(); v.push(3); v.push(1); v.push(2); v.sort(); let s = v.as_slice(); return s[0] * 100 + s[1] * 10 + s[2];", 123),
        // Growth stops at what the slots hold, not at the next doubling.
        ("five_slots", "let mut v = ArrayVec[i32, 5]::new(); for i in 0..5 { v.push(i); } return (v.capacity() * 10 + v.len()) as i32;", 55),
        ("drained", "let mut v = ArrayVec[Box[i32], 3]::new(); v.push(Box[i32]::new(2)); v.push(Box[i32]::new(5)); let mut t: i32 = 0; v.drain(fn(b: Box[i32]) { t = t + b.into_inner(); }); return t;", 7),
        // Inside a heap vector, the inline storage lives in a heap block.
        ("in_a_heap_vec", "let mut outer = Vec[ArrayVec[Box[i32], 2]]::new(); let mut a = ArrayVec[Box[i32], 2]::new(); a.push(Box[i32]::new(6)); outer.push(a); let inner = outer.get_mut(0) orelse unreachable; inner.push(Box[i32]::new(7)); return *(inner.get(1) orelse unreachable).get() * 10 + *(inner.get(0) orelse unreachable).get();", 76),
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

/// Generators: `-> gen T` bodies that `yield`, iterated by `for`, borrowing what their
/// parameters do, with locals that refer to one another across a `yield`, and dropped early by
/// ending where they wait.
#[test]
fn test_generators() {
    assert_runs(
        "generators",
        "static mut DROPS: i32 = 0;
opaque T {
    v: i32,
    impl drop { fn drop(&mut self) { unsafe { DROPS += self.v; } } }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
}
fn bump() { unsafe { DROPS += 100; } }
fn evens(n: u32) -> gen u32 {
    for i in 0..n {
        yield i * 2;
    }
}
fn parts(s: &str) -> gen &str {
    let mut start: usize = 0;
    for i in 0..s.len {
        if s[i] == 44 {
            yield s[start..i];
            start = i + 1;
        }
    }
    yield s[start..s.len];
}
fn held() -> gen i32 {
    let mut v = Vec[i32]::new();
    v.push(4);
    v.push(5);
    let r = &v;
    for i in 0..2 as usize {
        yield *(r.get(i) orelse unreachable);
    }
}
opaque Bag[E: copy] {
    items: Vec[E],
    pub fn new() -> Self { return Self { items: Vec[E]::new() }; }
    pub fn add(&mut self, e: E) { self.items.push(e); }
    pub fn each(&self) -> gen E {
        for i in 0..self.items.len() {
            yield *(self.items.get(i) orelse unreachable);
        }
    }
}
fn upto[N: integer](n: N) -> gen N {
    let mut i: N = 0;
    while i < n {
        yield i;
        i += 1;
    }
}
fn ones() -> gen i32 { yield 1; yield 1; }
fn twice() -> gen i32 {
    for a in ones() { yield a * 2; }
    for b in ones() { yield b * 3; }
}
fn names(n: i32) -> gen String {
    yield String::from(\"a\");
    if n < 2 {
        return;
    }
    yield String::from(\"bb\");
}
fn tracked(k: T) -> gen i32 {
    let a = T::new(10);
    defer bump();
    yield 1;
    let b = T::new(1000);
    yield 2;
    yield 3;
}
pub fn main() -> i32 {
    let mut total: u32 = 0;
    for x in evens(5) { total += x; }
    @assert(total == 20);
    let text = String::from(\"ab,c,def\");
    let mut lens: usize = 0;
    let mut count = 0;
    for p in parts(text.as_str()) { lens += p.len; count += 1; }
    @assert(lens == 6 && count == 3);
    let mut s = 0;
    for x in held() { s += x; }
    let mut b = Bag[i32]::new();
    b.add(3);
    b.add(4);
    for x in b.each() { s += x; }
    for y in upto[u8](4) { s += y as i32; }
    for z in twice() { s += z; }
    @assert(s == 9 + 7 + 6 + 10);
    let mut chars: usize = 0;
    for x in names(1) { chars += x.len(); }
    for x in names(5) { chars += x.len() * 10; }
    @assert(chars == 31);
    {
        let mut it = tracked(T::new(1));
        @assert((it.next() orelse 0) == 1 && (it.next() orelse 0) == 2);
    }
    @assert(unsafe { DROPS } == 1111);
    { let unstarted = tracked(T::new(5)); }
    @assert(unsafe { DROPS } == 1111 + 5);
    let mut whole = tracked(T::new(1));
    while let ?v = whole.next() { }
    @assert(whole.next().is_none() && unsafe { DROPS } == 1116 + 1111);
    let mut named: Gen[u32, tuple { u32 }] = evens(2);
    _ = named.next();
    return 42;
}",
        42,
    );
    let rejected = [
        (
            "fn bad() -> gen &i32 { let x: i32 = 3; yield &x; }
pub fn main() -> i32 { for r in bad() { } return 0; }",
            "in root::<body of bad> (fn",
        ),
        (
            "fn parts(s: &str) -> gen &str { yield s; }
pub fn main() -> i32 { let mut g = parts(\"x\"); { let text = String::from(\"ab\"); g = parts(text.as_str()); } _ = g.next(); return 0; }",
            "'text' is already borrowed",
        ),
        (
            "fn g() -> gen i32 { let f = fn() { yield 1; }; yield 2; }
pub fn main() -> i32 { return 0; }",
            "'yield' is allowed only in the body of a generator",
        ),
        (
            "fn f() -> i32 { yield 1; return 0; }
pub fn main() -> i32 { return f(); }",
            "'yield' is allowed only in the body of a generator",
        ),
        (
            "fn g() -> gen i32 { yield 1; }
pub fn main() -> i32 { let it = g(); let h = spawn(move fn() -> i32 { let mut i = it; return i.next() orelse 0; }); return h.join(); }",
            "does not satisfy comptime constraint 'send'",
        ),
        (
            "fn g(s: &str) -> gen i32 borrows(s) { yield 1; }
pub fn main() -> i32 { return 0; }",
            "takes no 'borrows(...)' clause",
        ),
        (
            "fn evens(n: u32) -> gen u32 { for i in 0..n { yield i * 2; } }
fn sum() -> u32 { let mut t: u32 = 0; for x in evens(4) { t += x; } return t; }
const S: u32 = sum();
pub fn main() -> i32 { return S as i32; }",
            "cannot run at compile time yet",
        ),
    ];
    for (i, (src, what)) in rejected.iter().enumerate() {
        assert_rejected(&format!("generator_rejected_{i}"), src, what);
    }
    // Linear items go to the caller of `next`; linear state held across a `yield` is refused,
    // as dropping the generator there would discard it.
    assert_runs(
        "generator_of_linear_items",
        &format!("{TX}
fn txs(n: i32) -> gen Tx {{ for i in 0..n {{ yield Tx::new(i); }} }}
pub fn main() -> i32 {{
    let mut s = 0;
    for t in txs(4) {{ s += t.commit(); }}
    let mut g = txs(3);
    if let ?t = g.next() {{ s += t.commit() * 100; }}
    if let ?t = g.next() {{ s += t.commit() * 10; }}
    return s + 26;
}}"),
        42,
    );
    assert_rejected(
        "generator_holding_linear_state",
        &format!("{TX}
fn txs() -> gen i32 {{ let t = Tx::new(1); yield 1; _ = t.commit(); }}
pub fn main() -> i32 {{ return 0; }}"),
        "Linear value 't' of type 'Tx' must be explicitly consumed before going out of scope in root::<body of txs>",
    );
}

/// A generator's frame keeps only what outlives a call of its resume function: here the
/// parameter and the loop's state, not the temporaries computed between `yield`s.
#[test]
fn test_generator_frame_keeps_only_what_crosses_a_yield() {
    let program = Compiler::compile_source(
        "fn g(n: i32) -> gen i32 {
    for i in 0..n {
        let a = i * 2;
        let b = a + 1;
        let c = b * b - a;
        yield c;
    }
}
pub fn main() -> i32 { let mut s = 0; for x in g(3) { s += x; } return s; }",
    )
    .unwrap();
    let body = program.functions.iter().find(|f| f.debug_name.as_deref() == Some("root::<body of g>")).unwrap();
    let crate::ir::Type::Ptr { pointee, .. } = &program.types[body.locals[4].0 as usize] else { panic!() };
    let crate::ir::Type::Struct(fields) = &program.types[pointee.0 as usize] else { panic!() };
    assert!(fields.len() <= 6, "{fields:?}");
}

/// `std::iter`: adapters over any iterator, written as generators, and lazy forms of `split`
/// and `words` and a `lines`, whose items borrow the string they come from.
#[test]
fn test_iterator_adapters_and_lazy_strings() {
    assert_runs(
        "iterator_adapters",
        "fn evens(n: u32) -> gen u32 { for i in 0..n { yield i * 2; } }
pub fn main() -> i32 {
    let mut s: u32 = 0;
    for x in evens(6).map(fn(v: u32) -> u32 { return v + 1; }).filter(fn(v: &u32) -> bool { return *v > 4; }) {
        s += x;
    }
    @assert(s == 32);
    let mut v = Vec[i32]::new();
    v.push(5);
    v.push(6);
    v.push(7);
    let mut t = 0;
    for p in v.iter().enumerate().skip(1) { t += p.0 as i32 * *p.1; }
    for q in v.iter().zip(evens(5)).take(2) { t += *q.0 + q.1 as i32; }
    @assert(t == 33 && evens(3).chain(evens(2)).collect().len() == 5);
    let text = String::from(\"a b\\n  cd\\r\\nef\\n\");
    let mut lens: usize = 0;
    for l in text.as_str().lines() { lens += l.len; }
    let firsts = text.as_str().words_iter().map(fn(w: &str) -> u8 { return w[0]; }).collect();
    @assert(lens == 9 && text.as_str().lines().count() == 3 && *(firsts.get(2) orelse unreachable) == 99);
    @assert(\"x,y,,z\".split_iter(\",\").count() == 4 && \"x,y,,z\".split(\",\").len() == 4);
    return 42;
}",
        42,
    );
    // A type of the program's own is an `Iterator` by implementing it, and then has the
    // adapters; one with only a `next` can be iterated by `for`, but not adapted.
    assert_runs(
        "own_iterator",
        "opaque Count {
    n: u32,
    impl Iterator {
        const Item: ?linear = u32;
        fn next(&mut self) -> ?u32 borrows(*self) {
            self.n += 1;
            if self.n > 3 { return null; }
            return self.n;
        }
        // Replaces the trait's.
        fn count(mut self) -> usize { return 100; }
    }
    pub fn new() -> Self { return Self { n: 0 }; }
}
fn doubled_count[I: Iterator](it: I) -> usize { return it.map(fn(x: u32) -> u32 { return x * 2; }).count(); }
pub fn main() -> i32 {
    let mut s: u32 = 0;
    for x in Count::new().map(fn(v: u32) -> u32 { return v * 10; }).skip(1) { s += x; }
    @assert(Count::new().count() == 100 && doubled_count(Count::new()) == 3);
    return s as i32 - 8;
}",
        42,
    );
    assert_rejected(
        "only_next",
        "opaque D { n: u32, pub fn next(&mut self) -> ?u32 { return null; } pub fn new() -> Self { return Self { n: 0 }; } }
pub fn main() -> i32 { for x in D::new() { } return D::new().count() as i32; }",
        "Type 'D' has no method 'count'; it is a method of trait 'Iterator', which 'D' does not implement",
    );
    // Linear items pass through the adapters that hand each one on; those that drop items need
    // items that may be dropped.
    assert_runs(
        "linear_items_adapted",
        &format!("{TX}
fn txs(n: i32) -> gen Tx {{ for i in 0..n {{ yield Tx::new(i); }} }}
pub fn main() -> i32 {{
    let mut s = 0;
    for t in txs(3).map(fn(t: Tx) -> Tx {{ return t; }}).take(2) {{ s += t.commit(); }}
    let mut v = Vec[i32]::new();
    v.push(20);
    v.push(21);
    let all = v.iter_mut().collect();
    for r in all.iter() {{ s += **r; }}
    return s;
}}"),
        42,
    );
    assert_rejected(
        "count_of_linear_items",
        &format!("{TX}
fn txs(n: i32) -> gen Tx {{ for i in 0..n {{ yield Tx::new(i); }} }}
pub fn main() -> i32 {{ return txs(2).count() as i32; }}"),
        "Method 'count' of trait 'Iterator' needs 'Self::Item: !linear'",
    );
    // `move r` hands a `&mut` over rather than lending it: `r` may be given a new value, and
    // not used before.
    assert_runs(
        "move_mut_ref",
        "pub fn main() -> i32 {
    let mut a: i32 = 40;
    let mut b: i32 = 2;
    let mut out = Vec[&mut i32]::new();
    let mut r: &mut i32 = &mut a;
    out.push(move r);
    r = &mut b;
    out.push(move r);
    let mut s = 0;
    for x in out.iter() { s += **x; }
    return s;
}",
        42,
    );
    assert_rejected(
        "use_after_move_mut_ref",
        "pub fn main() -> i32 { let mut a: i32 = 1; let mut out = Vec[&mut i32]::new(); let mut r: &mut i32 = &mut a; out.push(move r); *r = 5; return 0; }",
        "Use of moved or uninitialized value '*r'",
    );
    assert_rejected(
        "lines_outlive_text",
        "pub fn main() -> i32 {
    let mut first: &str = \"\";
    {
        let text = String::from(\"a\\nb\");
        for l in text.as_str().lines() { first = l; }
    }
    return first.len as i32;
}",
        "'text' is already borrowed",
    );
}

/// Allocation that may fail: `try_` forms that say why there is no memory instead of trapping,
/// `try_push` giving the value back, and huge requests answered with null.
#[test]
fn test_fallible_allocation() {
    assert_runs(
        "vec_out_of_memory",
        "/// Has  allocations to give, then none.
pub opaque Budget {
    cell left: i32,
    unsafe impl Allocator {
        fn alloc(&self, bytes: usize, align: usize) -> *mut u8 {
            if !self.spend() { return 0 as *mut u8; }
            return @raw_alloc(bytes);
        }
        fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
            if !self.spend() { return 0 as *mut u8; }
            return unsafe { @raw_realloc(ptr, bytes) };
        }
        fn dealloc(&self, ptr: *mut u8) { unsafe { @dealloc(ptr); } }
    }
    pub fn new(n: i32) -> Self { return Self { left: n }; }
    fn spend(&self) -> bool {
        if self.left == 0 { return false; }
        unsafe { *(&raw mut self.left) = self.left - 1; }
        return true;
    }
}
pub fn main() -> i32 {
    let budget = Budget::new(2);
    let mut v = Vec[i32, &Budget]::new_in(&budget);
    let mut pushed = 0;
    let mut refused = 0;
    for i in 0..20 {
        if let ?back = v.try_push(i) { refused += 1; @assert(back == i); } else { pushed += 1; }
    }
    @assert(pushed == 8 && refused == 12 && v.len() == 8);
    @assert(huge() == 1);
    return 42;
}
fn huge() -> i32 {
    let v = Vec[u64]::try_with_capacity(1 << 62) catch |e| {
        return match e { .TooLarge => 1, .OutOfMemory => 2 };
    };
    return 0;
}
",
        42,
    );
    assert_runs(
        "string_out_of_memory",
        "pub struct Limited { }
static mut LEFT: i32 = 3;
unsafe impl GlobalAllocator for Limited {
    fn alloc(bytes: usize, align: usize) -> *mut u8 {
        unsafe { if LEFT == 0 { return 0 as *mut u8; } LEFT = LEFT - 1; }
        return @raw_alloc(bytes);
    }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        unsafe { if LEFT == 0 { return 0 as *mut u8; } LEFT = LEFT - 1; return @raw_realloc(ptr, bytes); }
    }
    fn dealloc(ptr: *mut u8) { unsafe { @dealloc(ptr); } }
}
pub alias ProgramAllocator = Limited;
fn grow_until_full() -> i32 {
    let mut s = String::new();
    let mut n = 0;
    while true {
        s.try_push_str(\"0123456789\") catch |e| return n;
        n += 1;
    }
    return -1;
}
pub fn main() -> i32 {
    let n = grow_until_full();
    let t = String::try_from(\"x\") catch |e| return n + 100;
    return n;
}
",
        106,
    );
    assert_runs(
        "fallible_misc",
        &format!("{TX}
pub fn main() -> i32 {{
    let mut slots = ArrayVec[Tx, 2]::new();
    let mut s = 0;
    if let ?t = slots.try_push(Tx::new(1)) {{ s += t.commit() * 100; }}
    if let ?t = slots.try_push(Tx::new(2)) {{ s += t.commit() * 100; }}
    let back = slots.try_push(Tx::new(3)) orelse unreachable;
    s += back.commit();
    while let ?t = slots.pop() {{ s += t.commit(); }}
    slots.finish();
    let mut m = HashMap[i32, i32]::new();
    m.try_reserve(50) catch |e| return 1;
    for i in 0..50 {{ m.insert(i, i); }}
    m.try_reserve(1 << 59) catch |e| {{ s += 10; }};
    let b = Box[i32]::try_new(20) catch |e| return 2;
    let r = Rc[i32]::try_new(4) catch |e| return 3;
    let a = Arc[i32]::try_new(2) catch |e| return 4;
    let huge: usize = 1 << 40;
    @assert((@raw_alloc(huge) as usize) == 0);
    let p = @raw_alloc(8);
    @assert(unsafe {{ (@raw_realloc(p, huge) as usize) }} == 0);
    unsafe {{ @dealloc(p); }}
    return s + *b.get() + *r.get() + *a.get();
}}"),
        42,
    );
}

/// What is reserved is there for the operations that use it: once the allocator gives nothing,
/// they still succeed, and the first past it fails without losing its value.
#[test]
fn test_reserved_room_needs_no_allocation() {
    assert_runs(
        "reserved_room",
        "/// Has `left` allocations to give, then none.
pub opaque Budget {
    cell left: i32,
    unsafe impl Allocator {
        fn alloc(&self, bytes: usize, align: usize) -> *mut u8 {
            if !self.spend() { return 0 as *mut u8; }
            return @raw_alloc(bytes);
        }
        fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
            if !self.spend() { return 0 as *mut u8; }
            return unsafe { @raw_realloc(ptr, bytes) };
        }
        fn dealloc(&self, ptr: *mut u8) { unsafe { @dealloc(ptr); } }
    }
    pub fn new(n: i32) -> Self { return Self { left: n }; }
    fn spend(&self) -> bool {
        if self.left == 0 { return false; }
        unsafe { *(&raw mut self.left) = self.left - 1; }
        return true;
    }
}

fn evens(n: i32) -> gen i32 { for i in 0..n { yield i * 2; } }
pub fn main() -> i32 {
    let vb = Budget::new(1);
    let mut v = Vec[i32, &Budget]::new_in(&vb);
    v.try_reserve(10) catch |e| return 1;
    for i in 0..6 { v.push(i); }
    if let ?back = v.try_insert(0, 100) { return 2; }
    let arr: array[i32; 2] = .[7, 8];
    v.try_extend_from_slice(&arr[0..2]) catch |e| return 3;
    let mut more = evens(5);
    let missed = more.try_collect_into(&mut v) orelse return 4;
    @assert(v.len() == 10 && missed == 2 && (more.next() orelse 0) == 4);
    let mb = Budget::new(3);
    let mut m = HashMap[i32, i32, &Budget]::new_in(&mb);
    m.try_reserve(20) catch |e| return 5;
    for i in 0..20 { m.insert(i, i); }
    m.try_reserve(100) catch |e| { return 42; };
    return 6;
}",
        42,
    );
}

/// `oomsafe { ... }`: the block may reach no allocation that traps for want of memory, through
/// the calls and drops it makes, which the `try_` forms meet and the others do not.
#[test]
fn test_oomsafe_blocks() {
    assert_runs("oomsafe_try_forms", "pub fn main() -> i32 {
    let mut base = Vec[u32]::new();
    base.push(7);
    base.push(8);
    let mut v = Vec[&u32]::new();
    let mut m = HashMap[i32, i32]::new();
    oomsafe {
        let mut w = Vec[u32]::try_with_capacity(4) catch |e| return 1;
        if let ?b = w.try_push(1) { return 2; }
        if let ?b = w.try_insert(0, 2) { return 3; }
        let arr: array[u32; 2] = .[3, 4];
        w.try_extend_from_slice(&arr[0..2]) catch |e| return 4;
        w.try_reserve(10) catch |e| return 5;
        let mut src = base.iter();
        if let ?b = src.try_collect_into(&mut v) { return 6; }
        m.try_reserve(4) catch |e| return 7;
        _ = m.try_insert(1, 1) catch |e| return 8;
        let mut s = String::try_with_capacity(8) catch |e| return 9;
        s.try_push('x') catch |e| return 10;
        s.try_push_byte(65) catch |e| return 11;
        s.try_push_str(\"yz\") catch |e| return 12;
        let t = String::try_from(\"abc\") catch |e| return 13;
        let f = try_format(f\"{w.len()}\") catch |e| return 14;
        let b = Box[i32]::try_new(1) catch |e| return 15;
        let r = Rc[i32]::try_new(1) catch |e| return 16;
        let a = Arc[i32]::try_new(1) catch |e| return 17;
        let p = @raw_alloc(8);
        unsafe { @dealloc(p); }
        return (w.len() + v.len() + s.len() + t.len()) as i32 + 29;
    }
}
", 42);
    let refused = [
        ("pub fn main() -> i32 { let mut v = Vec[i32]::new(); oomsafe { v.push(1); } return 0; }", "Vec[i32]::push -> Vec[i32]::grow -> std::mem::out_of_memory"),
        ("pub fn main() -> i32 { let s = String::from(\"a\"); oomsafe { let t = s.clone(); } return 0; }", "String::clone -> String::from"),
        ("fn g() -> gen i32 { yield 1; } pub fn main() -> i32 { oomsafe { let it = g(); } return 0; }", "can trap for want of memory: root::g"),
        ("pub fn main() -> i32 { oomsafe { let p = unsafe { @alloc(i32, 1) }; } return 0; }", "'@alloc' traps when there is no memory"),
        ("fn f() -> i32 { return 1; } pub fn main() -> i32 { let h: fn() -> i32 = f; oomsafe { let x = h(); } return 0; }", "a call through a function value, which may reach anything"),
        ("pub fn main() -> i32 { let mut m = HashMap[i32, i32]::new(); oomsafe { m.insert(1, 1); } return 0; }", "HashMap[i32, i32]::insert -> HashMap[i32, i32]::reserve_one"),
    ];
    for (i, (src, what)) in refused.iter().enumerate() {
        assert_rejected(&format!("oomsafe_refused_{i}"), src, what);
    }
}

/// The rest of the fallible forms: shared slices and strings, channels, and threads; and the
/// hook a program sets to run before an allocation trap, which every such trap reaches.
#[test]
fn test_more_fallible_forms_and_the_oom_hook() {
    assert_runs("shared_slices_try", "pub fn main() -> i32 { oomsafe { let a: array[i32; 3] = .[1, 2, 3]; let r = RcSlice[i32]::try_from_slice(&a[0..3]) catch |e| return 1; let s = RcStr::try_from(\"hey\") catch |e| return 2; let x = ArcSlice[i32]::try_from_slice(&a[0..3]) catch |e| return 3; let y = ArcStr::try_from(\"yo\") catch |e| return 4; return r.get()[2] + s.len() as i32 + x.get()[1] + y.len() as i32 + 32; } }
", 42);
    assert_runs(
        "channel_and_spawn_try",
        "pub fn main() -> i32 {
    let ch = Channel[i32]::try_new() catch |e| return 1;
    oomsafe {
        if let ?back = ch.try_send(30) { return 2; }
    }
    let h = try_spawn(move fn() -> i32 { return 10; }) catch |e| return 3;
    let g = spawn(move fn() -> i32 { return 2; });
    return (ch.try_recv() orelse 0) + h.join() + g.join();
}",
        42,
    );
    let src = "pub struct Refuse { }
unsafe impl GlobalAllocator for Refuse {
    fn alloc(bytes: usize, align: usize) -> *mut u8 { return 0 as *mut u8; }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { return 0 as *mut u8; }
    fn dealloc(ptr: *mut u8) { }
}
pub alias ProgramAllocator = Refuse;
fn report() { eprintln(\"hook ran\"); }
pub fn main() -> i32 {
    _ = set_out_of_memory_hook(report);
    let p = unsafe { @alloc(i32, 4) };
    return 0;
}
";
    let mut program = Compiler::compile_source(src).unwrap();
    let err = super::run_vm_program(&mut program).expect_err("traps");
    assert!(err.contains("unreachable"), "{err}");
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, super::TRAP_EXIT).unwrap();
    let out = super::lli(&ir);
    assert_eq!(out.status.code(), Some(super::TRAP_EXIT));
    assert!(String::from_utf8_lossy(&out.stderr).contains("hook ran"), "{out:?}");
}

/// `try_clone`: a copy that says when there is no memory for it, written for a struct from its
/// fields, an opaque's own method, and std's types; one that fails part way leaves nothing.
#[test]
fn test_try_clone() {
    assert_runs("try_clone_kinds", "struct P { x: i32, y: i32 }
opaque Name {
    n: i32,
    pub fn new(n: i32) -> Self { return Self { n: n }; }
    pub fn try_clone(&self) -> AllocError!Self { return Self { n: self.n + 1 }; }
    pub fn n(&self) -> i32 { return self.n; }
}
struct Rec { p: P, name: Name, k: i32 }
fn dup[T: try_clone](t: &T) -> AllocError!T { return @try_clone(t); }
pub fn main() -> i32 {
    let p = P { x: 1, y: 2 };
    let q = p.try_clone() catch |e| return 1;
    let r = Rec { p: p, name: Name::new(10), k: 3 };
    let s = r.try_clone() catch |e| return 2;
    let t = dup(&r) catch |e| return 3;
    let n: i32 = 5;
    let m = @try_clone(n) catch |e| return 4;
    return q.x + q.y + s.name.n() + s.k + t.name.n() + m + 9;
}
", 42);
    assert_runs("try_clone_deep", "struct Person { name: String, tags: Vec[String], age: i32 }
pub fn main() -> i32 {
    let mut tags = Vec[String]::new();
    tags.push(String::from(\"a\"));
    tags.push(String::from(\"bc\"));
    let p = Person { name: String::from(\"ada\"), tags: tags, age: 36 };
    let mut all = Vec[Person]::new();
    all.push(p);
    let r = Rc[i32]::new(1);
    oomsafe {
        let copy = all.try_clone() catch |e| return 1;
        let r2 = r.try_clone() catch |e| return 2;
        let first = copy.get(0) orelse return 3;
        return first.name.len() as i32 + first.tags.len() as i32 + first.age + r2.strong_count() as i32 - 1;
    }
}
", 42);
    assert_runs("try_clone_partial", "pub struct Limited { }
static mut LEFT: i32 = 1000;
unsafe impl GlobalAllocator for Limited {
    fn alloc(bytes: usize, align: usize) -> *mut u8 {
        unsafe { if LEFT == 0 { return 0 as *mut u8; } LEFT = LEFT - 1; }
        return @raw_alloc(bytes);
    }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        unsafe { if LEFT == 0 { return 0 as *mut u8; } LEFT = LEFT - 1; return @raw_realloc(ptr, bytes); }
    }
    fn dealloc(ptr: *mut u8) { unsafe { @dealloc(ptr); } }
}
pub alias ProgramAllocator = Limited;
pub fn main() -> i32 {
    let mut v = Vec[String]::new();
    for i in 0..5 { v.push(String::from(\"word\")); }
    unsafe { LEFT = 3; }
    let copy = v.try_clone() catch |e| { return 42; };
    return 1;
}", 42);
    assert_rejected(
        "try_clone_opaque_without",
        "opaque B { v: i32, pub fn new() -> Self { return Self { v: 1 }; } }
struct H { b: B }
pub fn main() -> i32 { let h = H { b: B::new() }; let c = h.try_clone() catch |e| return 1; return 0; }",
        "'H' is not 'try_clone': its field 'b' ('B') is not",
    );
}

/// `@try_gen(g(x))`: a generator call that gives an `AllocError` when there is no memory for
/// its frame, for a function, a generic one, and a method.
#[test]
fn test_try_gen() {
    assert_runs("try_gen", "pub struct Limited { }
static mut LEFT: i32 = 1000;
unsafe impl GlobalAllocator for Limited {
    fn alloc(bytes: usize, align: usize) -> *mut u8 {
        unsafe { if LEFT == 0 { return 0 as *mut u8; } LEFT = LEFT - 1; }
        return @raw_alloc(bytes);
    }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        unsafe { if LEFT == 0 { return 0 as *mut u8; } LEFT = LEFT - 1; return @raw_realloc(ptr, bytes); }
    }
    fn dealloc(ptr: *mut u8) { unsafe { @dealloc(ptr); } }
}
pub alias ProgramAllocator = Limited;
fn evens(n: u32) -> gen u32 { for i in 0..n { yield i * 2; } }
fn upto[N: integer](n: N) -> gen N { let mut i: N = 0; while i < n { yield i; i += 1; } }
opaque Bag {
    items: Vec[i32],
    pub fn new() -> Self { return Self { items: Vec[i32]::new() }; }
    pub fn each(&self) -> gen i32 { for i in 0..self.items.len() { yield *(self.items.get(i) orelse unreachable); } }
}
pub fn main() -> i32 {
    let mut s: u32 = 0;
    let g = @try_gen(evens(4)) catch |e| return 1;
    for x in g { s += x; }
    let h = @try_gen(upto[u8](3)) catch |e| return 2;
    for y in h { s += y as u32; }
    let b = Bag::new();
    let k = @try_gen(b.each()) catch |e| return 3;
    unsafe { LEFT = 0; }
    let failed = @try_gen(evens(2)) catch |e| { return (s + 27) as i32; };
    return 4;
}
", 42);
    assert_rejected(
        "try_gen_of_a_function",
        "fn f() -> i32 { return 1; } pub fn main() -> i32 { let g = @try_gen(f()) catch |e| return 1; return 0; }",
        "'@try_gen' takes a call of a generator, and 'f' is not one",
    );
    assert_rejected(
        "try_gen_of_a_value",
        "pub fn main() -> i32 { let g = @try_gen(3) catch |e| return 1; return 0; }",
        "'@try_gen' takes a call of a generator",
    );
}

