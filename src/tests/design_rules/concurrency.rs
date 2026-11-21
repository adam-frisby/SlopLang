use super::*;

#[test]
fn test_thread_safety_declarations_and_cell_fields() {
    // Writing through a shared reference is allowed only into `cell` fields (or a type declaring
    // `unsafe sync`), so a type that looks immutable cannot race when shared.
    let counter = |decl: &str, field: &str, bump: &str| {
        format!(
            "pub opaque{decl} Counter {{
    {field}: u64,
    pub fn new() -> Self {{ return Self {{ n: 0 }}; }}
    pub fn bump(&self) {{ unsafe {{ {bump} }} }}
    pub fn get(&self) -> u64 {{ return self.n; }}
}}
"
        )
    };
    const CELL_BUMP: &str = "let p = &raw mut self.n; p.* = p.* + 1;";
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
            counter("", "n", "let p = self as *mut Self; p.*.n = p.*.n + 1;")
        ),
        "Cannot cast shared reference '&Counter' to '*mut Counter'",
    );
    reject(
        "raw_mut_to_non_cell",
        "pub opaque C {
    cell n: u64,
    m: u64,
    pub fn set(&self) { unsafe { let p = &raw mut self.m; p.* = 1; } }
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
    let h = spawn_scoped(move fn() -> i32 { let q = p.get().*; unsafe { q.* = q.* + 1; } return 0; });
    let _r = h.join();
    return x;
}",
        ),
        Some(42)
    );

    // A safe reference into a `cell` field is refused however it is made, as it is checked on
    // the lowered code: `for ref`, formatting, and `@clone` take one as `&self.n` does.
    for name in ["for_ref_over_a_cell", "format_a_cell", "clone_a_cell"] {
        let src = match name {
            "for_ref_over_a_cell" => "pub opaque(unsafe sync) C {
    cell a: [i32; 2],
    pub fn new() -> Self { return Self { a: .{ 1, 2 } }; }
    pub fn peek(&self) -> i32 { let mut t = 0; for ref x in self.a { t += x.*; } return t; }
}
pub fn main() -> i32 { let c = C::new(); return c.peek(); }",
            "format_a_cell" => "pub opaque(unsafe sync) C {
    cell s: String,
    pub fn new() -> Self { return Self { s: String::from(\"ab\") }; }
    pub fn show(&self) -> i32 { println(f\"{self.s}\"); return 0; }
}
pub fn main() -> i32 { let c = C::new(); return c.show(); }",
            _ => "pub opaque(unsafe sync) C {
    cell s: String,
    pub fn new() -> Self { return Self { s: String::from(\"ab\") }; }
    pub fn dup(&self) -> String { return @clone(self.s); }
}
pub fn main() -> i32 { let c = C::new(); let d = c.dup(); return d.len() as i32; }",
        };
        reject(name, src, "A safe reference to 'cell' field");
    }
    // A `Weak` holds its value behind a raw pointer, but `upgrade` gives it back: one of a
    // borrowing type is a borrow a thread could outlive.
    reject(
        "weak_of_a_borrow_to_a_thread",
        "fn start() -> JoinHandle[i32] {
    let x: i32 = 42;
    let a = Arc[&i32]::new(&x);
    let w = a.downgrade();
    return spawn(move fn() -> i32 { if let ?s = w.upgrade() { return s.get().*.*; } return -1; });
}
pub fn main() -> i32 { return start().join(); }",
        "passed to unscoped 'spawn' contains borrowed references",
    );
    // `@select` trusts what it waits on to keep its protocol, so only a type vouching for it can be.
    reject(
        "select_on_a_lookalike",
        "pub struct Fake {
    pub fn select_fast_recv(&self, out: *mut &i32) -> bool { return true; }
    pub fn select_register_recv(&self, node: *mut WaitNode, w: *const Waiter, i: i32, out: *mut &i32) -> bool { return true; }
    pub fn select_unregister(&self, node: *mut WaitNode) { }
}
pub fn main() -> i32 { let f = Fake { }; return @select { v = f.recv() => v.* }; }",
        "'@select' cannot wait on 'Fake'",
    );
    // A trait object says nothing of the type behind it, so it is neither `send` nor `sync`.
    let traits = "pub trait Get { fn get(&self) -> i32; }
struct R { v: Rc[i32], impl Get { fn get(&self) -> i32 { return self.v.get().*; } } }
fn need_send[T: send](t: T) -> i32 { return 0; }
fn need_sync[T: sync](t: &T) -> i32 { return 0; }
";
    for (name, body) in [
        ("trait_object_not_send", "let r = R { v: Rc[i32]::new(1) }; let obj: &Get = &r; return need_send(obj);"),
        ("trait_object_not_sync", "let r = R { v: Rc[i32]::new(1) }; let obj: &Get = &r; return need_sync(&obj);"),
    ] {
        reject(name, &format!("{traits}pub fn main() -> i32 {{ {body} }}"), "does not satisfy comptime constraint");
    }
    // Whether a type is `send` can turn on whether it is `sync`, through a reference to itself:
    // the one question met again on the way down does not answer the other.
    reject(
        "send_through_a_reference_to_itself",
        "struct Node { next: ?&Node, c: OnceCell[i32] }
fn need_send[T: send](t: &T) -> i32 { return 0; }
pub fn main() -> i32 { let n = Node { next: null, c: OnceCell[i32]::new() }; return need_send(&n); }",
        "Type 'Node' does not satisfy comptime constraint 'send'",
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
    pub fn bump(&self) { unsafe { let _old = @atomic_add(&raw mut self.n, 1); } }
    pub fn get(&self) -> u64 { return unsafe { @atomic_load(&raw mut self.n) }; }
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
    impl drop { fn drop(&mut self) {} }
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
        ("pointer_to_another_copy", "unsafe { N = 40; let p = (&raw mut N as usize); let t = spawn_scoped(fn() -> i32 { unsafe { let q = p as *mut i32; q.* = q.* + 2; } return unsafe { N }; }); let x = t.join(); return N + x - 5; }", 42),
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
fn test_spawn_returns_results_wider_than_a_pointer() {
    // The result used to overrun a pointer-sized slot on the joining stack, which only the
    // native run shows.
    assert_runs(
        "wide_result",
        "struct B { a: i64, b: i64, c: i64 }
fn work() -> i64 {
    let t = spawn(move fn() -> B { return B { a: 11, b: 22, c: 33 }; });
    let guard: [i64; 4] = [_; _]{ 7, 7, 7, 7 };
    let r = t.join();
    return r.a + r.b + r.c + guard[0] + guard[3];
}
pub fn main() -> i32 { return work() as i32; }",
        80,
    );
}

#[test]
fn test_race_detection_tells_fields_apart() {
    let shared = "pub opaque(unsafe sync) Pair {
    cell a: i32,
    cell b: i32,
    pub fn new() -> Self { return Self { a: 0, b: 0 }; }
    pub fn set_a(&self) { unsafe { (&raw mut self.a).* = 1; } }
    pub fn get_b(&self) -> i32 { return unsafe { (&raw mut self.b).* }; }
    pub fn get_a(&self) -> i32 { return unsafe { (&raw mut self.a).* }; }
}
struct Point { x: i32, y: i32 }
";
    let run = |name: &str, body: &str| super::run_vm(name, &format!("{shared}pub fn main() -> i32 {{ {body} }}"));
    let other = "let p = Pair::new(); let t = spawn_scoped(fn() -> i32 { p.set_a(); return 0; }); let b = p.get_b(); return b + t.join();";
    assert_eq!(run("other_field", other).map(|r| r.value), Ok(0));
    let same = "let p = Pair::new(); let t = spawn_scoped(fn() -> i32 { p.set_a(); return 0; }); let a = p.get_a(); return a + t.join();";
    assert!(run("same_field", same).is_err_and(|e| e.contains("data race")));
    // A whole access meets every field.
    let whole = "let mut s = Point { x: 0, y: 0 }; let addr = &raw mut s as usize; let t = spawn_scoped(move fn() -> i32 { unsafe { (addr as *mut Point).*.x = 1; } return 0; }); let c = unsafe { (addr as *mut Point).* }; return c.y + t.join();";
    assert!(run("whole_value", whole).is_err_and(|e| e.contains("data race")));
}

#[test]
fn test_blocking_channels_and_sleeps() {
    let prelude = "fn add_up(c: &Channel[i32], n: i32) -> i32 { let mut t: i32 = 0; for i in 0..n { t = t + c.recv(); } return t; }
fn feed(c: &Channel[i32], n: i32) -> i32 { for i in 0..n { c.send(i); } return n; }
fn hold(m: &Mutex[i32], held: &Channel[i32], c: &Channel[i32]) -> i32 { let mut g = m.lock(); g.get_mut().* = 5; held.send(0); let _a = c.recv(); g.get_mut().* = 6; g.unlock(); return 0; }
fn take(m: &Mutex[i32], held: &Channel[i32], c: &Channel[i32]) -> i32 { let _h = held.recv(); c.send(1); let mut g = m.lock(); let v = g.get_mut().*; g.unlock(); return v; }
fn picks(a: &Channel[i32], b: &Channel[i32]) -> i32 { return @select { v = a.recv() => 1, w = b.recv() => 2 }; }
fn cross(a: &Channel[i32], b: &Channel[i32]) -> i32 { let v = a.recv(); b.send(v); return v; }
fn relock(m: &Mutex[i32]) -> i32 { let mut g = m.lock(); let v = g.get_mut().*; g.unlock(); return v; }
";
    for (name, body, value) in [
        ("channel", "let c = Channel[i32]::with_capacity(1); let f = spawn_scoped(fn() -> i32 { return feed(&c, 20); }); let a = add_up(&c, 20); return a + f.join();", 210),
        ("select", "let a = Channel[i32]::new(); let b = Channel[i32]::new(); let t = spawn_scoped(fn() -> i32 { return picks(&a, &b); }); b.send(1); return t.join();", 2),
        // A lock held across a wait is waited for.
        ("mutex", "let m = Mutex[i32]::new(1); let held = Channel[i32]::new(); let c = Channel[i32]::new(); let h = spawn_scoped(fn() -> i32 { return hold(&m, &held, &c); }); let v = take(&m, &held, &c); return v + h.join();", 6),
        ("sleep", "let start = now_ms(); sleep_ms(2); return (now_ms() - start >= 2) as i32;", 1),
    ] {
        assert_runs(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}"), value);
    }
    // Threads waiting for each other with nothing left to wake them deadlock, which the VM says.
    for (name, body) in [
        ("each_waits_for_the_other", "let a = Channel[i32]::new(); let b = Channel[i32]::new(); let x = spawn_scoped(fn() -> i32 { return cross(&a, &b); }); let y = cross(&b, &a); return y + x.join();"),
        ("waiting_for_a_lock_held_by_the_waiter", "let m = Mutex[i32]::new(1); let c = Channel[i32]::new(); let g = m.lock(); let y = spawn_scoped(fn() -> i32 { return relock(&m); }); let _v = c.recv(); g.unlock(); return y.join();"),
    ] {
        let src = format!("{prelude}pub fn main() -> i32 {{ {body} }}");
        assert!(super::run_vm(name, &src).is_err_and(|e| !e.contains("step limit")), "[{name}]");
    }
    // Two threads handing a value back and forth wake each other thousands of times.
    let ping = "fn ping(to: &Channel[i32], from: &Channel[i32], n: i32) -> i32 { let mut sum: i32 = 0; for i in 0..n { to.send(i); let v = from.recv(); sum = (sum + v) % 1000; } return sum; }
fn pong(from: &Channel[i32], to: &Channel[i32], n: i32) -> i32 { for i in 0..n { let v = from.recv(); to.send(v + 1); } return 0; }
pub fn main() -> i32 { let a = Channel[i32]::new(); let b = Channel[i32]::new(); let q = spawn_scoped(fn() -> i32 { return pong(&a, &b, 300); }); let s = ping(&a, &b, 300); return s + q.join(); }";
    assert_runs("ping_pong", ping, 150);
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
    let t = spawn_scoped(move fn() -> i32 {{ unsafe {{ (addr as *mut i32).* = 1; let _a = {op}(&raw mut C, 1); }} return 0; }});
    let _b = unsafe {{ {op}(&raw mut C, 1) }};
    let v = unsafe {{ (addr as *mut i32).* }};
    return v * 0 + t.join();
}}"
        )
    };
    let err = super::run_vm("relaxed", &racy("@atomic_add_relaxed")).expect_err("race");
    assert!(err.contains("data race"), "{err}");
}

#[test]
fn test_tcp() {
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
    let conn = connect_to(\"127.0.0.1\", port) catch |e| match e { .Failed => return 7 };
    return 1;
}
extern fn fcntl(fd: i32, command: i32, arg: i32) -> i32;
fn closed_port() -> u16 { let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 0; return l.port(); }
";
    for (name, body, value) in [
        ("echo", "let listener = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let port = listener.port(); let server = spawn_scoped(fn() -> i32 { return echo(&listener); }); let a = client(port); return a + server.join();", 45),
        ("refused", "return try_connect(closed_port());", 7),
        ("bad_host", "let c = connect_to(\"not.an.address\", 80) catch |e| return 7; return 1;", 7),
        ("bind_bad_host", "if let ?l = TcpListener::bind(\"nope\", 0) { return 1; } return 7;", 7),
        // A connection is non-blocking underneath; a read or write that would block waits.
        ("stays_non_blocking", "let l = TcpListener::bind(\"127.0.0.1\", 0) orelse return 200; let c = connect_to(\"127.0.0.1\", l.port()) catch |e| return 90; return (unsafe { fcntl(c.raw(), 3, 0) } & 2048) / 2048;", 1),
    ] {
        assert_eq!(run_lli(name, &format!("{prelude}pub fn main() -> i32 {{ {body} }}")), Some(value), "[{name}]");
    }
}

#[test]
fn test_threads_under_other_interleavings() {
    let prelude = "fn add_up(c: &Channel[i32], n: i32) -> i32 { let mut t: i32 = 0; for i in 0..n { t = t + c.recv(); } return t; }
fn feed(c: &Channel[i32], n: i32) -> i32 { for i in 0..n { c.send(i); } return n; }
fn bump(m: &Mutex[i32], n: i32) -> i32 { for i in 0..n { let mut g = m.lock(); let v = g.get_mut(); v.* = v.* + 1; g.unlock(); } return 0; }
";
    // The same programs under other interleavings, where the VM reports races and deadlocks.
    for body in [
        "let c = Channel[i32]::with_capacity(1); let f = spawn_scoped(fn() -> i32 { return feed(&c, 3); }); let a = spawn_scoped(fn() -> i32 { return add_up(&c, 3); }); let n = f.join(); return a.join() + n;",
        "let m = Mutex[i32]::new(0); let a = spawn_scoped(fn() -> i32 { return bump(&m, 3); }); let b = spawn_scoped(fn() -> i32 { return bump(&m, 3); }); let _x = a.join(); let _y = b.join(); let mut g = m.lock(); let v = g.get_mut().*; g.unlock(); return v + 0;",
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
    // Each spins until it has seen the other, so only threads that really run at once finish.
    let together = "static mut A: u32 = 0;
static mut B: u32 = 0;
fn left() -> i32 { unsafe { @atomic_store(&raw mut A, 1); while @atomic_load(&raw mut B) == 0 { } } return 1; }
fn right() -> i32 { unsafe { @atomic_store(&raw mut B, 1); while @atomic_load(&raw mut A) == 0 { } } return 2; }
pub fn main() -> i32 { let a = spawn(move fn() -> i32 { return left(); }); let b = spawn(move fn() -> i32 { return right(); }); return a.join() + b.join(); }";
    assert_eq!(run_lli("really_parallel", together), Some(3));
}

#[test]
fn test_atomic_stores_keep_to_their_width() {
    // Each store must leave the static after it alone, which a wider one would overwrite.
    for ty in ["u8", "u16", "u32", "u64", "i8", "i16", "i32"] {
        assert_runs(
            ty,
            &format!(
                "static mut A: [{ty}; 2] = .{{ 9, 9 }};
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
fn test_wakes_between_threads_are_fast() {
    // Natively: thousands of wakes between threads in a time that only direct wakes can manage.
    let src = "fn ping(a: &Channel[i32], b: &Channel[i32], n: i32) -> i32 { for i in 0..n { a.send(i); let _r = b.recv(); } return 0; }
fn pong(a: &Channel[i32], b: &Channel[i32], n: i32) -> i32 { for i in 0..n { let r = a.recv(); b.send(r); } return 0; }
fn bump(m: &Mutex[i32], n: i32) -> i32 { for i in 0..n { let mut g = m.lock(); let v = g.get_mut(); v.* = v.* + 1; g.unlock(); } return 0; }
fn bump_on_threads(m: &Mutex[i32], left: i32) {
    if left == 0 { return; }
    let t = spawn_scoped(fn() -> i32 { return bump(m, 3000); });
    bump_on_threads(m, left - 1);
    _ = t.join();
}
pub fn main() -> i32 {
    let a = Channel[i32]::with_capacity(1);
    let b = Channel[i32]::with_capacity(1);
    let start = now_ms();
    let y = spawn_scoped(fn() -> i32 { return pong(&a, &b, 3000); });
    let _u = ping(&a, &b, 3000);
    let _v = y.join();
    let m = Mutex[i32]::new(0);
    bump_on_threads(&m, 8);
    let mut g = m.lock();
    let total = g.get_mut().*;
    g.unlock();
    if total != 24000 { return 2; }
    return (now_ms() - start > 1500) as i32;
}";
    assert_eq!(run_lli("fast_wakes", src), Some(0));
}

#[test]
fn test_wakes_between_threads_are_not_missed() {
    // A thread that waits for another waits on its condition before it lets go of the lock, so a
    // wake straight after cannot pass it by. The clock is stopped here, so a missed wake would
    // never be made up for and such a program would never finish. The seeds that catch a wrong
    // order are among those that keep one thread running long enough to fit in the window.
    for (name, src) in [
        // `Channel` waits on a condition.
        ("condition", "fn ping(a: &Channel[i32], b: &Channel[i32], n: i32) -> i64 {
    for i in 0..n { a.send(i); let _r = b.recv(); }
    return 0;
}
fn pong(a: &Channel[i32], b: &Channel[i32], n: i32) -> i64 {
    for i in 0..n { let v = a.recv(); b.send(v); }
    return 0;
}
pub fn main() -> i32 {
    let a = Channel[i32]::new();
    let b = Channel[i32]::new();
    let x = spawn_scoped(fn() -> i32 { return ping(&a, &b, 20) as i32; });
    let y = spawn_scoped(fn() -> i32 { return pong(&a, &b, 20) as i32; });
    return x.join() + y.join();
}"),
        // Each round, one task tries the lock just as the other lets go of it.
        ("lock", "fn holder(m: &Mutex[i32], c: &[Channel[i32]; 3], n: i32) -> i64 {
    for i in 0..n {
        let g = m.lock();
        c[0].send(i);
        let _trying = c[1].recv();
        g.unlock();
        let _done = c[2].recv();
    }
    return 0;
}
fn waiter(m: &Mutex[i32], c: &[Channel[i32]; 3], n: i32) -> i64 {
    for i in 0..n {
        let _held = c[0].recv();
        c[1].send(i);
        let g = m.lock();
        g.unlock();
        c[2].send(i);
    }
    return 0;
}
pub fn main() -> i32 {
    let m = Mutex[i32]::new(0);
    let c: [Channel[i32]; 3] = [_; _]{ Channel[i32]::new(), Channel[i32]::new(), Channel[i32]::new() };
    let x = spawn_scoped(fn() -> i32 { return holder(&m, &c, 20) as i32; });
    let y = spawn_scoped(fn() -> i32 { return waiter(&m, &c, 20) as i32; });
    return x.join() + y.join();
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
fn test_review_fixes_for_select_and_cells() {
    // `try` on a `@select` whose arms give their own error: it gives what its arms do.
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
    a.send(4);
    return (first(&a, &b) catch 0) - 8;
}",
        0,
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
fn f() -> i32 { return C.get_or_init(three).*; }
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
fn test_once_cell_lazy_cell_once_lock_and_lazy_lock() {
    assert_runs(
        "once_cell_and_lazy_cell_lifecycle",
        "static mut DROPPED: i32 = 0;
static mut CLOSURE_DROPPED: i32 = 0;

pub opaque Tracked {
    v: i32,
    impl drop {
        fn drop(&mut self) {
            unsafe { DROPPED += self.v; }
        }
    }
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    pub fn val(&self) -> i32 { return self.v; }
    pub fn add(&mut self, d: i32) { self.v += d; }
}

pub opaque Guard {
    tag: i32,
    impl drop {
        fn drop(&mut self) {
            unsafe { CLOSURE_DROPPED += self.tag; }
        }
    }
    pub fn new(tag: i32) -> Self { return Self { tag: tag }; }
    pub fn get(&self) -> i32 { return self.tag; }
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
        if let ?rejected = c.set(Tracked::new(10)) {
            return 1;
        }
        if let ?rejected = c.set(Tracked::new(3)) {
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
    let v1 = c2.get_or_init(fn() -> i32 { calls += 1; return 77; }).*;
    let v2 = c2.get_or_init(fn() -> i32 { calls += 1; return 99; }).*;
    @assert(v1 == 77 && v2 == 77 && calls == 1);
    @assert((c2.into_inner() orelse 0) == 77);

    // 5. LazyCell with function pointer default and with capturing closure.
    let l_fn = LazyCell[i32]::new(make_forty_two);
    @assert(!l_fn.is_initialized());
    @assert(l_fn.get().* == 42);
    @assert(l_fn.is_initialized());
    @assert((l_fn.into_inner() orelse 0) == 42);

    // Unforced LazyCell drops its captured closure and does not drop T.
    unsafe { DROPPED = 0; CLOSURE_DROPPED = 0; }
    if true {
        let g = Guard::new(7);
        let f = move fn() -> Tracked { return Tracked::new(g.get() * 10); };
        let _unforced = LazyCell[Tracked, @type_of(f)]::new(f);
    }
    @assert(unsafe { CLOSURE_DROPPED } == 7 && unsafe { DROPPED } == 0);

    // Forced LazyCell drops its closure when forced and drops T when the cell drops.
    unsafe { DROPPED = 0; CLOSURE_DROPPED = 0; }
    if true {
        let g = Guard::new(4);
        let f = move fn() -> Tracked { return Tracked::new(g.get() * 10); };
        let mut forced = LazyCell[Tracked, @type_of(f)]::new(f);
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
        "static_once_lock_and_lazy_lock_with_threads",
        "static mut INIT_COUNT: i32 = 0;
static mut ONCE_INIT_COUNT: i32 = 0;
static mut STR_INIT_COUNT: i32 = 0;

fn compute_config() -> i32 {
    let _old = unsafe { @atomic_add(&raw mut INIT_COUNT, 1) };
    sleep_ms(3);
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
static SLOW_LAZY: LazyLock[i32] = LazyLock[i32]::new(fn() -> i32 {
    sleep_ms(3);
    return 321;
});

fn slow_reader() -> i32 {
    return SLOW_LAZY.get().*;
}

pub fn main() -> i32 {
    @assert(!CONFIG.is_initialized());
    @assert((PRESET_ONCE.get() orelse unreachable).* == 55);

    // Multi-threaded contention on `LazyLock` and `OnceLock`.
    let t1 = spawn_scoped(fn() -> i32 {
        let a = CONFIG.get().*;
        let b = SHARED_ONCE.get_or_init(fn() -> i32 {
            let _old = unsafe { @atomic_add(&raw mut ONCE_INIT_COUNT, 1) };
            sleep_ms(2);
            return 77;
        }).*;
        return a + b;
    });
    let t2 = spawn_scoped(fn() -> i32 {
        let a = CONFIG.get().*;
        let b = SHARED_ONCE.get_or_init(fn() -> i32 {
            let _old = unsafe { @atomic_add(&raw mut ONCE_INIT_COUNT, 1) };
            return 88;
        }).*;
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

    // Two threads waiting for one slow initialization.
    let f1 = spawn_scoped(fn() -> i32 { return slow_reader(); });
    let f2 = spawn_scoped(fn() -> i32 { return slow_reader(); });
    @assert(f1.join() + f2.join() == 642);

    return 0;
}",
        0,
    );

    // Reentrant initialization traps for OnceCell, LazyCell, OnceLock, and LazyLock.
    let reentrant_once_cell = "pub fn main() -> i32 {
    let c = OnceCell[i32]::new();
    return c.get_or_init(fn() -> i32 {
        return c.get_or_init(fn() -> i32 { return 1; }).*;
    }).*;
}";
    assert_eq!(run_lli("reentrant_once_cell", reentrant_once_cell), Some(TRAP_EXIT));

    let reentrant_once_lock = "static LOCK: OnceLock[i32] = OnceLock[i32]::new();
pub fn main() -> i32 {
    return LOCK.get_or_init(fn() -> i32 {
        return LOCK.get_or_init(fn() -> i32 { return 1; }).*;
    }).*;
}";
    assert_eq!(run_lli("reentrant_once_lock", reentrant_once_lock), Some(TRAP_EXIT));

    let reentrant_lazy_lock = "fn bad() -> i32 { return LAZY.get().*; }
static LAZY: LazyLock[i32] = LazyLock[i32]::new(bad);
pub fn main() -> i32 { return LAZY.get().*; }";
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

/// A thread's result too big for a pointer has its room before the thread starts, so a thread
/// allocates nothing of its own.
#[test]
fn test_thread_results_without_traps() {
    assert_runs(
        "big_results",
        "struct Big { a: i64, b: i64, c: i64 }
pub fn main() -> i32 {
    let h = try_spawn(move fn() -> Big { return Big { a: 10, b: 20, c: 2 }; }) catch |e| return 1;
    let g = spawn(move fn() -> Big { return Big { a: 1, b: 1, c: 0 }; });
    let x = h.join();
    let y = g.join();
    return (x.a + x.b + x.c + y.c) as i32 + 10;
}",
        42,
    );
}

/// `@volatile_load` / `@volatile_store`: one access each, of a value of 1, 2, 4, or 8 bytes,
/// emitted as LLVM's volatile instructions; and `secure_zero`, which wipes with them.
#[test]
fn test_volatile_accesses() {
    assert_runs("volatile", "packed struct Ctrl { enable: bool, mode: u3, count: u12 }
pub fn main() -> i32 {
    let mut reg: u32 = 0;
    let mut c: Ctrl = .{ enable: false, mode: 0, count: 0 };
    let mut x: f64 = 1.5;
    unsafe {
        let p = &raw mut reg;
        @volatile_store(p, 40);
        @volatile_store(p, @volatile_load(p) + 2);
        let q = &raw mut c;
        @volatile_store(q, .{ enable: true, mode: 3, count: 7 });
        let r = @volatile_load(q);
        @assert(r.enable && r.mode == 3 && r.count == 7);
        let f = &raw mut x;
        @assert(@volatile_load(f) == 1.5);
        return @volatile_load(p as *const u32) as i32;
    }
}
", 42);
    assert_runs("secure_zero", "enum Mode { Off, On }
pub fn main() -> i32 {
    let mut key: [u8; 4] = .{ 1, 2, 3, 4 };
    secure_zero(&mut key[0..4]);
    let mut v = Vec[u8]::new();
    v.push(9);
    v.push(8);
    secure_zero(v.as_mut_slice());
    let mut m = Mode::On;
    unsafe { @volatile_store(&raw mut m, Mode::Off); @assert(@volatile_load(&raw mut m) == Mode::Off); }
    oomsafe { let mut b: [u8; 2] = .{ 5, 6 }; secure_zero(&mut b[0..2]); }
    return (key[0] + key[3] + (v.get(1) orelse unreachable).*) as i32 + 42;
}
", 42);
    let program = Compiler::compile_source("packed struct Ctrl { enable: bool, mode: u3, count: u12 }
pub fn main() -> i32 {
    let mut reg: u32 = 0;
    let mut c: Ctrl = .{ enable: false, mode: 0, count: 0 };
    let mut x: f64 = 1.5;
    unsafe {
        let p = &raw mut reg;
        @volatile_store(p, 40);
        @volatile_store(p, @volatile_load(p) + 2);
        let q = &raw mut c;
        @volatile_store(q, .{ enable: true, mode: 3, count: 7 });
        let r = @volatile_load(q);
        @assert(r.enable && r.mode == 3 && r.count == 7);
        let f = &raw mut x;
        @assert(@volatile_load(f) == 1.5);
        return @volatile_load(p as *const u32) as i32;
    }
}
").unwrap();
    let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, super::TRAP_EXIT).unwrap();
    assert!(ir.contains("load volatile i32") && ir.contains("store volatile i32"), "{ir}");
    let refused = [
        ("let mut r: u32 = 0; let p = &raw mut r; let v = @volatile_load(p); return 0;", "requires an 'unsafe { ... }' block"),
        ("let r: u32 = 0; let p = &raw const r; unsafe { @volatile_store(p, 1); } return 0;", "needs '*mut'"),
        ("let mut r: [u64; 2] = .{ 0, 0 }; let p = &raw mut r; unsafe { let v = @volatile_load(p); } return 0;", "accesses one value of 1, 2, 4, or 8 bytes"),
        ("let mut r: u32 = 0; unsafe { let v = @volatile_load(&r); } return 0;", "expects a raw pointer"),
    ];
    for (i, (body, what)) in refused.iter().enumerate() {
        assert_rejected(&format!("volatile_refused_{i}"), &format!("pub fn main() -> i32 {{ {body} }}"), what);
    }
}


#[test]
fn test_waits_on_different_threads_overlap_in_virtual_time() {
    // Two threads sleeping 10 ms at once take 10 ms, and a timed condition wait (a `@select`
    // with a timer) ends when it is signalled, 5 ms in, not at its timeout.
    let src = "fn nap() -> i32 { sleep_ms(10); return 0; }
pub fn main() -> i32 {
    let start = now_ms();
    let a = spawn(move fn() -> i32 { return nap(); });
    let b = spawn(move fn() -> i32 { return nap(); });
    let _x = a.join();
    let _y = b.join();
    let slept = now_ms() - start;
    let c = Channel[i32]::new();
    let t0 = now_ms();
    let h = spawn_scoped(fn() -> i32 { sleep_ms(5); c.send(7); return 0; });
    let got = @select { v = c.recv() => v, Timer::after_us(30000).wait() => -1 };
    let _j = h.join();
    let waited = now_ms() - t0;
    return (slept * 1000 + waited * 10) as i32 + got;
}";
    let run = super::run_vm("overlapping_waits", src).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(run.value, 10 * 1000 + 5 * 10 + 7);
}

#[test]
fn test_channels_hold_any_capacity_and_any_number_of_selects() {
    // A `@select` waiting on a channel is listed through its own `WaitNode`, so a dozen can
    // wait on one (a fixed list of eight left the rest waiting for good), and the buffer is as
    // large as asked (it was clamped to 64).
    assert_runs("many_selects_and_a_large_buffer", "fn picker(c: &Channel[i32], idle: &Channel[i32]) -> i32 {
    return @select { v = c.recv() => v, w = idle.recv() => -1000 };
}
fn many(c: &Channel[i32], idle: &Channel[i32], left: i32) -> i32 {
    if left == 0 {
        // Every picker is waiting, or about to be, before a value goes.
        sleep_ms(5);
        for i in 0..12 { c.send(1); }
        return 0;
    }
    let t = spawn_scoped(fn() -> i32 { return picker(c, idle); });
    let rest = many(c, idle, left - 1);
    return t.join() + rest;
}
pub fn main() -> i32 {
    let c = Channel[i32]::new();
    let idle = Channel[i32]::new();
    let got = many(&c, &idle, 12);
    let big = Channel[i32]::with_capacity(1000);
    for i in 0..1000 { if let ?v = big.try_send(i) { return 100; } }
    if let ?v = big.try_send(5) { } else { return 101; }
    let mut sum: i32 = 0;
    for i in 0..1000 { sum += big.recv(); }
    if sum != 499500 { return 102; }
    return got;
}", 12);
}
