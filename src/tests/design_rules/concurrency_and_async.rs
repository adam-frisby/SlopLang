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
    pub fn set(&self) { unsafe { let p = &raw mut self.m; *p = 1; } }
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
fn test_cancel_scopes() {
    let tx = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(self) -> i32 { return self.id; }
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
    pub fn commit(self) -> i32 { return self.id; }
}
";
    for (name, body, value) in [
        // Blocked with nothing to receive, until another thread cancels.
        ("recv_is_cancelled", "let s = CancelScope::new(); let c = Channel[i32]::new(); let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let r = s.run(fn() -> i32 { return c.recv() catch |e| 9; }); return r + t.join();", 9),
        ("send_is_cancelled_and_returns_the_value", "let s = CancelScope::new(); let c = Channel[i32]::with_capacity(1); let _a = c.send(1); let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let r = s.run(fn() -> i32 { if let ?v = c.send(7) { return v; } return 0; }); return r + t.join();", 7),
        ("linear_value_comes_back", "let s = CancelScope::new(); let c = Channel[Tx]::with_capacity(1); if let ?u = c.send(Tx::new(1)) { let _x = u.commit(); } let t = spawn_scoped(fn() -> i32 { s.cancel(); return 0; }); let cr = &c; let f = Tx::new(8); let r = s.run(move fn() -> i32 { if let ?v = cr.send(f) { return v.commit(); } return 0; }); let _j = t.join(); c.close_and_drain(fn(u: Tx) { let _x = u.commit(); }); return r;", 8),
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
fn test_spawn_returns_results_wider_than_a_pointer() {
    // The result used to overrun a pointer-sized slot on the joining stack, which only the
    // native run shows.
    assert_runs(
        "wide_result",
        "struct B { a: i64, b: i64, c: i64 }
fn work() -> i64 {
    let t = spawn(move fn() -> B { return B { a: 11, b: 22, c: 33 }; });
    let guard: array[i64; 4] = [7, 7, 7, 7];
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
    pub fn commit(self) -> i32 { let n = self.n; unsafe { @forget(self); } return n; }
}
fn make_tx() -> Tx { return Tx::new(4); }
fn commit(t: Tx) -> i32 { return t.commit(); }
pub struct C {
    n: i32,
    pub fn get(&self) -> i32 { return self.n; }
    pub fn bump(&mut self) -> i32 { self.n = self.n + 1; return self.n; }
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
    pub fn set_a(&self) { unsafe { *(&raw mut self.a) = 1; } }
    pub fn get_b(&self) -> i32 { return unsafe { *(&raw mut self.b) }; }
    pub fn get_a(&self) -> i32 { return unsafe { *(&raw mut self.a) }; }
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

#[test]
fn test_fibers() {
    let prelude = "fn sq(a: i32) -> i32 { return a * a; }
fn int_of(o: ?i32) -> i32 { if let ?x = o { return x; } return -1; }
fn add_up(c: &Channel[i32], n: i32) -> i32 { let mut t: i32 = 0; for i in 0..n { t = t + (c.recv() catch |e| 0); } return t; }
fn feed(c: &Channel[i32], n: i32) -> i32 { for i in 0..n { let _s = c.send(i); } return n; }
fn wait(c: &Channel[i32]) -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 7 }; }
fn deep(c: &Channel[i32], n: i32) -> i32 { if n == 0 { return c.recv() catch |e| 0; } return deep(c, n - 1) + 1; }
trait Source { fn next(&self) -> i32; }
pub struct Reader { c: Channel[i32], impl Source { fn next(&self) -> i32 { return self.c.recv() catch |e| 0; } } }
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
        ("many", "let mut hs = Vec[Task[i32]]::new(); for i in 0..50 { hs.push(async(Fibers { }) sq(2)); } let mut t: i32 = 0; while let ?h = hs.pop() { t = t + h.await(); } return t / 4;", 50),
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
fn test_a_fiber_overflowing_its_stack_faults() {
    // The guard page stops it. This overflows by a little, into the next fiber's stack below, so
    // without the guard it finishes normally, having written over that stack: about 500 frames fit.
    let src = "fn down(n: i32) -> i64 {
    let frame = @default(array[i64; 2048]);
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
fn test_tcp_on_fibers() {
    let prelude = "fn echo(listener: &TcpListener) -> i32 {
    let conn = listener.accept() catch |e| return 1;
    let mut buf: array[u8; 16] = @default(array[u8; 16]);
    let n = conn.read(&mut buf) catch |e| return 2;
    let _a = conn.write_all(\"pong\") catch |e| return 3;
    return n as i32;
}
fn client(port: u16) -> i32 {
    let conn = connect_to(\"127.0.0.1\", port) catch |e| return 90;
    let _a = conn.write_all(\"ping!\") catch |e| return 91;
    let mut buf: array[u8; 16] = @default(array[u8; 16]);
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
        ("bind_bad_host", "if let ?l = TcpListener::bind(\"nope\", 0) { return 1; } return 7;", 7),
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
fn test_worker_pools() {
    let prelude = "fn sq(a: i32) -> i32 { return a * a; }
fn add_up(c: &Channel[i32], n: i32) -> i32 { let mut t: i32 = 0; for i in 0..n { t = t + (c.recv() catch |e| 0); } return t; }
fn feed(c: &Channel[i32], n: i32) -> i32 { for i in 0..n { let _s = c.send(i); } return n; }
fn wait(c: &Channel[i32]) -> i32 { return c.recv() catch |e| match e { .TimedOut => 2, .Cancelled => 7 }; }
fn bump(m: &Mutex[i32], n: i32) -> i32 { for i in 0..n { let mut g = m.lock(); let v = g.get_mut(); *v = *v + 1; g.unlock(); } return 0; }
fn nap(ms: i64) -> i32 { let _a = sleep_ms(ms) catch |e| return 1; return 0; }
fn nested(p: &WorkerPool, a: i32) -> i32 { let t = async(p) sq(a); return t.await() + 1; }
fn owned(v: Vec[i32]) -> Vec[i32] { let mut w = v; w.push(2); return w; }
";
    for (name, body, value) in [
        ("one_task", "let p = WorkerPool::new(2); let t = async(&p) sq(3); return t.await();", 9),
        ("many_tasks", "let p = WorkerPool::new(2); let mut ts = Vec[Task[i32]]::new(); for i in 0..6 { ts.push(async(&p) sq(2)); } let mut t: i32 = 0; while let ?h = ts.pop() { t = t + h.await(); } return t;", 24),
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
    let burst = format!("{prelude}pub fn main() -> i32 {{ let p = WorkerPool::new(1); let mut cs = Vec[Channel[i32]]::new(); for i in 0..40 {{ cs.push(Channel[i32]::new()); }} let mut ts = Vec[Task[i32]]::new(); for i in 0..40 {{ ts.push(async(&p) wait(cs.get(i as usize) orelse unreachable)); }} let _a = sleep_ms(2); let start = now_ms(); for i in 0..40 {{ let _s = (cs.get(i as usize) orelse unreachable).send(1); }} let mut t: i32 = 0; while let ?h = ts.pop() {{ t = t + h.await(); }} if t != 40 {{ return 200; }} return (now_ms() - start) as i32; }}");
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
                "static mut A: array[{ty}; 2] = [9, 9];
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
    while let ?t = ts.pop() { let _w = t.await(); }
    let mut g = m.lock();
    let total = *g.get_mut();
    g.unlock();
    if total != 24000 { return 2; }
    return (now_ms() - start > 1500) as i32;
}";
    assert_eq!(run_lli("fast_wakes", src), Some(0));
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
        ("lock", "fn holder(m: &Mutex[i32], c: &array[Channel[i32]; 3], n: i32) -> i64 {
    for i in 0..n {
        let g = m.lock();
        let _held = c[0].send(i);
        let _trying = c[1].recv() catch |e| 0;
        g.unlock();
        let _done = c[2].recv() catch |e| 0;
    }
    return 0;
}
fn waiter(m: &Mutex[i32], c: &array[Channel[i32]; 3], n: i32) -> i64 {
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
    let c: array[Channel[i32]; 3] = [Channel[i32]::new(), Channel[i32]::new(), Channel[i32]::new()];
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
fn test_nosuspend_blocks() {
    // `nosuspend { ... }` holds a block to not waiting: no fiber parks in it, and no thread blocks
    // on a lock, a condition, a join, a sleep, or a poll. The error shows the way it would.
    let prelude = "fn add(a: i32, b: i32) -> i32 { return a + b; }
fn locks(m: &Mutex[i32]) -> i32 { let g = m.lock(); g.unlock(); return 1; }
opaque Waits { m: Mutex[i32],
    pub fn new() -> Self { return Self { m: Mutex[i32]::new(0) }; }
    impl drop { fn drop(&mut self) { let g = self.m.lock(); g.unlock(); } } }
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
        ("a_drop", "let w = Waits::new(); nosuspend { let x = w; }", "Waits"),
        // Each way of waiting alone: a fiber parking, and a thread blocking in C.
        ("parks", "nosuspend { let _y = std::sync::fiber_yield(); }", "std::sync::fiber_yield -> std::sync::switch_fiber"),
        ("blocks_in_c", "nosuspend { let _r = unsafe { usleep(10) }; }", "usleep"),
    ] {
        let src = format!("extern fn usleep(us: u32) -> i32;\n{prelude}pub fn main() -> i32 {{ {body} return 0; }}");
        assert_rejected(name, &src, path);
    }
}

#[test]
fn test_uncancelled_select_cancellation_and_task_select() {
    let prelude = "pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(self) -> i32 { return self.id; }
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
                    if let ?u = c.send(4) { return 92; }
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
                        if let ?u = c.send(tx) { return u.commit() + 100; }
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
            if let ?u = full.send(Tx::new(1)) { let _x = u.commit(); }
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

/// A thread's result too big for a pointer has its room before the thread starts, so a thread
/// allocates nothing of its own; and a worker pool can be made fallibly.
#[test]
fn test_thread_results_and_pools_without_traps() {
    assert_runs(
        "big_results_and_pool",
        "struct Big { a: i64, b: i64, c: i64 }
fn work(n: i32) -> i32 { return n * 2; }
pub fn main() -> i32 {
    let h = try_spawn(move fn() -> Big { return Big { a: 10, b: 20, c: 2 }; }) catch |e| return 1;
    let g = spawn(move fn() -> Big { return Big { a: 1, b: 1, c: 0 }; });
    let x = h.join();
    let y = g.join();
    let pool = WorkerPool::try_new(2) catch |e| return 2;
    let t = async(&pool) work(4);
    return (x.a + x.b + x.c + y.c) as i32 + t.await() + 2;
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
    let mut key: array[u8; 4] = [1, 2, 3, 4];
    secure_zero(&mut key[0..4]);
    let mut v = Vec[u8]::new();
    v.push(9);
    v.push(8);
    secure_zero(v.as_mut_slice());
    let mut m = Mode::On;
    unsafe { @volatile_store(&raw mut m, Mode::Off); @assert(@volatile_load(&raw mut m) == Mode::Off); }
    oomsafe { let mut b: array[u8; 2] = [5, 6]; secure_zero(&mut b[0..2]); }
    return (key[0] + key[3] + *(v.get(1) orelse unreachable)) as i32 + 42;
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
        ("let mut r: array[u64; 2] = [0, 0]; let p = &raw mut r; unsafe { let v = @volatile_load(p); } return 0;", "accesses one value of 1, 2, 4, or 8 bytes"),
        ("let mut r: u32 = 0; unsafe { let v = @volatile_load(&r); } return 0;", "expects a raw pointer"),
    ];
    for (i, (body, what)) in refused.iter().enumerate() {
        assert_rejected(&format!("volatile_refused_{i}"), &format!("pub fn main() -> i32 {{ {body} }}"), what);
    }
}

