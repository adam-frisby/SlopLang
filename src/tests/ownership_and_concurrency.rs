
use crate::llvm::LlvmLowering;
use crate::lower::Compiler;
use super::{lli, link_ir};

#[test]
fn test_linear_structs_consuming_methods_shared_drop_and_contagion() {
    let src = "\
// 1. Overloads on structural kinds (`opaque` refines `type`) and on the cross-cutting `linear`
//    property; `linear` is incomparable with structural kinds, so it gets its own overload set:
pub fn kind_tag(comptime T: type, self: &T) -> i32 {
    return 1;
}
pub fn kind_tag(comptime A: aggregate, self: &A) -> i32 {
    return 2;
}
pub fn kind_tag(comptime S: opaque, self: &S) -> i32 {
    return 3;
}
pub fn linearity_tag(comptime T: type, self: &T) -> i32 {
    return 1;
}
pub fn linearity_tag(comptime L: linear, self: &L) -> i32 {
    return 4;
}

pub opaque NormalBox {
    val: i32,
    pub fn new(v: i32) -> Self {
        return Self { val: v };
    }
}

// 2. Must-consume `opaque(linear)` with multiple consuming `move self` methods and shared `drop` cleanup:
pub opaque(linear) Transaction {
    id: i32,
    log: &mut i32,

    pub fn begin(id: i32, log: &mut i32) -> Self {
        return Self { id: id, log: log };
    }

    pub fn peek_id(self: &Self) -> i32 {
        return self.id;
    }

    pub fn commit(move self) -> i32 {
        *self.log += 10;
        return self.id;
        // Shared `drop(self: &mut Self)` runs automatically here (+100 to `*self.log`)!
    }

    pub fn rollback(move self) -> i32 {
        *self.log += 1;
        return 0;
        // Shared `drop(self: &mut Self)` runs automatically here (+100 to `*self.log`)!
    }

    // Delegating consuming method: moves `self` into `commit()` or `rollback()`, so `drop` runs only ONCE!
    pub fn finish(move self, ok: bool) -> i32 {
        if ok {
            return self.commit();
        } else {
            return self.rollback();
        }
    }

    drop(self: &mut Self) {
        *self.cleanup_check();
        *self.log += 100;
    }

    fn cleanup_check(self: &mut Self) -> &mut i32 {
        return self.log;
    }
}

pub fn main() -> i32 {
    let nb = NormalBox::new(7);
    let tag_normal = nb.kind_tag(); // selects `opaque` (`opaque` refines `type`) -> 3

    // A. Consuming `Transaction` via `commit(move self)` and `rollback(move self)`:
    let mut log_a: i32 = 0;
    let mut res_a: i32 = 0;
    let mut tag_tx: i32 = 0;
    if true {
        let tx1 = Transaction::begin(5, &mut log_a);
        tag_tx = tx1.linearity_tag(); // selects `linear` (`linear` refines `type`) -> 4
        let peeked = tx1.peek_id();   // 5 (shared borrow `&self` does not consume `tx1`)
        res_a = peeked + tx1.commit(); // 5 + 5 = 10; `log_a` gets +10 (commit) + 100 (shared drop) = 110
    }

    // B. Path-sensitive branching & delegating `finish(move self, ok)`:
    let mut log_b: i32 = 0;
    let tx2 = Transaction::begin(9, &mut log_b);
    let res_b = tx2.finish(false); // 0; `log_b` gets +1 (rollback) + 100 (shared drop once!) = 101

    // C. Contagious linearity in a `tuple`:
    let mut log_c: i32 = 0;
    let mut res_c: i32 = 0;
    let mut tag_pair: i32 = 0;
    if true {
        let pair: tuple { i32, Transaction } = { 3, Transaction::begin(4, &mut log_c) };
        tag_pair = pair.linearity_tag(); // selects `linear` (contagious through the tuple) -> 4
        let extracted_tx = pair.1;       // moves linear leaf `.1` out of `pair`
        res_c = pair.0 + extracted_tx.commit(); // 3 + 4 = 7; `log_c` = 110; `pair` exits scope cleanly!
    }

    // D. Contagious linearity in `?Transaction` optional (`if let`):
    let mut log_d: i32 = 0;
    let mut res_d: i32 = 0;
    if true {
        let maybe_tx: ?Transaction = Transaction::begin(6, &mut log_d);
        if let tx = maybe_tx {
            res_d = tx.commit(); // 6; `log_d` = 110
        }
    }

    // E. Contagious linearity in a single-use `move fn` closure (`FnOnce`):
    let mut log_e: i32 = 0;
    let mut res_e: i32 = 0;
    if true {
        let tx_cap = Transaction::begin(8, &mut log_e);
        let consume_once = move fn(bonus: i32) -> i32 {
            return tx_cap.commit() + bonus;
        };
        res_e = consume_once(2); // 8 + 2 = 10; `log_e` = 110
    }

    // Total:
    //   tags  = 3 + 4 + 4 = 11
    //   res   = 10 + 0 + 7 + 6 + 10 = 33
    //   logs  = (110 + 101 + 110 + 110 + 110) / 10 = 54
    //   Sum   = 11 + 33 + 54 = 98
    let logs_scaled = (log_a + log_b + log_c + log_d + log_e) / 10;
    return tag_normal + tag_tx + tag_pair + res_a + res_b + res_c + res_d + res_e + logs_scaled;
}
";

    let program =
        Compiler::compile_source(src).expect("Failed to compile linear opaque & shared drop test");
    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(98),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // 1. Verify that forgetting to consume a `opaque(linear)` before scope exit is rejected by Stage 3b:
    let bad_unconsumed_src = "\
pub opaque(linear) Ticket {
    code: i32,
    pub fn new(c: i32) -> Self { return Self { code: c }; }
    pub fn redeem(move self) -> i32 { return self.code; }
}
pub fn main() -> i32 {
    let t = Ticket::new(42);
    return 0;
}
";
    let err1 = Compiler::compile_source(bad_unconsumed_src)
        .expect_err("Expected unconsumed `Ticket` at scope exit to fail Stage 3b drop check");
    assert!(
        err1.contains("Linear value")
            && err1.contains("Ticket")
            && err1.contains("must be explicitly consumed"),
        "Unexpected error: {err1}"
    );

    // 2. Verify that consuming a `opaque(linear)` on only ONE branch of an `if`/`else` is rejected:
    let bad_partial_branch_src = "\
pub opaque(linear) Ticket {
    code: i32,
    pub fn new(c: i32) -> Self { return Self { code: c }; }
    pub fn redeem(move self) -> i32 { return self.code; }
}
pub fn run(flag: bool) -> i32 {
    let t = Ticket::new(42);
    if flag {
        return t.redeem();
    }
    return 0;
}
pub fn main() -> i32 {
    return run(true);
}
";
    let err2 = Compiler::compile_source(bad_partial_branch_src).expect_err(
        "Expected consuming `Ticket` on only one branch of `if` to fail Stage 3b drop check",
    );
    assert!(
        err2.contains("Linear value")
            && err2.contains("Ticket")
            && err2.contains("must be explicitly consumed"),
        "Unexpected error: {err2}"
    );

    // 3. Verify that forgetting to consume a `tuple` or `?Ticket` containing a `opaque(linear)` is rejected:
    let bad_tuple_src = "\
pub opaque(linear) Ticket {
    code: i32,
    pub fn new(c: i32) -> Self { return Self { code: c }; }
    pub fn redeem(move self) -> i32 { return self.code; }
}
pub fn main() -> i32 {
    let pair: tuple { i32, Ticket } = { 1, Ticket::new(10) };
    return pair.0;
}
";
    let err3 = Compiler::compile_source(bad_tuple_src).expect_err(
        "Expected unconsumed linear element inside `tuple` to fail Stage 3b drop check",
    );
    assert!(
        err3.contains("Linear value")
            && err3.contains("Ticket")
            && err3.contains("must be explicitly consumed"),
        "Unexpected error: {err3}"
    );

    // 4. Verify that calling a single-use `move fn` linear closure twice is rejected as a use-after-move:
    let bad_closure_twice_src = "\
pub opaque(linear) Ticket {
    code: i32,
    pub fn new(c: i32) -> Self { return Self { code: c }; }
    pub fn redeem(move self) -> i32 { return self.code; }
}
pub fn main() -> i32 {
    let t = Ticket::new(10);
    let f = move fn() -> i32 {
        return t.redeem();
    };
    let a = f();
    let b = f();
    return a + b;
}
";
    let err4 = Compiler::compile_source(bad_closure_twice_src).expect_err(
        "Expected calling a linear `move fn` closure twice to fail Stage 3b move check",
    );
    assert!(
        err4.contains("Use of moved or uninitialized value"),
        "Unexpected error: {err4}"
    );

    // 5. Verify that defining `clone` on a `opaque(linear)` is rejected at compile time:
    let bad_clone_linear_src = "\
pub opaque(linear) Ticket {
    code: i32,
    clone(self: &Self) -> Self {
        return Self { code: self.code };
    }
}
pub fn main() -> i32 { return 0; }
";
    let err5 = Compiler::compile_source(bad_clone_linear_src)
        .expect_err("Expected `clone` hook on `opaque(linear)` to fail compilation");
    assert!(
        err5.contains("Linear opaque 'Ticket' cannot implement `clone`"),
        "Unexpected error: {err5}"
    );
}

#[test]
fn test_rel_references_slices_str_and_nll_borrows() {
    let src = "\
pub opaque InlinePacket {
    nums: [i32; 4],
    buf: [u8; 6],
    focus: &rel i32,
    window: &rel [i32],
    label: &rel str,

    pub fn new(a: i32, b: i32, c: i32, d: i32) -> Self {
        return Self {
            nums: { a, b, c, d },
            buf: { 79, 75, 95, 82, 69, 76 },
            focus: &rel self.nums[1],
            window: &rel self.nums[1..4],
            label: &rel self.buf[0..2],
        };
    }

    pub fn read_focus(self: &Self) -> i32 {
        return *self.focus;
    }

    pub fn get_window(self: &Self) -> &[i32] {
        return self.window;
    }

    pub fn get_label(self: &Self) -> &str {
        return self.label;
    }

    pub fn add_to_focus(self: &mut Self, delta: i32) {
        *self.focus += delta;
    }

    pub fn write_window_elem(self: &mut Self, idx: usize, val: i32) {
        self.window[idx] = val;
    }

    pub fn retarget(self: &mut Self, idx: usize, lo: usize, hi: usize) {
        self.focus = &rel self.nums[idx];
        self.window = &rel self.nums[lo..hi];
        self.label = &rel self.buf[3..6];
    }
}

pub fn bounce_by_value(pkt: InlinePacket) -> tuple { i32, InlinePacket } {
    return { 100, pkt };
}

pub fn main() -> i32 {
    let pkt1 = InlinePacket::new(10, 20, 30, 40);
    // Move `pkt1` by value through a function and into a `tuple { i32, InlinePacket }`,
    // then extract it into `pkt` at a completely different stack address!
    let pair = bounce_by_value(pkt1);
    let mut pkt = pair.1;

    // 1. Verify `&rel i32`, `&rel [i32]`, and `&rel str` resolve to `pkt`'s new address after moves:
    let f0 = pkt.read_focus(); // 20
    let w0: &[i32] = pkt.get_window();
    let w_sum = w0[0] + w0[1] + w0[2] + (w0.len as i32); // 20 + 30 + 40 + 3 = 93
    let lbl0: &str = pkt.get_label();
    let l0 = (lbl0[0] as i32) + (lbl0[1] as i32) + (lbl0.len as i32); // 79 + 75 + 2 = 156

    // 2. Option A inherited mutability via `&mut Self`:
    // Notice `w0` and `lbl0` are no longer used after `l0` (NLL borrow ends), so we can mutate `pkt`!
    pkt.add_to_focus(5); // nums[1] becomes 25
    pkt.write_window_elem(2, 50); // window[2] (nums[3]) becomes 50
    let f1 = pkt.read_focus(); // 25

    // 3. Retarget `&rel` fields to different elements/subslices inside `self`:
    pkt.retarget(3, 0, 2);
    let f2 = pkt.read_focus(); // nums[3] == 50
    let w1 = pkt.get_window();
    let w1_sum = w1[0] + w1[1] + (w1.len as i32); // 10 + 25 + 2 = 37
    let lbl1 = pkt.get_label();
    let l1 = (lbl1[0] as i32) + (lbl1.len as i32); // 82 ('R') + 3 = 85

    // Total: (20 + 93 - 113) + (156 - 156) + (25 + 50 + 37 + 85) = 197
    return (f0 + w_sum - 113) + (l0 - 156) + f1 + f2 + w1_sum + l1;
}
";
    let program =
        Compiler::compile_source(src).expect("Failed to compile relative reference (&rel) test");
    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(197),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // 1. Verify that using `&rel` in a transparent `struct` (or outside an `opaque` field) is rejected:
    let bad_record_rel_src = "\
pub struct BadRec {
    x: i32,
    p: &rel i32,
}
pub fn main() -> i32 { return 0; }
";
    let err1 = Compiler::compile_source(bad_record_rel_src)
        .expect_err("Expected `&rel` inside a transparent `struct` to be rejected");
    assert!(
        err1.contains(
            "'&rel' relative references are only permitted in 'opaque' field declarations"
        ),
        "Unexpected error: {err1}"
    );

    // 2. Verify that pointing `&rel` at an outer stack variable violates the Co-Residence Rule:
    let bad_outer_rel_src = "\
pub opaque BadHolder {
    x: i32,
    focus: &rel i32,
    pub fn new(outer: &i32) -> Self {
        let local_val = *outer;
        return Self {
            x: 1,
            focus: &rel local_val,
        };
    }
}
pub fn main() -> i32 {
    let v = 10;
    let _h = BadHolder::new(&v);
    return 0;
}
";
    let err2 = Compiler::compile_source(bad_outer_rel_src)
        .expect_err("Expected `&rel` pointing at outer local variable to fail Co-Residence check");
    assert!(
        err2.contains("Co-Residence violation")
            && err2.contains("must reside inside the enclosing struct 'self'"),
        "Unexpected error: {err2}"
    );

    // 3. Verify that pointing `&rel` through an external pointer/slice dereference violates Co-Residence:
    let bad_deref_rel_src = "\
pub opaque BadExt {
    ext: &[i32],
    window: &rel [i32],
    pub fn new(s: &[i32]) -> Self {
        return Self {
            ext: s,
            window: &rel self.ext[0..2],
        };
    }
}
pub fn main() -> i32 { return 0; }
";
    let err3 = Compiler::compile_source(bad_deref_rel_src).expect_err(
        "Expected `&rel` traversing a slice/pointer dereference to fail Co-Residence check",
    );
    assert!(
        err3.contains("Co-Residence violation")
            && err3.contains("cannot traverse a pointer or slice dereference"),
        "Unexpected error: {err3}"
    );

    // 4. Verify Option A mutability enforcement: mutating through `*self.focus` inside `self: &Self` is rejected:
    let bad_imm_mut_src = "\
pub opaque Holder {
    x: i32,
    focus: &rel i32,
    pub fn bad_mutate(self: &Self) {
        *self.focus = 99;
    }
}
pub fn main() -> i32 { return 0; }
";
    let err4 = Compiler::compile_source(bad_imm_mut_src)
        .expect_err("Expected mutating through `&rel` in `self: &Self` to be rejected");
    assert!(
            err4.contains("Cannot mutably access '&rel' field 'Holder.focus' through an immutable '&Self' reference"),
            "Unexpected error: {err4}"
        );

    // 5. Verify Stage 3 NLL borrow checking: mutating `pkt` while a slice `w` resolved from `&rel [i32]` is still live is rejected:
    let bad_nll_conflict_src = "\
pub opaque Packet {
    nums: [i32; 4],
    focus: &rel i32,
    window: &rel [i32],
    pub fn new() -> Self {
        return Self {
            nums: { 1, 2, 3, 4 },
            focus: &rel self.nums[0],
            window: &rel self.nums[0..2],
        };
    }
    pub fn get_window(self: &Self) -> &[i32] {
        return self.window;
    }
    pub fn mutate(self: &mut Self) {
        *self.focus = 99;
    }
}
pub fn main() -> i32 {
    let mut pkt = Packet::new();
    let w: &[i32] = pkt.get_window();
    pkt.mutate();
    return w[0];
}
";
    let err5 = Compiler::compile_source(bad_nll_conflict_src)
            .expect_err("Expected mutating `pkt` while `w` (derived from `&rel [i32]`) is still live to fail NLL borrow check");
    assert!(
        err5.contains("Borrow check error"),
        "Unexpected error: {err5}"
    );
}

#[test]
fn test_safe_threading_send_sync_scoped_threads_and_linear_mutex() {
    let src = "\
extern fn malloc(size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
extern fn pthread_create(
    thread: *mut u64,
    attr: *const u8,
    start_routine: fn(*mut u8) -> *mut u8,
    arg: *mut u8
) -> i32;
extern fn pthread_join(thread: u64, retval: *mut *mut u8) -> i32;
extern fn pthread_mutex_init(mutex: *mut u8, attr: *const u8) -> i32;
extern fn pthread_mutex_lock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_unlock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_destroy(mutex: *mut u8) -> i32;

// 1. Option C Linear `MutexGuard(T)`: wraps raw pointers (`*mut u8`, `*mut T`) without `sync`,
//    so it is automatically `!send` and `!sync` and must be consumed via `.unlock(move self)`.
pub fn MutexGuard(comptime T: send) -> type {
    return opaque(linear) {
        raw_mtx: *mut u8,
        data_ptr: *mut T,

        pub fn create(raw_mtx: *mut u8, data_ptr: *mut T) -> Self {
            return Self {
                raw_mtx: raw_mtx,
                data_ptr: data_ptr,
            };
        }

        pub fn get_mut(self: &mut Self) -> &mut T {
            unsafe {
                return &mut *self.data_ptr;
            }
        }

        pub fn unlock(move self) {
            unsafe {
                let _rc = pthread_mutex_unlock(self.raw_mtx);
            }
        }
    };
}

// 2. `Mutex(T)` (`opaque(unsafe sync)`): encapsulates the OS mutex and protected payload `data: T`.
//    Even if it stores internal raw pointers, `opaque(unsafe sync)` marks it `send` and `sync` iff `T: send`.
pub fn Mutex(comptime T: send) -> type {
    return opaque(unsafe sync) {
        raw: [u64; 6],
        raw_handle: *mut u8,
        data: T,

        drop(self: &mut Self) {
            unsafe {
                let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
                let _rc = pthread_mutex_destroy(ptr);
            }
        }

        pub fn new(val: T) -> Self {
            let mut m = Self {
                raw: { 0, 0, 0, 0, 0, 0 },
                raw_handle: 0 as *mut u8,
                data: val,
            };
            unsafe {
                let ptr = &mut m.raw[0] as *mut u64 as *mut u8;
                let _rc = pthread_mutex_init(ptr, 0 as *const u8);
            }
            return m;
        }

        pub fn lock(self: &Self) -> MutexGuard(T) {
            let self_mut = self as *mut Self;
            unsafe {
                let raw_ptr = &mut (*self_mut).raw[0] as *mut u64 as *mut u8;
                let data_ptr = &mut (*self_mut).data as *mut T;
                let _rc = pthread_mutex_lock(raw_ptr);
                return MutexGuard(T)::create(raw_ptr, data_ptr);
            }
        }

        pub fn with_lock(comptime F: callable, self: &Self, f: F) -> i32 {
            let mut guard = self.lock();
            let out: i32 = f(guard.get_mut());
            guard.unlock();
            return out;
        }
    };
}

// 3. Flat Scoped Thread Handle (`opaque(linear)`): retains `anchor: *mut F` so Stage 3 NLL borrow
//    checking keeps all stack borrows captured by `f` active until `.join(move self)` is called!
pub fn ScopedHandle(comptime F: send) -> type {
    return opaque(linear) {
        tid: u64,
        anchor: *mut F,

        pub fn create(tid: u64, anchor: *mut F) -> Self {
            return Self {
                tid: tid,
                anchor: anchor,
            };
        }

        pub fn join(move self) -> i32 {
            let mut raw_ret: *mut u8 = 0 as *mut u8;
            let _rc = pthread_join(self.tid, &mut raw_ret);
            return raw_ret as usize as i32;
        }
    };
}

pub fn spawn_scoped(comptime F: send, f: F) -> ScopedHandle(F) {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let f_ptr = raw_ctx as *mut F;
        unsafe {
            let mut local_f = move *f_ptr;
            free(raw_ctx);
            let res: i32 = local_f();
            return res as usize as *mut u8;
        }
    };
    let box_ptr = malloc(64);
    let box_f = box_ptr as *mut F;
    unsafe {
        *box_f = move f;
    }
    let mut tid: u64 = 0;
    let _rc = pthread_create(&mut tid, 0 as *const u8, entry, box_ptr);
    return ScopedHandle(F)::create(tid, box_f);
}

pub fn main() -> i32 {
    let shared_arr: [i32; 4] = { 10, 20, 30, 40 };
    let shared_slice: &[i32] = shared_arr[0..4];
    let mut child_out: i32 = 0;
    let mut parent_out: i32 = 0;
    let mtx = Mutex(i32)::new(100);

    // Flat scoped thread borrows `shared_slice` (`&[i32]`), `&mut child_out`, and `&mtx` (`&Mutex(i32)`)
    // directly in the parent function body without any nested `thread::scope(|s| ...)` callback pyramid!
    let worker = spawn_scoped(fn() -> i32 {
        *(&mut child_out) = shared_slice[0] + shared_slice[3];
        let mut g = mtx.lock();
        let v = g.get_mut();
        *v += 50;
        g.unlock();
        return 7;
    });

    // Parent thread concurrently mutates its own disjoint stack variable `parent_out`
    // and accesses `&mtx` via the ergonomic `.with_lock(...)` helper:
    parent_out = shared_slice[1] + shared_slice[2];
    let after_parent = mtx.with_lock(fn(v: &mut i32) -> i32 {
        *v += 25;
        return *v;
    });

    // Consuming `.join()` ends the NLL borrow of `child_out`, `shared_slice`, and `mtx`!
    let worker_status = worker.join();

    // After `worker.join()`, `child_out` is readable/mutable again in the parent thread:
    let final_counter = mtx.with_lock(fn(v: &mut i32) -> i32 {
        return *v;
    });

    if child_out == 50
        && parent_out == 50
        && worker_status == 7
        && (after_parent == 125 || after_parent == 175)
        && final_counter == 175
    {
        return 42;
    }
    return 1;
}
";
    let program = Compiler::compile_source(src).expect(
        "Failed to compile safe threading, send/sync, scoped threads, and linear Mutex program",
    );
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(42),
        "Expected exit code 42 from lli, got {:?}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    // Negative Test 1: Capturing a `!send` raw pointer (`*mut i32`) in `spawn_scoped` is rejected by `comptime F: send`:
    let bad_raw_ptr_send_src = format!(
            "{src}\n",
        ).replace(
            "pub fn main() -> i32 {",
            "pub fn main() -> i32 {\n    let mut x: i32 = 1;\n    let raw_p: *mut i32 = &mut x as *mut i32;\n    let w = spawn_scoped(fn() -> i32 { unsafe { *raw_p = 2; } return 0; });\n    let _ = w.join();\n    return 0;\n}\npub fn unused_main() -> i32 {"
        );
    let err1 = Compiler::compile_source(&bad_raw_ptr_send_src)
        .expect_err("Expected capturing `*mut i32` in `spawn_scoped` to fail `comptime F: send`");
    assert!(
        err1.contains("does not satisfy comptime constraint 'send'"),
        "Unexpected error: {err1}"
    );

    // Negative Test 2: Capturing a `!send` linear `MutexGuard(i32)` across threads is rejected by `comptime F: send`:
    let bad_guard_send_src = format!(
            "{src}\n",
        ).replace(
            "pub fn main() -> i32 {",
            "pub fn main() -> i32 {\n    let mtx = Mutex(i32)::new(0);\n    let mut g = mtx.lock();\n    let w = spawn_scoped(fn() -> i32 { let v = g.get_mut(); *v = 1; return 0; });\n    let _ = w.join();\n    g.unlock();\n    return 0;\n}\npub fn unused_main() -> i32 {"
        );
    let err2 = Compiler::compile_source(&bad_guard_send_src).expect_err(
        "Expected capturing `&mut MutexGuard(i32)` in `spawn_scoped` to fail `comptime F: send`",
    );
    assert!(
        err2.contains("does not satisfy comptime constraint 'send'"),
        "Unexpected error: {err2}"
    );

    // Negative Test 3: Mutating `child_out` in parent thread BEFORE `worker.join()` is rejected by Stage 3 NLL borrow checker:
    let bad_race_before_join_src = format!("{src}\n",).replace(
        "let worker_status = worker.join();",
        "child_out = 999;\n    let worker_status = worker.join();",
    );
    let err3 = Compiler::compile_source(&bad_race_before_join_src).expect_err(
        "Expected mutating `child_out` before `worker.join()` to fail Stage 3 NLL borrow check",
    );
    assert!(
        err3.contains("Borrow check error") && err3.contains("borrowed"),
        "Unexpected error: {err3}"
    );

    // Negative Test 4: Forgetting to call `worker.join()` before scope exit is rejected by Stage 3b linear type checker:
    let bad_unjoined_handle_src = format!("{src}\n",).replace(
        "let worker_status = worker.join();",
        "let worker_status: i32 = 7;",
    );
    let err4 = Compiler::compile_source(&bad_unjoined_handle_src)
        .expect_err("Expected forgetting `worker.join()` to fail Stage 3b linear type checking");
    assert!(
        err4.contains("Linear value") && err4.contains("must be explicitly consumed"),
        "Unexpected error: {err4}"
    );

    // Negative Test 5: Using `&mut i32` obtained from `g.get_mut()` AFTER `g.unlock()` is rejected by Stage 3 NLL borrow checker:
    let bad_use_after_unlock_src = format!(
            "{src}\n",
        ).replace(
            "pub fn main() -> i32 {",
            "pub fn main() -> i32 {\n    let mtx = Mutex(i32)::new(10);\n    let mut g = mtx.lock();\n    let v: &mut i32 = g.get_mut();\n    g.unlock();\n    *v = 99;\n    return 0;\n}\npub fn unused_main() -> i32 {"
        );
    let err5 = Compiler::compile_source(&bad_use_after_unlock_src)
        .expect_err("Expected using `v` after `g.unlock()` to fail Stage 3 NLL borrow check");
    assert!(
        err5.contains("Borrow check error") && err5.contains("borrowed"),
        "Unexpected error: {err5}"
    );
}

#[test]
fn test_soundness_review_fixes() {
    // 1. A transparent `struct` holding `&mut T` is NOT Copy (cannot be copied to create two live `&mut T`):
    let record_with_mut_ref_src = r#"
pub struct MutHolder {
    r: &mut i32,
}
pub fn main() -> i32 {
    let mut x: i32 = 10;
    let h1 = MutHolder { r: &mut x };
    let h2 = h1;
    *h1.r = 20;
    *h2.r = 30;
    return x;
}
"#;
    let err1 = Compiler::compile_source(record_with_mut_ref_src)
        .expect_err("Expected copying `struct { r: &mut i32 }` to fail move analysis");
    assert!(
        err1.contains("Use of moved or uninitialized value"),
        "Unexpected error: {err1}"
    );

    // 2. A plain `opaque` with no lifecycle hooks is move-only by default (never implicitly Copy):
    let plain_struct_move_only_src = r#"
pub opaque Token {
    id: i32,
    pub fn new(id: i32) -> Self { return Self { id: id }; }
    pub fn get(self: &Self) -> i32 { return self.id; }
}
pub fn consume(t: Token) -> i32 { return t.get(); }
pub fn main() -> i32 {
    let t = Token::new(7);
    let a = consume(t);
    let b = consume(t);
    return a + b;
}
"#;
    let err2 = Compiler::compile_source(plain_struct_move_only_src)
        .expect_err("Expected plain `opaque` to be move-only by default");
    assert!(
        err2.contains("Use of moved or uninitialized value"),
        "Unexpected error: {err2}"
    );

    // 3. Private function returning a reference read through a dereference (`fn unnest(x: &&i32) -> &i32 { return *x; }`)
    //    infers its borrow origin from `x`:
    let deref_return_origin_src = r#"
fn unnest(x: &&i32) -> &i32 {
    return *x;
}
pub fn main() -> i32 {
    let mut val: i32 = 42;
    let r1: &i32 = &val;
    let r2: &&i32 = &r1;
    let inner: &i32 = unnest(r2);
    val = 99;
    return *inner;
}
"#;
    let err3 = Compiler::compile_source(deref_return_origin_src)
        .expect_err("Expected `unnest(x: &&i32) -> &i32` to infer borrow of `val`");
    assert!(
        err3.contains("Borrow check error") && err3.contains("borrowed"),
        "Unexpected error: {err3}"
    );

    // 4. Private method building a reference from a raw pointer field (`self.ptr`) infers borrow of `self`:
    let raw_ptr_field_borrow_src = r#"
pub opaque RawBuf {
    ptr: *const i32,
    pub fn from_ref(r: &i32) -> Self {
        return Self { ptr: r as *const i32 };
    }
    fn get_private(self: &Self) -> &i32 {
        unsafe {
            return &*self.ptr;
        }
    }
    pub fn leak_check(mut buf: Self) -> i32 {
        let elem_ref: &i32 = buf.get_private();
        let moved_buf = move buf;
        let _keep = moved_buf;
        return *elem_ref;
    }
}
pub fn main() -> i32 {
    let x: i32 = 5;
    let b = RawBuf::from_ref(&x);
    return RawBuf::leak_check(b);
}
"#;
    let err4 = Compiler::compile_source(raw_ptr_field_borrow_src)
        .expect_err("Expected private method returning `&*self.ptr` to keep `buf` borrowed");
    assert!(
        err4.contains("Borrow check error") && err4.contains("borrowed"),
        "Unexpected error: {err4}"
    );

    // 5. Parameter-to-parameter borrow flow (`fn stash(dst: &mut RefSlot, x: &i32) { dst.r = x; }`):
    let param_to_param_flow_src = r#"
pub struct RefSlot {
    r: &i32,
}
fn stash(dst: &mut RefSlot, x: &i32) {
    dst.r = x;
}
pub fn main() -> i32 {
    let long_lived: i32 = 1;
    let mut slot = RefSlot { r: &long_lived };
    if true {
        let short_lived: i32 = 2;
        stash(&mut slot, &short_lived);
    }
    return *slot.r;
}
"#;
    let err5 = Compiler::compile_source(param_to_param_flow_src).expect_err(
        "Expected storing `&short_lived` into `slot` via `stash` to fail when `short_lived` dies",
    );
    assert!(
        err5.contains("Borrow check error")
            && err5.contains("goes out of scope (StorageDead) while still borrowed"),
        "Unexpected error: {err5}"
    );

    // 6. `@drop` on a linear type (including via raw pointer in a generic container) is rejected:
    let drop_linear_in_container_src = r#"
pub opaque(linear) MustCommit {
    v: i32,
    pub fn finish(move self) -> i32 { return self.v; }
}
pub fn bad_drop_ptr(p: *mut MustCommit) {
    unsafe {
        @drop(p);
    }
}
pub fn main() -> i32 { return 0; }
"#;
    let err6 = Compiler::compile_source(drop_linear_in_container_src)
        .expect_err("Expected `@drop` on linear type pointer to be rejected");
    assert!(
        err6.contains("Linear value") && err6.contains("cannot be dropped via '@drop'"),
        "Unexpected error: {err6}"
    );

    // 7. Bare `opaque(sync)` without `unsafe` is rejected at compile time:
    let bare_sync_struct_src = r#"
pub opaque(sync) UncheckedSync {
    ptr: *mut u8,
}
pub fn main() -> i32 { return 0; }
"#;
    let err7 = Compiler::compile_source(bare_sync_struct_src)
        .expect_err("Expected bare `opaque(sync)` without `unsafe` to be rejected");
    assert!(
        err7.contains("requires 'opaque(unsafe sync)'"),
        "Unexpected error: {err7}"
    );

    // 8. `unreachable` in safe code compiles and lowers to `@llvm.trap()` + `unreachable`:
    let safe_unreachable_src = r#"
pub fn unwrap_or_trap(opt: ?i32) -> i32 {
    return opt orelse unreachable;
}
pub fn main() -> i32 {
    return unwrap_or_trap(77);
}
"#;
    let prog8 = Compiler::compile_source(safe_unreachable_src)
        .expect("Expected `opt orelse unreachable` to compile");
    let ir8 = LlvmLowering::lower(&prog8).expect("Expected LLVM IR emission to succeed");
    assert!(
        ir8.contains("call void @llvm.trap()"),
        "Expected `@llvm.trap()` in LLVM IR for `unreachable`:\n{ir8}"
    );

    // 9. `opaque(copy)` is implicitly copyable (`Copy`), supports `@clone`, satisfies `comptime T: copy`,
    //    and rejects `drop` hooks or non-copy fields:
    let copy_struct_src = r#"
pub opaque(copy) UserId {
    id: i32,
    pub fn new(id: i32) -> Self { return Self { id: id }; }
    pub fn get(self: &Self) -> i32 { return self.id; }
}
pub fn duplicate_copy(comptime T: copy, x: T) -> i32 {
    let a = x;
    let b = @clone(x);
    return 1;
}
pub fn consume_id(u: UserId) -> i32 {
    return u.get();
}
pub fn main() -> i32 {
    let u = UserId::new(21);
    let x = consume_id(u);
    let y = consume_id(u);
    let z = duplicate_copy(u);
    return x + y + z - 1;
}
"#;
    let prog9 = Compiler::compile_source(copy_struct_src)
        .expect("Expected `opaque(copy)` to be implicitly copyable and satisfy `comptime T: copy`");
    let _ir9 =
        LlvmLowering::lower(&prog9).expect("Expected LLVM lowering of `opaque(copy)` to succeed");

    let bad_copy_struct_drop_src = r#"
pub opaque(copy) BadCopy {
    x: i32,
    drop(self: &mut Self) {}
}
pub fn main() -> i32 { return 0; }
"#;
    let err9 = Compiler::compile_source(bad_copy_struct_drop_src)
        .expect_err("Expected `opaque(copy)` with `drop` hook to be rejected");
    assert!(
        err9.contains("Copy opaque 'BadCopy' ('opaque(copy)') cannot implement `drop`"),
        "Unexpected error: {err9}"
    );
}

#[test]
fn test_conditional_drop_hooks_vec_linear_and_affine_drain() {
    use crate::llvm::LlvmLowering;
    use crate::lower::Compiler;

    let src = r#"
extern fn malloc(size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);

pub opaque(linear) Transaction {
    id: i32,
    audit_log: *mut i32,

    pub fn begin(id: i32, audit_log: *mut i32) -> Self {
        return Self { id: id, audit_log: audit_log };
    }

    pub fn commit(move self) {
        unsafe {
            *self.audit_log = *self.audit_log + self.id;
        }
    }

    drop(self: &mut Self) {
        unsafe {
            *self.audit_log = *self.audit_log + 100;
        }
    }
}

pub fn Vec(comptime T: type) -> type {
    return opaque {
        ptr: ?*mut T = null,
        len: usize = 0,
        cap: usize = 0,

        pub fn new(cap: usize, elem_size: usize, drop_tracker: *mut i32) -> Self {
            unsafe {
                let raw = malloc(cap * elem_size);
                return Self {
                    ptr: raw as *mut T,
                    len: 0,
                    cap: cap,
                    drop_tracker: drop_tracker,
                };
            }
        }

        drop_tracker: *mut i32,

        pub fn push(self: &mut Self, val: T) borrows(self: val) {
            unsafe {
                let p = self.ptr orelse unreachable;
                *(p + (self.len as isize)) = val;
                self.len += 1;
            }
        }

        pub fn clear(self: &mut Self) where T: !linear {
            unsafe {
                if let p = self.ptr {
                    let mut i: usize = 0;
                    while i < self.len {
                        @drop(p + (i as isize));
                        i += 1;
                    }
                }
                self.len = 0;
            }
        }

        pub fn drain(comptime F: callable, move mut self, f: F) {
            unsafe {
                let p = self.ptr orelse return;
                let n = self.len;
                self.len = 0;
                let mut i: usize = 0;
                while i < n {
                    f(*(p + (i as isize)));
                    i += 1;
                }
            }
        }

        clone(self: &Self) -> Self where T: clone {
            unsafe {
                let p = self.ptr orelse unreachable;
                let raw = malloc(self.cap * 4);
                let dst = raw as *mut T;
                let mut i: usize = 0;
                while i < self.len {
                    *(dst + (i as isize)) = @clone(&(*(p + (i as isize))));
                    i += 1;
                }
                return Self {
                    ptr: dst,
                    len: self.len,
                    cap: self.cap,
                    drop_tracker: self.drop_tracker,
                };
            }
        }

        drop(self: &mut Self) where T: !linear {
            unsafe {
                if let p = self.ptr {
                    let mut i: usize = 0;
                    while i < self.len {
                        @drop(p + (i as isize));
                        i += 1;
                    }
                    free(p as *mut u8);
                }
                *self.drop_tracker = *self.drop_tracker + 1;
            }
        }

        drop(self: &mut Self) where T: linear {
            unsafe {
                if let p = self.ptr {
                    free(p as *mut u8);
                }
                *self.drop_tracker = *self.drop_tracker + 10;
            }
        }
    };
}

pub fn main() -> i32 {
    unsafe {
        let raw_cnt = malloc(8);
        let audit_log: *mut i32 = raw_cnt as *mut i32;
        let vec_drops: *mut i32 = audit_log + 1;
        *audit_log = 0;
        *vec_drops = 0;

        // 1. `Vec(i32)` is `opaque(affine)`: supports `clear()`, `@clone(&v)`, and implicit scope-exit drop (`where T: !linear`):
        if true {
            let mut vi = Vec(i32)::new(4, 4, vec_drops);
            vi.push(10);
            vi.push(20);
            let mut vi_clone = @clone(&vi);
            vi_clone.clear();
        }
        // Both `vi` and `vi_clone` ran `drop where T: !linear`, so `*vec_drops == 2`!

        // 2. `Vec(Transaction)` is automatically upgraded to `opaque(linear)` because `drop where T: linear` matched:
        //    Consuming via `txs.drain(...)` commits every linear `Transaction` (running each `Transaction::commit` + `Transaction::drop`)
        //    and then runs `Vec(Transaction)::drop where T: linear` as shared teardown at the exit of `drain`!
        let mut txs = Vec(Transaction)::new(4, 16, vec_drops);
        txs.push(Transaction::begin(5, audit_log));
        txs.push(Transaction::begin(7, audit_log));
        txs.drain(fn(tx: Transaction) {
            tx.commit();
        });

        let final_audit = *audit_log;
        let final_drops = *vec_drops;
        free(raw_cnt);

        // `final_audit` = (5 + 100) + (7 + 100) = 212
        // `final_drops` = 2 (from `vi` and `vi_clone`) + 10 (from `txs` shared `drop where T: linear`) = 12
        if final_audit == 212 && final_drops == 12 {
            return 42;
        }
        return 1;
    }
}
"#;
    let program = Compiler::compile_source(src)
            .expect("Expected `Vec(i32)` and `Vec(Transaction)` with paired `where T: !linear` / `where T: linear` drop hooks to compile");
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(42),
        "Expected exit code 42 from lli, got {:?}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    // Negative Test 1: Forgetting to consume `Vec(Transaction)` via `drain` fails Stage 3b linear type checking!
    let forgotten_drain_src = src.replace(
        "        txs.drain(fn(tx: Transaction) {\n            tx.commit();\n        });",
        "        // forgot to drain `txs`!",
    );
    let err1 = Compiler::compile_source(&forgotten_drain_src)
        .expect_err("Expected unconsumed `Vec(Transaction)` to fail Stage 3b linear type checking");
    assert!(
        err1.contains("Linear value") && err1.contains("must be explicitly consumed"),
        "Unexpected error: {err1}"
    );

    // Negative Test 2: Calling `txs.clear()` on `Vec(Transaction)` fails `where T: !linear`!
    let bad_clear_src = src.replace(
        "        txs.drain(fn(tx: Transaction) {",
        "        txs.clear();\n        txs.drain(fn(tx: Transaction) {",
    );
    let err2 = Compiler::compile_source(&bad_clear_src)
        .expect_err("Expected `txs.clear()` on `Vec(Transaction)` to fail `where T: !linear`");
    assert!(
        err2.contains("where-clause constraint 'T: !linear' is not satisfied"),
        "Unexpected error: {err2}"
    );

    // Negative Test 3: Defining `drop(self: &mut Self) where T: !linear` WITHOUT a matching
    // `drop(self: &mut Self) where T: linear` is rejected when instantiated with linear `Transaction`:
    let missing_linear_drop_src = r#"
pub opaque(linear) Transaction {
    id: i32,
    pub fn commit(move self) -> i32 { return self.id; }
}
pub fn BadVec(comptime T: type) -> type {
    return opaque {
        ptr: ?*mut T = null,
        drop(self: &mut Self) where T: !linear {}
    };
}
pub fn main() -> i32 {
    let v: BadVec(Transaction) = BadVec(Transaction) { ptr: null };
    return 0;
}
"#;
    let err3 = Compiler::compile_source(missing_linear_drop_src)
        .expect_err("Expected `BadVec(Transaction)` missing `drop where T: linear` to be rejected");
    assert!(
            err3.contains("defines 'drop' with 'where T: !linear', but is missing a matching 'drop(self: &mut Self) where T: linear' teardown hook"),
            "Unexpected error: {err3}"
        );
}

#[test]
fn test_surface_pub_fn_borrows_contracts_and_param_flows() {
    // 1. Valid `pub fn` with explicit `borrows(a, b)`, `borrows(second)`, and `borrows(dst: x)`:
    let valid_src = r#"
pub struct RefSlot {
    r: &i32,
}

pub fn pick_longer(a: &str, b: &str) -> &str borrows(a, b) {
    if a.len >= b.len {
        return a;
    }
    return b;
}

pub fn second_ref(first: &i32, second: &i32) -> &i32 borrows(second) {
    let _unused: i32 = *first;
    return second;
}

pub fn stash(dst: &mut RefSlot, x: &i32) borrows(dst: x) {
    dst.r = x;
}

pub fn main() -> i32 {
    let s1: &str = "hi";
    let s2: &str = "world";
    let chosen: &str = pick_longer(s1, s2);

    let mut x: i32 = 10;
    let y: i32 = 30;
    let r2: &i32 = second_ref(&x, &y);
    // `x` is NOT borrowed by `r2` because `second_ref` declares `borrows(second)`:
    x = 7;

    let mut slot = RefSlot { r: &y };
    stash(&mut slot, &x);

    if chosen.len == 5 && *r2 == 30 && *slot.r == 7 {
        return 42;
    }
    return 1;
}
"#;
    let program = Compiler::compile_source(valid_src)
        .expect("Expected valid `pub fn` `borrows(...)` contracts to compile");
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");
    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(42),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // 2. Ambiguous `pub fn` returning a reference with multiple reference parameters and no `borrows(...)`:
    let missing_ret_contract_src = r#"
pub fn pick_longer(a: &str, b: &str) -> &str {
    if a.len >= b.len {
        return a;
    }
    return b;
}
pub fn main() -> i32 {
    let s = pick_longer("a", "bb");
    return s.len as i32;
}
"#;
    let err1 = Compiler::compile_source(missing_ret_contract_src)
        .expect_err("Expected ambiguous `pub fn` without `borrows(...)` to be rejected");
    assert!(
            err1.contains("Public function 'pick_longer' returns a reference and takes multiple reference parameters; add an explicit 'borrows(...)' contract"),
            "Unexpected error: {err1}"
        );

    // 3. `pub fn` return contract violation (`borrows(second)` but body returns `first`):
    let violated_ret_contract_src = r#"
pub fn bad_second(first: &i32, second: &i32) -> &i32 borrows(second) {
    let _unused: i32 = *second;
    return first;
}
pub fn main() -> i32 {
    let a: i32 = 1;
    let b: i32 = 2;
    return *bad_second(&a, &b);
}
"#;
    let err2 = Compiler::compile_source(violated_ret_contract_src)
        .expect_err("Expected `bad_second` violating `borrows(second)` to be rejected");
    assert!(
            err2.contains("return value borrows from parameter 'first', which is not permitted by its contract borrows(second); add 'first'"),
            "Unexpected error: {err2}"
        );

    // 4. `pub fn stash(dst: &mut RefSlot, x: &i32)` without `borrows(dst: x)` is rejected:
    let missing_param_flow_contract_src = r#"
pub struct RefSlot {
    r: &i32,
}
pub fn stash(dst: &mut RefSlot, x: &i32) {
    dst.r = x;
}
pub fn main() -> i32 {
    let a: i32 = 1;
    let mut slot = RefSlot { r: &a };
    stash(&mut slot, &a);
    return *slot.r;
}
"#;
    let err3 = Compiler::compile_source(missing_param_flow_contract_src)
        .expect_err("Expected `pub fn stash` without `borrows(dst: x)` to be rejected");
    assert!(
            err3.contains("parameter 'dst' stores a borrow from parameter 'x', which its contract does not declare; add 'borrows(dst: x)'"),
            "Unexpected error: {err3}"
        );

    // 5. `pub fn stash(dst: &mut RefSlot, x: &i32) borrows(dst: x)` rejects caller when `x` dies before `dst`:
    let caller_dangling_stash_src = r#"
pub struct RefSlot {
    r: &i32,
}
pub fn stash(dst: &mut RefSlot, x: &i32) borrows(dst: x) {
    dst.r = x;
}
pub fn main() -> i32 {
    let long_lived: i32 = 1;
    let mut slot = RefSlot { r: &long_lived };
    if true {
        let short_lived: i32 = 2;
        stash(&mut slot, &short_lived);
    }
    return *slot.r;
}
"#;
    let err4 = Compiler::compile_source(caller_dangling_stash_src).expect_err(
            "Expected caller of `pub fn stash(...) borrows(dst: x)` with short-lived `x` to fail borrow check",
        );
    assert!(
        err4.contains("Borrow check error") && err4.contains("borrowed"),
        "Unexpected error: {err4}"
    );
}

#[test]
fn test_surface_uninit_stack_vec_and_overlay_syntax() {
    use crate::llvm::LlvmLowering;
    use crate::lower::Compiler;
    

    // 1. Full end-to-end StackVec(T, cap) from DESIGN.md Section 7.2 + surface `overlay` + `uninit T`:
    let src = r#"
pub error CapacityError {
    Full,
}

static mut AFFINE_DROP_SUM: i32 = 0;
static mut LINEAR_COMMIT_SUM: i32 = 0;

pub opaque Resource {
    val: i32,

    pub fn new(val: i32) -> Self {
        return Self { val: val };
    }

    pub fn get(self: &Self) -> i32 {
        return self.val;
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.val += delta;
    }

    clone(self: &Self) -> Self {
        return Self { val: self.val };
    }

    drop(self: &mut Self) {
        unsafe {
            AFFINE_DROP_SUM += self.val;
        }
    }
}

pub opaque(linear) Transaction {
    id: i32,

    pub fn begin(id: i32) -> Self {
        return Self { id: id };
    }

    pub fn commit(move self) {
        unsafe {
            LINEAR_COMMIT_SUM += self.id;
        }
    }
}

pub fn StackVec(comptime T: type, comptime cap: usize) -> type {
    return opaque {
        data: [uninit T; cap],
        len: usize,

        pub fn new() -> Self {
            return Self {
                data: uninit,
                len: 0,
            };
        }

        pub fn try_push(self: &mut Self, value: T) -> CapacityError!void where T: !linear {
            if self.len == cap {
                return CapacityError::Full;
            }
            self.data[self.len] = uninit(move value);
            self.len += 1;
        }

        pub fn push(self: &mut Self, value: T) {
            if self.len == cap {
                unreachable;
            }
            self.data[self.len] = uninit(move value);
            self.len += 1;
        }

        pub fn pop(self: &mut Self) -> ?T {
            if self.len == 0 {
                return null;
            }
            self.len -= 1;
            unsafe {
                return move self.data[self.len].assume_init;
            }
        }

        pub fn get(self: &Self, index: usize) -> ?&T {
            if index >= self.len {
                return null;
            }
            unsafe {
                return &self.data[index].assume_init;
            }
        }

        pub fn get_mut(self: &mut Self, index: usize) -> ?&mut T {
            if index >= self.len {
                return null;
            }
            unsafe {
                return &mut self.data[index].assume_init;
            }
        }

        pub fn drain(comptime F: callable, move mut self, f: F) {
            let n = self.len;
            self.len = 0;
            let mut i: usize = 0;
            while i < n {
                unsafe {
                    f(move self.data[i].assume_init);
                }
                i += 1;
            }
        }

        default() -> Self {
            return Self::new();
        }

        clone(self: &Self) -> Self where T: clone {
            let mut out = Self::new();
            let mut i: usize = 0;
            while i < self.len {
                unsafe {
                    let elem_ref: &T = &self.data[i].assume_init;
                    out.data[i] = uninit(@clone(elem_ref));
                }
                out.len += 1;
                i += 1;
            }
            return out;
        }

        drop(self: &mut Self) where T: !linear {
            let mut i: usize = 0;
            while i < self.len {
                unsafe {
                    @drop(&mut self.data[i].assume_init);
                }
                i += 1;
            }
        }

        drop(self: &mut Self) where T: linear {
            // Shared teardown for linear StackVec
        }
    };
}

export overlay WordBytes {
    word: u32,
    bytes: [u8; 4],
}

pub fn check_is_overlay(comptime T: overlay, _x: &T) -> i32 {
    return 1;
}

pub fn main() -> i32 {
    // A. Standalone `uninit T` local + `uninit(...)` + `.assume_init`
    let mut slot: uninit Resource = uninit;
    slot = uninit(Resource::new(7));
    let seven: i32 = unsafe {
        let r_ref: &Resource = &slot.assume_init;
        let v = r_ref.get();
        @drop(&mut slot.assume_init);
        v
    };
    if seven != 7 {
        return 1;
    }
    if unsafe { AFFINE_DROP_SUM } != 7 {
        return 2;
    }

    // B. Affine StackVec(Resource, 3): push, try_push overflow, get, get_mut, clone, pop, scope-exit drop
    if true {
        let mut sv: StackVec(Resource, 3) = @default(StackVec(Resource, 3));
        sv.push(Resource::new(10));
        sv.push(Resource::new(20));
        sv.push(Resource::new(30));

        // Overflowing try_push drops the rejected Resource(99) immediately:
        let mut overflowed = false;
        sv.try_push(Resource::new(99)) catch {
            overflowed = true;
        };
        if !overflowed {
            return 3;
        }
        if unsafe { AFFINE_DROP_SUM } != 106 {
            return 4;
        }

        // Mutate element 1 via `get_mut`:
        if let elem1 = sv.get_mut(1) {
            elem1.add(5); // 20 -> 25
        } else {
            return 5;
        }

        // Read element 1 via `get`:
        if let elem1_ref = sv.get(1) {
            if elem1_ref.get() != 25 {
                return 6;
            }
        } else {
            return 7;
        }

        // Pop top element (30):
        if let popped = sv.pop() {
            if popped.get() != 30 {
                return 8;
            }
            // `popped` (30) drops at end of `if let` block -> AFFINE_DROP_SUM = 136
        } else {
            return 9;
        }

        // Clone `sv` (elements 10 and 25):
        let sv_cloned = @clone(&sv);
        if let c0 = sv_cloned.get(0) {
            if c0.get() != 10 {
                return 10;
            }
        } else {
            return 11;
        }
        // At scope exit, both `sv` (10 + 25 = 35) and `sv_cloned` (10 + 25 = 35) drop!
        // Total AFFINE_DROP_SUM = 136 + 70 = 206.
    }
    if unsafe { AFFINE_DROP_SUM } != 206 {
        return 12;
    }

    // C. Linear StackVec(Transaction, 4): must be consumed via `drain`
    let mut tx_vec = StackVec(Transaction, 4)::new();
    tx_vec.push(Transaction::begin(100));
    tx_vec.push(Transaction::begin(200));
    tx_vec.push(Transaction::begin(300));
    tx_vec.drain(fn(tx: Transaction) {
        tx.commit();
    });
    if unsafe { LINEAR_COMMIT_SUM } != 600 {
        return 13;
    }

    // D. Named & anonymous `overlay` types
    let mut wb = WordBytes { word: 0x01020304 };
    if check_is_overlay(&wb) != 1 {
        return 14;
    }
    let low_byte: u8 = unsafe { wb.bytes[0] };
    if low_byte != 4 && low_byte != 1 {
        return 15;
    }
    wb.word = 42;
    let w_val: u32 = unsafe { wb.word };
    if w_val != 42 {
        return 16;
    }

    let mut anon_ov: overlay { a: i32, b: u32 } = overlay { a: i32, b: u32 } { a: -1 };
    let b_bits: u32 = unsafe { anon_ov.b };
    if b_bits != 0xFFFFFFFF {
        return 17;
    }
    anon_ov.b = 123;
    if unsafe { anon_ov.a } != 123 {
        return 18;
    }

    return 0;
}
"#;

    let (program, header) = Compiler::compile_source_with_c_header(src)
        .expect("Expected StackVec + overlay program to compile");
    assert!(
        header.contains("typedef union WordBytes WordBytes;")
            && header.contains("union WordBytes {"),
        "Expected C header to contain `union WordBytes` definition, got:\n{header}"
    );

    let llvm_ir = LlvmLowering::lower(&program).expect("Expected LLVM lowering to succeed");
    assert!(
        llvm_ir.contains("; uninit field 0 of"),
        "Expected `data: uninit` in `StackVec::new` to emit zero memory writes in LLVM IR:\n{llvm_ir}"
    );

    let run_out = link_ir("uninit_stack_vec", &llvm_ir).run(&[]);
    assert_eq!(run_out.status.code(), Some(0));

    // 2. Negative test: accessing `.assume_init` outside `unsafe` is rejected:
    let bad_assume_init_src = r#"
pub fn main() -> i32 {
    let mut x: uninit i32 = uninit;
    x = uninit(42);
    return x.assume_init;
}
"#;
    let err1 = Compiler::compile_source(bad_assume_init_src)
        .expect_err("Expected `.assume_init` outside `unsafe` to be rejected");
    assert!(
        err1.contains("Accessing '.assume_init' on 'uninit i32' is unsafe"),
        "Unexpected error: {err1}"
    );

    // 3. Negative test: accessing an `overlay` field outside `unsafe` is rejected:
    let bad_overlay_read_src = r#"
pub overlay IntFloat {
    i: i32,
    f: f32,
}
pub fn main() -> i32 {
    let ov = IntFloat { i: 10 };
    return ov.i;
}
"#;
    let err2 = Compiler::compile_source(bad_overlay_read_src)
        .expect_err("Expected reading overlay field outside `unsafe` to be rejected");
    assert!(
        err2.contains("Accessing field 'i' of overlay 'IntFloat' is unsafe"),
        "Unexpected error: {err2}"
    );

    // 4. Negative test: `uninit` literal on a non-`uninit` type is rejected:
    let bad_uninit_type_src = r#"
pub fn main() -> i32 {
    let x: i32 = uninit;
    return x;
}
"#;
    let err3 = Compiler::compile_source(bad_uninit_type_src)
        .expect_err("Expected `let x: i32 = uninit;` to be rejected");
    assert!(
        err3.contains("`uninit` can only initialize `uninit T` or `[uninit T; N]`"),
        "Unexpected error: {err3}"
    );
}

#[test]
fn test_unscoped_spawn_join_handle_and_execution_agnostic_select() {
    let src = r#"
pub fn check_sync(comptime T: sync) -> i32 {
    return 1;
}

pub fn main() -> i32 {
    // 1. Verify `JoinHandle(i32)` is `sync` (`opaque(linear, unsafe sync)`):
    let sync_ok = check_sync(JoinHandle(i32));
    if sync_ok != 1 {
        return 10;
    }

    // 2. Unscoped `spawn` with a non-borrowing `move fn() -> i32` and `.join(move self) -> i32`:
    let base: i32 = 15;
    let delta: i32 = 27;
    let h1: JoinHandle(i32) = spawn(move fn() -> i32 {
        return base + delta;
    });
    let joined_val = h1.join();
    if joined_val != 42 {
        return 11;
    }

    // 3. Unscoped `spawn` with `.detach(move self)` communicating back via a shared `Channel(i32)`:
    let detached_ch = Channel(i32)::new();
    let base2: i32 = 99;
    let h2 = spawn(move fn() -> i32 {
        return base2 + 1;
    });
    h2.detach();

    // Let a scoped worker send on `detached_ch` after a short delay while main thread parks in `@select`:
    let ch_a = Channel(i32)::new();
    let ch_b = Channel(i32)::new();

    // 4. `@select` FastPoll path (`ch_a` already has a buffered message ready):
    ch_a.send(77);
    let fast_picked: i32 = @select {
        let v = ch_a.recv() => {
            v + 1
        },
        let u = ch_b.recv() => {
            u + 100
        },
    };
    if fast_picked != 78 {
        return 12;
    }

    // 5. `@select` with `default` non-blocking branch when both channels are empty:
    let default_picked: i32 = @select {
        v = ch_a.recv() => v,
        u = ch_b.recv() => u,
        default => 333,
    };
    if default_picked != 333 {
        return 13;
    }

    // 6. `@select` slow path (`FastPoll -> Register -> Park -> Unregister -> SwitchInt(winner)`):
    //    `ch_a` and `ch_b` are empty; worker thread sleeps briefly then sends `55` on `ch_b`,
    //    claiming the stack-allocated `Waiter` (`WAITING -> CLAIMED(1)`) before the 200ms timer!
    let producer = spawn_scoped(fn() -> i32 {
        let t = Timer::after_us(3000);
        let _ = t.wait();
        ch_b.send(55);
        return 0;
    });
    let slow_timer = Timer::after_us(200000);
    let slow_picked: i32 = @select {
        a = ch_a.recv() => a + 1000,
        b = ch_b.recv() => b + 2000,
        _ = slow_timer.wait() => 9999,
    };
    let _ = producer.join();
    if slow_picked != 2055 {
        return 14;
    }

    // 7. `@select` send branch (`ch_a.send(123) => ...`) and timer wakeup (`Timer::after_us`):
    let send_res: i32 = @select {
        ch_a.send(123) => 500,
        x = ch_b.recv() => x,
    };
    if send_res != 500 {
        return 15;
    }
    if ch_a.recv() != 123 {
        return 16;
    }

    let short_timer = Timer::after_us(1000);
    let timer_won: i32 = @select {
        x = ch_a.recv() => x,
        _ = short_timer.wait() => 888,
    };
    if timer_won != 888 {
        return 17;
    }

    let _ = detached_ch.try_send(1);
    return 42;
}
"#;

    let program = Compiler::compile_source(src)
        .expect("Failed to compile unscoped spawn, JoinHandle, Channel, and @select program");
    let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

    let output = lli(&llvm_ir);
    assert_eq!(
        output.status.code(),
        Some(42),
        "Expected exit code 42 from lli, got {:?}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    // Negative Test 1: Passing a borrowing closure (non-`move fn`) to unscoped `spawn` is rejected:
    let bad_borrowing_closure_src = r#"
pub fn main() -> i32 {
    let x: i32 = 10;
    let h = spawn(fn() -> i32 {
        return x;
    });
    return h.join();
}
"#;
    let err1 = Compiler::compile_source(bad_borrowing_closure_src)
        .expect_err("Expected borrowing closure in unscoped `spawn` to be rejected");
    assert!(
        err1.contains("Unscoped 'spawn' requires a non-borrowing 'move fn' closure"),
        "Unexpected error: {err1}"
    );

    // Negative Test 2: Passing a `move fn` that captures a safe reference `&i32` to `spawn` is rejected:
    let bad_move_ref_capture_src = r#"
pub fn main() -> i32 {
    let x: i32 = 10;
    let r: &i32 = &x;
    let h = spawn(move fn() -> i32 {
        return *r;
    });
    return h.join();
}
"#;
    let err2 = Compiler::compile_source(bad_move_ref_capture_src)
        .expect_err("Expected `move fn` capturing `&i32` in unscoped `spawn` to be rejected");
    assert!(
        err2.contains("contains borrowed references"),
        "Unexpected error: {err2}"
    );

    // Negative Test 3: Forgetting both `.join()` and `.detach()` on linear `JoinHandle(i32)` is rejected:
    let bad_unconsumed_join_handle_src = r#"
pub fn main() -> i32 {
    let y: i32 = 5;
    let h = spawn(move fn() -> i32 {
        return y;
    });
    return 0;
}
"#;
    let err3 = Compiler::compile_source(bad_unconsumed_join_handle_src)
        .expect_err("Expected unconsumed `JoinHandle(i32)` to fail Stage 3b linear type checking");
    assert!(
        err3.contains("Linear value") && err3.contains("must be explicitly consumed"),
        "Unexpected error: {err3}"
    );
}

#[test]
fn test_std_vec() {
    // `Vec(T)` from the prelude: growth, access, slices, element drops, linear elements consumed
    // through `drain`, and nesting.
    let src = "
static mut DROPS: i32 = 0;
opaque Tracked {
    v: i32,
    pub fn new(v: i32) -> Self { return Self { v: v }; }
    drop(self: &mut Self) { unsafe { DROPS = DROPS + self.v; } }
}
opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { return Self { id: i }; }
    pub fn commit(move self) -> i32 { return self.id; }
}
pub fn main() -> i32 {
    let mut v = Vec(i64)::new();
    for i in 0..100 { v.push(i); }
    let mut s: i64 = 0;
    for x in v.as_slice() { s += x; }
    if s != 4950 || v.len() != 100 { return 1; }
    for ref mut x in v.as_mut_slice() { *x = 1; }
    let last = v.pop() orelse return 2;
    if last != 1 || v.len() != 99 { return 3; }
    if let missing = v.get(500) { return 4; }

    if true {
        let mut t = Vec(Tracked)::new();
        t.push(Tracked::new(1));
        t.push(Tracked::new(10));
        t.push(Tracked::new(100));
        t.truncate(1);                          // drops 10 + 100
        if unsafe { DROPS } != 110 { return 5; }
    }                                           // drops the remaining 1
    if unsafe { DROPS } != 111 { return 6; }

    let mut txs = Vec(Tx)::new();
    txs.push(Tx::new(20));
    txs.push(Tx::new(22));
    let mut committed: i32 = 0;
    txs.drain(fn(t: Tx) { committed += t.commit(); });

    let mut nested = Vec(Vec(i32))::new();
    let mut inner = Vec(i32)::new();
    inner.push(0);
    nested.push(inner);
    let first = nested.get(0) orelse return 7;
    return committed + (first.len() as i32) - 1;
}
";
    let program = Compiler::compile_source(src).expect("compiles");
    let ir = LlvmLowering::lower(&program).expect("lowers");
    let out = lli(&ir);
    assert_eq!(out.status.code(), Some(42), "{}", String::from_utf8_lossy(&out.stderr));
    for (src, expected) in [
        (
            "opaque(linear) Tx { id: i32, pub fn new(i: i32) -> Self { return Self { id: i }; } pub fn commit(move self) -> i32 { return self.id; } }\npub fn main() -> i32 { let mut v = Vec(Tx)::new(); v.push(Tx::new(1)); return 0; }",
            "must be explicitly consumed",
        ),
        (
            "opaque(linear) Tx { id: i32, pub fn new(i: i32) -> Self { return Self { id: i }; } pub fn commit(move self) -> i32 { return self.id; } }\npub fn main() -> i32 { let mut v = Vec(Tx)::new(); v.clear(); v.drain(fn(t: Tx) { let _ = t.commit(); }); return 0; }",
            "'T: !linear' is not satisfied",
        ),
    ] {
        let err = Compiler::compile_source(src).expect_err("rejected");
        assert!(err.contains(expected), "{err}");
    }
}

#[test]
fn test_std_string_io_and_hashmap() {
    let path = std::env::temp_dir().join(format!("lrrr_std_io_{}.txt", std::process::id()));
    let path = path.to_str().unwrap().to_string();
    let src = format!(
        "
opaque(linear) Tx {{
    id: i32,
    pub fn new(i: i32) -> Self {{ return Self {{ id: i }}; }}
    pub fn commit(move self) -> i32 {{ return self.id; }}
}}
pub fn main() -> i32 {{
    let mut s = String::from(\"caf\");
    s.push('é');
    s.push_str(\" 🦀\");
    if s.as_str() != \"café 🦀\" || s.len() != 10 {{ return 1; }}
    if !write_file(\"{path}\", s.as_str()) {{ return 2; }}
    let back = read_file(\"{path}\") orelse return 3;
    if back.as_str() != s.as_str() {{ return 4; }}
    let line = read_line() orelse return 5;
    if line.as_str() != \"input\" {{ return 6; }}

    let mut counts = HashMap(&str, i32)::new();
    for w in 0..3 {{
        let _ = counts.insert(\"a\", w);
    }}
    let _ = counts.insert(\"b\", 30);
    let a = counts.get(\"a\") orelse return 7;
    let b = counts.get(\"b\") orelse return 8;
    let mut big = HashMap(u32, u32)::new();
    for i in 0..500 {{ let _ = big.insert(i, i); }}
    for i in 0..250 {{ let _ = big.remove(i); }}
    if big.len() != 250 || big.contains_key(3) {{ return 9; }}

    let mut txs = HashMap(i32, Tx)::new();
    let r = txs.insert(1, Tx::new(10));
    let mut done: i32 = 0;
    txs.drain(fn(k: i32, t: Tx) {{ done += t.commit(); }});
    if let t = r {{ done += t.commit(); }}
    return *a + *b + done;                      // 2 + 30 + 10
}}"
    );
    let program = Compiler::compile_source(&src).expect("compiles");
    let ir = LlvmLowering::lower(&program).expect("lowers");
    // `read_line` reads the first line of standard input.
    let ll = std::env::temp_dir().join(format!("lrrr_std_io_{}.ll", std::process::id()));
    std::fs::write(&ll, ir).unwrap();
    let out = std::process::Command::new("sh")
        .arg("-c")
        .arg(format!("printf 'input\\nrest' | lli {}", ll.display()))
        .output()
        .unwrap();
    let _ = std::fs::remove_file(&ll);
    let _ = std::fs::remove_file(&path);
    assert_eq!(out.status.code(), Some(42), "{}", String::from_utf8_lossy(&out.stderr));
}
