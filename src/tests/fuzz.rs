//! Randomized soundness testing of the borrow, move, and drop checkers. Generates safe programs
//! over scopes, references, containers of references, linear values in every container shape,
//! pattern matching, `drop` hooks that read their borrows, iterators, closures, threads, nested
//! tuples (assembled field by field, reached by paths, split and joined), functions with
//! `borrows` contracts, user-written containers and views, arrays of `Box`es, recursive lists
//! (some deep enough to queue their drops), a `clone`-bounded generic, vectors with inline
//! storage (alone, and inside heap vectors), `zeroinit` values, and generators (helpers driven
//! fully, partly, or not at all, and a generated body per program whose locals cross its
//! `yield`s), and checks
//! that every program the compiler accepts:
//! - runs under the compile-time VM without undefined behaviour or leaks,
//! - consumes every linear `Tx` it creates exactly once (`main` returns -1 otherwise), and
//! - computes what the native build computes,
//!
//! under the VM's default thread order and, for threaded programs, several seeded interleavings.
//!
//! `SLOPLANG_FUZZ_CASES` (default 50), `SLOPLANG_FUZZ_SEED` (default 1), and `SLOPLANG_FUZZ_WORKERS` (default
//! the number of cores) control the run; a failure
//! prints the seed and a shrunk program, which `SLOPLANG_FUZZ_SEED=<seed> SLOPLANG_FUZZ_CASES=1`
//! reproduces.

use super::{TRAP_EXIT, VmRun, lli, run_vm_scheduled};
use crate::lower::Compiler;

/// xorshift64*: deterministic across platforms, so a seed always reproduces its program.
pub(super) struct Rng(u64);

impl Rng {
    pub(super) fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    pub(super) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum Kind {
    Int,
    Ref,
    /// A `&mut i32`, whose writes conflict with every other borrow of its target.
    MutRef,
    VecRef,
    VecInt,
    BoxRef,
    IterRef,
    IterMut,
    /// A struct holding a reference (`RefPair`).
    RefField,
    /// A value whose `drop` hook reads the reference it holds (`Peek`).
    Peek,
    VecPeek,
    Tx,
    OptTx,
    UnionTx,
    PairTx,
    BoxTx,
    VecTx,
    WrapTx,
    /// A `ScopedHandle` (linear: joined exactly once).
    Thread,
    MutexInt,
    ChanInt,
    ChanTx,
    /// A nested tuple of `i32` (`TI`), reached by field paths.
    TreeInt,
    /// A nested tuple of linear `Tx` (`TT`), possibly assembled and refilled field by field.
    TreeTx,
    /// Droppable values, moved on some paths only: what is left must be dropped exactly once.
    BoxInt,
    OwnedStr,
    OptBox,
    UnionBox,
    BoxTuple,
    /// A `Box` from the `Tracked` allocator, which must be freed by it.
    TrackedBox,
    /// A `Box` from an allocator instance, which it must not outlive.
    PoolBox,
    /// A trait object over a value holding a reference.
    TraitRef,
    /// The `ByRef` a trait object is taken from.
    ByRefHolder,
    /// An inline array, and a slice of one.
    IntArray,
    SliceRef,
    /// A value with `&rel` fields into itself, which must survive moves.
    Relative,
    /// A struct filled through a function's `borrows(dst: x)` contract (`Slot`).
    Slot,
    /// A user-written owning container of a reference (`Held`).
    HeldRef,
    /// A user-written view that declares what it borrows (`View`).
    ViewRef,
    /// An array of `Box`es, whose elements are replaced and which is dropped or moved whole.
    BoxArray,
    /// A recursive list (`Node` through `?Box`), sometimes deep enough to defer its drops.
    List,
    /// A vector with inline storage (`ArrayVec[Box[i32], 4]`), which moves with its slots.
    SlotVec,
}

impl Kind {
    /// A linear kind: must be consumed exactly once.
    fn linear(self) -> bool {
        matches!(
            self,
            Kind::Tx
                | Kind::OptTx
                | Kind::UnionTx
                | Kind::PairTx
                | Kind::BoxTx
                | Kind::VecTx
                | Kind::WrapTx
                | Kind::Thread
                | Kind::ChanTx
                | Kind::TreeTx
        )
    }
}

/// Types every program can use. `LIVE` counts `Tx` values created and not yet committed.
const PRELUDE: &str = "\
static mut LIVE: i32 = 0;
static mut SINK: i32 = 0;
pub opaque(linear) Tx {
    id: i32,
    pub fn new(i: i32) -> Self { unsafe { LIVE = LIVE + 1; } return Self { id: i }; }
    pub fn commit(self) -> i32 { unsafe { LIVE = LIVE - 1; } return self.id; }
}
pub struct Pair { t: Tx, n: i32 }
fn x_commit(t: Tx) { unsafe { SINK = SINK + t.commit(); } }
pub struct RefPair { r: &i32, n: i32 }
union UT { A(Tx), B(i32) }
union UB { S(Box[i32]), N(i32) }
pub opaque Peek {
    r: &i32,
    impl drop { fn drop(&mut self) { unsafe { SINK = SINK + *self.r; } } }
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
}
pub opaque(linear) Wrap {
    t: Tx,
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn finish(self) -> i32 { return self.t.commit(); }
}
static mut TRACKED: i32 = 0;
extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
pub struct Tracked { }
unsafe impl Allocator for Tracked {
    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 {
        unsafe { TRACKED = TRACKED + 1; return malloc(bytes); }
    }
    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        unsafe { return realloc(ptr, bytes); }
    }
    fn dealloc(&self, ptr: *mut u8) { unsafe { TRACKED = TRACKED - 1; free(ptr); } }
}
pub struct TPool { x: i32 }
unsafe impl Allocator for TPool {
    fn alloc(&self, bytes: usize, align: usize) -> *mut u8 {
        unsafe { TRACKED = TRACKED + self.x; return malloc(bytes); }
    }
    fn realloc(&self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        unsafe { return realloc(ptr, bytes); }
    }
    fn dealloc(&self, ptr: *mut u8) { unsafe { TRACKED = TRACKED - self.x; free(ptr); } }
}
fn eat_any[B: unchecked](b: B) -> i32 { return b.into_inner(); }
fn mkv(n: i32) -> Vec[i32] { let mut v = Vec[i32]::new(); v.push(n); return v; }
fn vlen(v: &Vec[i32]) -> i32 { return v.len() as i32; }
fn positive(v: &Vec[i32]) -> ?i32 { let n = *(v.get(0) orelse unreachable); if n > 0 { return n; } return null; }
fn vec_sum(n: i32) -> i32 {
    let mut w = Vec[Box[i32, Tracked], Tracked]::new();
    for i in 0..n { w.push(Box[i32, Tracked]::new(i)); }
    let mut t: i32 = 0;
    for x in w.iter() { t = t + *x.get(); }
    return t + eat_any(Box[i32]::new(n));
}
union UB { A(Box[i32]), B(i32) }
fn eat_box(b: Box[i32]) -> i32 { return b.into_inner(); }
fn eat_str(t: String) -> i32 { return t.len() as i32; }
fn eat_vec(w: Vec[i32]) -> i32 { return w.len() as i32; }
fn pass_box(b: Box[i32]) -> Box[i32] { return b; }
pub struct Slot { r: &i32 }
fn bump(a: &mut i32) -> &mut i32 borrows(a) { *a = *a + 1; return a; }
fn id_ref[T](x: &T) -> &T { return x; }
fn keep[T](v: &mut Vec[T], x: T) borrows(v: x) { v.push(x); }
fn either[T](a: &T, b: &T, c: bool) -> &T borrows(a, b) { if c { return a; } return b; }
fn Held[T]() -> type {
    return opaque {
        ptr: *own T,
        unsafe impl drop(may_dangle T) {
            fn drop(&mut self) { unsafe { @drop(self.ptr); @dealloc(self.ptr); } }
        }
        pub fn new(val: T) -> Self {
            let p: *own T = unsafe { @alloc(T, 1) as *own T };
            unsafe { *p = val; }
            return Self { ptr: p };
        }
        pub fn get(&self) -> &T { unsafe { return &*self.ptr; } }
        pub fn into_inner(self) -> T {
            unsafe {
                let p: *mut T = self.ptr;
                let val = move *p;
                @dealloc(p);
                @forget(self);
                return val;
            }
        }
    };
}
fn View[T]() -> type {
    return opaque {
        p: *ref T,
        pub fn at(x: &T) -> Self borrows(x) { return Self { p: x as *ref T }; }
        pub fn get(&self) -> &T borrows(*self) { unsafe { return &*self.p; } }
    };
}
fn view(x: &i32) -> View[i32] borrows(x) { return View[i32]::at(x); }
pub trait Reader { fn value(&self) -> i32; }
pub struct ByRef { r: &i32 }
impl Reader for ByRef { fn value(&self) -> i32 { return *self.r; } }
fn read_it[T: Reader](x: &T) -> i32 { return x.value(); }
fn run[F: callable](f: F) -> i32 { return f(); }
fn sum(a: &[i32]) -> i32 { let mut t: i32 = 0; for i in 0..a.len { t = t + a[i]; } return t; }
fn tail(a: &[i32]) -> &[i32] borrows(a) { return a[1..]; }
pub opaque Rel {
    nums: [i32; 4],
    focus: &rel i32,
    window: &rel [i32],
    pub fn new(n: i32) -> Self {
        return Self { nums: [n, 1, 2, 3], focus: &rel self.nums[1], window: &rel self.nums[1..3] };
    }
    pub fn read(&self) -> i32 { return *self.focus + self.window[1]; }
    pub fn set(&mut self, v: i32) { *self.focus += v; self.window[1] = v; }
    pub fn refocus(&mut self, i: usize) { self.focus = &rel self.nums[i]; }
    pub fn peek(&self) -> &i32 { return self.focus; }
}
fn relay(x: Rel) -> tuple { i32, Rel } { return .{ 1, x }; }
fn eat_arr(a: [Box[i32]; 2]) -> i32 { return *a[0].get() + *a[1].get(); }
pub struct Node { v: i32, next: ?Box[Node] }
fn chain(n: i32) -> ?Box[Node] {
    if n == 0 { return null; }
    return Box[Node]::new(Node { v: n, next: chain(n - 1) });
}
fn total(n: &Node) -> i32 { let mut t = n.v; if let ?ref b = n.next { t = t + total(b.get()); } return t; }
fn bump_all(n: &mut Node) { n.v = n.v + 1; if let ?ref mut b = n.next { bump_all(b.get_mut()); } }
fn eat_list(n: Node) -> i32 { return total(&n); }
fn twin[T: clone](x: &T) -> tuple { T, T } { return .{ @clone(x), @clone(x) }; }
fn pass_on[T: ?linear](x: T) -> T { return x; }
fn Cell[T: ?linear]() -> type {
    return opaque {
        v: T,
        pub fn new(v: T) -> Self { return Self { v: v }; }
        pub fn take(self) -> T { return self.v; }
    };
}
alias TI = tuple { i32, tuple { i32, i32 } };
alias TT = tuple { Tx, tuple { Tx, Tx } };
fn only_int[T: unchecked](x: T) -> i32 {
    if @satisfies(T, integer) { return x as i32; } else { @compile_error(\"only_int: got \", T); }
}
";

/// Builds one program: `body` sums values read through the borrows it creates into `s`.
struct Gen {
    rng: Rng,
    out: String,
    /// Top-level items the body uses: the program's generated generator.
    items: String,
    scopes: Vec<Vec<(String, Kind)>>,
    next_name: usize,
}

impl Gen {
    fn pick(&mut self, kind: Kind) -> Option<String> {
        self.pick_in(kind, 0..self.scopes.len())
    }

    /// A variable of `kind` from the scopes in `range` (outermost first).
    fn pick_in(&mut self, kind: Kind, range: std::ops::Range<usize>) -> Option<String> {
        let vars: Vec<String> = self.scopes[range]
            .iter()
            .flatten()
            .filter(|(_, k)| *k == kind)
            .map(|(n, _)| n.clone())
            .collect();
        (!vars.is_empty()).then(|| vars[self.rng.below(vars.len())].clone())
    }

    /// Picks a variable of `kind` to move: usually from the innermost scope (so the move is
    /// unconditional and the program can compile), sometimes from any scope.
    fn take(&mut self, kind: Kind) -> Option<String> {
        let inner = self.scopes.len() - 1;
        let range = if self.rng.below(4) == 0 { 0..inner + 1 } else { inner..inner + 1 };
        let name = self.pick_in(kind, range)?;
        for scope in &mut self.scopes {
            scope.retain(|(n, _)| *n != name);
        }
        Some(name)
    }

    fn declare(&mut self, prefix: &str, kind: Kind) -> String {
        self.next_name += 1;
        let name = format!("{prefix}{}", self.next_name);
        self.scopes.last_mut().unwrap().push((name.clone(), kind));
        name
    }

    fn line(&mut self, depth: usize, text: &str) {
        self.out.push_str(&"    ".repeat(depth + 1));
        self.out.push_str(text);
        self.out.push('\n');
    }

    fn local_int(&mut self, depth: usize) {
        let n = self.declare("n", Kind::Int);
        let v = self.rng.below(9);
        self.line(depth, &format!("let mut {n}: i32 = {v};"));
    }

    fn small(&mut self) -> usize {
        self.rng.below(3)
    }

    fn block(&mut self, depth: usize, len: usize) {
        for _ in 0..len {
            self.stmt(depth);
        }
    }

    /// A nested scope that ends by consuming the linear values declared in it.
    fn nested(&mut self, depth: usize, head: &str) {
        self.line(depth, head);
        self.scopes.push(Vec::new());
        self.local_int(depth + 1);
        let len = 1 + self.rng.below(5);
        self.block(depth + 1, len);
        self.close_scope(depth + 1);
        self.scopes.pop();
        self.line(depth, "}");
        // What the block let escape dangles now: reading it is what shows that.
        for _ in 0..2 {
            self.read(depth);
        }
    }

    /// Consumes, soundly, every linear value still alive in the innermost scope.
    fn close_scope(&mut self, depth: usize) {
        let linear: Vec<(String, Kind)> = self
            .scopes
            .last()
            .unwrap()
            .iter()
            .filter(|(_, k)| k.linear())
            .cloned()
            .collect();
        for (name, kind) in linear {
            self.scopes.last_mut().unwrap().retain(|(n, _)| *n != name);
            let id = self.next_name;
            self.next_name += 1;
            let text = consume(&name, kind, id, true);
            self.line(depth, &text);
        }
    }

    /// Inside a nested block: an outer borrow-holder borrows a local of this block, the pattern
    /// behind every escaping borrow. Whether it compiles depends on what comes after.
    fn escape(&mut self, depth: usize) -> bool {
        let inner = self.scopes.len() - 1;
        if inner == 0 {
            return false;
        }
        let Some(local) = self.pick_in(Kind::Int, inner..inner + 1) else {
            return false;
        };
        let kinds = [
            Kind::Ref,
            Kind::MutRef,
            Kind::VecRef,
            Kind::BoxRef,
            Kind::RefField,
            Kind::Peek,
            Kind::VecPeek,
            Kind::Slot,
            Kind::HeldRef,
            Kind::ViewRef,
            Kind::ByRefHolder,
        ];
        let kind = kinds[self.rng.below(kinds.len())];
        let Some(outer) = self.pick_in(kind, 0..inner) else {
            return false;
        };
        let text = match kind {
            Kind::Ref => format!("{outer} = &{local};"),
            Kind::MutRef => format!("{outer} = &mut {local};"),
            Kind::VecRef => format!("{outer}.push(&{local});"),
            Kind::BoxRef => format!("{outer} = Box[&i32]::new(&{local});"),
            Kind::RefField => format!("{outer}.r = &{local};"),
            Kind::Peek => format!("{outer} = Peek::new(&{local});"),
            Kind::Slot => format!("stash(&mut {outer}, &{local}, &{local});"),
            Kind::HeldRef => format!("{outer} = Held[&i32]::new(&{local});"),
            Kind::ViewRef => format!("{outer} = view(&{local});"),
            Kind::ByRefHolder => format!("{outer}.r = &{local};"),
            _ => format!("{outer}.push(Peek::new(&{local}));"),
        };
        self.line(depth, &text);
        true
    }

    /// A read through some borrow-holding variable in scope.
    fn read(&mut self, depth: usize) {
        let k = self.small();
        let text = match self.rng.below(10) {
            7 => self.pick(Kind::Slot).map(|n| format!("s = s + *{n}.r;")),
            8 => self.pick(Kind::HeldRef).map(|n| format!("s = s + **{n}.get();")),
            9 => self.pick(Kind::ViewRef).map(|n| format!("s = s + *{n}.get();")),
            6 => self.pick(Kind::MutRef).map(|m| format!("*{m} = *{m} + 1; s = s + *{m};")),
            0 => self.pick(Kind::Ref).map(|r| format!("s = s + *{r};")),
            1 => self
                .pick(Kind::VecRef)
                .map(|v| format!("if let ?e = {v}.get({k}) {{ s = s + **e; }}")),
            2 => self.pick(Kind::BoxRef).map(|b| format!("s = s + **{b}.get();")),
            3 => self
                .pick(Kind::IterRef)
                .map(|t| format!("if let ?e = {t}.next() {{ s = s + **e; }}")),
            4 => self.pick(Kind::RefField).map(|p| format!("s = s + *{p}.r + {p}.n;")),
            _ => self
                .pick(Kind::IterMut)
                .map(|t| format!("if let ?a = {t}.next() {{ *a = *a + 1; s = s + *a; }}")),
        };
        if let Some(text) = text {
            self.line(depth, &text);
        }
    }

    fn stmt(&mut self, depth: usize) {
        let choice = self.rng.below(155);
        if choice >= 151 {
            self.union_match(depth);
            return;
        }
        if choice >= 140 {
            self.generators(depth, choice - 140);
            return;
        }
        if choice >= 134 {
            self.heap(depth, choice - 112);
            return;
        }
        if choice >= 131 {
            self.heap(depth, if choice == 131 { 20 } else { 21 });
            return;
        }
        if choice >= 125 {
            self.temporaries(depth);
            return;
        }
        // Each of `erased`'s 18 statements.
        if choice >= 107 {
            self.erased(depth, choice - 107);
            return;
        }
        if choice >= 86 {
            self.signature(depth, choice - 86);
            return;
        }
        if choice >= 66 {
            self.heap(depth, choice - 66);
            return;
        }
        if choice >= 54 {
            self.tree(depth, choice - 54);
            return;
        }
        if choice >= 46 {
            self.concurrent(depth, choice - 46);
            return;
        }
        if choice >= 40 {
            // Escapes and reads are what exercise scope ends; make them common.
            if choice < 42 && self.escape(depth) {
                return;
            }
            self.read(depth);
            return;
        }
        let Some(i) = self.pick(Kind::Int) else {
            self.local_int(depth);
            return;
        };
        let k = self.small();
        let v = self.rng.below(9);
        let id = self.next_name + 1;
        match choice {
            0 | 1 => self.local_int(depth),
            2 | 3 => {
                if self.rng.below(3) == 0 {
                    // Half the time of an integer of its own, which nothing else names, so
                    // that what it writes (from a thread, say) conflicts with nothing else.
                    if self.rng.below(2) == 0 {
                        self.next_name += 1;
                        let n = self.declare("mr", Kind::MutRef);
                        self.line(depth, &format!("let mut mt{id}: i32 = {v};"));
                        self.line(depth, &format!("let mut {n}: &mut i32 = &mut mt{id};"));
                    } else {
                        let n = self.declare("mr", Kind::MutRef);
                        self.line(depth, &format!("let mut {n}: &mut i32 = &mut {i};"));
                    }
                } else {
                    let n = self.declare("r", Kind::Ref);
                    self.line(depth, &format!("let mut {n}: &i32 = &{i};"));
                }
            }
            4 => match self.pick(Kind::Ref) {
                Some(r) => self.line(depth, &format!("{r} = &{i};")),
                None => self.line(depth, &format!("{i} = {i} + 1;")),
            },
            5 => self.line(depth, &format!("{i} = {i} + 1;")),
            6 => {
                let n = self.declare("v", Kind::VecRef);
                self.line(depth, &format!("let mut {n} = Vec[&i32]::new();"));
            }
            7 => match (self.pick(Kind::VecRef), self.pick(Kind::Ref)) {
                (Some(vr), Some(r)) if self.rng.below(2) == 0 => {
                    self.line(depth, &format!("{vr}.push({r});"));
                }
                (Some(vr), _) => self.line(depth, &format!("{vr}.push(&{i});")),
                (None, _) => self.line(depth, &format!("s = s + {i};")),
            },
            8 => {
                let n = self.declare("w", Kind::VecInt);
                self.line(depth, &format!("let mut {n} = Vec[i32]::new();"));
            }
            9 => {
                if let Some(w) = self.pick(Kind::VecInt) {
                    self.line(depth, &format!("{w}.push({v});"));
                }
            }
            10 => match (self.pick(Kind::VecInt), self.pick(Kind::Ref)) {
                (Some(w), Some(r)) => self.line(depth, &format!("{r} = {w}.get({k}) orelse {r};")),
                (Some(w), None) => {
                    self.line(depth, &format!("if let ?e = {w}.get({k}) {{ s = s + *e; }}"));
                }
                _ => {}
            },
            11 => {
                let n = self.declare("b", Kind::BoxRef);
                self.line(depth, &format!("let mut {n} = Box[&i32]::new(&{i});"));
            }
            12 => {
                let kind = [Kind::VecRef, Kind::VecInt, Kind::BoxRef, Kind::VecPeek][self.rng.below(4)];
                if let Some(x) = self.take(kind) {
                    if self.rng.below(2) == 0 {
                        self.line(depth, &format!("@drop({x});"));
                    } else {
                        let n = self.declare("m", kind);
                        self.line(depth, &format!("let mut {n} = {x};"));
                    }
                }
            }
            13 => {
                if let Some(vr) = self.pick(Kind::VecRef) {
                    let n = self.declare("t", Kind::IterRef);
                    self.line(depth, &format!("let mut {n} = {vr}.iter();"));
                }
            }
            14 => match (self.pick(Kind::VecRef), self.pick(Kind::Ref)) {
                (Some(vr), Some(r)) => {
                    self.line(depth, &format!("if let ?e = {vr}.get({k}) {{ {r} = *e; }}"));
                }
                _ => {}
            },
            15 => {
                if let Some(r) = self.pick(Kind::Ref) {
                    let n = self.declare("c", Kind::Int);
                    self.line(depth, &format!("let g{n} = fn() -> i32 {{ return *{r}; }};"));
                    self.line(depth, &format!("let mut {n}: i32 = g{n}();"));
                }
            }
            16 => {
                if let Some(w) = self.pick(Kind::VecInt) {
                    if self.rng.below(2) == 0 {
                        self.line(depth, &format!("for x in {w}.iter_mut() {{ *x = *x + 1; }}"));
                    } else {
                        let n = self.declare("im", Kind::IterMut);
                        self.line(depth, &format!("let mut {n} = {w}.iter_mut();"));
                    }
                }
            }
            17 => {
                let n = self.declare("p", Kind::RefField);
                self.line(depth, &format!("let mut {n} = RefPair {{ r: &{i}, n: {v} }};"));
            }
            18 => {
                let n = self.declare("k", Kind::Peek);
                self.line(depth, &format!("let mut {n} = Peek::new(&{i});"));
            }
            19 => {
                let n = self.declare("q", Kind::VecPeek);
                self.line(depth, &format!("let mut {n} = Vec[Peek]::new();"));
                self.line(depth, &format!("{n}.push(Peek::new(&{i}));"));
            }
            // Linear values, in every container shape.
            20 | 21 => {
                // Sometimes through a generic that takes linear values.
                let made = match self.rng.below(6) {
                    0 => format!("pass_on(Tx::new({v}))"),
                    1 => format!("Cell[Tx]::new(Tx::new({v})).take()"),
                    _ => format!("Tx::new({v})"),
                };
                if self.rng.below(2) == 0
                    && let Some(y) = self.take(Kind::Tx)
                {
                    let a = self.declare("x", Kind::Tx);
                    let b = self.declare("x", Kind::Tx);
                    self.line(depth, &format!("let .{{ {a}, {b} }} = swap_pair({made}, {y});"));
                } else {
                    let n = self.declare("x", Kind::Tx);
                    self.line(depth, &format!("let {n} = {made};"));
                }
            }
            22 => {
                let n = self.declare("o", Kind::OptTx);
                let init = match self.rng.below(4) {
                    0 => "null".to_string(),
                    1 => format!("some_of(Tx::new({v}), {i} > {k})"),
                    _ => format!("Tx::new({v})"),
                };
                self.line(depth, &format!("let {n}: ?Tx = {init};"));
            }
            23 => {
                let n = self.declare("y", Kind::UnionTx);
                let init = if self.rng.below(2) == 0 { format!("UT::A(Tx::new({v}))") } else { format!("UT::B({v})") };
                self.line(depth, &format!("let {n} = {init};"));
            }
            24 => {
                let n = self.declare("z", Kind::PairTx);
                self.line(depth, &format!("let {n} = Pair {{ t: Tx::new({v}), n: {k} }};"));
            }
            25 => {
                let n = self.declare("h", Kind::BoxTx);
                self.line(depth, &format!("let {n} = Box[Tx]::new(Tx::new({v}));"));
            }
            26 => {
                let n = self.declare("d", Kind::VecTx);
                self.line(depth, &format!("let mut {n} = Vec[Tx]::new();"));
            }
            27 => {
                if let Some(d) = self.pick(Kind::VecTx) {
                    self.line(depth, &format!("{d}.push(Tx::new({v}));"));
                }
            }
            28 => {
                let n = self.declare("j", Kind::WrapTx);
                self.line(depth, &format!("let {n} = Wrap::new(Tx::new({v}));"));
            }
            29..=32 => {
                // Consume a linear value, sometimes in a way that should not compile.
                let kinds = [Kind::Tx, Kind::OptTx, Kind::UnionTx, Kind::PairTx, Kind::BoxTx, Kind::VecTx, Kind::WrapTx, Kind::TreeTx];
                let kind = kinds[self.rng.below(kinds.len())];
                if let Some(x) = self.take(kind) {
                    let sound = self.rng.below(4) != 0;
                    let text = consume(&x, kind, id, sound);
                    self.next_name += 1;
                    self.line(depth, &text);
                }
            }
            33 => {
                if let Some(x) = self.take(Kind::Tx) {
                    self.next_name += 1;
                    self.line(depth, &format!("let fc{id} = move fn() -> i32 {{ return {x}.commit(); }};"));
                    self.line(depth, &format!("s = s + fc{id}();"));
                }
            }
            34 | 35 => {
                // Move a linear value into a container or another binding.
                if let Some(x) = self.take(Kind::Tx) {
                    match self.rng.below(7) {
                        0 => {
                            if let Some(d) = self.pick(Kind::VecTx) {
                                self.line(depth, &format!("{d}.push({x});"));
                            } else {
                                let n = self.declare("x", Kind::Tx);
                                self.line(depth, &format!("let {n} = {x};"));
                            }
                        }
                        1 => {
                            let n = self.declare("o", Kind::OptTx);
                            self.line(depth, &format!("let {n}: ?Tx = {x};"));
                        }
                        2 => {
                            let n = self.declare("j", Kind::WrapTx);
                            self.line(depth, &format!("let {n} = Wrap::new({x});"));
                        }
                        // Through generics that take linear values.
                        3 => {
                            let n = self.declare("x", Kind::Tx);
                            self.line(depth, &format!("let {n} = pass_on({x});"));
                        }
                        4 => {
                            self.next_name += 1;
                            let n = self.declare("x", Kind::Tx);
                            self.line(depth, &format!("let ce{id} = Cell[Tx]::new({x});"));
                            self.line(depth, &format!("let {n} = ce{id}.take();"));
                        }
                        5 => {
                            let n = self.declare("o", Kind::OptTx);
                            self.line(depth, &format!("let {n} = some_of({x}, {i} > {k});"));
                        }
                        _ => match self.take(Kind::Tx) {
                            Some(y) => {
                                let a = self.declare("x", Kind::Tx);
                                let b = self.declare("x", Kind::Tx);
                                self.line(depth, &format!("let .{{ {a}, {b} }} = swap_pair({x}, {y});"));
                            }
                            None => {
                                let n = self.declare("x", Kind::Tx);
                                self.line(depth, &format!("let {n} = pass_on({x});"));
                            }
                        },
                    }
                }
            }
            36 | 37 => self.nested(depth, "if true {"),
            _ => {
                let counter = format!("l{id}");
                self.next_name += 1;
                self.nested(depth, &format!("for {counter} in 0..2 {{"));
            }
        }
    }
}

impl Gen {
    /// Scoped threads, a shared `Mutex`, and channels (of `i32` and of linear `Tx`). The results
    /// of `try_send` and `try_recv` stay out of `s`: whether one succeeds depends on how threads
    /// interleave.
    fn concurrent(&mut self, depth: usize, which: usize) {
        let v = self.rng.below(9);
        let id = self.next_name + 1;
        // The closure returns `v`, not the mutex's value, which depends on which thread locks first.
        let lock = format!("with_lock(fn(x{id}: &mut i32) -> i32 {{ *x{id} = *x{id} + {v}; return {v}; }})");
        match which {
            0 => {
                // A thread reading borrows of this or outer scopes; joined at scope end at latest.
                let body = self.thread_body(v, id, &lock, false);
                let n = self.declare("th", Kind::Thread);
                self.line(depth, &format!("let {n} = spawn_scoped(fn() -> i32 {{ {body} }});"));
            }
            1 => {
                // A thread live for a statement or two, which the checker must keep away from
                // what the thread writes (and from writing what it reads); the VM reports races.
                let body = self.thread_body(v, id, &lock, true);
                let n = format!("tw{id}");
                self.next_name += 1;
                // `async` lowers to `start_task`; a generated body has no function to call.
                let task = format!("fn() -> i32 {{ {body} }}");
                let start = match self.rng.below(3) {
                    0 => format!("spawn_scoped({task})"),
                    1 => format!("std::thread::start_task({task})"),
                    _ => format!("std::thread::start_task_on({task}, Fibers {{ }})"),
                };
                self.line(depth, &format!("let {n} = {start};"));
                for _ in 0..1 + self.rng.below(2) {
                    self.stmt(depth);
                }
                self.line(depth, &format!("s = s + {n}.await();"));
            }
            2 => {
                if let Some(t) = self.take(Kind::Thread) {
                    self.line(depth, &format!("s = s + {t}.join();"));
                }
            }
            3 => {
                let n = self.declare("mx", Kind::MutexInt);
                self.line(depth, &format!("let {n} = Mutex[i32]::new({v});"));
            }
            4 => {
                if let Some(m) = self.pick(Kind::MutexInt) {
                    self.line(depth, &format!("s = s + {m}.{lock};"));
                }
            }
            5 => {
                if self.rng.below(2) == 0 {
                    let n = self.declare("ch", Kind::ChanInt);
                    self.line(depth, &format!("let {n} = Channel[i32]::new();"));
                } else {
                    let n = self.declare("cx", Kind::ChanTx);
                    self.line(depth, &format!("let {n} = Channel[Tx]::new();"));
                }
            }
            6 => match (self.pick(Kind::ChanInt), self.pick(Kind::ChanTx)) {
                (Some(c), _) if self.rng.below(2) == 0 => {
                    let send = format!("if let ?b{id} = {c}.try_send({v}) {{ let _u{id} = b{id}; }}");
                    self.next_name += 1;
                    self.line(depth, &send);
                }
                (_, Some(c)) => {
                    let send = format!(
                        "if let ?b{id} = {c}.try_send(Tx::new({v})) {{ let _u{id} = b{id}.commit(); }}"
                    );
                    self.next_name += 1;
                    self.line(depth, &send);
                }
                (Some(c), None) => {
                    let n = self.declare("th", Kind::Thread);
                    self.line(
                        depth,
                        &format!("let {n} = spawn_scoped(fn() -> i32 {{ if let ?b{id} = {c}.try_send({v}) {{ let _u{id} = b{id}; }} return 0; }});"),
                    );
                }
                _ => {}
            },
            _ => match (self.pick(Kind::ChanInt), self.pick(Kind::ChanTx)) {
                (Some(c), _) if self.rng.below(2) == 0 => {
                    self.next_name += 1;
                    self.line(depth, &format!("if let ?g{id} = {c}.try_recv() {{ let _u{id} = g{id}; }}"));
                }
                (_, Some(c)) => {
                    self.next_name += 1;
                    self.line(depth, &format!("if let ?g{id} = {c}.try_recv() {{ let _u{id} = g{id}.commit(); }}"));
                }
                _ => {}
            },
        }
    }
}

impl Gen {
    /// Values with no name, which something borrows: they must be dropped, on every path, and a
    /// reference to one must not outlive it.
    fn temporaries(&mut self, depth: usize) {
        let v = self.rng.below(5);
        let id = self.next_name + 1;
        self.next_name += 1;
        let line = match self.rng.below(10) {
            0 => format!("s = s + mkv({v}).len() as i32;"),
            1 => format!("s = s + vlen(&mkv({v}));"),
            2 => format!("s = s + *Box[i32]::new({v}).get();"),
            3 => format!("s = s + format({v}).len() as i32;"),
            4 => format!("if mkv({v}).len() == 1 {{ s = s + 1; }}"),
            5 => format!("let mut tn{id}: i32 = {v}; while let ?x{id} = positive(&mkv(tn{id})) {{ s = s + x{id}; tn{id} = tn{id} - 1; }}"),
            6 => format!("let tr{id} = &mkv({v}); s = s + vlen(tr{id});"),
            7 => format!("let cn{id}: i32 = {v}; if cn{id} > 1 && mkv(cn{id}).len() == 1 {{ s = s + 1; }}"),
            8 => format!("if let ?tp{id} = mkv({v}).pop() {{ s = s + tp{id}; }}"),
            // The temporary is gone by the time this reads it: this must not be accepted.
            _ => format!("let tg{id} = mkv({v}).get(0); if let ?x{id} = tg{id} {{ s = s + *x{id}; }}"),
        };
        self.line(depth, &line);
    }

    /// The body of a scoped thread: reads or writes variables of this or outer scopes (usually
    /// writes, if `write`).
    fn thread_body(&mut self, v: usize, id: usize, lock: &str, write: bool) -> String {
        let choice = if write && self.rng.below(4) != 0 {
            // Writing through a `&mut` or into a vector needs one to be there; prefer them when
            // they are, as they are rarer than an integer.
            if self.rng.below(2) == 0 && self.pick(Kind::MutRef).is_some() {
                2
            } else if self.rng.below(2) == 0 && self.pick(Kind::VecInt).is_some() {
                4
            } else {
                [1, 2, 4, 7][self.rng.below(4)]
            }
        } else {
            self.rng.below(9)
        };
        let body = match choice {
            0 => self.pick(Kind::MutexInt).map(|m| format!("return {m}.{lock};")),
            1 => self.pick(Kind::Int).map(|i| format!("{i} = {i} + {v}; return 0;")),
            2 => self.pick(Kind::MutRef).map(|m| format!("*{m} = *{m} + {v}; return 0;")),
            3 => self.pick(Kind::VecInt).map(|w| {
                format!("let mut t{id}: i32 = 0; for e{id} in {w}.iter() {{ t{id} = t{id} + *e{id}; }} return t{id};")
            }),
            4 => self.pick(Kind::VecInt).map(|w| format!("{w}.push({v}); return 0;")),
            5 => self.pick(Kind::RefField).map(|p| format!("return *{p}.r + {p}.n;")),
            6 => self.pick(Kind::TreeInt).map(|t| {
                let p = self.int_path();
                format!("return @field({t}, {p});")
            }),
            7 => self.pick(Kind::TreeInt).map(|t| {
                let p = self.int_path();
                format!("@field({t}, {p}) = {v}; return 0;")
            }),
            _ => None,
        };
        body.unwrap_or_else(|| match (self.pick(Kind::Ref), self.pick(Kind::Int)) {
            (Some(r), Some(i)) => format!("return *{r} + {i};"),
            (_, Some(i)) => format!("return {i};"),
            _ => format!("return {v};"),
        })
    }
}

impl Gen {
    /// A path to an `i32` of `TI`.
    fn int_path(&mut self) -> &'static str {
        ["&[\"0\"]", "&[\"1\", \"0\"]", "&[\"1\", \"1\"]"][self.rng.below(3)]
    }

    /// A path to a `Tx` of `TT`.
    fn tx_path(&mut self) -> &'static str {
        ["&[\"0\"]", "&[\"1\", \"0\"]", "&[\"1\", \"1\"]"][self.rng.below(3)]
    }

    /// A run-time condition, so the compiler cannot see which branch is taken.
    fn condition(&mut self) -> String {
        format!("s < {}", self.rng.below(40))
    }

    /// Deferred initialization, field paths, `@leaves`, tuple concat and split, and
    /// `@compile_error`. Field-by-field initialization sometimes leaves a field out or fills it
    /// on only one branch: the compiler must reject any use of it, and must drop or consume
    /// exactly what was initialized at the scope's end.
    fn tree(&mut self, depth: usize, which: usize) {
        // A statement over a tree starts one if there is none yet.
        if (4..=7).contains(&which) && self.pick(Kind::TreeInt).is_none() {
            return self.tree(depth, 1);
        }
        if which >= 9 && self.pick(Kind::TreeTx).is_none() {
            return self.tree(depth, 2);
        }
        let v = self.rng.below(9);
        let id = self.next_name + 1;
        match which {
            0 => {
                let n = self.declare("dn", Kind::Int);
                self.line(depth, &format!("let mut {n}: i32;"));
                let cond = self.condition();
                match self.rng.below(4) {
                    0 => self.line(depth, &format!("{n} = {v};")),
                    1 => self.line(depth, &format!("if {cond} {{ {n} = {v}; }}")),
                    _ => self.line(depth, &format!("if {cond} {{ {n} = {v}; }} else {{ {n} = 1; }}")),
                }
            }
            1 => {
                let t = self.declare("ti", Kind::TreeInt);
                self.line(depth, &format!("let mut {t}: TI;"));
                let skipped = self.rng.below(12);
                for (i, field) in ["0", "1.0", "1.1"].into_iter().enumerate() {
                    if i == skipped {
                        continue;
                    }
                    let cond = self.condition();
                    match self.rng.below(5) {
                        0 => {
                            let p = field.split('.').map(|s| format!("\"{s}\"")).collect::<Vec<_>>().join(", ");
                            self.line(depth, &format!("@field({t}, &[{p}]) = {v};"));
                        }
                        1 => self.line(depth, &format!("if {cond} {{ {t}.{field} = {v}; }} else {{ {t}.{field} = 2; }}")),
                        _ => self.line(depth, &format!("{t}.{field} = {v};")),
                    }
                }
            }
            2 => {
                let t = self.declare("dt", Kind::TreeTx);
                self.line(depth, &format!("let mut {t}: TT;"));
                let skipped = self.rng.below(36);
                for (i, field) in ["0", "1.0", "1.1"].into_iter().enumerate() {
                    if i == skipped {
                        continue;
                    }
                    let cond = self.condition();
                    match self.rng.below(32) {
                        0 => self.line(depth, &format!("if {cond} {{ {t}.{field} = Tx::new({v}); }}")),
                        1 => self.line(depth, &format!("if {cond} {{ {t}.{field} = Tx::new({v}); }} else {{ {t}.{field} = Tx::new(2); }}")),
                        _ => self.line(depth, &format!("{t}.{field} = Tx::new({v});")),
                    }
                }
            }
            3 => {
                // Not used again: only what was initialized may be dropped, exactly once.
                let b = format!("bp{id}");
                self.next_name += 1;
                self.line(depth, &format!("let mut {b}: tuple {{ Box[i32], Box[i32] }};"));
                self.line(depth, &format!("{b}.0 = Box[i32]::new({v});"));
                let cond = self.condition();
                self.line(depth, &format!("if {cond} {{ {b}.1 = Box[i32]::new({v}); }}"));
                match self.rng.below(4) {
                    0 => self.line(depth, &format!("{b}.0 = Box[i32]::new(1);")),
                    1 => self.line(depth, &format!("s = s + {b}.0.into_inner();")),
                    2 => {
                        let cond = self.condition();
                        self.line(depth, &format!("if {cond} {{ s = s + {b}.0.into_inner(); }}"));
                    }
                    _ => {}
                }
            }
            4 => {
                if let Some(t) = self.pick(Kind::TreeInt) {
                    let p = self.int_path();
                    if self.rng.below(2) == 0 {
                        let r = self.declare("r", Kind::Ref);
                        self.line(depth, &format!("let mut {r}: &i32 = &@field({t}, {p});"));
                    } else {
                        let m = self.declare("mr", Kind::MutRef);
                        self.line(depth, &format!("let mut {m}: &mut i32 = &mut @field({t}, {p});"));
                    }
                }
            }
            5 => {
                if let Some(t) = self.pick(Kind::TreeInt) {
                    let (p, q) = (self.int_path(), self.int_path());
                    self.line(depth, &format!("@field({t}, {p}) = @field({t}, {q}) + {v};"));
                }
            }
            6 => {
                if let Some(t) = self.pick(Kind::TreeInt) {
                    self.next_name += 1;
                    let body = match self.rng.below(2) {
                        0 => format!("s = s + @field({t}, q{id});"),
                        _ => format!("@field({t}, q{id}) = @field({t}, q{id}) + 1;"),
                    };
                    self.line(depth, &format!("comptime for q{id} in @leaves(TI) {{ {body} }}"));
                }
            }
            7 => {
                if let Some(t) = self.pick(Kind::TreeInt) {
                    self.next_name += 1;
                    let (p, q) = (self.int_path(), self.int_path());
                    self.line(depth, &format!("let a{id} = &mut @field({t}, {p});"));
                    self.line(depth, &format!("let c{id} = &mut @field({t}, {q});"));
                    self.line(depth, &format!("*a{id} = *c{id} + {v};"));
                    self.line(depth, &format!("*c{id} = *c{id} + 1;"));
                }
            }
            8 => {
                if let Some(i) = self.pick(Kind::Int) {
                    self.line(depth, &format!("s = s + only_int({i});"));
                }
            }
            9 => {
                if let Some(t) = self.take(Kind::TreeTx) {
                    self.next_name += 1;
                    let lost = self.rng.below(4) == 0;
                    self.line(depth, &format!("let sp{id} = tuple_split[1, TT]({t});"));
                    let middle = if lost { String::new() } else { format!(" + sp{id}.1.0.0.commit()") };
                    self.line(depth, &format!("s = s + sp{id}.0.0.commit(){middle} + sp{id}.1.0.1.commit();"));
                }
            }
            10 => {
                if let Some(t) = self.take(Kind::TreeTx) {
                    self.next_name += 1;
                    self.line(depth, &format!("let e{id}: tuple {{ Tx }} = .{{ Tx::new({v}) }};"));
                    self.line(depth, &format!("let cc{id} = tuple_concat({t}, e{id});"));
                    self.line(
                        depth,
                        &format!("s = s + cc{id}.0.commit() + cc{id}.1.0.commit() + cc{id}.1.1.commit() + cc{id}.2.commit();"),
                    );
                }
            }
            _ => {
                if let Some(t) = self.pick(Kind::TreeTx) {
                    // Refills what it moved, usually: another path leaves a hole and a double fill.
                    let p = self.tx_path();
                    let q = if self.rng.below(8) == 0 { self.tx_path() } else { p };
                    self.line(depth, &format!("s = s + (@field({t}, {p})).commit();"));
                    self.line(depth, &format!("@field({t}, {q}) = Tx::new({v});"));
                }
            }
        }
    }
}

/// Functions whose contracts the checkers rely on at every call. A program sometimes gets one
/// with a contract its body breaks, which must be rejected at the definition.
const CONTRACTS: [(&str, &str); 10] = [
    // Generators: what they yield may borrow only what their parameters do, they hold no
    // linear value across a `yield`, and two `&mut` items never alias.
    (
        "fn gen_refs(v: &Vec[&i32]) -> gen &i32 { for i in 0..v.len() { yield *(v.get(i) orelse unreachable); } }\n",
        "fn gen_refs(v: &Vec[&i32]) -> gen &i32 { let k: i32 = 5; yield &k; for i in 0..v.len() { yield *(v.get(i) orelse unreachable); } }\n",
    ),
    (
        "fn gen_tx(n: i32) -> gen Tx { for i in 0..n { yield Tx::new(i); } }\n",
        "fn gen_tx(n: i32) -> gen Tx { let t = Tx::new(9); for i in 0..n { yield Tx::new(i); } unsafe { SINK = SINK + t.commit(); } }\n",
    ),
    (
        "fn gen_mut(a: &mut i32, b: &mut i32) -> gen &mut i32 { yield &mut *a; yield &mut *b; }\n",
        "fn gen_mut(a: &mut i32, b: &mut i32) -> gen &mut i32 { yield &mut *a; yield &mut *a; }\n",
    ),
    (
        "fn gen_peek(r: &i32) -> gen i32 { let p = Peek::new(r); yield *r; let b = Box[i32]::new(*r + 1); yield *b.get(); }\n",
        "fn gen_peek(r: &i32) -> gen i32 { let k: i32 = *r; let p = Peek::new(&k); yield k; let b = Box[i32]::new(k + 1); yield *b.get(); }\n",
    ),
    (
        "fn pick2(a: &i32, b: &i32) -> &i32 borrows(a, b) { if *a > 0 { return a; } return b; }\n",
        "fn pick2(a: &i32, b: &i32) -> &i32 borrows(a) { if *a > 0 { return a; } return b; }\n",
    ),
    (
        "fn second(a: &i32, b: &i32) -> &i32 borrows(b) { return b; }\n",
        "fn second(a: &i32, b: &i32) -> &i32 borrows(b) { return a; }\n",
    ),
    (
        "fn unnest(x: &&i32, y: &i32) -> &i32 borrows(*x) { return *x; }\n",
        "fn unnest(x: &&i32, y: &i32) -> &i32 borrows(*x) { return y; }\n",
    ),
    (
        "fn stash(dst: &mut Slot, x: &i32, y: &i32) borrows(dst: y) { dst.r = y; }\n",
        "fn stash(dst: &mut Slot, x: &i32, y: &i32) borrows(dst: y) { dst.r = x; }\n",
    ),
    // Generics over linear values, held to consuming each `T` (one drops it on a path).
    (
        "fn some_of[T: ?linear](x: T, c: bool) -> ?T { if c { return x; } let o: ?T = x; return o; }\n",
        "fn some_of[T: ?linear](x: T, c: bool) -> ?T { if c { return x; } return null; }\n",
    ),
    (
        "fn swap_pair[T: ?linear](a: T, b: T) -> tuple { T, T } { return .{ b, a }; }\n",
        "fn swap_pair[T: ?linear](a: T, b: T) -> tuple { T, T } { let k = b; return .{ a, a }; }\n",
    ),
];

impl Gen {
    /// Calls whose result or side effect carries borrows only by a function's contract, and
    /// user-written containers. An accepted program must keep what the contract names alive.
    fn signature(&mut self, depth: usize, which: usize) {
        let v = self.rng.below(9);
        let id = self.next_name + 1;
        let cond = self.condition();
        // An inner local with an outer holder, usually: only then does it matter which of its
        // arguments a call's result borrows.
        let inner = self.scopes.len() - 1;
        let nested = inner > 0 && self.rng.below(4) != 0;
        let i = nested.then(|| self.pick_in(Kind::Int, inner..inner + 1)).flatten();
        let r = nested.then(|| self.pick_in(Kind::Ref, 0..inner)).flatten();
        let (Some(i), Some(r)) = (i.or_else(|| self.pick(Kind::Int)), r.or_else(|| self.pick(Kind::Ref))) else {
            return self.local_int(depth);
        };
        match which {
            0 => self.line(depth, &format!("{r} = pick2({r}, &{i});")),
            1 => self.line(depth, &format!("{r} = second(&{i}, {r});")),
            2 => self.line(depth, &format!("{r} = second({r}, &{i});")),
            3 => self.line(depth, &format!("{r} = id_ref(&{i});")),
            4 => self.line(depth, &format!("{r} = either({r}, &{i}, {cond});")),
            5 => {
                // Of an integer of its own half the time, as for a plain `&mut`.
                let target = if self.rng.below(2) == 0 {
                    self.next_name += 1;
                    self.line(depth, &format!("let mut mt{id}: i32 = {v};"));
                    format!("mt{id}")
                } else {
                    i.clone()
                };
                let m = self.declare("mr", Kind::MutRef);
                self.line(depth, &format!("let mut {m}: &mut i32 = bump(&mut {target});"));
            }
            6 => {
                let q = self.declare("r", Kind::Ref);
                self.line(depth, &format!("let mut {q}: &i32 = {r};"));
                self.line(depth, &format!("{r} = unnest(&{q}, &{i});"));
            }
            7 => {
                let n = self.declare("sl", Kind::Slot);
                self.line(depth, &format!("let mut {n} = Slot {{ r: &{i} }};"));
            }
            8 => match nested.then(|| self.pick_in(Kind::Slot, 0..inner)).flatten().or_else(|| self.pick(Kind::Slot)) {
                Some(n) => self.line(depth, &format!("stash(&mut {n}, &{i}, {r});")),
                None => self.line(depth, &format!("s = s + *{r};")),
            },
            9 => {
                if let Some(n) = self.pick(Kind::Slot) {
                    self.line(depth, &format!("s = s + *{n}.r + {v};"));
                    self.line(depth, &format!("{r} = {n}.r;"));
                }
            }
            10 => {
                let n = self.declare("hd", Kind::HeldRef);
                self.line(depth, &format!("let mut {n} = Held[&i32]::new(&{i});"));
            }
            11 => {
                if let Some(n) = self.pick(Kind::HeldRef) {
                    self.line(depth, &format!("s = s + **{n}.get();"));
                    self.line(depth, &format!("{r} = *{n}.get();"));
                }
            }
            12 => {
                if let Some(n) = self.take(Kind::HeldRef) {
                    self.line(depth, &format!("{r} = {n}.into_inner();"));
                }
            }
            13 => {
                if let Some(n) = self.pick(Kind::VecRef) {
                    self.line(depth, &format!("keep(&mut {n}, &{i});"));
                }
            }
            14 => {
                let n = self.declare("vw", Kind::ViewRef);
                self.line(depth, &format!("let mut {n} = view(&{i});"));
            }
            15 => {
                if let Some(n) = self.pick(Kind::ViewRef) {
                    self.line(depth, &format!("s = s + *{n}.get();"));
                    self.line(depth, &format!("{r} = {n}.get();"));
                }
            }
            // Fine if the contract tells the truth, dangling if not: a block's local passed to a
            // parameter the contract says the result does not borrow, and a read after the block.
            19 => {
                // What is taken out holds what the container held, and does not borrow it.
                self.next_name += 1;
                self.line(depth, &format!("let mut ta{id} = Vec[&i32]::new();"));
                self.line(depth, &format!("ta{id}.push({r});"));
                self.line(depth, &format!("let tk{id} = ta{id}.pop();"));
                self.line(depth, &format!("ta{id}.push(&{i});"));
                self.line(depth, &format!("if let ?e{id} = tk{id} {{ {r} = e{id}; }}"));
                self.line(depth, &format!("s = s + *{r};"));
            }
            20 => {
                // A value taken out of a block's container, kept past the block: it must take
                // the block's borrows with it.
                self.next_name += 1;
                let (take, keep) = match self.rng.below(3) {
                    0 => (format!("tb{id}.pop()"), format!("tb{id}.push(&l{id});")),
                    1 => (format!("tm{id}.remove(1)"), format!("let _o{id} = tm{id}.insert(1, &l{id});")),
                    _ => (format!("tb{id}.pop()"), format!("tb{id}.push(&l{id});")),
                };
                let container = if take.starts_with("tm") {
                    format!("let mut tm{id} = HashMap[i32, &i32]::new();")
                } else {
                    format!("let mut tb{id} = Vec[&i32]::new();")
                };
                self.line(depth, &format!("if s > -9999 {{ let l{id}: i32 = {v}; {container} {keep} if let ?e{id} = {take} {{ {r} = e{id}; }} }}"));
                self.line(depth, &format!("s = s + *{r};"));
            }
            16 => {
                self.next_name += 1;
                self.line(depth, &format!("if s > -9999 {{ let l{id}: i32 = {v}; {r} = second(&l{id}, {r}); }}"));
                self.line(depth, &format!("s = s + *{r};"));
            }
            17 => {
                self.next_name += 1;
                self.line(depth, &format!("if s > -9999 {{ let l{id}: i32 = {v}; let q{id}: &i32 = {r}; {r} = unnest(&q{id}, &l{id}); }}"));
                self.line(depth, &format!("s = s + *{r};"));
            }
            _ => {
                let n = self.declare("sl", Kind::Slot);
                self.line(depth, &format!("let mut {n} = Slot {{ r: {r} }};"));
                self.line(depth, &format!("if s > -9999 {{ let l{id}: i32 = {v}; stash(&mut {n}, &l{id}, {r}); }}"));
                self.line(depth, &format!("s = s + *{n}.r;"));
            }
        }
    }
}

impl Gen {
    /// Borrows the type system stops showing: trait objects and closures erase what they hold,
    /// slices and `&rel` fields are offsets from what they view. The checkers must still see
    /// through each one.
    fn erased(&mut self, depth: usize, which: usize) {
        // A statement that needs a value starts by making one, if there is none yet, and then
        // goes on: one that needs two makes both.
        if (1..=4).contains(&which) && self.pick(Kind::TraitRef).is_none() {
            self.erased(depth, 0);
            if which == 1 {
                return;
            }
        }
        if (9..=12).contains(&which) && self.pick(Kind::IntArray).is_none() {
            self.erased(depth, 8);
        }
        if (10..=11).contains(&which) && self.pick(Kind::SliceRef).is_none() {
            self.erased(depth, 9);
        }
        if (14..=16).contains(&which) && self.pick(Kind::Relative).is_none() {
            self.erased(depth, 13);
            if which == 16 {
                return;
            }
        }
        let v = self.rng.below(9);
        let k = self.rng.below(4);
        let id = self.next_name + 1;
        let cond = self.condition();
        let Some(i) = self.pick(Kind::Int) else {
            return self.local_int(depth);
        };
        match which {
            0 => {
                let b = self.declare("bh", Kind::ByRefHolder);
                self.line(depth, &format!("let mut {b} = ByRef {{ r: &{i} }};"));
                let t = self.declare("tr", Kind::TraitRef);
                self.line(depth, &format!("let mut {t}: &Reader = &{b};"));
                self.line(depth, &format!("s = s + {t}.value();"));
            }
            1 => {
                if let Some(t) = self.pick(Kind::TraitRef) {
                    self.line(depth, &format!("s = s + {t}.value();"));
                }
            }
            2 => {
                if let (Some(t), Some(b)) = (self.pick(Kind::TraitRef), self.pick(Kind::ByRefHolder)) {
                    self.line(depth, &format!("{t} = &{b};"));
                }
            }
            3 => {
                if let Some(b) = self.pick(Kind::ByRefHolder) {
                    self.line(depth, &format!("s = s + read_it(&{b});"));
                }
            }
            4 => {
                // The referent dies first, behind the object's erased type.
                if let Some(t) = self.pick(Kind::TraitRef) {
                    self.next_name += 1;
                    self.line(depth, &format!("if {cond} {{ let l{id}: i32 = {v}; let b{id} = ByRef {{ r: &l{id} }}; {t} = &b{id}; }}"));
                    self.line(depth, &format!("s = s + {t}.value();"));
                }
            }
            5 => {
                self.next_name += 1;
                self.line(depth, &format!("let cr{id} = fn() -> i32 {{ return {i} + {v}; }};"));
                self.line(depth, &format!("s = s + cr{id}();"));
                if self.rng.below(4) == 0 {
                    self.line(depth, &format!("{i} = {i} + 1;"));
                    self.line(depth, &format!("s = s + cr{id}();"));
                }
            }
            6 => {
                self.next_name += 1;
                self.line(depth, &format!("let cm{id} = fn() -> i32 {{ {i} = {i} + {v}; return {i}; }};"));
                if self.rng.below(4) == 0 {
                    self.line(depth, &format!("s = s + {i};"));
                }
                self.line(depth, &format!("s = s + run(cm{id});"));
            }
            7 => {
                if let Some(r) = self.pick(Kind::Ref) {
                    self.next_name += 1;
                    self.line(depth, &format!("s = s + run(fn() -> i32 {{ return *{r} + {i}; }});"));
                }
            }
            8 => {
                let a = self.declare("ar", Kind::IntArray);
                self.line(depth, &format!("let mut {a}: [i32; 4] = [{v}, 1, 2, 3];"));
            }
            9 => {
                if let Some(a) = self.pick(Kind::IntArray) {
                    let n = self.declare("sl", Kind::SliceRef);
                    self.line(depth, &format!("let mut {n}: &[i32] = &{a};"));
                    self.line(depth, &format!("s = s + sum({n});"));
                }
            }
            10 => {
                if let (Some(n), Some(a)) = (self.pick(Kind::SliceRef), self.pick(Kind::IntArray)) {
                    self.line(depth, &format!("{n} = &{a};"));
                    self.line(depth, &format!("s = s + {n}[{k}];"));
                }
            }
            11 => {
                if let Some(n) = self.pick(Kind::SliceRef) {
                    self.line(depth, &format!("s = s + sum({n}[1..]) + sum(tail({n})) + {n}.len as i32;"));
                }
            }
            12 => {
                if let Some(a) = self.pick(Kind::IntArray) {
                    self.next_name += 1;
                    self.line(depth, &format!("let ms{id}: &mut [i32] = &mut {a};"));
                    self.line(depth, &format!("ms{id}[{k}] = {v};"));
                    if let Some(n) = self.pick(Kind::SliceRef) {
                        self.line(depth, &format!("ms{id}[0] = {n}[0];"));
                    }
                }
            }
            13 => {
                let r = self.declare("rl", Kind::Relative);
                self.line(depth, &format!("let mut {r} = Rel::new({v});"));
                self.line(depth, &format!("s = s + {r}.read();"));
            }
            14 => {
                if let Some(r) = self.pick(Kind::Relative) {
                    match self.rng.below(3) {
                        0 => self.line(depth, &format!("{r}.set({v});")),
                        1 => self.line(depth, &format!("{r}.refocus({k});")),
                        _ => {
                            self.next_name += 1;
                            self.line(depth, &format!("let p{id} = {r}.peek();"));
                            if self.rng.below(3) == 0 {
                                self.line(depth, &format!("{r}.set({v});"));
                            }
                            self.line(depth, &format!("s = s + *p{id};"));
                        }
                    }
                }
            }
            15 => {
                // Offsets must survive every way of moving the value.
                if let Some(r) = self.take(Kind::Relative) {
                    let n = self.declare("rl", Kind::Relative);
                    match self.rng.below(3) {
                        0 => self.line(depth, &format!("let mut {n} = {r};")),
                        1 => self.line(depth, &format!("let mut {n} = relay({r}).1;")),
                        _ => self.line(depth, &format!("let mut {n} = Box[Rel]::new({r}).into_inner();")),
                    }
                    self.line(depth, &format!("s = s + {n}.read();"));
                }
            }
            16 => {
                if let Some(r) = self.pick(Kind::Relative) {
                    self.line(depth, &format!("s = s + {r}.read();"));
                }
            }
            _ => {
                // A slice of an inner array, read after the array dies.
                if let Some(n) = self.pick(Kind::SliceRef) {
                    self.next_name += 1;
                    self.line(depth, &format!("if {cond} {{ let a{id}: [i32; 4] = [{v}, 1, 2, 3]; {n} = &a{id}; }}"));
                    self.line(depth, &format!("s = s + {n}[0];"));
                }
            }
        }
    }
}

/// The expression moving droppable `name` into a call.
fn eat(kind: Kind, name: &str) -> String {
    match kind {
        Kind::BoxInt => format!("eat_box({name})"),
        Kind::OwnedStr => format!("eat_str({name})"),
        _ => format!("eat_vec({name})"),
    }
}

/// An expression reading droppable `name` without moving it.
fn peek(kind: Kind, name: &str) -> String {
    match kind {
        Kind::BoxInt => format!("*{name}.get()"),
        _ => format!("{name}.len() as i32"),
    }
}

/// A new value of droppable `kind`.
fn fresh(kind: Kind, v: usize) -> String {
    match kind {
        Kind::BoxInt => format!("Box[i32]::new({v})"),
        Kind::OwnedStr => "String::from(\"ab\")".to_string(),
        _ => "Vec[i32]::new()".to_string(),
    }
}

impl Gen {
    /// A droppable variable, declared here if none exists. Usually taken out of the scopes, so
    /// the program can compile; sometimes left there, so later code may use it after the move.
    fn owned(&mut self, depth: usize) -> (String, Kind) {
        let kinds = [Kind::BoxInt, Kind::OwnedStr, Kind::VecInt];
        let kind = kinds[self.rng.below(3)];
        let leave = self.rng.below(30) == 0;
        let name = if leave { self.pick(kind) } else { self.take(kind) };
        let name = name.unwrap_or_else(|| {
            let n = self.declare_owned(depth, kind);
            // Taken out as one found would be, unless it is left there on purpose.
            if !leave {
                for scope in &mut self.scopes {
                    scope.retain(|(m, _)| *m != n);
                }
            }
            n
        });
        (name, kind)
    }

    fn declare_owned(&mut self, depth: usize, kind: Kind) -> String {
        let v = self.rng.below(9);
        let n = self.declare("hp", kind);
        self.line(depth, &format!("let mut {n} = {};", fresh(kind, v)));
        n
    }

    /// Conditional moves of droppable values: each path leaves a different set of values to
    /// drop, which only the drop flags know.
    fn heap(&mut self, depth: usize, which: usize) {
        let v = self.rng.below(9);
        let id = self.next_name + 1;
        let cond = self.condition();
        match which {
            0 => {
                let kind = [Kind::BoxInt, Kind::OwnedStr, Kind::VecInt][self.rng.below(3)];
                self.declare_owned(depth, kind);
            }
            1 => {
                let (x, k) = self.owned(depth);
                self.line(depth, &format!("if {cond} {{ s = s + {}; }}", eat(k, &x)));
            }
            2 => {
                let (x, k) = self.owned(depth);
                self.line(depth, &format!("if {cond} {{ s = s + {}; }} else {{ s = s + 1; }}", eat(k, &x)));
            }
            3 => {
                let (x, k) = self.owned(depth);
                self.next_name += 1;
                self.line(depth, &format!("for l{id} in 0..3 {{ if {cond} {{ s = s + {}; break; }} s = s + 1; }}", eat(k, &x)));
            }
            4 => {
                let (x, k) = self.owned(depth);
                self.line(depth, &format!("s = s + match s % 3 {{ 0 => {}, _ => 1 }};", eat(k, &x)));
            }
            5 => {
                let (x, k) = self.owned(depth);
                self.next_name += 1;
                // Only a linear closure may move its captures out: this one reads, then drops them.
                self.line(depth, &format!("let cl{id} = move fn() -> i32 {{ return {}; }};", peek(k, &x)));
                self.line(depth, &format!("if {cond} {{ s = s + cl{id}(); }}"));
            }
            6 => {
                let (x, k) = self.owned(depth);
                self.next_name += 1;
                self.line(depth, &format!("let th{id} = spawn(move fn() -> i32 {{ return {}; }});", peek(k, &x)));
                self.line(depth, &format!("s = s + th{id}.join();"));
            }
            7 => {
                let (x, k) = self.owned(depth);
                self.line(depth, &format!("if {cond} {{ s = s + {}; return s; }}", eat(k, &x)));
            }
            8 => {
                // Moved, and refilled on the same or another path.
                let kind = [Kind::BoxInt, Kind::OwnedStr, Kind::VecInt][self.rng.below(3)];
                let x = match self.pick(kind) {
                    Some(x) => x,
                    None => self.declare_owned(depth, kind),
                };
                let (again, e, new) = (self.condition(), eat(kind, &x), fresh(kind, v));
                self.line(depth, &format!("if {cond} {{ s = s + {e}; {x} = {new}; }}"));
                if self.rng.below(2) == 0 {
                    self.line(depth, &format!("if {again} {{ {x} = {new}; }}"));
                }
            }
            9 => {
                if let Some(x) = self.take(Kind::BoxInt) {
                    let n = self.declare("hp", Kind::BoxInt);
                    self.line(depth, &format!("let mut {n} = pass_box({x});"));
                }
            }
            10 => {
                let n = self.declare("hq", Kind::BoxTuple);
                self.line(depth, &format!("let mut {n}: tuple {{ Box[i32], Box[i32] }} = .{{ Box[i32]::new({v}), Box[i32]::new(1) }};"));
            }
            11 => {
                if let Some(x) = self.pick(Kind::BoxTuple) {
                    let f = self.rng.below(2);
                    let again = self.condition();
                    self.line(depth, &format!("if {cond} {{ s = s + {x}.{f}.into_inner(); }}"));
                    if self.rng.below(2) == 0 {
                        self.line(depth, &format!("if {again} {{ {x}.{f} = Box[i32]::new({v}); }}"));
                    }
                }
            }
            12 => {
                let n = self.declare("ho", Kind::OptBox);
                let value = if v % 3 == 0 { "null".to_string() } else { format!("Box[i32]::new({v})") };
                self.line(depth, &format!("let mut {n}: ?Box[i32] = {value};"));
                let x = self.take(Kind::OptBox).unwrap_or(n);
                self.next_name += 1;
                self.line(depth, &format!("if {cond} {{ if let ?y{id} = {x} {{ s = s + eat_box(y{id}); }} }}"));
            }
            13 => {
                let n = self.declare("hu", Kind::UnionBox);
                let value = if v % 2 == 0 { format!(".A(Box[i32]::new({v}))") } else { format!(".B({v})") };
                self.line(depth, &format!("let mut {n}: UB = {value};"));
                let x = self.take(Kind::UnionBox).unwrap_or(n);
                self.next_name += 1;
                self.line(depth, &format!("if {cond} {{ s = s + match {x} {{ .A(y{id}) => eat_box(y{id}), .B(z{id}) => z{id} }}; }}"));
            }
            14 => {
                // Blocking on both sides of a full channel. Each channel is new, so what is
                // received does not depend on how threads interleave.
                let (c, t) = (format!("cb{id}"), format!("tb{id}"));
                self.next_name += 1;
                let sends = format!("_ = {c}.send({v}); _ = {c}.send(1); _ = {c}.send(2);");
                self.line(depth, &format!("let {c} = Channel[i32]::with_capacity(1);"));
                if self.rng.below(2) == 0 {
                    self.line(depth, &format!("let {t} = spawn_scoped(fn() -> i32 {{ {sends} return 0; }});"));
                    self.line(depth, &format!("s = s + ({c}.recv() catch |e| unreachable) + ({c}.recv() catch |e| unreachable) + ({c}.recv() catch |e| unreachable);"));
                } else {
                    self.line(depth, &format!("let {t} = spawn_scoped(fn() -> i32 {{ return ({c}.recv() catch |e| unreachable) + ({c}.recv() catch |e| unreachable) + ({c}.recv() catch |e| unreachable); }});"));
                    self.line(depth, &sends);
                }
                self.line(depth, &format!("s = s + {t}.join();"));
            }
            15 => {
                // The old value must be dropped, once, wherever the reference came from.
                let kind = [Kind::BoxInt, Kind::OwnedStr, Kind::VecInt][self.rng.below(3)];
                let x = match self.pick(kind) {
                    Some(x) => x,
                    None => self.declare_owned(depth, kind),
                };
                self.next_name += 1;
                self.line(depth, &format!("let m{id} = &mut {x};"));
                self.line(depth, &format!("*m{id} = {};", fresh(kind, v)));
            }
            16 => {
                // A `&mut self` call whose argument reads the receiver.
                if let Some(w) = self.pick(Kind::VecInt) {
                    self.line(depth, &format!("{w}.push({w}.len() as i32);"));
                }
            }
            17 => {
                // The count must move for this allocation, and not for a default one: balanced
                // frees alone would not show one instance serving both types.
                let id = self.next_name + 1;
                self.next_name += 1;
                self.line(depth, &format!("let t{id} = unsafe {{ TRACKED }};"));
                let n = self.declare("tb", Kind::TrackedBox);
                self.line(depth, &format!("let mut {n} = Box[i32, Tracked]::new({v});"));
                self.line(depth, &format!("if unsafe {{ TRACKED }} != t{id} + 1 {{ return -3; }}"));
                self.line(depth, &format!("let d{id} = Box[i32]::new({v});"));
                self.line(depth, &format!("if unsafe {{ TRACKED }} != t{id} + 1 {{ return -3; }}"));
                self.line(depth, &format!("s = s + d{id}.into_inner();"));
            }
            18 => {
                if let Some(x) = self.take(Kind::TrackedBox) {
                    self.line(depth, &format!("if {cond} {{ s = s + eat_any({x}); }}"));
                }
            }
            21 => {
                // An outer arena's value, reassigned from an arena that may die first.
                let id = self.next_name + 1;
                self.next_name += 1;
                let outer = self.pick(Kind::PoolBox);
                match outer {
                    Some(b) => {
                        self.line(depth, &format!("if {cond} {{ let pi{id} = TPool {{ x: 1 }}; {b} = Box[i32, &TPool]::new_in({v}, &pi{id}); }}"));
                        self.line(depth, &format!("s = s + *{b}.get();"));
                    }
                    None => {
                        self.line(depth, &format!("let pl{id} = TPool {{ x: 1 }};"));
                        let b = self.declare("pb", Kind::PoolBox);
                        self.line(depth, &format!("let mut {b} = Box[i32, &TPool]::new_in({v}, &pl{id});"));
                    }
                }
                self.line(depth, &format!("let pa{id} = TPool {{ x: 1 }};"));
                self.line(depth, &format!("let mut pv{id} = Vec[i32, &TPool]::new_in(&pa{id});"));
                self.line(depth, &format!("pv{id}.push({v});"));
                self.line(depth, &format!("s = s + *(pv{id}.get(0) orelse unreachable);"));
            }
            19 => {
                self.line(depth, &format!("s = s + vec_sum({v});"));
                if let Some(x) = self.pick(Kind::TrackedBox) {
                    self.line(depth, &format!("if {cond} {{ {x} = Box[i32, Tracked]::new({v}); }}"));
                    self.line(depth, &format!("s = s + *{x}.get();"));
                }
            }
            22 => match self.pick(Kind::BoxArray) {
                None => {
                    let n = self.declare("ha", Kind::BoxArray);
                    self.line(depth, &format!("let mut {n}: [Box[i32]; 2] = [Box[i32]::new({v}), Box[i32]::new(1)];"));
                }
                // Replacing an element drops the old one; the array drops what is left.
                Some(x) => match self.rng.below(3) {
                    0 => {
                        let i = self.rng.below(2);
                        self.line(depth, &format!("if {cond} {{ {x}[{i}] = Box[i32]::new({v}); }}"));
                        self.line(depth, &format!("s = s + *{x}[{i}].get();"));
                    }
                    1 => self.line(depth, &format!("s = s + *{x}[0].get() + *{x}[1].get();")),
                    _ => {
                        let x = self.take(Kind::BoxArray).unwrap_or(x);
                        self.line(depth, &format!("if {cond} {{ s = s + eat_arr({x}); }}"));
                    }
                },
            },
            23 => match self.pick(Kind::List) {
                None => {
                    // Past 128 nodes the drops of a chain queue rather than recurse.
                    let len = if self.rng.below(6) == 0 { 200 } else { self.rng.below(4) as i32 };
                    let n = self.declare("hl", Kind::List);
                    self.line(depth, &format!("let mut {n} = Node {{ v: {v}, next: chain({len}) }};"));
                }
                Some(x) => match self.rng.below(4) {
                    0 => {
                        let len = self.rng.below(3);
                        self.line(depth, &format!("if {cond} {{ {x}.next = chain({len}); }}"));
                    }
                    1 => self.line(depth, &format!("bump_all(&mut {x}); s = s + total(&{x});")),
                    2 => {
                        // The list moves into its own new head.
                        self.line(depth, &format!("if {cond} {{ {x} = Node {{ v: {v}, next: Box[Node]::new(move {x}) }}; }}"));
                        self.line(depth, &format!("s = s + total(&{x});"));
                    }
                    _ => {
                        let x = self.take(Kind::List).unwrap_or(x);
                        self.line(depth, &format!("if {cond} {{ s = s + eat_list({x}); }}"));
                    }
                },
            },
            24 => {
                // A bounded generic's clones: both are new values, one maybe left to drop.
                let kind = [Kind::OwnedStr, Kind::VecInt][self.rng.below(2)];
                let x = match self.pick(kind) {
                    Some(x) => x,
                    None => self.declare_owned(depth, kind),
                };
                self.next_name += 1;
                self.line(depth, &format!("let tw{id} = twin(&{x});"));
                self.line(depth, &format!("s = s + {};", eat(kind, &format!("tw{id}.0"))));
                self.line(depth, &format!("if {cond} {{ s = s + {}; }}", eat(kind, &format!("tw{id}.1"))));
            }
            25 => match self.pick(Kind::SlotVec) {
                None => {
                    let n = self.declare("hs", Kind::SlotVec);
                    self.line(depth, &format!("let mut {n} = ArrayVec[Box[i32], 4]::new();"));
                    self.line(depth, &format!("{n}.push(Box[i32]::new({v}));"));
                }
                // What its slots hold must be dropped once, wherever the vector has moved.
                Some(x) => match self.rng.below(6) {
                    0 => self.line(depth, &format!("if {x}.len() < 4 {{ {x}.push(Box[i32]::new({v})); }}")),
                    1 => self.line(depth, &format!("if let ?b{id} = {x}.pop() {{ s = s + b{id}.into_inner(); }}")),
                    2 => self.line(depth, &format!("if {x}.len() < 4 {{ {x}.insert(0, Box[i32]::new({v})); }}")),
                    3 => self.line(depth, &format!("if let ?b{id} = {x}.remove(0) {{ s = s + *b{id}.get(); }}")),
                    4 => self.line(depth, &format!("for b{id} in {x}.iter() {{ s = s + *b{id}.get(); }}")),
                    _ => {
                        let x = self.take(Kind::SlotVec).unwrap_or(x);
                        self.next_name += 1;
                        self.line(depth, &format!("if {cond} {{ let mv{id} = move {x}; s = s + mv{id}.len() as i32; }}"));
                    }
                },
            },
            26 => {
                // All-zero values: one store, read back as zeros.
                let k = self.rng.below(8);
                self.next_name += 1;
                self.line(depth, &format!("let z{id}: [i64; 8] = zeroinit;"));
                self.line(depth, &format!("let zv{id} = Vec[i64]::zeroed({v} + 1);"));
                self.line(depth, &format!("s = s + z{id}[{k}] as i32 + zv{id}.len() as i32 + *(zv{id}.get({v}) orelse unreachable) as i32;"));
            }
            27 => {
                // Inline storage inside a heap vector, grown in place through a reference.
                self.next_name += 1;
                self.line(depth, &format!("let mut nest{id} = Vec[ArrayVec[String, 2]]::new();"));
                self.line(depth, &format!("let mut in{id} = ArrayVec[String, 2]::new();"));
                self.line(depth, &format!("in{id}.push(String::from(\"ab\"));"));
                self.line(depth, &format!("nest{id}.push(in{id});"));
                self.line(depth, &format!("if {cond} {{ if let ?e{id} = nest{id}.get_mut(0) {{ if e{id}.len() < 2 {{ e{id}.push(String::from(\"c\")); }} }} }}"));
                self.line(depth, &format!("for e{id} in nest{id}.iter() {{ s = s + e{id}.len() as i32; }}"));
            }
            _ => {
                // A direct read, which must not overlap a live `&mut` of the same variable.
                if let (Some(i), Some(m)) = (self.pick(Kind::Int), self.pick(Kind::MutRef)) {
                    self.line(depth, &format!("s = s + {i};"));
                    self.line(depth, &format!("*{m} = *{m} + {v};"));
                }
            }
        }
    }
}

/// A statement consuming linear `name` of `kind`; unless `sound`, one that may lose the value
/// (the compiler must reject it).
fn consume(name: &str, kind: Kind, id: usize, sound: bool) -> String {
    match (kind, sound) {
        (Kind::Tx, _) => format!("s = s + {name}.commit();"),
        (Kind::OptTx, true) => format!("if let ?t{id} = {name} {{ s = s + t{id}.commit(); }}"),
        (Kind::OptTx, false) => format!("if let ?t{id} = {name} {{ s = s + 1; }}"),
        (Kind::UnionTx, true) => {
            format!("s = s + match {name} {{ .A(t{id}) => t{id}.commit(), .B(b{id}) => b{id} }};")
        }
        (Kind::UnionTx, false) => format!("s = s + match {name} {{ .B(b{id}) => b{id}, _ => 0 }};"),
        (Kind::PairTx, true) => {
            format!("s = s + match {name} {{ Pair {{ t: t{id}, n: b{id} }} => t{id}.commit() + b{id} }};")
        }
        (Kind::PairTx, false) => format!("s = s + match {name} {{ {{ n: b{id}, .. }} => b{id} }};"),
        (Kind::BoxTx, true) => format!("s = s + {name}.into_inner().commit();"),
        (Kind::BoxTx, false) => format!("@drop({name});"),
        (Kind::VecTx, true) => {
            format!("{name}.drain(fn(t{id}: Tx) {{ let _c{id} = t{id}.commit(); }});")
        }
        (Kind::VecTx, false) => format!("{name}.drain(fn(t{id}: Tx) {{ }});"),
        (Kind::WrapTx, _) => format!("s = s + {name}.finish();"),
        (Kind::Thread, _) => format!("s = s + {name}.join();"),
        (Kind::ChanTx, true) => {
            format!("{name}.close_and_drain(fn(t{id}: Tx) {{ let _c{id} = t{id}.commit(); }});")
        }
        (Kind::ChanTx, false) => format!("{name}.close_and_drain(fn(t{id}: Tx) {{ }});"),
        (Kind::TreeTx, true) if id % 2 == 0 => {
            format!("comptime for q{id} in @leaves(TT) {{ s = s + (@field({name}, q{id})).commit(); }}")
        }
        (Kind::TreeTx, true) => format!("s = s + {name}.0.commit() + {name}.1.0.commit() + {name}.1.1.commit();"),
        (Kind::TreeTx, false) => format!("s = s + {name}.0.commit() + {name}.1.0.commit();"),
        _ => String::new(),
    }
}

/// The program for `seed`.
impl Gen {
    /// Drives generators: to the end, partly (dropping one where it waits), or not at all,
    /// with linear items, items kept past the loop, and one holding a borrow that sometimes
    /// outlives what it borrows.
    fn generators(&mut self, depth: usize, which: usize) {
        let id = self.next_name + 1;
        self.next_name += 1;
        let v = self.rng.below(9);
        let k = self.rng.below(4);
        match which {
            0 => self.line(depth, &format!("for x{id} in gen_tx({k}) {{ s = s + x{id}.commit(); }}")),
            1 => {
                self.line(depth, &format!("let mut gt{id} = gen_tx({k});"));
                self.line(depth, &format!("if let ?t{id} = gt{id}.next() {{ s = s + t{id}.commit(); }}"));
            }
            2 => match self.pick(Kind::VecRef) {
                Some(vr) => {
                    let r = self.pick(Kind::Ref);
                    let keep = r.map_or(String::new(), |r| format!(" {r} = x{id};"));
                    self.line(depth, &format!("for x{id} in gen_refs(&{vr}) {{ s = s + *x{id};{keep} }}"));
                }
                None => self.local_int(depth),
            },
            3 => {
                self.line(depth, &format!("let mut ga{id}: i32 = {v};"));
                self.line(depth, &format!("let mut gb{id}: i32 = {k};"));
                self.line(depth, &format!("for m{id} in gen_mut(&mut ga{id}, &mut gb{id}) {{ *m{id} = *m{id} + 1; }}"));
                self.line(depth, &format!("s = s + ga{id} + gb{id};"));
            }
            4 => match self.pick(Kind::Ref) {
                Some(r) => {
                    // Mostly sound: replaced with one over the outer reference, or over a
                    // block's local, which it must not outlive.
                    let src = if self.rng.below(3) == 0 { format!("&l{id}") } else { r.clone() };
                    self.line(depth, &format!("let mut gh{id}: Gen[i32, tuple {{ &i32 }}] = gen_peek({r});"));
                    self.line(depth, &format!("if s > -9999 {{ let l{id}: i32 = {v}; gh{id} = gen_peek({src}); s = s + (gh{id}.next() orelse 0); }}"));
                    self.line(depth, &format!("s = s + (gh{id}.next() orelse 0);"));
                }
                None => self.local_int(depth),
            },
            5 | 6 | 7 => {
                let name = self.generated_generator();
                let r = self.pick(Kind::Ref).unwrap_or_else(|| "&s".to_string());
                match which {
                    5 => self.line(depth, &format!("for x{id} in {name}({v}, {r}) {{ s = s + x{id}; }}")),
                    6 => {
                        let steps = self.rng.below(4);
                        self.line(depth, &format!("let mut gg{id} = {name}({v}, {r});"));
                        for _ in 0..steps {
                            self.line(depth, &format!("s = s + (gg{id}.next() orelse 0);"));
                        }
                    }
                    _ => self.line(depth, &format!("if s > -9999 {{ let gn{id} = {name}({v}, {r}); }}")),
                }
            }
            8 => {
                let name = self.generated_generator();
                let r = self.pick(Kind::Ref).unwrap_or_else(|| "&s".to_string());
                self.line(depth, &format!("if s > -9999 {{ let mut gp{id} = {name}({k}, {r}); s = s + (gp{id}.next() orelse 0); }}"));
            }
            _ => match self.pick(Kind::Ref) {
                // Kept past a block whose local it was given, half the time: it must not be.
                Some(r) => {
                    let name = self.generated_generator();
                    let src = if self.rng.below(3) == 0 { format!("&l{id}") } else { r.clone() };
                    self.line(depth, &format!("let mut gk{id} = {name}({v}, {r});"));
                    self.line(depth, &format!("if s > -9999 {{ let l{id}: i32 = {k}; gk{id} = {name}({v}, {src}); s = s + (gk{id}.next() orelse 0); }}"));
                    self.line(depth, &format!("s = s + (gk{id}.next() orelse 0) + (gk{id}.next() orelse 0);"));
                }
                None => self.local_int(depth),
            },
        }
    }

    /// A union with a droppable variant matched by value: an arm of the `copy` variant retires
    /// the scrutinee, which must then not be dropped as well.
    fn union_match(&mut self, depth: usize) {
        self.next_name += 1;
        let id = self.next_name;
        let v = self.rng.below(9);
        let cond = self.condition();
        let rest = if self.rng.below(2) == 0 { "_ => 0".to_string() } else { format!(".S(b{id}) => *b{id}.get()") };
        self.line(depth, &format!("let ub{id}: UB = if {cond} {{ .N({v}) }} else {{ .S(Box[i32]::new({v})) }};"));
        self.line(depth, &format!("s = s + match ub{id} {{ .N(n{id}) => n{id}, {rest} }};"));
    }

    /// The program's generated generator, written on first use: `fn rg(a: i32, r: &i32) -> gen i32`.
    fn generated_generator(&mut self) -> &'static str {
        if self.items.is_empty() {
            let mut body = String::new();
            let mut names = 0;
            let len = 3 + self.rng.below(6);
            let mut ints = vec!["a".to_string()];
            self.gen_stmts(&mut body, 1, len, &mut ints, &mut names);
            self.items = format!("fn note() {{ unsafe {{ SINK = SINK + 1; }} }}\nfn rg(a: i32, r: &i32) -> gen i32 {{\n{body}}}\n");
        }
        "rg"
    }

    /// Statements of a generated generator's body. `ints` are the `i32` locals in scope, which
    /// later statements read, so locals cross the `yield`s between.
    fn gen_stmts(&mut self, out: &mut String, depth: usize, len: usize, ints: &mut Vec<String>, names: &mut usize) {
        let pad = "    ".repeat(depth);
        let scope_start = ints.len();
        for _ in 0..len {
            *names += 1;
            let n = *names;
            let any = ints[self.rng.below(ints.len())].clone();
            let v = self.rng.below(9);
            match self.rng.below(15) {
                0 | 1 => out.push_str(&format!("{pad}yield {any} + {v};\n")),
                2 => out.push_str(&format!("{pad}yield *r;\n")),
                3 => {
                    out.push_str(&format!("{pad}let mut x{n}: i32 = {any} + {v};\n"));
                    ints.push(format!("x{n}"));
                }
                4 => {
                    // A reference to a local, read after a `yield`.
                    out.push_str(&format!("{pad}let q{n} = &{any};\n{pad}yield {v};\n{pad}yield *q{n};\n"));
                }
                5 => {
                    out.push_str(&format!("{pad}let b{n} = Box[i32]::new({any});\n{pad}yield *b{n}.get();\n"));
                    ints.push(format!("*b{n}.get()"));
                }
                6 => {
                    // An array read and written at a local index on both sides of a `yield`.
                    out.push_str(&format!(
                        "{pad}let mut ar{n}: [i32; 3] = [{any}, {v}, 1];\n{pad}let j{n}: usize = {};\n{pad}yield ar{n}[j{n}];\n{pad}ar{n}[j{n}] = ar{n}[j{n}] + 1;\n{pad}yield ar{n}[j{n}];\n",
                        self.rng.below(3)
                    ));
                }
                7 => {
                    out.push_str(&format!("{pad}let pk{n} = Peek::new(r);\n{pad}yield {v};\n"));
                }
                8 => {
                    out.push_str(&format!("{pad}let st{n} = String::from(\"ab\");\n{pad}yield st{n}.len() as i32;\n"));
                }
                9 => {
                    // Linear, consumed before the next `yield`.
                    out.push_str(&format!("{pad}let t{n} = Tx::new({v});\n{pad}x_commit(t{n});\n{pad}yield {any};\n"));
                }
                10 => out.push_str(&format!("{pad}defer note();\n")),
                11 => out.push_str(&format!("{pad}if {any} > {v} {{ return; }}\n")),
                12 | 13 if depth < 3 => {
                    let head = if self.rng.below(2) == 0 {
                        format!("for gi{n} in 0..{} {{\n", 1 + self.rng.below(3))
                    } else {
                        format!("if {any} < {v} {{\n")
                    };
                    out.push_str(&format!("{pad}{head}"));
                    let inner = 1 + self.rng.below(3);
                    self.gen_stmts(out, depth + 1, inner, ints, names);
                    out.push_str(&format!("{pad}}}\n"));
                }
                _ => out.push_str(&format!("{pad}yield {v};\n")),
            }
        }
        ints.truncate(scope_start.max(1));
    }
}

fn generate(seed: u64) -> String {
    let mut g = Gen {
        rng: Rng::new(seed),
        out: String::new(),
        items: String::new(),
        scopes: vec![Vec::new()],
        next_name: 0,
    };
    // One of each borrow-holding kind up front, so nested blocks have outer borrows to escape into.
    g.local_int(0);
    let n = g.pick(Kind::Int).unwrap();
    let r = g.declare("r", Kind::Ref);
    g.line(0, &format!("let mut {r}: &i32 = &{n};"));
    let v = g.declare("v", Kind::VecRef);
    g.line(0, &format!("let mut {v} = Vec[&i32]::new();"));
    let b = g.declare("b", Kind::BoxRef);
    g.line(0, &format!("let mut {b} = Box[&i32]::new(&{n});"));
    if g.rng.below(2) == 0 {
        let p = g.declare("p", Kind::RefField);
        g.line(0, &format!("let mut {p} = RefPair {{ r: &{n}, n: 1 }};"));
    }
    if g.rng.below(2) == 0 {
        let k = g.declare("k", Kind::Peek);
        g.line(0, &format!("let mut {k} = Peek::new(&{n});"));
    }
    let len = 6 + g.rng.below(16);
    g.block(0, len);
    g.close_scope(0);
    let mut contracts = String::new();
    let broken = (g.rng.below(12) == 0).then(|| g.rng.below(CONTRACTS.len()));
    for (i, (sound, unsound)) in CONTRACTS.iter().enumerate() {
        contracts.push_str(if broken == Some(i) { unsound } else { sound });
    }
    format!(
        "{PRELUDE}{contracts}{}fn body() -> i32 {{\n    let mut s: i32 = 0;\n{}    return s;\n}}\n\
         pub fn main() -> i32 {{\n    let r = body();\n    if unsafe {{ LIVE }} != 0 {{\n        return -1;\n    }}\n    if unsafe {{ TRACKED }} != 0 {{\n        return -2;\n    }}\n    return r;\n}}\n",
        g.items, g.out
    )
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// Thread interleavings tried for each threaded program, besides the VM's default order.
const SCHEDULES: u64 = 4;

/// Why `src` shows a soundness bug, if the compiler accepts it: undefined behaviour or a leak in
/// the VM, a linear value created and not consumed exactly once, or a result that differs from
/// the native build. `None` when the compiler rejects it or it runs correctly.
fn failure(src: &str) -> Option<String> {
    failure_of(Compiler::compile_source(src).ok()?, src)
}

/// `failure` for a program that compiled.
fn failure_of(mut program: crate::ir::Program, src: &str) -> Option<String> {
    let native = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT)
        .map(|ir| lli(&ir).status.code());
    let schedules = if src.contains("spawn") { SCHEDULES } else { 0 };
    std::iter::once(None).chain((1..=schedules).map(Some)).find_map(|seed| {
        let on = seed.map_or(String::new(), |s| format!(" under schedule {s}"));
        match run_vm_scheduled(&mut program, seed) {
            Err(e) => Some(format!("VM: {e}{on}")),
            Ok(VmRun { leaks, .. }) if leaks > 0 => Some(format!("{leaks} heap block(s) leaked{on}")),
            Ok(VmRun { value: -1, .. }) => Some(format!("a linear Tx was not consumed exactly once{on}")),
            Ok(VmRun { value: -2, .. }) => Some(format!("a Tracked allocation was freed elsewhere or lost{on}")),
            Ok(VmRun { value: -3, .. }) => Some(format!("an allocation used the wrong context{on}")),
            Ok(VmRun { value, .. }) => {
                let expected = Some((value & 0xff) as i32);
                (native.as_ref().ok() != Some(&expected))
                    .then(|| format!("VM returned {value}{on}, native run gave {native:?}"))
            }
        }
    })
}

/// The failure category, so shrinking keeps the same bug rather than drifting to another.
fn category(why: &str) -> &str {
    why.split(':').next().unwrap_or(why)
}

/// Shrinks a failing program by deleting statements and whole blocks of the body while it still
/// fails the same way.
fn shrink(src: &str, why: &str) -> String {
    let mut lines: Vec<String> = src.lines().map(str::to_string).collect();
    let body_start = lines.iter().position(|l| l.starts_with("fn body()")).unwrap_or(0) + 2;
    let mut changed = true;
    while changed {
        changed = false;
        let mut i = lines.len();
        while i > body_start {
            i -= 1;
            let Some(end) = statement_end(&lines, i, body_start) else {
                continue;
            };
            let mut candidate = lines.clone();
            candidate.drain(i..=end);
            let text = candidate.join("\n") + "\n";
            if failure(&text).is_some_and(|w| category(&w) == category(why)) {
                lines = candidate;
                changed = true;
                i = i.min(lines.len());
            }
        }
    }
    lines.join("\n") + "\n"
}

/// The last line of the body statement starting at line `i` (a block runs to its closing brace),
/// or `None` if line `i` is not the start of a body statement.
fn statement_end(lines: &[String], i: usize, body_start: usize) -> Option<usize> {
    let line = &lines[i];
    let indent = line.len() - line.trim_start().len();
    if i < body_start || indent < 4 || line.trim() == "}" || line.trim_start().starts_with("return s;") {
        return None;
    }
    if !line.trim_end().ends_with('{') {
        return Some(i);
    }
    (i + 1..lines.len()).find(|&j| {
        let l = &lines[j];
        l.trim() == "}" && l.len() - l.trim_start().len() == indent
    })
}

#[test]
fn fuzz_borrow_and_drop_checking() {
    let cases = env_u64("SLOPLANG_FUZZ_CASES", 50);
    let first_seed = env_u64("SLOPLANG_FUZZ_SEED", 1);
    // Cases are independent: workers take seeds in turn, and failures are reported in seed order.
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
    let workers = env_u64("SLOPLANG_FUZZ_WORKERS", cores);
    let next = std::sync::atomic::AtomicU64::new(first_seed);
    let results: Vec<(usize, usize, Vec<(u64, String, String)>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..workers.min(cases.max(1)))
            .map(|_| {
                scope.spawn(|| {
                    let (mut accepted, mut rejected, mut failures) = (0, 0, Vec::new());
                    loop {
                        let seed = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        if seed >= first_seed + cases {
                            return (accepted, rejected, failures);
                        }
                        let src = generate(seed);
                        let Ok(program) = Compiler::compile_source(&src) else {
                            rejected += 1;
                            continue;
                        };
                        accepted += 1;
                        if let Some(why) = failure_of(program, &src) {
                            failures.push((seed, src, why));
                        }
                    }
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let accepted: usize = results.iter().map(|r| r.0).sum();
    let rejected: usize = results.iter().map(|r| r.1).sum();
    let mut failures: Vec<_> = results.into_iter().flat_map(|r| r.2).collect();
    failures.sort_by_key(|f| f.0);
    println!("fuzz: {accepted} accepted, {rejected} rejected, {} failed", failures.len());
    if let Some((seed, src, why)) = failures.first() {
        let small = shrink(src, why);
        panic!(
            "{} of {accepted} accepted programs failed; first (seed {seed}): {why}\nshrunk:\n{small}",
            failures.len()
        );
    }
    assert!(
        accepted as u64 * 5 >= cases,
        "only {accepted} of {cases} generated programs compiled; the generator needs tuning"
    );
}

/// The fuzzer's oracle: the VM reports undefined behaviour in `unsafe` code that the compiler
/// cannot see, and runs std containers without leaks.
#[test]
fn test_vm_detects_undefined_behaviour() {
    use super::run_vm;
    use crate::vm::UB_PREFIX;
    for (name, src, value) in [
        ("vec", "pub fn main() -> i32 { let mut v = Vec[i32]::new(); for i in 0..20 { v.push(i); } let mut s: i32 = 0; for x in v.iter() { s += *x; } return s; }", 190),
        ("box", "pub fn main() -> i32 { let c = Box[Box[i32]]::new(Box[i32]::new(3)); return c.into_inner().into_inner(); }", 3),
        ("string", "pub fn main() -> i32 { let mut s = String::from(\"hey\"); s.push_str(\" you\"); return s.len() as i32; }", 7),
        ("hashmap", "pub fn main() -> i32 { let mut m = HashMap[i32, i32]::new(); for i in 0..30 { let _o = m.insert(i, i * 2); } return *(m.get(7) orelse unreachable); }", 14),
    ] {
        assert_eq!(run_vm(name, src), Ok(VmRun { value, leaks: 0, output: String::new() }), "[{name}]");
    }
    for (name, src, what) in [
        (
            "stale_local",
            "pub fn main() -> i32 { let mut p: *const i32 = 0 as *const i32; if true { let x: i32 = 5; p = (&raw const x as usize) as *const i32; } return unsafe { *p }; }",
            "whose storage has ended",
        ),
        (
            "returned_frame",
            "fn mk() -> *const i32 { let x: i32 = 5; return (&raw const x as usize) as *const i32; }\npub fn main() -> i32 { let p = mk(); return unsafe { *p }; }",
            "of a function that has returned",
        ),
        (
            "use_after_free",
            "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 1); unsafe { *p = 1; @dealloc(p); return *p; } }",
            "after it was freed",
        ),
        (
            "double_free",
            "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 1); unsafe { @dealloc(p); @dealloc(p); } return 0; }",
            "already freed",
        ),
        (
            "stale_after_realloc",
            "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 1); unsafe { *p = 1; let q: *mut i32 = @realloc(i32, p, 8); let v = *p; @dealloc(q); return v; } }",
            "after it was freed",
        ),
        (
            "out_of_bounds",
            "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 2); unsafe { *(p + 5) = 1; @dealloc(p); } return 0; }",
            "out of bounds",
        ),
    ] {
        let err = run_vm(name, src).expect_err(name);
        assert!(err.starts_with(UB_PREFIX) && err.contains(what), "[{name}] {err}");
    }
    assert_eq!(
        run_vm("leak", "pub fn main() -> i32 { let p: *mut i32 = @alloc(i32, 2); return 0; }"),
        Ok(VmRun { value: 0, leaks: 1, output: String::new() })
    );
}

#[test]
fn test_vm_reports_stack_overflow() {
    // The VM's frames live on the heap, so it would run recursion that overflows the native
    // stack; it counts what native frames would take instead, and refuses the call past 8 MB.
    let src = |depth: i32| {
        format!(
            "fn deep(n: i32) -> i64 {{
    if n == 0 {{ return 0; }}
    let pad: [i64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
    return deep(n - 1) + pad[(n % 8) as usize] - pad[(n % 8) as usize] + 1;
}}
pub fn main() -> i32 {{ return (deep({depth}) % 100) as i32; }}"
        )
    };
    let mut shallow = Compiler::compile_source(&src(10_000)).unwrap();
    assert_eq!(run_vm_scheduled(&mut shallow, None).map(|r| r.value), Ok(0));
    let native = crate::llvm::LlvmLowering::lower_with_trap_exit(&shallow, TRAP_EXIT).unwrap();
    assert_eq!(lli(&native).status.code(), Some(0), "10,000 frames fit natively");
    let mut deep = Compiler::compile_source(&src(200_000)).unwrap();
    let err = run_vm_scheduled(&mut deep, None).unwrap_err();
    assert!(err.contains("Stack overflow") && err.contains("root::deep"), "{err}");
    let native = crate::llvm::LlvmLowering::lower_with_trap_exit(&deep, TRAP_EXIT).unwrap();
    assert_ne!(lli(&native).status.code(), Some(0), "200,000 frames overflow natively");
}

#[test]
fn test_vm_detects_data_races() {
    use super::run_vm;
    use crate::vm::UB_PREFIX;
    // A `cell` counter whose `bump` is atomic, or a plain (racy) read-modify-write.
    let counter = |bump: &str| {
        format!(
            "pub opaque(unsafe sync) Counter {{
    cell n: i32,
    pub fn new() -> Self {{ return Self {{ n: 0 }}; }}
    pub fn bump(&self) {{ {bump} }}
    pub fn get(&self) -> i32 {{ return unsafe {{ @atomic_load(&raw mut self.n) }}; }}
}}
"
        )
    };
    let atomic = counter("unsafe { let _old = @atomic_add(&raw mut self.n, 1); }");
    let plain = counter("unsafe { let p = &raw mut self.n; *p = *p + 1; }");
    let two_threads = "pub fn main() -> i32 {
    let c = Counter::new();
    let a = spawn_scoped(fn() -> i32 { for i in 0..10 { c.bump(); } return 0; });
    let b = spawn_scoped(fn() -> i32 { for i in 0..10 { c.bump(); } return 0; });
    return a.join() + b.join() + c.get();
}";
    // The second thread's plain accesses are ordered after the first's only by the join.
    let joined_between = "pub fn main() -> i32 {
    let c = Counter::new();
    let a = spawn_scoped(fn() -> i32 { c.bump(); return 0; });
    let x = a.join();
    let b = spawn_scoped(fn() -> i32 { c.bump(); return 0; });
    return x + b.join() + c.get();
}";
    let read_before_join = "pub fn main() -> i32 {
    let c = Counter::new();
    let a = spawn_scoped(fn() -> i32 { c.bump(); return 0; });
    c.bump();
    return a.join() + c.get();
}";
    // A plain access unordered with another thread's atomic one races; once a join orders them
    // it does not.
    let mixed = |bump: &str, read: &str| {
        format!(
            "pub opaque(unsafe sync) Mixed {{
    cell n: i32,
    pub fn new() -> Self {{ return Self {{ n: 0 }}; }}
    pub fn bump(&self) {{ {bump} }}
    pub fn atomic_read(&self) -> i32 {{ return unsafe {{ @atomic_load(&raw mut self.n) }}; }}
    pub fn plain_read(&self) -> i32 {{ return unsafe {{ *(&raw mut self.n) }}; }}
}}
pub fn main() -> i32 {{
    let c = Mixed::new();
    let a = spawn_scoped(fn() -> i32 {{ c.bump(); return 0; }});
    {read}
}}"
        )
    };
    let add = "unsafe { let _old = @atomic_add(&raw mut self.n, 1); }";
    let plain_add = "unsafe { let p = &raw mut self.n; *p = *p + 1; }";
    for (name, src) in [
        ("plain_read_of_atomic", mixed(add, "let v = c.plain_read(); return a.join() + v;")),
        ("atomic_read_of_plain", mixed(plain_add, "let v = c.atomic_read(); return a.join() + v;")),
    ] {
        let err = run_vm(name, &src).expect_err(name);
        assert!(err.starts_with(UB_PREFIX) && err.contains("data race"), "[{name}] {err}");
    }
    assert_eq!(
        run_vm("plain_read_after_join", &mixed(add, "let j = a.join(); return j + c.plain_read();")),
        Ok(VmRun { value: 1, leaks: 0, output: String::new() })
    );
    let mutex = "pub fn main() -> i32 {
    let m = Mutex[i32]::new(0);
    let a = spawn_scoped(fn() -> i32 { for i in 0..10 { let _v = m.with_lock(fn(x: &mut i32) -> i32 { *x = *x + 1; return 0; }); } return 0; });
    let b = spawn_scoped(fn() -> i32 { for i in 0..10 { let _v = m.with_lock(fn(x: &mut i32) -> i32 { *x = *x + 1; return 0; }); } return 0; });
    let _x = a.join();
    let _y = b.join();
    return m.with_lock(fn(x: &mut i32) -> i32 { return *x; });
}";
    for (name, src, value) in [
        ("atomic", format!("{atomic}{two_threads}"), 20),
        ("joined_between", format!("{plain}{joined_between}"), 2),
        ("mutex", mutex.to_string(), 20),
    ] {
        assert_eq!(run_vm(name, &src), Ok(VmRun { value, leaks: 0, output: String::new() }), "[{name}]");
    }
    for (name, src) in [
        ("plain", format!("{plain}{two_threads}")),
        ("read_before_join", format!("{plain}{read_before_join}")),
    ] {
        let err = run_vm(name, &src).expect_err(name);
        assert!(err.starts_with(UB_PREFIX) && err.contains("data race"), "[{name}] {err}");
    }
}



/// The kind of a compile error, with names, types, and numbers blanked so errors group by check.
fn error_kind(err: &str) -> String {
    let first = err.lines().next().unwrap_or(err);
    let mut out = String::new();
    let mut quoted = None;
    for c in first.chars() {
        match (quoted, c) {
            (None, '\'' | '`') => {
                quoted = Some(c);
                out.push(c);
                out.push('_');
            }
            (Some(q), c) if c == q => {
                quoted = None;
                out.push(c);
            }
            (Some(_), _) => {}
            (None, c) if c.is_ascii_digit() => {}
            (None, c) => out.push(c),
        }
    }
    out
}

/// Which compiler checks the generated programs reach: run with
/// `cargo test --lib fuzz_check_coverage -- --ignored --nocapture` (scale with `SLOPLANG_FUZZ_CASES`).
/// A check that never fires is one the fuzzer cannot test; the generator needs a construct that
/// reaches it.
#[test]
#[ignore]
fn fuzz_check_coverage() {
    let cases = env_u64("SLOPLANG_FUZZ_CASES", 400);
    let first_seed = env_u64("SLOPLANG_FUZZ_SEED", 1);
    // Constructs whose presence in *accepted* programs is what lets the oracle test them.
    let constructs = [
        "spawn_scoped", "Mutex[i32]", "Channel[i32]", "Channel[Tx]", "try_recv", "Peek::new",
        "iter_mut", "match ", "drain(", "Wrap::new", "Box[Tx]", "&mut ", "move fn", "@drop",
        // Threads writing an outer `i32`, writing through a `&mut`, iterating and pushing a `Vec`.
        "-> i32 { n", "-> i32 { *mr", "-> i32 { let mut t", "-> i32 { w", "tw",
        // Trees: deferred `let` of each shape, paths, `@leaves`, and tuple functions.
        "let mut dn", "let mut ti", "let mut dt", "let mut bp", "= &@field", "= &mut @field",
        "in @leaves(TI)", "in @leaves(TT)", "tuple_split", "tuple_concat", "(@field", "only_int(",
        // Conditional moves of droppable values.
        "eat_box(hp", "eat_str(hp", "eat_vec(hp", "let cl", "= spawn(move", "for l", "= pass_box(", "let mut hq", "let mut ho", "let mut hu",
        // Blocking channels.
        "with_capacity(1)",
        // Values taken out of containers.
        "let tk",
        // Temporaries.
        "mkv(", "vlen(&mkv(", "positive(&mkv(", "= &mkv(", ".pop() {",
        // Container allocators.
        "let mut tb", "eat_any(tb", "vec_sum(", "let mut pb", "let mut pv",
        // Contracts and user containers.
        "pass_on(", "Cell[Tx]::new(", "some_of(", "= swap_pair(",
        "= pick2(", "= second(", "= either(", "= unnest(", "stash(&mut", "keep(&mut", "= bump(", "let mut hd", "into_inner();\n", "let mut vw", "= view(", "*vw",
        // Erased borrows.
        "&Reader", "= &b", "let cr", "let cm", "run(fn", "let mut sl", "sum(tail", "let ms", "Rel::new", "= relay(", "Box[Rel]::new(", "peek()",
    ];
    let mut in_accepted = vec![0usize; constructs.len()];
    // Constructs that are wrong wherever they appear: a program with one must be rejected.
    let never = [
        // A box from an arena that dies at the end of an `if`, read after it.
        ", &pi",
    ];
    let mut kinds: std::collections::BTreeMap<String, usize> = Default::default();
    let mut accepted = 0;
    for seed in first_seed..first_seed + cases {
        let src = generate(seed);
        match Compiler::compile_source(&src) {
            Err(e) => *kinds.entry(error_kind(&e)).or_default() += 1,
            Ok(_) => {
                accepted += 1;
                for c in never {
                    assert!(!src.contains(c), "seed {seed} was accepted with '{c}'");
                }
                for (count, c) in in_accepted.iter_mut().zip(constructs) {
                    *count += usize::from(src.contains(c));
                }
            }
        }
    }
    println!("rejections by check:");
    let mut sorted: Vec<_> = kinds.into_iter().collect();
    sorted.sort_by(|a, b| b.1.cmp(&a.1));
    for (kind, n) in sorted {
        println!("{n:5}  {kind}");
    }
    println!("constructs in the {accepted} accepted programs:");
    for (c, n) in constructs.iter().zip(in_accepted) {
        println!("{n:5}  {c}");
    }
}

#[test]
fn test_vm_detects_aliasing() {
    use super::run_vm;
    use crate::vm::UB_PREFIX;
    // References forged from a raw pointer laundered through an integer, so the borrow checker
    // cannot see the conflict.
    let launder = |place: &str| format!("let p = (&raw mut {place} as usize) as *mut i32;");
    let one = format!("let mut x: i32 = 1; {}", launder("x"));
    for (name, body) in [
        ("two_mut", format!("{one} let q = (&raw mut x as usize) as *mut i32; let a = unsafe {{ &mut *p }}; let b = unsafe {{ &mut *q }}; *a = 2; *b = 3; *a = 4; return x;")),
        ("read_ends_mut", format!("{one} let q = (&raw mut x as usize) as *mut i32; let a = unsafe {{ &mut *p }}; let b = unsafe {{ &mut *q }}; let y = *a; *b = y; let z = *a; return z;")),
        ("owner_write", format!("{one} let a = unsafe {{ &mut *p }}; *a = 2; x = 3; *a = 4; return x;")),
        ("owner_read", format!("{one} let a = unsafe {{ &mut *p }}; *a = 2; let y = x; *a = 4; return y;")),
        ("write_ends_shared", format!("{one} let r = unsafe {{ &*p }}; let n = *r; x = 2; return n + *r;")),
        ("field", format!("let mut t: tuple {{ i32, i32 }} = .{{ 1, 2 }}; {} let a = unsafe {{ &mut *p }}; *a = 2; t.0 = 3; *a = 4; return t.0;", launder("t.0"))),
        // A reference from a raw pointer that did not come from `a` ends `a`, though `a` holds
        // the whole array around what it writes.
        ("raw_inside_another", format!("let mut x: [i32; 2] = [1, 2]; {} let a = &mut x; let r = unsafe {{ &mut *p }}; *r = 5; a[1] = 3; return x[0];", launder("x[0]"))),
        // An ended reference stays ended after the record of it is reclaimed and its slot is
        // used by many others.
        ("ended_then_reused", format!("{one} let a = unsafe {{ &mut *p }}; *a = 2; x = 3; let mut y: i32 = 0; for i in 0..50 {{ let b = &mut y; *b = *b + 1; }} *a = 4; return x + y;")),
    ] {
        let src = format!("pub fn main() -> i32 {{ {body} }}");
        let err = run_vm(name, &src).expect_err(name);
        assert!(err.starts_with(UB_PREFIX) && err.contains("invalidated"), "[{name}] {err}");
    }
    // Sound patterns: reborrows, disjoint fields, shared reads, interior mutability, and
    // references from raw pointers used one at a time.
    for (name, body, value) in [
        ("reborrow", "let mut x: i32 = 1; let a = &mut x; let b = &mut *a; *b = 2; *a = *a + 1; return x;", 3),
        ("disjoint", "let mut t: tuple { i32, i32 } = .{ 1, 2 }; let a = &mut t.0; let b = &mut t.1; *a = 5; *b = 6; *a = *a + *b; return t.0;", 11),
        ("shared", "let x: i32 = 4; let a = &x; let b = &x; let c = x; return *a + *b + c;", 12),
        // A raw pointer remembers the reference it came from: what is made from it again
        // descends from that one, and leaves it alive.
        ("raw_from_a_reference", "let mut x: [i32; 2] = [1, 2]; let a = &mut x; let p = &mut a[0] as *mut i32; let r = unsafe { &mut *p }; *r = 5; a[1] = 3; return x[0] + x[1];", 8),
        ("forged_in_turn", "let mut x: i32 = 1; let p = (&raw mut x as usize) as *mut i32; let a = unsafe { &mut *p }; *a = 2; let b = unsafe { &mut *p }; *b = 3; return x;", 3),
        ("vec", "let mut v = Vec[i32]::new(); v.push(1); let n = v.len() as i32; v.push(n); let r = v.get(1) orelse unreachable; return *r;", 1),
        ("mutex", "let m = Mutex[i32]::new(1); let a = &m; let b = &m; let x = a.with_lock(fn(p: &mut i32) -> i32 { *p = 2; return *p; }); return x + b.with_lock(fn(p: &mut i32) -> i32 { return *p; });", 4),
    ] {
        let src = format!("pub fn main() -> i32 {{ {body} }}");
        assert_eq!(run_vm(name, &src), Ok(VmRun { value, leaks: 0, output: String::new() }), "[{name}]");
    }
}

#[test]
fn test_vm_schedules_threads() {
    use super::{run_vm, run_vm_program};
    use crate::vm::UB_PREFIX;
    let on_schedule = |name: &str, src: &str, seed: u64| {
        let mut program = Compiler::compile_source(src).unwrap_or_else(|e| panic!("[{name}] {e}"));
        run_vm_scheduled(&mut program, Some(seed))
    };
    // Blocking in a condition wait: the receiver starts first and waits for the send.
    let channel = "pub fn main() -> i32 {
    let c = Channel[i32]::new();
    let rx = spawn_scoped(fn() -> i32 { return (c.recv() catch |e| unreachable) + (c.recv() catch |e| unreachable); });
    _ = c.send(4);
    _ = c.send(5);
    return rx.join();
}";
    assert_eq!(run_vm("channel", channel), Ok(VmRun { value: 9, leaks: 0, output: String::new() }));
    let contended = "pub fn main() -> i32 {
    let m = Mutex[i32]::new(0);
    let a = spawn_scoped(fn() -> i32 { for i in 0..5 { let _v = m.with_lock(fn(x: &mut i32) -> i32 { *x = *x + 1; return 0; }); } return 0; });
    let b = spawn_scoped(fn() -> i32 { for i in 0..5 { let _v = m.with_lock(fn(x: &mut i32) -> i32 { *x = *x + 1; return 0; }); } return 0; });
    let _x = a.join();
    let _y = b.join();
    return m.with_lock(fn(x: &mut i32) -> i32 { return *x; });
}";
    for seed in 1..=20 {
        assert_eq!(on_schedule("channel", channel, seed), Ok(VmRun { value: 9, leaks: 0, output: String::new() }), "seed {seed}");
        assert_eq!(on_schedule("contended", contended, seed), Ok(VmRun { value: 10, leaks: 0, output: String::new() }), "seed {seed}");
    }
    // A race that only exists when the second thread locks first: it reads the flag as unset
    // and writes `n`, unordered with the first thread's write after its unlock.
    let lock_order = "pub opaque(unsafe sync) Shared {
    cell n: i32,
    pub fn new() -> Self { return Self { n: 0 }; }
    pub fn set(&self) { unsafe { *(&raw mut self.n) = 1; } }
}
pub fn main() -> i32 {
    let m = Mutex[i32]::new(0);
    let c = Shared::new();
    let a = spawn_scoped(fn() -> i32 { let _v = m.with_lock(fn(x: &mut i32) -> i32 { *x = 1; return 0; }); c.set(); return 0; });
    let b = spawn_scoped(fn() -> i32 { if m.with_lock(fn(x: &mut i32) -> i32 { return *x; }) == 0 { c.set(); } return 0; });
    return a.join() + b.join();
}";
    assert_eq!(run_vm("lock_order", lock_order), Ok(VmRun { value: 0, leaks: 0, output: String::new() }), "hidden in the default order");
    let raced: Vec<u64> = (1..=20)
        .filter(|&seed| on_schedule("lock_order", lock_order, seed).is_err_and(|e| e.contains("data race")))
        .collect();
    assert!(!raced.is_empty() && raced.len() < 20, "races on seeds {raced:?}");
    // A schedule is reproducible.
    for &seed in &raced {
        assert!(on_schedule("lock_order", lock_order, seed).is_err_and(|e| e.contains("data race")));
    }
    let deadlock = "pub fn main() -> i32 {
    let m = Mutex[i32]::new(0);
    return m.with_lock(fn(x: &mut i32) -> i32 { return m.with_lock(fn(y: &mut i32) -> i32 { return *y; }); });
}";
    let err = run_vm("deadlock", deadlock).expect_err("self deadlock");
    assert!(err.starts_with(UB_PREFIX) && err.contains("deadlock"), "{err}");
    let opposite = "pub fn main() -> i32 {
    let p = Mutex[i32]::new(0);
    let q = Mutex[i32]::new(0);
    let a = spawn_scoped(fn() -> i32 { return p.with_lock(fn(x: &mut i32) -> i32 { return q.with_lock(fn(y: &mut i32) -> i32 { return *y; }); }); });
    let b = spawn_scoped(fn() -> i32 { return q.with_lock(fn(x: &mut i32) -> i32 { return p.with_lock(fn(y: &mut i32) -> i32 { return *y; }); }); });
    return a.join() + b.join();
}";
    assert!((1..=20).any(|seed| on_schedule("opposite", opposite, seed).is_err_and(|e| e.contains("deadlock"))));
    let mut program = Compiler::compile_source(opposite).unwrap();
    assert_eq!(run_vm_program(&mut program), Ok(VmRun { value: 0, leaks: 0, output: String::new() }), "no deadlock in the default order");
}
