//! Randomized soundness testing of the borrow, move, and drop checkers. Generates safe programs
//! over scopes, references, containers of references, linear values in every container shape,
//! pattern matching, `drop` hooks that read their borrows, iterators, closures, and threads, and
//! checks
//! that every program the compiler accepts:
//! - runs under the compile-time VM without undefined behaviour or leaks,
//! - consumes every linear `Tx` it creates exactly once (`main` returns -1 otherwise), and
//! - computes what the native build computes.
//!
//! `LRRR_FUZZ_CASES` (default 50), `LRRR_FUZZ_SEED` (default 1), and `LRRR_FUZZ_WORKERS` (default
//! the number of cores) control the run; a failure
//! prints the seed and a shrunk program, which `LRRR_FUZZ_SEED=<seed> LRRR_FUZZ_CASES=1`
//! reproduces.

use super::{TRAP_EXIT, VmRun, lli, run_vm_program};
use crate::lower::Compiler;

/// xorshift64*: deterministic across platforms, so a seed always reproduces its program.
struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
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
    pub fn commit(move self) -> i32 { unsafe { LIVE = LIVE - 1; } return self.id; }
}
pub struct Pair { t: Tx, n: i32 }
pub struct RefPair { r: &i32, n: i32 }
union UT { A(Tx), B(i32) }
pub opaque Peek {
    r: &i32,
    impl drop { fn drop(self: &mut Self) { unsafe { SINK = SINK + *self.r; } } }
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
}
pub opaque(linear) Wrap {
    t: Tx,
    pub fn new(t: Tx) -> Self { return Self { t: t }; }
    pub fn finish(move self) -> i32 { return self.t.commit(); }
}
";

/// Builds one program: `body` sums values read through the borrows it creates into `s`.
struct Gen {
    rng: Rng,
    out: String,
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
        let kinds = [Kind::Ref, Kind::MutRef, Kind::VecRef, Kind::BoxRef, Kind::RefField, Kind::Peek, Kind::VecPeek];
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
            _ => format!("{outer}.push(Peek::new(&{local}));"),
        };
        self.line(depth, &text);
        true
    }

    /// A read through some borrow-holding variable in scope.
    fn read(&mut self, depth: usize) {
        let k = self.small();
        let text = match self.rng.below(7) {
            6 => self.pick(Kind::MutRef).map(|m| format!("*{m} = *{m} + 1; s = s + *{m};")),
            0 => self.pick(Kind::Ref).map(|r| format!("s = s + *{r};")),
            1 => self
                .pick(Kind::VecRef)
                .map(|v| format!("if let e = {v}.get({k}) {{ s = s + **e; }}")),
            2 => self.pick(Kind::BoxRef).map(|b| format!("s = s + **{b}.get();")),
            3 => self
                .pick(Kind::IterRef)
                .map(|t| format!("if let e = {t}.next() {{ s = s + **e; }}")),
            4 => self.pick(Kind::RefField).map(|p| format!("s = s + *{p}.r + {p}.n;")),
            _ => self
                .pick(Kind::IterMut)
                .map(|t| format!("if let a = {t}.next() {{ *a = *a + 1; s = s + *a; }}")),
        };
        if let Some(text) = text {
            self.line(depth, &text);
        }
    }

    fn stmt(&mut self, depth: usize) {
        let choice = self.rng.below(54);
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
                    let n = self.declare("mr", Kind::MutRef);
                    self.line(depth, &format!("let mut {n}: &mut i32 = &mut {i};"));
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
                    self.line(depth, &format!("if let e = {w}.get({k}) {{ s = s + *e; }}"));
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
                    self.line(depth, &format!("if let e = {vr}.get({k}) {{ {r} = *e; }}"));
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
                let n = self.declare("x", Kind::Tx);
                self.line(depth, &format!("let {n} = Tx::new({v});"));
            }
            22 => {
                let n = self.declare("o", Kind::OptTx);
                let init = if self.rng.below(3) == 0 { "null".to_string() } else { format!("Tx::new({v})") };
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
                let kinds = [Kind::Tx, Kind::OptTx, Kind::UnionTx, Kind::PairTx, Kind::BoxTx, Kind::VecTx, Kind::WrapTx];
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
                    match self.rng.below(3) {
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
                        _ => {
                            let n = self.declare("j", Kind::WrapTx);
                            self.line(depth, &format!("let {n} = Wrap::new({x});"));
                        }
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
    /// Scoped threads, a shared `Mutex`, and channels (of `i32` and of linear `Tx`). Channel
    /// operations never block (`try_send` / `try_recv`), since the VM runs threads one at a time,
    /// and their results stay out of `s`: whether one succeeds depends on how threads interleave.
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
                self.line(depth, &format!("let {n} = spawn_scoped(fn() -> i32 {{ {body} }});"));
                for _ in 0..1 + self.rng.below(2) {
                    self.stmt(depth);
                }
                self.line(depth, &format!("s = s + {n}.join();"));
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
                    let send = format!("if let b{id} = {c}.try_send({v}) {{ let _u{id} = b{id}; }}");
                    self.next_name += 1;
                    self.line(depth, &send);
                }
                (_, Some(c)) => {
                    let send = format!(
                        "if let b{id} = {c}.try_send(Tx::new({v})) {{ let _u{id} = b{id}.commit(); }}"
                    );
                    self.next_name += 1;
                    self.line(depth, &send);
                }
                (Some(c), None) => {
                    let n = self.declare("th", Kind::Thread);
                    self.line(
                        depth,
                        &format!("let {n} = spawn_scoped(fn() -> i32 {{ if let b{id} = {c}.try_send({v}) {{ let _u{id} = b{id}; }} return 0; }});"),
                    );
                }
                _ => {}
            },
            _ => match (self.pick(Kind::ChanInt), self.pick(Kind::ChanTx)) {
                (Some(c), _) if self.rng.below(2) == 0 => {
                    self.next_name += 1;
                    self.line(depth, &format!("if let g{id} = {c}.try_recv() {{ let _u{id} = g{id}; }}"));
                }
                (_, Some(c)) => {
                    self.next_name += 1;
                    self.line(depth, &format!("if let g{id} = {c}.try_recv() {{ let _u{id} = g{id}.commit(); }}"));
                }
                _ => {}
            },
        }
    }
}

impl Gen {
    /// The body of a scoped thread: reads or writes variables of this or outer scopes (usually
    /// writes, if `write`).
    fn thread_body(&mut self, v: usize, id: usize, lock: &str, write: bool) -> String {
        let choice = if write && self.rng.below(4) != 0 { [1, 2, 4][self.rng.below(3)] } else { self.rng.below(7) };
        let body = match choice {
            0 => self.pick(Kind::MutexInt).map(|m| format!("return {m}.{lock};")),
            1 => self.pick(Kind::Int).map(|i| format!("{i} = {i} + {v}; return 0;")),
            2 => self.pick(Kind::MutRef).map(|m| format!("*{m} = *{m} + {v}; return 0;")),
            3 => self.pick(Kind::VecInt).map(|w| {
                format!("let mut t{id}: i32 = 0; for e{id} in {w}.iter() {{ t{id} = t{id} + *e{id}; }} return t{id};")
            }),
            4 => self.pick(Kind::VecInt).map(|w| format!("{w}.push({v}); return 0;")),
            5 => self.pick(Kind::RefField).map(|p| format!("return *{p}.r + {p}.n;")),
            _ => None,
        };
        body.unwrap_or_else(|| match (self.pick(Kind::Ref), self.pick(Kind::Int)) {
            (Some(r), Some(i)) => format!("return *{r} + {i};"),
            (_, Some(i)) => format!("return {i};"),
            _ => format!("return {v};"),
        })
    }
}

/// A statement consuming linear `name` of `kind`; unless `sound`, one that may lose the value
/// (the compiler must reject it).
fn consume(name: &str, kind: Kind, id: usize, sound: bool) -> String {
    match (kind, sound) {
        (Kind::Tx, _) => format!("s = s + {name}.commit();"),
        (Kind::OptTx, true) => format!("if let t{id} = {name} {{ s = s + t{id}.commit(); }}"),
        (Kind::OptTx, false) => format!("if let t{id} = {name} {{ s = s + 1; }}"),
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
        _ => String::new(),
    }
}

/// The program for `seed`.
fn generate(seed: u64) -> String {
    let mut g = Gen {
        rng: Rng::new(seed),
        out: String::new(),
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
    format!(
        "{PRELUDE}fn body() -> i32 {{\n    let mut s: i32 = 0;\n{}    return s;\n}}\n\
         pub fn main() -> i32 {{\n    let r = body();\n    if unsafe {{ LIVE }} != 0 {{\n        return -1;\n    }}\n    return r;\n}}\n",
        g.out
    )
}

fn env_u64(name: &str, default: u64) -> u64 {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// Why `src` shows a soundness bug, if the compiler accepts it: undefined behaviour or a leak in
/// the VM, a linear value created and not consumed exactly once, or a result that differs from
/// the native build. `None` when the compiler rejects it or it runs correctly.
fn failure(src: &str) -> Option<String> {
    let mut program = Compiler::compile_source(src).ok()?;
    let native = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT)
        .map(|ir| lli(&ir).status.code());
    match run_vm_program(&mut program) {
        Err(e) => Some(format!("VM: {e}")),
        Ok(VmRun { leaks, .. }) if leaks > 0 => Some(format!("{leaks} heap block(s) leaked")),
        Ok(VmRun { value: -1, .. }) => Some("a linear Tx was not consumed exactly once".to_string()),
        Ok(VmRun { value, .. }) => {
            let expected = Some((value & 0xff) as i32);
            (native.as_ref().ok() != Some(&expected))
                .then(|| format!("VM returned {value}, native run gave {native:?}"))
        }
    }
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
    let cases = env_u64("LRRR_FUZZ_CASES", 50);
    let first_seed = env_u64("LRRR_FUZZ_SEED", 1);
    // Cases are independent: workers take seeds in turn, and failures are reported in seed order.
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get()) as u64;
    let workers = env_u64("LRRR_FUZZ_WORKERS", cores);
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
                        if Compiler::compile_source(&src).is_err() {
                            rejected += 1;
                            continue;
                        }
                        accepted += 1;
                        if let Some(why) = failure(&src) {
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
        assert_eq!(run_vm(name, src), Ok(VmRun { value, leaks: 0 }), "[{name}]");
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
        Ok(VmRun { value: 0, leaks: 1 })
    );
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
    pub fn bump(self: &Self) {{ {bump} }}
    pub fn get(self: &Self) -> i32 {{ return unsafe {{ @atomic_load(&raw mut self.n) }}; }}
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
        assert_eq!(run_vm(name, &src), Ok(VmRun { value, leaks: 0 }), "[{name}]");
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
/// `cargo test --lib fuzz_check_coverage -- --ignored --nocapture` (scale with `LRRR_FUZZ_CASES`).
/// A check that never fires is one the fuzzer cannot test; the generator needs a construct that
/// reaches it.
#[test]
#[ignore]
fn fuzz_check_coverage() {
    let cases = env_u64("LRRR_FUZZ_CASES", 400);
    let first_seed = env_u64("LRRR_FUZZ_SEED", 1);
    // Constructs whose presence in *accepted* programs is what lets the oracle test them.
    let constructs = [
        "spawn_scoped", "Mutex[i32]", "Channel[i32]", "Channel[Tx]", "try_recv", "Peek::new",
        "iter_mut", "match ", "drain(", "Wrap::new", "Box[Tx]", "&mut ", "move fn", "@drop",
        // Threads writing an outer `i32`, writing through a `&mut`, iterating and pushing a `Vec`.
        "-> i32 { n", "-> i32 { *mr", "-> i32 { let mut t", "-> i32 { w", "tw",
    ];
    let mut in_accepted = vec![0usize; constructs.len()];
    let mut kinds: std::collections::BTreeMap<String, usize> = Default::default();
    let mut accepted = 0;
    for seed in first_seed..first_seed + cases {
        let src = generate(seed);
        match Compiler::compile_source(&src) {
            Err(e) => *kinds.entry(error_kind(&e)).or_default() += 1,
            Ok(_) => {
                accepted += 1;
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
