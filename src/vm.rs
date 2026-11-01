use crate::ir::{
    BinOp, BlockId, ConstValue, FuncId, Function, GlobalId, LocalId, Operand, Place, Program,
    Projection, Rvalue, Statement, Terminator, Type, TypeId, UnOp,
};
use crate::wide::Wide;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PtrTarget {
    /// A local of the frame at index `frame`, as it was at `epoch`: each local gets a fresh epoch
    /// when its frame is created and at every `StorageLive` / `StorageDead`, so a pointer that
    /// outlives the storage it was taken from no longer matches (see `check_local`).
    Local {
        frame: usize,
        local: LocalId,
        epoch: u64,
    },
    /// Block `id` of the emulated heap (`malloc` / `realloc` / `free`).
    Heap(usize),
    Global(GlobalId),
    /// Thread `thread`'s copy of a `thread_local` global: a pointer keeps naming the copy of
    /// the thread that took it.
    ThreadLocal { thread: usize, global: GlobalId },
    Str(String),
    /// Non-null, aligned null-page pointer to a zero-sized type (`addr == k * align_of(T)`).
    Dangling { addr: i128, ty: TypeId },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ResolvedProj {
    Field(u32),
    Variant(u32),
    Index(usize),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Uninit,
    Void,
    Bool(bool),
    Int(i128),
    /// An integer that does not fit in `i128` (values of `u128`..`u512` / `i129`..`i512` types).
    Wide(Box<crate::wide::Wide>),
    Float(u64), // IEEE 754 bits
    Type(TypeId),
    Func(FuncId),
    Str(String),
    Array(Vec<Value>),
    Struct {
        ty: TypeId,
        fields: Vec<Value>,
    },
    Overlay {
        ty: TypeId,
        active_field: Option<u32>,
        val: Box<Value>,
    },
    Union {
        ty: TypeId,
        variant: u32,
        payload: Box<Value>,
    },
    Ptr {
        target: PtrTarget,
        projections: Vec<ResolvedProj>,
        tag: Tag,
    },
}

/// Identifies the reference a pointer value was created as, for alias checking (see
/// `Aliasing`). Pointers compare by address, so all tags are equal; `Tag(0)` is untracked.
#[derive(Debug, Clone, Copy, Default)]
pub struct Tag(u64);

impl PartialEq for Tag {
    fn eq(&self, _: &Tag) -> bool {
        true
    }
}

impl Eq for Tag {}

/// How the place just resolved was reached: from a local or global, through a tracked
/// reference, or through a raw pointer (which unsafe code answers for).
#[derive(Debug, Clone, Copy, PartialEq)]
enum Via {
    Owner,
    Reference(u64),
    Raw,
}

/// One reference: the place it borrows, the reference it was reborrowed from (or 0), and
/// whether it can still be used.
#[derive(Debug, Clone)]
struct Borrow {
    path: Vec<ResolvedProj>,
    mutable: bool,
    parent: u64,
    live: bool,
    /// Derived from a raw pointer: an unsafe abstraction, such as a `Mutex` handing out a `&mut`
    /// to data inside a shared value.
    from_raw: bool,
}

/// Which references are still usable, to catch aliasing the compiler should have rejected. An
/// access through a reference or owner ends every overlapping reference that it was not derived
/// from: a write ends all of them, a read only the `&mut` ones. Using an ended reference is
/// undefined behaviour. Raw pointers are not tracked: `Mutex`, `cell` fields, and containers
/// are built on them. A write through a `&T` is interior mutation and ends nothing, and a write
/// through a reference derived from a raw pointer does not end shared references, for the same
/// reason.
#[derive(Debug, Default)]
struct Aliasing {
    /// Reference `Tag(i)` is `borrows[i - 1]`.
    borrows: Vec<Borrow>,
    /// The live references into each allocation.
    by_target: std::collections::HashMap<PtrTarget, LiveBorrows>,
}

/// The live references into one allocation. A read ends only `&mut` ones, so that shared ones,
/// of which a long-lived value collects one each time it is used, need no look until a write.
#[derive(Debug, Default)]
struct LiveBorrows {
    shared: Vec<u64>,
    mutable: Vec<u64>,
}

impl Aliasing {
    fn borrow(&self, tag: u64) -> &Borrow {
        &self.borrows[tag as usize - 1]
    }

    /// Whether `tag` is `of` or one of the references `of` was derived from.
    fn is_ancestor(&self, tag: u64, of: u64) -> bool {
        let mut cur = of;
        while cur != 0 {
            if cur == tag {
                return true;
            }
            cur = self.borrow(cur).parent;
        }
        false
    }

    fn access(&mut self, target: &PtrTarget, path: &[ResolvedProj], via: Via, write: bool) {
        let by = match via {
            Via::Raw => return,
            Via::Owner => 0,
            Via::Reference(t) if write && !self.borrow(t).mutable => return,
            Via::Reference(t) => t,
        };
        let Some(live) = self.by_target.get_mut(target) else {
            return;
        };
        let mut live = std::mem::take(live);
        let interior = by != 0 && self.borrow(by).from_raw;
        self.end_overlapping(&mut live.mutable, path, by);
        if write && !interior {
            self.end_overlapping(&mut live.shared, path, by);
        }
        self.by_target.insert(target.clone(), live);
    }

    /// Ends the `tags` that overlap `path` and were not what `by` was derived from.
    fn end_overlapping(&mut self, tags: &mut Vec<u64>, path: &[ResolvedProj], by: u64) {
        tags.retain(|&tag| {
            let overlaps = self.borrow(tag).path.iter().zip(path).all(|(x, y)| x == y);
            if overlaps && !self.is_ancestor(tag, by) {
                self.borrows[tag as usize - 1].live = false;
                return false;
            }
            true
        });
    }
}

impl Value {
    /// An integer value in canonical form: `Int` when it fits in `i128`, otherwise `Wide`.
    pub fn from_wide(v: crate::wide::Wide) -> Self {
        match v.to_i128() {
            Some(n) => Value::Int(n),
            None => Value::Wide(Box::new(v)),
        }
    }

    pub fn from_f64(v: f64) -> Self {
        Self::Float(v.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        if let Self::Float(bits) = self {
            Some(f64::from_bits(*bits))
        } else {
            None
        }
    }

    pub fn to_const(&self) -> Result<ConstValue, String> {
        match self {
            Value::Void => Ok(ConstValue::Void),
            Value::Bool(b) => Ok(ConstValue::Bool(*b)),
            Value::Int(n) => Ok(ConstValue::I64(*n)),
            Value::Float(bits) => Ok(ConstValue::F64(*bits)),
            Value::Type(id) => Ok(ConstValue::Type(*id)),
            Value::Func(id) => Ok(ConstValue::Func(*id)),
            Value::Str(s) => Ok(ConstValue::Str(s.clone())),
            Value::Array(elems) | Value::Struct { fields: elems, .. } => {
                let mut cvs = Vec::with_capacity(elems.len());
                for e in elems {
                    cvs.push(e.to_const()?);
                }
                Ok(ConstValue::Aggregate(cvs))
            }
            _ => Err(format!(
                "Cannot convert runtime/composite value {self:?} to immediate ConstValue"
            )),
        }
    }
}

struct Frame {
    func_id: FuncId,
    locals: Vec<Value>,
    /// The current epoch of each local (see `PtrTarget::Local`).
    epochs: Vec<u64>,
    /// For the entry frame of an emulated thread (`pthread_create`): the thread whose result
    /// its return value is.
    thread: Option<usize>,
    block: BlockId,
    /// When this frame returns, where in the caller frame should `_0` be written, and which block to jump to?
    caller_return: Option<(Option<Place>, BlockId)>,
}

/// A `malloc` block of the VM's emulated heap, holding `T`-typed slots: `u8` from `malloc`, and
/// retyped by the first cast of its pointer to `*mut T` while all slots are uninitialized.
#[derive(Debug, Clone)]
struct HeapBlock {
    bytes: u64,
    elem: TypeId,
    slots: Value,
    freed: bool,
}

/// A memory slot for race detection: a target and, for an array or heap block, the element.
type SlotKey = (PtrTarget, Option<usize>);

fn slot_key(target: &PtrTarget, projs: &[ResolvedProj]) -> SlotKey {
    let elem = match projs.first() {
        Some(ResolvedProj::Index(i)) => Some(*i),
        _ => None,
    };
    (target.clone(), elem)
}

/// The field of a slot an access reaches, or `None` for all of it. Fields are separate memory, so
/// a lock-free read of one does not race with writes to another, but a whole access meets them all.
fn slot_field(projs: &[ResolvedProj]) -> Option<u32> {
    let rest = match projs.first() {
        Some(ResolvedProj::Index(_)) => &projs[1..],
        _ => projs,
    };
    match rest.first() {
        Some(ResolvedProj::Field(field)) => Some(*field),
        _ => None,
    }
}

/// The last write to a slot and the reads since, each as `(thread, that thread's clock)`.
#[derive(Debug, Clone, Default)]
struct Shadow {
    write: Option<(usize, u64)>,
    reads: Vec<(usize, u64)>,
}

/// Happens-before data-race detection over the emulated threads, with vector clocks. Enabled
/// at the first `pthread_create`. A created thread runs to completion, but its accesses stay
/// unordered with its creator's later ones until a `join`, a mutex hand-off, or an atomic
/// operation orders them, so races are found whatever order the threads happened to run in.
#[derive(Debug, Clone, Default)]
struct RaceState {
    /// The vector clock of each thread: 0 is the main thread, pthread `i` is thread `i + 1`.
    clocks: Vec<Vec<u64>>,
    /// The running thread.
    current: usize,
    /// Final clocks of finished threads, for `pthread_join`.
    finished: Vec<Option<Vec<u64>>>,
    shadow: std::collections::HashMap<SlotKey, std::collections::HashMap<Option<u32>, Shadow>>,
    /// Release clocks of mutexes and atomic locations.
    sync: std::collections::HashMap<SlotKey, Vec<u64>>,
}

fn clock(vc: &[u64], thread: usize) -> u64 {
    vc.get(thread).copied().unwrap_or(0)
}

fn join_clock(into: &mut Vec<u64>, other: &[u64]) {
    if into.len() < other.len() {
        into.resize(other.len(), 0);
    }
    for (a, &b) in into.iter_mut().zip(other) {
        *a = (*a).max(b);
    }
}

impl RaceState {
    fn tick(&mut self) {
        let t = self.current;
        let vc = &mut self.clocks[t];
        if vc.len() <= t {
            vc.resize(t + 1, 0);
        }
        vc[t] += 1;
    }

    /// Takes in the release clock of `key` (a lock, or an atomic location).
    fn acquire(&mut self, key: &SlotKey) {
        if let Some(released) = self.sync.get(key).cloned() {
            join_clock(&mut self.clocks[self.current], &released);
        }
    }

    /// Publishes the current thread's clock at `key`.
    fn release(&mut self, key: SlotKey) {
        let vc = self.clocks[self.current].clone();
        join_clock(self.sync.entry(key).or_default(), &vc);
        self.tick();
    }
}

/// Frames of thread `t` have ids from `t * FRAME_STRIDE`, so a pointer to a local stays
/// meaningful in any thread.
const FRAME_STRIDE: usize = 1 << 24;

/// What a blocked thread waits for. Thread ids are as in `RaceState`.
#[derive(Debug, Clone)]
enum Wait {
    Mutex(SlotKey),
    Join(usize),
    Cond,
}

/// A pthread call that cannot finish yet; the scheduler retries it once its wait is over.
struct Blocked {
    symbol: String,
    args: Vec<Value>,
    destination: Place,
    target: BlockId,
    wait: Wait,
}

/// The outcome of an emulated pthread call.
enum Pthread {
    Done(Value),
    Block(Wait),
}

/// A thread's progress through `pthread_cond_wait`.
#[derive(Debug, Clone, Copy, PartialEq, Default)]
enum CondWait {
    #[default]
    None,
    Waiting,
    Woken,
}

/// What a descriptor reads from and writes to: one end of a pipe, or for a connected socket,
/// one pipe each way.
#[derive(Debug, Clone, Copy, Default)]
struct Ends {
    read: Option<usize>,
    write: Option<usize>,
}

#[derive(Debug, Default)]
struct Listener {
    port: u16,
    pending: std::collections::VecDeque<i32>,
}

#[derive(Debug)]
struct OpenFile {
    path: String,
    at: usize,
}

/// The emulated threads. One runs at a time, in `Vm::frames`, until it blocks, ends, or reaches
/// a synchronization point where a seeded schedule picks the next thread. Without a seed a
/// created thread runs first and threads switch only when they must.
#[derive(Default)]
struct Scheduler {
    running: usize,
    /// Each thread's stack; the running thread's is empty, being in `Vm::frames`.
    stacks: Vec<Vec<Frame>>,
    blocked: Vec<Option<Blocked>>,
    done: Vec<bool>,
    cond: Vec<CondWait>,
    /// Threads waiting on each condition variable, longest first.
    cond_waiters: std::collections::HashMap<SlotKey, Vec<usize>>,
    /// The holder of each locked mutex.
    held: std::collections::HashMap<SlotKey, usize>,
    /// Virtual time, advanced only by bounded waits and sleeps.
    clock_ns: u64,
    /// Fibers: threads that only run when switched to, sharing the thread-locals of the thread
    /// that made them.
    parked: std::collections::HashSet<usize>,
    /// The fiber that each saved `ucontext_t` resumes.
    contexts: std::collections::HashMap<SlotKey, usize>,
    /// The thread each fiber belongs to.
    fiber_home: std::collections::HashMap<usize, usize>,
    /// The buffer behind each emulated pipe, and for each open descriptor, its ends.
    pipes: Vec<std::collections::VecDeque<u8>>,
    fds: std::collections::HashMap<i32, Ends>,
    /// Sockets bound with `bind`, each with the connections `accept` has yet to take.
    listeners: std::collections::HashMap<i32, Listener>,
    next_port: u16,
    /// Emulated files by path, and those open, by the heap block standing for the `FILE`.
    files: std::collections::HashMap<String, Vec<u8>>,
    open_files: std::collections::HashMap<usize, OpenFile>,
    /// What the program wrote to stdout and stderr, once `allow_io` let it.
    output: Option<Vec<u8>>,
    /// What each emulated `epoll` watches: the descriptor, its event as given, and if it fired.
    epolls: std::collections::HashMap<i32, Vec<(i32, [i128; 3], bool)>>,
    next_fd: i32,
    /// Each OS thread's `errno`, the block behind it. A fiber uses that of its thread.
    errno: std::collections::HashMap<usize, Value>,
    /// For tests: every other read or write of a pipe fails with `EINTR`.
    interrupt_io: bool,
    interrupted: bool,
    /// A wait in `poll` timed out, so other threads should get a turn.
    yield_after: bool,
    /// A `swapcontext` waiting to happen, once its result is written.
    pending_switch: Option<(usize, SlotKey)>,
    /// Each thread's copy of a `thread_local` global, made when it first takes its address.
    thread_locals: std::collections::HashMap<(usize, GlobalId), Value>,
    rng: Option<u64>,
}

impl Scheduler {
    fn new() -> Self {
        let mut sched = Scheduler::default();
        sched.add(0);
        sched
    }

    /// Makes room for thread `t`.
    /// The thread whose thread-locals `t` uses.
    fn os_thread(&self, t: usize) -> usize {
        self.fiber_home.get(&t).copied().unwrap_or(t)
    }

    fn add(&mut self, t: usize) {
        self.stacks.resize_with(t + 1, Vec::new);
        self.blocked.resize_with(t + 1, || None);
        self.done.resize(t + 1, false);
        self.cond.resize(t + 1, CondWait::None);
    }

    fn can_run(&self, t: usize) -> bool {
        !self.done[t]
            && !self.parked.contains(&t)
            && match self.blocked[t].as_ref().map(|b| &b.wait) {
                None => true,
                Some(Wait::Mutex(key)) => !self.held.contains_key(key),
                Some(Wait::Join(thread)) => self.done[*thread],
                Some(Wait::Cond) => self.cond[t] == CondWait::Woken,
            }
    }

    /// The next thread to run, from those that can. `avoid_running` prefers any other.
    fn pick(&mut self, avoid_running: bool) -> Option<usize> {
        let ready: Vec<usize> = (0..self.done.len()).filter(|&t| self.can_run(t)).collect();
        if let Some(state) = &mut self.rng {
            *state ^= *state >> 12;
            *state ^= *state << 25;
            *state ^= *state >> 27;
            let r = state.wrapping_mul(0x2545_F491_4F6C_DD1D) >> 32;
            return (!ready.is_empty()).then(|| ready[r as usize % ready.len()]);
        }
        if !avoid_running && ready.contains(&self.running) {
            return Some(self.running);
        }
        let after = ready.iter().find(|&&t| t > self.running);
        after.or(ready.first()).copied()
    }
}

/// Prefix of the VM's errors for undefined behaviour in the evaluated program, as opposed to
/// operations the VM does not support.
pub const UB_PREFIX: &str = "Undefined behaviour: ";

/// Addresses the VM gives pointers cast to integers: non-zero and aligned for any type.
const PIPE_CAPACITY: usize = 1024;
/// `POLLIN` and `POLLOUT`, which `EPOLLIN` and `EPOLLOUT` equal.
const EVENT_IN: i128 = 1;
const EVENT_OUT: i128 = 4;

const EXPOSED_BASE: i128 = 1 << 32;
const EXPOSED_STRIDE: i128 = 1 << 24;

pub struct Vm<'a> {
    pure: bool,
    program: &'a mut Program,
    globals: Vec<Value>,
    frames: Vec<Frame>,
    heap: Vec<HeapBlock>,
    next_epoch: u64,
    /// Results of the emulated threads (`pthread_create`), until joined.
    threads: Vec<Option<Value>>,
    race: std::cell::RefCell<Option<RaceState>>,
    /// Set while an atomic operation accesses memory, which synchronizes instead of racing.
    in_atomic: std::cell::Cell<bool>,
    sched: Scheduler,
    /// Enabled by `check_aliasing`.
    aliasing: std::cell::RefCell<Option<Aliasing>>,
    /// How `resolve_place` last reached a place.
    last_via: std::cell::Cell<Via>,
    /// Pointers cast to integers, at `EXPOSED_BASE + i * EXPOSED_STRIDE`, so an integer cast
    /// back to a pointer recovers the pointer (and its epoch or heap block) exactly.
    exposed: Vec<Value>,
    /// Each pointer exposed, by its address.
    exposed_at: std::collections::HashMap<i128, Value>,
    steps: usize,
    max_steps: usize,
    /// The destination and continuation of the host call the VM is suspended in.
    pending_host: Option<(Place, BlockId)>,
    /// Bodies of the functions run so far (see `get_function`).
    fn_cache: std::collections::HashMap<FuncId, std::rc::Rc<Function>>,
}

/// Symbol prefix of host functions: externs that the compiler, not C, implements during
/// compile-time evaluation (see `VmExit::Host`).
pub const HOST_PREFIX: &str = "slir.host.";

/// How a run of the VM ends: the root call returned, or the VM suspended in a call to a host
/// function (an extern whose symbol starts with `HOST_PREFIX`), to be resumed with its result.
#[derive(Debug)]
pub enum VmExit {
    Return(Value),
    Host { symbol: String, args: Vec<Value> },
}

/// A suspended VM, detached from the program so its owner can use the program (to answer a
/// host call) before resuming it with `Vm::from_state`.
pub struct VmState {
    globals: Vec<Value>,
    frames: Vec<Frame>,
    heap: Vec<HeapBlock>,
    next_epoch: u64,
    /// Results of the emulated threads (`pthread_create`), until joined.
    threads: Vec<Option<Value>>,
    race: Option<RaceState>,
    sched: Scheduler,
    /// Pointers cast to integers, at `EXPOSED_BASE + i * EXPOSED_STRIDE`, so an integer cast
    /// back to a pointer recovers the pointer (and its epoch or heap block) exactly.
    exposed: Vec<Value>,
    /// Each pointer exposed, by its address.
    exposed_at: std::collections::HashMap<i128, Value>,
    steps: usize,
    max_steps: usize,
    pending_host: Option<(Place, BlockId)>,
}

impl<'a> Vm<'a> {
    pub fn new(program: &'a mut Program) -> Self {
        let globals = program
            .globals
            .iter()
            .map(|g| Self::const_to_val_typed(&g.init, g.ty, &program.types))
            .collect();
        Self {
            pure: false,
            program,
            globals,
            frames: Vec::new(),
            heap: Vec::new(),
            next_epoch: 0,
            threads: Vec::new(),
            race: std::cell::RefCell::new(None),
            in_atomic: std::cell::Cell::new(false),
            sched: Scheduler::new(),
            aliasing: std::cell::RefCell::new(None),
            last_via: std::cell::Cell::new(Via::Owner),
            exposed: Vec::new(),
            exposed_at: std::collections::HashMap::new(),
            steps: 0,
            max_steps: 1_000_000,
            pending_host: None,
            fn_cache: std::collections::HashMap::new(),
        }
    }

    /// Detaches the VM's state from the program (see `VmState`).
    pub fn into_state(self) -> VmState {
        VmState {
            globals: self.globals,
            frames: self.frames,
            heap: self.heap,
            next_epoch: self.next_epoch,
            threads: self.threads,
            race: self.race.into_inner(),
            sched: self.sched,
            exposed: self.exposed,
            exposed_at: self.exposed_at,
            steps: self.steps,
            max_steps: self.max_steps,
            pending_host: self.pending_host,
        }
    }

    /// Re-attaches a suspended VM to `program`, which may have gained functions, types, and
    /// globals in the meantime.
    pub fn from_state(program: &'a mut Program, state: VmState) -> Self {
        let mut globals = state.globals;
        for g in &program.globals[globals.len().min(program.globals.len())..] {
            globals.push(Self::const_to_val_typed(&g.init, g.ty, &program.types));
        }
        Self {
            pure: false,
            program,
            globals,
            frames: state.frames,
            heap: state.heap,
            next_epoch: state.next_epoch,
            threads: state.threads,
            race: std::cell::RefCell::new(state.race),
            in_atomic: std::cell::Cell::new(false),
            sched: state.sched,
            aliasing: std::cell::RefCell::new(None),
            last_via: std::cell::Cell::new(Via::Owner),
            exposed: state.exposed,
            exposed_at: state.exposed_at,
            steps: state.steps,
            max_steps: state.max_steps,
            pending_host: state.pending_host,
            fn_cache: std::collections::HashMap::new(),
        }
    }

    /// Starts a call of `func_id`, running until it returns or calls a host function.
    pub fn start_call(&mut self, func_id: FuncId, args: Vec<Value>) -> Result<VmExit, String> {
        self.push_root_frame(func_id, args)?;
        self.run()
    }

    /// Resumes a VM suspended in a host call, with the call's result.
    pub fn resume(&mut self, result: Value) -> Result<VmExit, String> {
        let (dest, next_block) = self
            .pending_host
            .take()
            .ok_or("The compile-time VM is not suspended in a host call")?;
        self.write_place(&dest, result)?;
        let top = self.frames.len() - 1;
        self.frames[top].block = next_block;
        self.run()
    }

    /// Heap blocks and descriptors not yet given back: leaks, once the program has returned.
    pub fn live_allocations(&self) -> usize {
        let blocks = self.heap.iter().filter(|b| !b.freed).count();
        blocks - self.sched.errno.len() + self.sched.fds.len() + self.sched.epolls.len()
    }

    fn fresh_epochs(&mut self, n: usize) -> Vec<u64> {
        (0..n)
            .map(|_| {
                self.next_epoch += 1;
                self.next_epoch
            })
            .collect()
    }

    /// Renews `local`'s storage in the current frame: pointers taken before no longer reach it.
    fn renew_storage(&mut self, local: LocalId) {
        self.next_epoch += 1;
        let frame = self.frames.len() - 1;
        if let Some(e) = self.frames[frame].epochs.get_mut(local.0 as usize) {
            *e = self.next_epoch;
        }
    }

    /// The frame with id `id` (see `FRAME_STRIDE`).
    fn frame_at(&self, id: usize) -> Option<&Frame> {
        let (thread, index) = (id / FRAME_STRIDE, id % FRAME_STRIDE);
        if thread == self.sched.running {
            self.frames.get(index)
        } else {
            self.sched.stacks.get(thread)?.get(index)
        }
    }

    fn frame_at_mut(&mut self, id: usize) -> Option<&mut Frame> {
        let (thread, index) = (id / FRAME_STRIDE, id % FRAME_STRIDE);
        if thread == self.sched.running {
            self.frames.get_mut(index)
        } else {
            self.sched.stacks.get_mut(thread)?.get_mut(index)
        }
    }

    /// Runs thread selection with `seed`, trying a different interleaving for each seed.
    /// Makes reading a mutable static or calling out of the program an error, for an expression
    /// the compiler would like to fold: its value must not depend on when it runs.
    pub fn require_purity(&mut self) {
        self.pure = true;
    }

    /// Makes every other read or write of a pipe fail with `EINTR`, as a signal can.
    /// Lets the program do I/O, all of it emulated in memory: stdout and stderr are collected for
    /// `output`, files last as long as the VM, and sockets connect to each other. Without this,
    /// as in compile-time evaluation, it is refused.
    pub fn allow_io(&mut self) {
        self.sched.output = Some(Vec::new());
    }

    /// What the program wrote since `allow_io`.
    pub fn output(&self) -> &[u8] {
        self.sched.output.as_deref().unwrap_or_default()
    }

    pub fn set_interrupt_io(&mut self) {
        self.sched.interrupt_io = true;
    }

    pub fn set_schedule(&mut self, seed: u64) {
        self.sched.rng = Some(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    }

    fn switch_to(&mut self, thread: usize) {
        let running = self.sched.running;
        if thread == running {
            return;
        }
        self.sched.stacks[running] = std::mem::take(&mut self.frames);
        self.frames = std::mem::take(&mut self.sched.stacks[thread]);
        self.sched.running = thread;
        if let Some(race) = self.race.get_mut().as_mut() {
            race.current = thread;
        }
    }

    /// Moves on to the next thread that can run, finishing the pthread call it blocked in.
    fn reschedule(&mut self, avoid_running: bool) -> Result<(), String> {
        loop {
            let Some(thread) = self.sched.pick(avoid_running) else {
                return Err(format!(
                    "{UB_PREFIX}deadlock: every thread is blocked on a lock, a join, or a condition"
                ));
            };
            self.switch_to(thread);
            let Some(blocked) = self.sched.blocked[thread].take() else {
                return Ok(());
            };
            match self.call_pthread(&blocked.symbol, &blocked.args)? {
                Some(Pthread::Done(result)) => {
                    self.write_place(&blocked.destination, result)?;
                    self.frames.last_mut().unwrap().block = blocked.target;
                    return Ok(());
                }
                Some(Pthread::Block(wait)) => {
                    self.sched.blocked[thread] = Some(Blocked { wait, ..blocked });
                }
                None => unreachable!("only pthread calls block"),
            }
        }
    }

    /// A point where a seeded schedule may switch threads.
    fn sync_point(&mut self) -> Result<(), String> {
        if self.sched.rng.is_some() && self.sched.done.len() > 1 {
            self.reschedule(false)?;
        }
        Ok(())
    }

    /// The local a pointer reaches, if its storage is still the one the pointer was taken from.
    fn check_local(&self, frame: usize, local: LocalId, epoch: u64) -> Result<(), String> {
        let current = self.frame_at(frame).and_then(|f| f.epochs.get(local.0 as usize));
        match current {
            Some(&e) if e == epoch => Ok(()),
            Some(_) => Err(format!(
                "{UB_PREFIX}access through a pointer to {local}, whose storage has ended (it went out of scope or was moved and re-created)"
            )),
            None => Err(format!(
                "{UB_PREFIX}access through a pointer to {local} of a function that has returned"
            )),
        }
    }

    /// The live heap block `id`.
    fn heap_block(&self, id: usize) -> Result<&HeapBlock, String> {
        let block = self.heap.get(id).ok_or_else(|| format!("Undefined heap block {id}"))?;
        if block.freed {
            return Err(format!("{UB_PREFIX}use of heap memory after it was freed"));
        }
        Ok(block)
    }

    /// A new heap block of `bytes`, as `elem` slots.
    fn allocate(&mut self, bytes: u64, elem: TypeId) -> Result<Value, String> {
        let (size, _) = self.program.type_size_align(elem)?;
        let count = if size == 0 { 0 } else { bytes / size };
        let slot = self.uninit_shape(elem);
        self.heap.push(HeapBlock {
            bytes,
            elem,
            slots: Value::Array(vec![slot; count as usize]),
            freed: false,
        });
        Ok(Value::Ptr {
            target: PtrTarget::Heap(self.heap.len() - 1),
            projections: vec![ResolvedProj::Index(0)],
            tag: Tag::default(),
        })
    }

    /// The heap block `ptr` points to the start of, for `free` / `realloc`.
    fn block_start(&self, ptr: &Value, what: &str) -> Result<Option<usize>, String> {
        match ptr {
            Value::Int(0) => Ok(None),
            Value::Ptr {
                target: PtrTarget::Heap(id),
                projections,
                ..
            } => {
                let block = self.heap.get(*id).ok_or_else(|| format!("Undefined heap block {id}"))?;
                if block.freed {
                    return Err(format!("{UB_PREFIX}'{what}' of heap memory that was already freed"));
                }
                if !matches!(projections.as_slice(), [] | [ResolvedProj::Index(0)]) {
                    return Err(format!(
                        "{UB_PREFIX}'{what}' of a pointer into the middle of a heap block"
                    ));
                }
                Ok(Some(*id))
            }
            other => Err(format!("{UB_PREFIX}'{what}' of a pointer that 'malloc' did not return ({other:?})")),
        }
    }

    /// Emulates the C allocator, which the VM implements as a typed heap that detects misuse.
    fn call_allocator(&mut self, symbol: &str, args: &[Value]) -> Result<Option<Value>, String> {
        let u8_ty = self.program.intern_type(Type::Int {
            signed: false,
            bits: 8,
        });
        let bytes = |v: &Value| match v {
            Value::Int(n) if *n >= 0 => Ok(*n as u64),
            other => Err(format!("Allocation size must be a non-negative integer, found {other:?}")),
        };
        match symbol {
            "malloc" => Ok(Some(self.allocate(bytes(&args[0])?, u8_ty)?)),
            "free" => {
                if let Some(id) = self.block_start(&args[0], "free")? {
                    let block = &mut self.heap[id];
                    block.freed = true;
                    block.slots = Value::Array(Vec::new());
                }
                Ok(Some(Value::Void))
            }
            "realloc" => {
                let new_bytes = bytes(&args[1])?;
                let Some(id) = self.block_start(&args[0], "realloc")? else {
                    return Ok(Some(self.allocate(new_bytes, u8_ty)?));
                };
                // A reallocation always moves, so pointers into the old block are caught.
                let elem = self.heap[id].elem;
                let new_ptr = self.allocate(new_bytes, elem)?;
                let old = std::mem::replace(&mut self.heap[id].slots, Value::Array(Vec::new()));
                self.heap[id].freed = true;
                let new_id = self.heap.len() - 1;
                if let (Value::Array(old), Value::Array(new)) = (old, &mut self.heap[new_id].slots) {
                    for (dst, src) in new.iter_mut().zip(old) {
                        *dst = src;
                    }
                }
                Ok(Some(new_ptr))
            }
            _ => Ok(None),
        }
    }

    /// The integer address of pointer `ptr`, the same each time it is exposed.
    fn expose(&mut self, ptr: Value) -> i128 {
        let located = match &ptr {
            Value::Ptr {
                target,
                projections,
                ..
            } => self.byte_offset(target, projections).map(|off| (target.clone(), off)),
            _ => None,
        };
        // Pointers into one allocation share a base, so address differences are real ones.
        let existing = self.exposed.iter().position(|p| match (p, &located) {
            (Value::Ptr { target, .. }, Some((t, _))) => target == t,
            _ => *p == ptr,
        });
        let idx = existing.unwrap_or_else(|| {
            self.exposed.push(ptr.clone());
            self.exposed.len() - 1
        });
        let addr = EXPOSED_BASE + idx as i128 * EXPOSED_STRIDE + located.map_or(0, |(_, off)| off);
        self.exposed_at.insert(addr, ptr);
        addr
    }

    /// The type of the whole allocation `target` names, for a local or global.
    fn root_type(&self, target: &PtrTarget) -> Option<TypeId> {
        match target {
            PtrTarget::Local { frame, local, .. } => {
                let frame = self.frame_at(*frame)?;
                self.fn_cache.get(&frame.func_id)?.locals.get(local.0 as usize).copied()
            }
            _ => None,
        }
    }

    /// The bytes from the start of `target` to `projs`, if its layout is known.
    fn byte_offset(&self, target: &PtrTarget, projs: &[ResolvedProj]) -> Option<i128> {
        let (mut ty, rest, mut off) = match (target, projs) {
            (PtrTarget::Heap(id), [ResolvedProj::Index(i), rest @ ..]) => {
                let elem = self.heap.get(*id)?.elem;
                let (size, _) = self.program.type_size_align(elem).ok()?;
                (elem, rest, *i as i128 * size as i128)
            }
            _ => (self.root_type(target)?, projs, 0),
        };
        for proj in rest {
            match (self.program.types.get(ty.0 as usize)?, proj) {
                (Type::Struct(fields), ResolvedProj::Field(i)) => {
                    off += *self.field_offsets(fields).ok()?.get(*i as usize)? as i128;
                    ty = *fields.get(*i as usize)?;
                }
                (&Type::Array { elem, .. } | &Type::Simd { elem, .. }, ResolvedProj::Index(i)) => {
                    off += *i as i128 * self.program.type_size_align(elem).ok()?.0 as i128;
                    ty = elem;
                }
                (Type::Union { tag, variants }, ResolvedProj::Variant(v)) => {
                    if self.program.union_niche(ty).is_none() {
                        off += self.union_payload_offset(*tag, variants).ok()? as i128;
                    }
                    ty = *variants.get(*v as usize)?;
                }
                _ => return None,
            }
        }
        Some(off)
    }

    /// The projections reaching a `pointee` at `off` bytes into a value of type `ty`.
    fn path_to(&self, mut ty: TypeId, mut off: i128, pointee: TypeId, path: &mut Vec<ResolvedProj>) -> Option<()> {
        // A slice's data pointer, of type `[T; 0]`, reaches element 0.
        let wanted = match self.program.types.get(pointee.0 as usize) {
            Some(&Type::Array { elem, len: 0 }) => elem,
            _ => pointee,
        };
        loop {
            if ty == wanted && off == 0 {
                return Some(());
            }
            match self.program.types.get(ty.0 as usize)? {
                Type::Struct(fields) => {
                    let offsets = self.field_offsets(fields).ok()?;
                    let i = (0..fields.len()).rev().find(|&i| offsets[i] as i128 <= off)?;
                    path.push(ResolvedProj::Field(i as u32));
                    off -= offsets[i] as i128;
                    ty = fields[i];
                }
                &Type::Array { elem, len } => {
                    let (size, _) = self.program.type_size_align(elem).ok()?;
                    let i = off / (size.max(1) as i128);
                    if i >= len as i128 {
                        return None;
                    }
                    path.push(ResolvedProj::Index(i as usize));
                    off -= i * size as i128;
                    ty = elem;
                }
                _ => return None,
            }
        }
    }

    /// The pointer at an address: the `pointee` at that many bytes into an exposed allocation
    /// (a struct and its first field share an address, so the type decides), or one exposed
    /// there, or a slot of it (as `buf as usize + len` computes).
    fn unexpose(&self, addr: i128, pointee: TypeId) -> Option<Value> {
        let off = addr.checked_sub(EXPOSED_BASE)?;
        if off < 0 {
            return None;
        }
        let base = self.exposed.get((off / EXPOSED_STRIDE) as usize)?;
        let delta = off % EXPOSED_STRIDE;
        let Value::Ptr {
            target,
            projections,
            ..
        } = base
        else {
            return None;
        };
        let root = match target {
            PtrTarget::Heap(id) => {
                let elem = self.heap.get(*id)?.elem;
                let (size, _) = self.program.type_size_align(elem).ok()?;
                let size = size.max(1) as i128;
                Some((elem, delta % size, vec![ResolvedProj::Index((delta / size) as usize)]))
            }
            _ => self.root_type(target).map(|ty| (ty, delta, Vec::new())),
        };
        if let Some((ty, within, mut path)) = root
            && self.path_to(ty, within, pointee, &mut path).is_some()
        {
            return Some(Value::Ptr {
                target: target.clone(),
                projections: path,
                tag: Tag::default(),
            });
        }
        if let Some(exact) = self.exposed_at.get(&addr) {
            return Some(exact.clone());
        }
        let delta = delta - self.byte_offset(target, projections).unwrap_or(0);
        let (size, _) = self.program.type_size_align(pointee).ok()?;
        if size == 0 || delta < 0 || delta % size as i128 != 0 {
            return None;
        }
        Self::offset_ptr(base, (delta / size as i128) as usize).ok()
    }

    /// Uninitialized storage of type `ty`, shaped like it (arrays of slots, struct fields,
    /// overlays), so code can address its parts before writing them.
    fn uninit_shape(&self, ty: TypeId) -> Value {
        match self.program.types.get(ty.0 as usize) {
            Some(&Type::Array { elem, len } | &Type::Simd { elem, len }) => {
                Value::Array(vec![self.uninit_shape(elem); len as usize])
            }
            Some(Type::Struct(fields)) => Value::Struct {
                ty,
                fields: fields.clone().into_iter().map(|f| self.uninit_shape(f)).collect(),
            },
            Some(Type::Overlay(_)) => Value::Overlay {
                ty,
                active_field: None,
                val: Box::new(Value::Uninit),
            },
            _ => Value::Uninit,
        }
    }

    /// Whether `v` holds nothing written yet.
    fn is_uninit_shape(v: &Value) -> bool {
        match v {
            Value::Uninit => true,
            Value::Array(vs) => vs.iter().all(Self::is_uninit_shape),
            Value::Struct { fields, .. } => fields.iter().all(Self::is_uninit_shape),
            Value::Overlay {
                active_field: None,
                ..
            } => true,
            _ => false,
        }
    }

    /// `ptr + i` for a pointer into a sequence of slots (an array or heap block).
    fn offset_ptr(ptr: &Value, i: usize) -> Result<Value, String> {
        let Value::Ptr {
            target,
            projections,
            ..
        } = ptr
        else {
            return Err(format!("Expected a pointer, found {ptr:?}"));
        };
        if i == 0 {
            return Ok(ptr.clone());
        }
        let mut projections = projections.clone();
        let Some(ResolvedProj::Index(idx)) = projections.last_mut() else {
            return Err(format!(
                "{UB_PREFIX}access {i} slots past a pointer to a single value"
            ));
        };
        *idx += i;
        Ok(Value::Ptr {
            target: target.clone(),
            projections,
            tag: Tag::default(),
        })
    }

    /// Writes `val` through pointer `ptr`.
    fn write_through(&mut self, ptr: &Value, val: Value) -> Result<(), String> {
        let Value::Ptr {
            target,
            projections,
            ..
        } = ptr
        else {
            return Err(format!("Expected a pointer, found {ptr:?}"));
        };
        self.write_resolved(target, projections, val)
    }

    /// `@memcpy` / `@memmove(dest, src, count)`: copies `count` slots, reading all of the source
    /// first so overlapping moves are exact. Uninitialized slots copy as uninitialized.
    fn copy_slots(&mut self, args: &[Value]) -> Result<(), String> {
        let Value::Int(count) = args[2] else {
            return Err(format!("Copy count must be an integer, found {:?}", args[2]));
        };
        let mut vals = Vec::with_capacity(count as usize);
        for i in 0..count as usize {
            let Value::Ptr {
                target,
                projections,
                ..
            } = Self::offset_ptr(&args[1], i)?
            else {
                unreachable!()
            };
            vals.push(self.read_resolved_raw(&target, &projections)?);
        }
        for (i, v) in vals.into_iter().enumerate() {
            let dest = Self::offset_ptr(&args[0], i)?;
            self.write_through(&dest, v)?;
        }
        Ok(())
    }

    /// Whether `fd`, one of the emulated pipes, is ready. The VM never blocks in one: a wait is a
    /// loop of `poll` in std, which the step limit ends if nothing comes.
    fn fd_ready(&self, fd: i32, events: i128) -> bool {
        if let Some(listener) = self.sched.listeners.get(&fd) {
            return !listener.pending.is_empty();
        }
        let Some(&Ends { read, write }) = self.sched.fds.get(&fd) else {
            return false;
        };
        let readable = read.is_some_and(|p| !self.has_writer(p) || !self.sched.pipes[p].is_empty());
        let writable =
            write.is_some_and(|p| !self.has_reader(p) || self.sched.pipes[p].len() < PIPE_CAPACITY);
        (events & EVENT_IN != 0 && readable) || (events & EVENT_OUT != 0 && writable)
    }

    fn has_reader(&self, pipe: usize) -> bool {
        self.sched.fds.values().any(|e| e.read == Some(pipe))
    }

    fn has_writer(&self, pipe: usize) -> bool {
        self.sched.fds.values().any(|e| e.write == Some(pipe))
    }

    /// `poll(list, count, timeout_ms)`. If nothing is ready, the timeout passes in virtual time and
    /// other threads get a turn.
    fn emulate_poll(&mut self, args: &[Value]) -> Result<i128, String> {
        let (Value::Ptr { target, projections, .. }, Value::Int(count), Value::Int(timeout)) =
            (&args[0], &args[1], &args[2])
        else {
            return Err(format!("Unexpected arguments to poll: {args:?}"));
        };
        let base = projections.split_last().map_or(0, |(last, _)| match last {
            ResolvedProj::Index(i) => *i,
            _ => 0,
        });
        let prefix = match projections.last() {
            Some(ResolvedProj::Index(_)) => &projections[..projections.len() - 1],
            _ => &projections[..],
        };
        let is_array = matches!(projections.last(), Some(ResolvedProj::Index(_)));
        let mut ready = 0;
        for i in 0..*count as usize {
            let mut at = prefix.to_vec();
            if is_array {
                at.push(ResolvedProj::Index(base + i));
            }
            let mut fd_at = at.clone();
            fd_at.push(ResolvedProj::Field(0));
            let Value::Int(fd) = self.read_resolved(target, &fd_at)? else {
                return Err("poll: a descriptor is not an integer".to_string());
            };
            let mut events_at = at.clone();
            events_at.push(ResolvedProj::Field(1));
            let Value::Int(events) = self.read_resolved(target, &events_at)? else {
                return Err("poll: an event mask is not an integer".to_string());
            };
            let mut revents_at = at;
            revents_at.push(ResolvedProj::Field(2));
            let is_ready = self.fd_ready(fd as i32, events);
            ready += is_ready as i128;
            self.write_resolved(target, &revents_at, Value::Int(is_ready as i128))?;
        }
        if ready == 0 && *timeout > 0 {
            self.sched.clock_ns += *timeout as u64 * 1_000_000;
            self.sched.yield_after = true;
        }
        Ok(ready)
    }

    /// `epoll_ctl(epoll, op, fd, event)`, adding or removing a watch. As in Linux, a descriptor can
    /// be added once, and one that is not a pipe, like a regular file, cannot be.
    fn emulate_epoll_ctl(&mut self, args: &[Value]) -> Result<i128, String> {
        let (Value::Int(epoll), Value::Int(op), Value::Int(fd)) = (&args[0], &args[1], &args[2]) else {
            return Err(format!("Unexpected arguments to epoll_ctl: {args:?}"));
        };
        let (epoll, fd) = (*epoll as i32, *fd as i32);
        if *op == 2 {
            self.sched.epolls.get_mut(&epoll).ok_or("epoll_ctl: not an epoll")?.retain(|w| w.0 != fd);
            return Ok(0);
        }
        if !self.sched.fds.contains_key(&fd) {
            return self.fail_io(1);
        }
        let present = self.sched.epolls[&epoll].iter().any(|w| w.0 == fd);
        if present && *op == 1 {
            return self.fail_io(17);
        }
        if !present && *op == 3 {
            return self.fail_io(2);
        }
        let mut event = [0; 3];
        for (i, word) in event.iter_mut().enumerate() {
            let Value::Ptr { target, projections, .. } = Self::pointer_plus(&args[3], i)? else {
                return Err("epoll_ctl: expected a pointer".to_string());
            };
            let Value::Int(value) = self.read_resolved(&target, &projections)? else {
                return Err("epoll_ctl: expected an event".to_string());
            };
            *word = value;
        }
        let watches = self.sched.epolls.get_mut(&epoll).ok_or("epoll_ctl: not an epoll")?;
        watches.retain(|w| w.0 != fd);
        watches.push((fd, event, false));
        Ok(0)
    }

    /// `epoll_wait(epoll, events, max, timeout_ms)`, for watches that fire once. If nothing is
    /// ready, the timeout passes in virtual time and other threads get a turn.
    fn emulate_epoll_wait(&mut self, args: &[Value]) -> Result<i128, String> {
        let (Value::Int(epoll), Value::Int(max), Value::Int(timeout)) = (&args[0], &args[2], &args[3]) else {
            return Err(format!("Unexpected arguments to epoll_wait: {args:?}"));
        };
        let epoll = *epoll as i32;
        let mut ready = Vec::new();
        let watches = self.sched.epolls.get(&epoll).ok_or("epoll_wait: not an epoll")?;
        for (i, (fd, event, fired)) in watches.iter().enumerate() {
            if !fired && self.fd_ready(*fd, event[0]) && ready.len() < *max as usize {
                ready.push((i, *event));
            }
        }
        for (n, (i, event)) in ready.iter().enumerate() {
            // Only a watch asked to fire once stops.
            let once = event[0] & (1 << 30) != 0;
            self.sched.epolls.get_mut(&epoll).expect("found above")[*i].2 = once;
            for (word, value) in event.iter().enumerate() {
                let at = Self::pointer_plus(&args[1], n * 3 + word)?;
                self.write_through(&at, Value::Int(*value))?;
            }
        }
        if ready.is_empty() && *timeout > 0 {
            self.sched.clock_ns += *timeout as u64 * 1_000_000;
            self.sched.yield_after = true;
        }
        Ok(ready.len() as i128)
    }

    fn new_fd(&mut self) -> i32 {
        let fd = self.sched.next_fd + 3;
        self.sched.next_fd += 1;
        fd
    }

    /// The field of a `sockaddr_in` at `address` that holds the port.
    fn port_field(address: &Value) -> Result<Value, String> {
        let Value::Ptr { target, projections, tag } = address else {
            return Err(format!("Expected an address, found {address:?}"));
        };
        let mut projections = projections.clone();
        projections.push(ResolvedProj::Field(1));
        Ok(Value::Ptr { target: target.clone(), projections, tag: *tag })
    }

    /// The port a `sockaddr_in` at `address` names, which it keeps in network order.
    fn read_port(&self, address: &Value) -> Result<u16, String> {
        let Value::Ptr { target, projections, .. } = Self::port_field(address)? else {
            unreachable!("port_field makes a pointer");
        };
        let Value::Int(port) = self.read_resolved(&target, &projections)? else {
            return Err("sockaddr_in: expected a port".to_string());
        };
        Ok((port as u16).swap_bytes())
    }

    /// `bind(fd, address, len)`. Port 0 picks one nothing else has.
    fn emulate_bind(&mut self, args: &[Value]) -> Result<(), String> {
        let Value::Int(fd) = args[0] else {
            return Err(format!("Unexpected arguments to bind: {args:?}"));
        };
        let mut port = self.read_port(&args[1])?;
        if port == 0 {
            self.sched.next_port += 1;
            port = 49152 + self.sched.next_port;
        }
        self.sched.listeners.insert(fd as i32, Listener { port, ..Listener::default() });
        Ok(())
    }

    fn emulate_getsockname(&mut self, args: &[Value]) -> Result<(), String> {
        let Value::Int(fd) = args[0] else {
            return Err(format!("Unexpected arguments to getsockname: {args:?}"));
        };
        let port = self.sched.listeners.get(&(fd as i32)).map_or(0, |l| l.port);
        self.write_through(&Self::port_field(&args[1])?, Value::Int(port.swap_bytes() as i128))
    }

    /// `connect(fd, address, len)`: a pipe each way, and the other end waits for `accept`.
    fn emulate_connect(&mut self, args: &[Value]) -> Result<i128, String> {
        let Value::Int(fd) = args[0] else {
            return Err(format!("Unexpected arguments to connect: {args:?}"));
        };
        let port = self.read_port(&args[1])?;
        if !self.sched.listeners.values().any(|l| l.port == port) {
            return self.fail_io(111);
        }
        let there = self.sched.pipes.len();
        let back = there + 1;
        self.sched.pipes.push(std::collections::VecDeque::new());
        self.sched.pipes.push(std::collections::VecDeque::new());
        self.sched.fds.insert(fd as i32, Ends { read: Some(back), write: Some(there) });
        let accepted = self.new_fd();
        self.sched.fds.insert(accepted, Ends { read: Some(there), write: Some(back) });
        let listener = self.sched.listeners.values_mut().find(|l| l.port == port);
        listener.expect("checked above").pending.push_back(accepted);
        Ok(0)
    }

    fn emulate_accept(&mut self, args: &[Value]) -> Result<i128, String> {
        let Value::Int(fd) = args[0] else {
            return Err(format!("Unexpected arguments to accept: {args:?}"));
        };
        let listener = self.sched.listeners.get_mut(&(fd as i32)).ok_or("accept: not listening")?;
        match listener.pending.pop_front() {
            Some(accepted) => Ok(accepted as i128),
            None => self.fail_io(11),
        }
    }

    /// The C string at `ptr`.
    fn read_c_string(&self, ptr: &Value) -> Result<String, String> {
        let mut bytes = Vec::new();
        loop {
            let byte = self.read_bytes(&Self::pointer_plus(ptr, bytes.len())?, 1)?[0];
            if byte == 0 {
                return Ok(String::from_utf8_lossy(&bytes).into_owned());
            }
            bytes.push(byte);
        }
    }

    /// `fopen(path, mode)`, as the `?*mut u8` std declares: "wb" replaces a file, "rb" fails
    /// without one.
    fn emulate_fopen(&mut self, args: &[Value]) -> Result<Value, String> {
        let path = self.read_c_string(&args[0])?;
        let writing = self.read_bytes(&args[1], 1)?[0] == b'w';
        let ret = self.program.externs.iter().find(|e| e.symbol == "fopen").ok_or("no fopen")?.ret;
        if !writing && !self.sched.files.contains_key(&path) {
            return Ok(Value::Union { ty: ret, variant: 0, payload: Box::new(Value::Void) });
        }
        if writing {
            self.sched.files.insert(path.clone(), Vec::new());
        }
        let u8_ty = self.program.intern_type(Type::Int { signed: false, bits: 8 });
        let file = self.allocate(1, u8_ty)?;
        let id = self.block_start(&file, "fopen")?.expect("just allocated");
        self.sched.open_files.insert(id, OpenFile { path, at: 0 });
        Ok(Value::Union { ty: ret, variant: 1, payload: Box::new(file) })
    }

    fn emulate_fread(&mut self, args: &[Value]) -> Result<i128, String> {
        let (Value::Int(size), Value::Int(count)) = (&args[1], &args[2]) else {
            return Err(format!("Unexpected arguments to fread: {args:?}"));
        };
        let id = self.block_start(&args[3], "fread")?.ok_or("fread of null")?;
        let file = self.sched.open_files.get_mut(&id).ok_or("fread: not an open file")?;
        let contents = &self.sched.files[&file.path];
        let n = ((size * count) as usize).min(contents.len() - file.at);
        let bytes = contents[file.at..file.at + n].to_vec();
        file.at += n;
        for (i, byte) in bytes.into_iter().enumerate() {
            self.write_through(&Self::pointer_plus(&args[0], i)?, Value::Int(byte as i128))?;
        }
        Ok(n as i128 / size)
    }

    fn emulate_fwrite(&mut self, args: &[Value]) -> Result<i128, String> {
        let (Value::Int(size), Value::Int(count)) = (&args[1], &args[2]) else {
            return Err(format!("Unexpected arguments to fwrite: {args:?}"));
        };
        let bytes = self.read_bytes(&args[0], (size * count) as usize)?;
        let id = self.block_start(&args[3], "fwrite")?.ok_or("fwrite of null")?;
        let file = self.sched.open_files.get(&id).ok_or("fwrite: not an open file")?;
        let path = file.path.clone();
        self.sched.files.get_mut(&path).expect("open files exist").extend(bytes);
        Ok(*count)
    }

    /// `read(fd, buf, len)`, of the bytes a pipe has. `None` for a descriptor that is not a pipe.
    fn emulate_read(&mut self, args: &[Value]) -> Result<Option<i128>, String> {
        let (Value::Int(fd), Value::Int(len)) = (&args[0], &args[2]) else {
            return Err(format!("Unexpected arguments to read: {args:?}"));
        };
        let Some(pipe) = self.sched.fds.get(&(*fd as i32)).and_then(|e| e.read) else {
            return Ok(None);
        };
        if self.interrupted_now() {
            return self.fail_io(4).map(Some);
        }
        let open = self.has_writer(pipe);
        if self.sched.pipes[pipe].is_empty() && open {
            return self.fail_io(11).map(Some);
        }
        let n = (*len as usize).min(self.sched.pipes[pipe].len());
        for i in 0..n {
            let byte = self.sched.pipes[pipe].pop_front().expect("counted above");
            let at = Self::pointer_plus(&args[1], i)?;
            self.write_through(&at, Value::Int(byte as i128))?;
        }
        Ok(Some(n as i128))
    }

    /// `write(fd, buf, len)` to a pipe, up to what it has room for. `None` for anything else.
    fn emulate_write(&mut self, args: &[Value]) -> Result<Option<i128>, String> {
        let (Value::Int(fd), Value::Int(len)) = (&args[0], &args[2]) else {
            return Err(format!("Unexpected arguments to write: {args:?}"));
        };
        if matches!(*fd, 1 | 2) && self.sched.output.is_some() {
            let bytes = self.read_bytes(&args[1], *len as usize)?;
            self.sched.output.as_mut().expect("just checked").extend(bytes);
            return Ok(Some(*len));
        }
        let Some(pipe) = self.sched.fds.get(&(*fd as i32)).and_then(|e| e.write) else {
            return Ok(None);
        };
        if self.interrupted_now() {
            return self.fail_io(4).map(Some);
        }
        if !self.has_reader(pipe) {
            return self.fail_io(32).map(Some);
        }
        let room = PIPE_CAPACITY - self.sched.pipes[pipe].len().min(PIPE_CAPACITY);
        if room == 0 {
            return self.fail_io(11).map(Some);
        }
        let n = (*len as usize).min(room);
        let bytes = self.read_bytes(&args[1], n)?;
        self.sched.pipes[pipe].extend(bytes);
        Ok(Some(n as i128))
    }

    /// The `n` bytes at `ptr`.
    fn read_bytes(&self, ptr: &Value, n: usize) -> Result<Vec<u8>, String> {
        if let Value::Str(s) = ptr {
            return Ok(s.as_bytes()[..n].to_vec());
        }
        let mut bytes = Vec::with_capacity(n);
        for i in 0..n {
            let Value::Ptr { target, projections, .. } = Self::pointer_plus(ptr, i)? else {
                return Err(format!("write: expected a pointer, found {ptr:?}"));
            };
            let Value::Int(byte) = self.read_resolved(&target, &projections)? else {
                return Err("write: expected bytes".to_string());
            };
            bytes.push(byte as u8);
        }
        Ok(bytes)
    }

    /// Whether this read or write is one `set_interrupt_io` fails.
    fn interrupted_now(&mut self) -> bool {
        self.sched.interrupted = self.sched.interrupt_io && !self.sched.interrupted;
        self.sched.interrupted
    }

    /// The running thread's `errno`.
    fn errno_block(&mut self) -> Result<Value, String> {
        let thread = self.sched.os_thread(self.sched.running);
        if let Some(block) = self.sched.errno.get(&thread) {
            return Ok(block.clone());
        }
        let i32_ty = self.program.intern_type(Type::Int { signed: true, bits: 32 });
        let block = self.allocate(4, i32_ty)?;
        self.write_through(&block, Value::Int(0))?;
        self.sched.errno.insert(thread, block.clone());
        Ok(block)
    }

    /// Sets `errno` and yields the -1 of a failed call.
    fn fail_io(&mut self, errno: i128) -> Result<i128, String> {
        let block = self.errno_block()?;
        self.write_through(&block, Value::Int(errno))?;
        Ok(-1)
    }

    /// `ptr + offset`, for a pointer into an array or heap block.
    fn pointer_plus(ptr: &Value, offset: usize) -> Result<Value, String> {
        if offset == 0 {
            return Ok(ptr.clone());
        }
        let mut moved = ptr.clone();
        let Value::Ptr { projections, .. } = &mut moved else {
            return Err(format!("Expected a pointer, found {ptr:?}"));
        };
        match projections.last_mut() {
            Some(ResolvedProj::Index(i)) => *i += offset,
            _ => return Err("Expected a pointer into an array".to_string()),
        }
        Ok(moved)
    }

    /// Emulates the pthread functions std uses over the VM's threads (see `Scheduler`). `None`
    /// if `symbol` is not one of them.
    fn call_pthread(&mut self, symbol: &str, args: &[Value]) -> Result<Option<Pthread>, String> {
        let ok = Some(Pthread::Done(Value::Int(0)));
        let sync_key = |arg: &Value| match arg {
            Value::Ptr {
                target,
                projections,
                ..
            } => Ok(slot_key(target, projections)),
            other => Err(format!("Expected a pointer to a sync object, found {other:?}")),
        };
        match symbol {
            "pthread_create" => {
                self.threads.push(None);
                self.write_through(&args[0], Value::Int(self.threads.len() as i128 - 1))?;
                Ok(ok)
            }
            "pthread_join" => {
                let Value::Int(id) = args[0] else {
                    return Err(format!("Thread id must be an integer, found {:?}", args[0]));
                };
                let id = id as usize;
                let finished = self.sched.done.get(id + 1).copied();
                if finished == Some(false) {
                    return Ok(Some(Pthread::Block(Wait::Join(id + 1))));
                }
                let result = self
                    .threads
                    .get_mut(id)
                    .and_then(Option::take)
                    .ok_or_else(|| format!("{UB_PREFIX}join of thread {id}, which is unknown or already joined"))?;
                // Everything the thread did happens before the join returns.
                if let Some(race) = self.race.get_mut().as_mut()
                    && let Some(Some(done)) = race.finished.get(id + 1).cloned()
                {
                    join_clock(&mut race.clocks[race.current], &done);
                    race.tick();
                }
                if matches!(args[1], Value::Ptr { .. }) {
                    self.write_through(&args[1], result)?;
                }
                Ok(ok)
            }
            "pthread_mutex_lock" => {
                let key = sync_key(&args[0])?;
                if self.sched.held.contains_key(&key) {
                    return Ok(Some(Pthread::Block(Wait::Mutex(key))));
                }
                self.sched.held.insert(key.clone(), self.sched.running);
                if let Some(race) = self.race.get_mut().as_mut() {
                    race.acquire(&key);
                }
                Ok(ok)
            }
            "pthread_mutex_trylock" => {
                let key = sync_key(&args[0])?;
                if self.sched.held.contains_key(&key) {
                    return Ok(Some(Pthread::Done(Value::Int(16))));
                }
                self.sched.held.insert(key.clone(), self.sched.running);
                if let Some(race) = self.race.get_mut().as_mut() {
                    race.acquire(&key);
                }
                Ok(ok)
            }
            "pthread_mutex_unlock" => {
                self.unlock(sync_key(&args[0])?);
                Ok(ok)
            }
            "signal" => Ok(ok),
            "__errno_location" => self.errno_block().map(|b| Some(Pthread::Done(b))),
            "socket" | "setsockopt" | "getsockopt" | "bind" | "listen" | "connect" | "getsockname"
            | "accept4" | "fopen" | "fread" | "fwrite" | "fclose"
                if self.sched.output.is_none() =>
            {
                Ok(None)
            }
            "socket" => {
                let fd = self.new_fd();
                self.sched.fds.insert(fd, Ends::default());
                Ok(Some(Pthread::Done(Value::Int(fd as i128))))
            }
            "setsockopt" | "listen" => Ok(ok),
            "getsockopt" => {
                self.write_through(&args[3], Value::Int(0))?;
                Ok(ok)
            }
            "bind" => self.emulate_bind(args).map(|()| ok),
            "connect" => self.emulate_connect(args).map(|n| Some(Pthread::Done(Value::Int(n)))),
            "getsockname" => self.emulate_getsockname(args).map(|()| ok),
            "accept4" => self.emulate_accept(args).map(|n| Some(Pthread::Done(Value::Int(n)))),
            "fopen" => self.emulate_fopen(args).map(|f| Some(Pthread::Done(f))),
            "fread" => self.emulate_fread(args).map(|n| Some(Pthread::Done(Value::Int(n)))),
            "fwrite" => self.emulate_fwrite(args).map(|n| Some(Pthread::Done(Value::Int(n)))),
            "fclose" => {
                let id = self.block_start(&args[0], "fclose")?.ok_or("fclose of null")?;
                self.sched.open_files.remove(&id);
                let _ = self.call_allocator("free", &args[..1])?;
                Ok(ok)
            }
            // Pipes are in memory.
            "pipe" => {
                let id = self.sched.pipes.len();
                self.sched.pipes.push(std::collections::VecDeque::new());
                let reader = self.sched.next_fd + 3;
                self.sched.next_fd += 2;
                self.sched.fds.insert(reader, Ends { read: Some(id), write: None });
                self.sched.fds.insert(reader + 1, Ends { read: None, write: Some(id) });
                let ends = vec![Value::Int(reader as i128), Value::Int(reader as i128 + 1)];
                self.write_through(&args[0], Value::Array(ends))?;
                Ok(ok)
            }
            "close" => {
                let Value::Int(fd) = args[0] else {
                    return Err(format!("close takes a descriptor, found {:?}", args[0]));
                };
                if self.sched.epolls.remove(&(fd as i32)).is_some() {
                    return Ok(ok);
                }
                if let Some(listener) = self.sched.listeners.remove(&(fd as i32)) {
                    for pending in listener.pending {
                        self.sched.fds.remove(&pending);
                    }
                }
                if self.sched.fds.remove(&(fd as i32)).is_none() {
                    return Err(format!("{UB_PREFIX}close of descriptor {fd}, which is not open"));
                }
                Ok(ok)
            }
            "epoll_create1" => {
                let fd = self.new_fd();
                self.sched.epolls.insert(fd, Vec::new());
                Ok(Some(Pthread::Done(Value::Int(fd as i128))))
            }
            "fcntl" => Ok(ok),
            "epoll_ctl" => self.emulate_epoll_ctl(args).map(|r| Some(Pthread::Done(Value::Int(r)))),
            "epoll_wait" => self.emulate_epoll_wait(args).map(|n| Some(Pthread::Done(Value::Int(n)))),
            "poll" => self.emulate_poll(args).map(|ready| Some(Pthread::Done(Value::Int(ready)))),
            "read" => self.emulate_read(args).map(|n| n.map(|n| Pthread::Done(Value::Int(n)))),
            "write" => self.emulate_write(args).map(|n| n.map(|n| Pthread::Done(Value::Int(n)))),
            // A fiber is a thread that runs only when switched to, on a stack the VM provides.
            "getcontext" | "mprotect" => Ok(ok),
            "makecontext" => {
                self.threads.push(None);
                let child = self.threads.len();
                let creator = self.sched.running;
                let home = self.sched.os_thread(creator);
                self.start_thread(&[Value::Void, Value::Void, args[1].clone(), Value::Int(0)])?;
                self.switch_to(creator);
                self.sched.parked.insert(child);
                self.sched.fiber_home.insert(child, home);
                self.sched.contexts.insert(sync_key(&args[0])?, child);
                Ok(ok)
            }
            "swapcontext" => {
                let (from, to) = (sync_key(&args[0])?, sync_key(&args[1])?);
                let Some(&target) = self.sched.contexts.get(&to) else {
                    return Err("swapcontext to a context nothing saved".to_string());
                };
                let running = self.sched.running;
                self.sched.contexts.insert(from, running);
                self.sched.parked.insert(running);
                self.sched.parked.remove(&target);
                if let Some(race) = self.race.get_mut().as_mut() {
                    race.release(to.clone());
                }
                self.sched.pending_switch = Some((target, to));
                Ok(ok)
            }
            // Fiber stacks are most of what is mapped, and the VM runs fibers on frames of its
            // own, so a mapping has no slots until a cast says what they hold: at the size of
            // a `Value` each, a 1 MB stack would take 64 MB.
            "mmap" => {
                let Value::Int(bytes) = args[1] else {
                    return Err(format!("Unexpected arguments to mmap: {args:?}"));
                };
                let u8_ty = self.program.intern_type(Type::Int { signed: false, bits: 8 });
                self.heap.push(HeapBlock {
                    bytes: bytes as u64,
                    elem: u8_ty,
                    slots: Value::Array(Vec::new()),
                    freed: false,
                });
                Ok(Some(Pthread::Done(Value::Ptr {
                    target: PtrTarget::Heap(self.heap.len() - 1),
                    projections: vec![ResolvedProj::Index(0)],
                    tag: Tag::default(),
                })))
            }
            "munmap" => {
                let _ = self.call_allocator("free", &args[..1])?;
                Ok(ok)
            }
            // A bounded wait: give others a turn, then report a timeout. Its caller rechecks.
            "pthread_cond_timedwait" => {
                let mutex = sync_key(&args[1])?;
                let thread = self.sched.running;
                if self.sched.cond[thread] == CondWait::None {
                    self.unlock(mutex.clone());
                    self.sched.cond[thread] = CondWait::Woken;
                    return Ok(Some(Pthread::Block(Wait::Mutex(mutex))));
                }
                if self.sched.held.contains_key(&mutex) {
                    return Ok(Some(Pthread::Block(Wait::Mutex(mutex))));
                }
                self.sched.cond[thread] = CondWait::None;
                self.sched.held.insert(mutex.clone(), thread);
                if let Some(race) = self.race.get_mut().as_mut() {
                    race.acquire(&mutex);
                }
                self.sched.clock_ns += 1_000_000;
                Ok(Some(Pthread::Done(Value::Int(110))))
            }
            // Virtual time, so timeouts are deterministic: it passes only through waiting.
            "clock_gettime" => {
                let ns = self.sched.clock_ns as i128;
                let now = Value::Array(vec![Value::Int(ns / 1_000_000_000), Value::Int(ns % 1_000_000_000)]);
                self.write_through(&args[1], now)?;
                Ok(ok)
            }
            "usleep" => {
                let Value::Int(us) = args[0] else {
                    return Err(format!("usleep takes an integer, found {:?}", args[0]));
                };
                self.sched.clock_ns += us as u64 * 1000;
                Ok(ok)
            }
            "pthread_cond_wait" => {
                let (cond, mutex) = (sync_key(&args[0])?, sync_key(&args[1])?);
                let thread = self.sched.running;
                match self.sched.cond[thread] {
                    CondWait::None => {
                        self.unlock(mutex);
                        self.sched.cond[thread] = CondWait::Waiting;
                        self.sched.cond_waiters.entry(cond).or_default().push(thread);
                        Ok(Some(Pthread::Block(Wait::Cond)))
                    }
                    CondWait::Waiting => Ok(Some(Pthread::Block(Wait::Cond))),
                    // Woken: the mutex is taken back before the wait returns.
                    CondWait::Woken => {
                        if self.sched.held.contains_key(&mutex) {
                            return Ok(Some(Pthread::Block(Wait::Mutex(mutex))));
                        }
                        self.sched.cond[thread] = CondWait::None;
                        self.sched.held.insert(mutex.clone(), thread);
                        if let Some(race) = self.race.get_mut().as_mut() {
                            race.acquire(&mutex);
                        }
                        Ok(ok)
                    }
                }
            }
            "pthread_cond_signal" | "pthread_cond_broadcast" => {
                let waiters = self.sched.cond_waiters.entry(sync_key(&args[0])?).or_default();
                let count = if symbol == "pthread_cond_signal" { waiters.len().min(1) } else { waiters.len() };
                let woken: Vec<usize> = waiters.drain(..count).collect();
                for thread in woken {
                    self.sched.cond[thread] = CondWait::Woken;
                }
                Ok(ok)
            }
            "pthread_detach" | "pthread_mutex_init" | "pthread_mutex_destroy" | "pthread_cond_init"
            | "pthread_cond_destroy" => Ok(ok),
            _ => Ok(None),
        }
    }

    /// Unlocking releases the holder's accesses to the next locker.
    fn unlock(&mut self, key: SlotKey) {
        self.sched.held.remove(&key);
        if let Some(race) = self.race.get_mut().as_mut() {
            race.release(key);
        }
    }

    /// Starts the thread `pthread_create(tid, attr, entry, arg)` just registered, on a new stack
    /// holding a frame for `entry(arg)` whose return records the thread's result.
    fn start_thread(&mut self, args: &[Value]) -> Result<(), String> {
        let Value::Func(entry) = args[2] else {
            return Err(format!("Thread entry must be a function, found {:?}", args[2]));
        };
        let func = self.get_function(entry)?;
        let mut locals = vec![Value::Uninit; func.locals.len()];
        if func.arg_count == 1 {
            locals[1] = args[3].clone();
        }
        // The new thread starts after everything its creator did so far.
        let pthread = self.threads.len() - 1;
        let child = pthread + 1;
        let race = self.race.get_mut().get_or_insert_with(|| RaceState {
            clocks: vec![vec![1]],
            finished: vec![None],
            ..RaceState::default()
        });
        if race.clocks.len() <= child {
            race.clocks.resize(child + 1, Vec::new());
            race.finished.resize(child + 1, None);
        }
        let mut vc = race.clocks[race.current].clone();
        if vc.len() <= child {
            vc.resize(child + 1, 0);
        }
        vc[child] = 1;
        race.clocks[child] = vc;
        race.tick();
        let epochs = self.fresh_epochs(locals.len());
        self.sched.add(child);
        self.sched.stacks[child].push(Frame {
            func_id: entry,
            locals,
            epochs,
            thread: Some(pthread),
            block: BlockId(0),
            caller_return: None,
        });
        if self.sched.rng.is_none() {
            self.switch_to(child);
        }
        Ok(())
    }

    /// Retypes a fresh heap block when its pointer is first cast to `*mut T`.
    fn retype_heap_block(&mut self, ptr: &Value, pointee: TypeId) -> Result<(), String> {
        let Value::Ptr {
            target: PtrTarget::Heap(id),
            projections,
            ..
        } = ptr
        else {
            return Ok(());
        };
        let Some(block) = self.heap.get(*id) else {
            return Ok(());
        };
        let untouched = matches!(&block.slots, Value::Array(slots) if slots.iter().all(Self::is_uninit_shape));
        let unmapped = matches!(&block.slots, Value::Array(slots) if slots.is_empty());
        if block.freed
            || (block.elem == pointee && !unmapped)
            || !untouched
            || !matches!(projections.as_slice(), [ResolvedProj::Index(0)])
        {
            return Ok(());
        }
        let (size, _) = self.program.type_size_align(pointee)?;
        if size == 0 {
            return Ok(());
        }
        let bytes = block.bytes;
        let slot = self.uninit_shape(pointee);
        let block = &mut self.heap[*id];
        block.elem = pointee;
        block.slots = Value::Array(vec![slot; (bytes / size) as usize]);
        Ok(())
    }

    pub fn set_max_steps(&mut self, max_steps: usize) {
        self.max_steps = max_steps;
    }

    pub fn eval_call(&mut self, func_id: FuncId, args: Vec<Value>) -> Result<Value, String> {
        self.call_root(func_id, args)
    }

    pub fn read_ptr_value(
        &self,
        target: &PtrTarget,
        projs: &[ResolvedProj],
    ) -> Result<Value, String> {
        self.read_resolved(target, projs)
    }

    fn const_to_val_typed(cv: &ConstValue, ty_id: TypeId, types: &[Type]) -> Value {
        // `null` for an optional: the variant that holds nothing.
        if let (ConstValue::Void, Some(Type::Union { variants, .. })) = (cv, types.get(ty_id.0 as usize))
            && let Some(variant) = variants.iter().position(|v| matches!(types[v.0 as usize], Type::Void))
        {
            return Value::Union {
                ty: ty_id,
                variant: variant as u32,
                payload: Box::new(Value::Void),
            };
        }
        if let ConstValue::Aggregate(items) = cv {
            match types.get(ty_id.0 as usize) {
                Some(Type::Struct(ftys)) => {
                    let fields = items
                        .iter()
                        .enumerate()
                        .map(|(i, item)| {
                            let fty = ftys.get(i).copied().unwrap_or(ty_id);
                            Self::const_to_val_typed(item, fty, types)
                        })
                        .collect();
                    return Value::Struct { ty: ty_id, fields };
                }
                Some(Type::Array { elem, .. }) => {
                    let elems = items
                        .iter()
                        .map(|item| Self::const_to_val_typed(item, *elem, types))
                        .collect();
                    return Value::Array(elems);
                }
                _ => {}
            }
        }
        Self::const_to_val(cv)
    }

    fn const_to_val(cv: &ConstValue) -> Value {
        match cv {
            ConstValue::Void => Value::Void,
            ConstValue::Bool(b) => Value::Bool(*b),
            ConstValue::I64(n) => Value::Int(*n),
            ConstValue::Wide(w) => Value::Wide(w.clone()),
            ConstValue::F64(bits) => Value::Float(*bits),
            ConstValue::Type(id) => Value::Type(*id),
            ConstValue::Func(id) => Value::Func(*id),
            ConstValue::Global(id) => Value::Ptr {
                target: PtrTarget::Global(*id),
                projections: Vec::new(),
                tag: Tag::default(),
            },
            ConstValue::Str(s) => Value::Str(s.clone()),
            ConstValue::Aggregate(items) => {
                Value::Array(items.iter().map(Self::const_to_val).collect())
            }
        }
    }

    /// Evaluates `func_id(args)` at compile-time (or runtime interpretation),
    /// allowing Zig-style `comptime` functions to compute both values and new types in `Program`.
    pub fn eval(
        program: &'a mut Program,
        func_id: FuncId,
        args: Vec<Value>,
    ) -> Result<Value, String> {
        let mut vm = Self::new(program);
        vm.call_root(func_id, args)
    }

    /// The body of function `id`, shared rather than copied on every block the VM enters.
    fn get_function(&mut self, id: FuncId) -> Result<std::rc::Rc<Function>, String> {
        if let Some(f) = self.fn_cache.get(&id) {
            return Ok(f.clone());
        }
        let func = self
            .program
            .functions
            .iter()
            .find(|f| f.id == id)
            .cloned()
            .ok_or_else(|| format!("Undefined function {id}"))?;
        let func = std::rc::Rc::new(func);
        self.fn_cache.insert(id, func.clone());
        Ok(func)
    }

    fn call_root(&mut self, func_id: FuncId, args: Vec<Value>) -> Result<Value, String> {
        match self.start_call(func_id, args)? {
            VmExit::Return(v) => Ok(v),
            VmExit::Host { symbol, .. } => Err(format!(
                "Comptime VM sandbox violation: host function '{symbol}' is not available here"
            )),
        }
    }

    fn push_root_frame(&mut self, func_id: FuncId, args: Vec<Value>) -> Result<(), String> {
        let func = self.get_function(func_id)?;
        if args.len() != func.arg_count {
            return Err(format!(
                "Function {} expected {} arguments, got {}",
                func_id,
                func.arg_count,
                args.len()
            ));
        }

        let mut locals = vec![Value::Uninit; func.locals.len()];
        for (i, arg) in args.into_iter().enumerate() {
            locals[i + 1] = arg;
        }

        let epochs = self.fresh_epochs(locals.len());
        self.frames.push(Frame {
            func_id,
            locals,
            epochs,
            thread: None,
            block: BlockId(0),
            caller_return: None,
        });
        Ok(())
    }

    /// Runs until the root frame returns or a host function is called.
    fn run(&mut self) -> Result<VmExit, String> {
        loop {
            let current_frame_idx = self.frames.len() - 1;
            let func_id = self.frames[current_frame_idx].func_id;
            let block_id = self.frames[current_frame_idx].block;
            let func = self.get_function(func_id)?;

            let block = func
                .blocks
                .get(block_id.0 as usize)
                .ok_or_else(|| format!("Invalid block {block_id} in {func_id}"))?;

            for stmt in &block.statements {
                self.steps += 1;
                if self.steps > self.max_steps {
                    return Err(format!(
                        "Comptime VM sandbox violation: evaluation exceeded step limit of {}",
                        self.max_steps
                    ));
                }
                self.exec_statement(&func, stmt)?;
            }
            self.steps += 1;
            if self.steps > self.max_steps {
                return Err(format!(
                    "Comptime VM sandbox violation: evaluation exceeded step limit of {}",
                    self.max_steps
                ));
            }

            match &block.terminator {
                Terminator::Goto { target } => {
                    self.frames[current_frame_idx].block = *target;
                }
                Terminator::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                } => {
                    let val = self.eval_operand(discr)?;
                    let switch_val = match val {
                        Value::Int(n) => n,
                        Value::Bool(b) => i128::from(b),
                        Value::Type(ty) => i128::from(ty.0),
                        _ => {
                            return Err(format!(
                                "switchInt expected integer/bool/type, got {val:?}"
                            ));
                        }
                    };
                    let next_block = targets
                        .iter()
                        .find(|(v, _)| *v == switch_val)
                        .map(|(_, b)| *b)
                        .unwrap_or(*otherwise);
                    self.frames[current_frame_idx].block = next_block;
                }
                Terminator::Call {
                    func: callee_op,
                    args: call_args,
                    destination,
                    target,
                } => {
                    let callee_val = self.eval_operand(callee_op)?;
                    let Value::Func(callee_id) = callee_val else {
                        return Err(format!("Expected function in call, found {callee_val:?}"));
                    };
                    let mut evaluated_args = Vec::with_capacity(call_args.len());
                    for arg_op in call_args {
                        evaluated_args.push(self.eval_operand(arg_op)?);
                    }

                    let allocator = self
                        .program
                        .externs
                        .iter()
                        .find(|e| e.id == callee_id)
                        .map(|e| e.symbol.clone());
                    if let Some(symbol) = allocator {
                        if self.pure && !matches!(symbol.as_str(), "malloc" | "realloc" | "free") {
                            return Err(format!("Calling '{symbol}' is not constant"));
                        }
                        if let Some(result) = self.call_allocator(&symbol, &evaluated_args)? {
                            self.write_place(destination, result)?;
                            self.frames[current_frame_idx].block = *target;
                            continue;
                        }
                        if symbol.starts_with(crate::ir::MEMCOPY_PREFIX) {
                            self.copy_slots(&evaluated_args)?;
                            self.frames[current_frame_idx].block = *target;
                            continue;
                        }
                        match self.call_pthread(&symbol, &evaluated_args)? {
                            Some(Pthread::Done(result)) => {
                                self.write_place(destination, result)?;
                                self.frames[current_frame_idx].block = *target;
                                if symbol == "pthread_create" {
                                    self.start_thread(&evaluated_args)?;
                                }
                                if let Some((fiber, context)) = self.sched.pending_switch.take() {
                                    self.switch_to(fiber);
                                    if let Some(race) = self.race.get_mut().as_mut() {
                                        race.acquire(&context);
                                    }
                                } else if symbol == "usleep" || std::mem::take(&mut self.sched.yield_after) {
                                    self.reschedule(true)?;
                                } else {
                                    self.sync_point()?;
                                }
                                continue;
                            }
                            Some(Pthread::Block(wait)) => {
                                let running = self.sched.running;
                                let bounded = symbol == "pthread_cond_timedwait";
                                self.sched.blocked[running] = Some(Blocked {
                                    symbol,
                                    args: evaluated_args,
                                    destination: destination.clone(),
                                    target: *target,
                                    wait,
                                });
                                self.reschedule(bounded)?;
                                continue;
                            }
                            None => {}
                        }
                    }
                    let atomic = self
                        .program
                        .externs
                        .iter()
                        .find(|e| e.id == callee_id)
                        .and_then(|e| {
                            let rest = e.symbol.strip_prefix(crate::ir::ATOMIC_PREFIX)?;
                            let elem_ty = if e.args.len() > 1 { e.args[1] } else { e.ret };
                            Some((rest.split('.').next()?.to_string(), elem_ty))
                        });
                    if let Some((op, elem_ty)) = atomic {
                        let result = self.eval_atomic(&op, elem_ty, &evaluated_args)?;
                        self.write_place(destination, result)?;
                        self.frames[current_frame_idx].block = *target;
                        self.sync_point()?;
                        continue;
                    }
                    if let Some(ext) = self.program.externs.iter().find(|e| e.id == callee_id) {
                        if ext.symbol.starts_with(HOST_PREFIX) {
                            self.pending_host = Some((destination.clone(), *target));
                            return Ok(VmExit::Host {
                                symbol: ext.symbol.clone(),
                                args: evaluated_args,
                            });
                        }
                        return Err(format!(
                            "Comptime VM sandbox violation: cannot call extern function '{}' during comptime evaluation",
                            ext.symbol
                        ));
                    }

                    let callee_func = self.get_function(callee_id)?;
                    if evaluated_args.len() != callee_func.arg_count {
                        return Err(format!(
                            "Function {} expected {} args, got {}",
                            callee_id,
                            callee_func.arg_count,
                            evaluated_args.len()
                        ));
                    }

                    let mut new_locals = vec![Value::Uninit; callee_func.locals.len()];
                    for (i, arg_val) in evaluated_args.into_iter().enumerate() {
                        new_locals[i + 1] = arg_val;
                    }

                    let epochs = self.fresh_epochs(new_locals.len());
                    self.frames.push(Frame {
                        func_id: callee_id,
                        locals: new_locals,
                        epochs,
                        thread: None,
                        block: BlockId(0),
                        caller_return: Some((Some(destination.clone()), *target)),
                    });
                }
                Terminator::Drop { place, target } => {
                    // If unelaborated in VM, check if the place has an initialized value and a registered destructor
                    let ty_id = self.place_type(&func, place)?;
                    let (ptr_target, projs) = self.resolve_place(place)?;
                    let is_init = self.read_resolved(&ptr_target, &projs).is_ok();
                    if is_init
                        && let Some((_, dtor_fn)) =
                            self.program.destructors.iter().find(|(t, _)| *t == ty_id)
                    {
                        let dtor_id = *dtor_fn;
                        let dtor_func = self.get_function(dtor_id)?;
                        let ptr_val = Value::Ptr {
                            target: ptr_target,
                            projections: projs,
                            tag: Tag::default(),
                        };
                        let mut new_locals = vec![Value::Uninit; dtor_func.locals.len()];
                        if dtor_func.arg_count == 1 {
                            new_locals[1] = ptr_val;
                        }
                        let epochs = self.fresh_epochs(new_locals.len());
                        self.frames.push(Frame {
                            func_id: dtor_id,
                            locals: new_locals,
                            epochs,
                            thread: None,
                            block: BlockId(0),
                            caller_return: Some((None, *target)),
                        });
                    } else {
                        self.frames[current_frame_idx].block = *target;
                    }
                }
                Terminator::Return => {
                    let finished = self.frames.pop().unwrap();
                    let ret_val = finished.locals.into_iter().next().unwrap_or(Value::Void);
                    if matches!(ret_val, Value::Uninit) {
                        return Err(format!(
                            "Function {} returned uninitialized _0",
                            finished.func_id
                        ));
                    }
                    if let Some(thread) = finished.thread {
                        // An emulated thread finished; another takes over.
                        self.threads[thread] = Some(ret_val);
                        if let Some(race) = self.race.get_mut().as_mut() {
                            race.finished[thread + 1] = Some(race.clocks[thread + 1].clone());
                        }
                        self.sched.done[thread + 1] = true;
                        self.reschedule(false)?;
                    } else if let Some((dest_place, next_block)) = finished.caller_return {
                        // A destructor run for `Drop` has nowhere to put its result.
                        if let Some(dest_place) = dest_place {
                            let _ = self.write_place(&dest_place, ret_val);
                        }
                        let caller_idx = self.frames.len() - 1;
                        self.frames[caller_idx].block = next_block;
                    } else {
                        return Ok(VmExit::Return(ret_val));
                    }
                }
                Terminator::Unreachable => {
                    return Err(format!("Reached 'unreachable' terminator in {func_id}"));
                }
            }
        }
    }

    fn exec_statement(&mut self, func: &Function, stmt: &Statement) -> Result<(), String> {
        match stmt {
            Statement::Line(_) => Ok(()),
            Statement::StorageLive(local) => {
                let frame_idx = self.frames.len() - 1;
                if let Some(&ty_id) = func.locals.get(local.0 as usize) {
                    let init_val = match self.program.types.get(ty_id.0 as usize) {
                        Some(Type::Union { .. }) => Value::Union {
                            ty: ty_id,
                            variant: 0,
                            payload: Box::new(Value::Uninit),
                        },
                        _ => self.uninit_shape(ty_id),
                    };
                    self.frames[frame_idx].locals[local.0 as usize] = init_val;
                }
                self.renew_storage(*local);
                Ok(())
            }
            Statement::StorageDead(local) => {
                let frame_idx = self.frames.len() - 1;
                self.frames[frame_idx].locals[local.0 as usize] = Value::Uninit;
                self.renew_storage(*local);
                Ok(())
            }
            Statement::SetDiscriminant(place, variant) => {
                let ty_id = self.place_type(func, place)?;
                let (target, projs) = self.resolve_place(place)?;
                let cur = self.read_resolved(&target, &projs).unwrap_or(Value::Union {
                    ty: ty_id,
                    variant: *variant,
                    payload: Box::new(Value::Uninit),
                });
                let new_val = match cur {
                    Value::Union { ty, payload, .. } => Value::Union {
                        ty,
                        variant: *variant,
                        payload,
                    },
                    _ => Value::Union {
                        ty: ty_id,
                        variant: *variant,
                        payload: Box::new(Value::Uninit),
                    },
                };
                self.write_resolved(&target, &projs, new_val)
            }
            Statement::Assign(dest, rvalue) => {
                let dest_ty = self.place_type(func, dest)?;
                let mut val = self.eval_rvalue(func, rvalue, dest_ty)?;
                if matches!(val, Value::Void) {
                    val = Self::uninit_value_for_type(self.program, dest_ty);
                }
                self.validate_pattern_value(dest_ty, &val)?;
                self.write_place(dest, val)
            }
        }
    }

    fn uninit_value_for_type(program: &Program, ty_id: TypeId) -> Value {
        match program.types.get(ty_id.0 as usize) {
            Some(Type::Overlay(_)) => Value::Overlay {
                ty: ty_id,
                active_field: Some(0),
                val: Box::new(Value::Void),
            },
            Some(Type::Array { elem, len } | Type::Simd { elem, len }) => Value::Array(vec![
                Self::uninit_value_for_type(program, *elem);
                *len as usize
            ]),
            _ => Value::Void,
        }
    }

    fn validate_pattern_value(&self, ty_id: TypeId, val: &Value) -> Result<(), String> {
        if let (Value::Wide(w), Some(Type::Pattern { ranges, .. })) =
            (val, self.program.types.get(ty_id.0 as usize))
            && !crate::ir::pattern_contains(ranges, w)
        {
            return Err(format!(
                "Value {w} is outside valid pattern ranges for type {}",
                self.program.type_label(ty_id)
            ));
        }
        let Value::Int(n) = val else {
            return Ok(());
        };
        match self.program.types.get(ty_id.0 as usize) {
            Some(Type::Rune) => {
                if !((0..=0xD7FF).contains(n) || (0xE000..=0x10FFFF).contains(n)) {
                    return Err(format!(
                        "Value {n} (0x{n:X}) is not a valid Unicode scalar value for 'rune'"
                    ));
                }
                Ok(())
            }
            Some(Type::Pattern { ranges, .. }) => {
                if !crate::ir::pattern_contains(ranges, &Wide::from_i128(*n)) {
                    return Err(format!(
                        "Value {n} is outside valid pattern ranges for type {}",
                        self.program.type_label(ty_id)
                    ));
                }
                Ok(())
            }
            _ => Ok(()),
        }
    }

    fn place_type(&self, func: &Function, place: &Place) -> Result<TypeId, String> {
        let mut cur_ty = *func
            .locals
            .get(place.local.0 as usize)
            .ok_or_else(|| format!("Undefined local {} in {}", place.local, func.id))?;
        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    let Some(Type::Ptr { pointee, .. }) = self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot deref non-pointer type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    };
                    cur_ty = *pointee;
                }
                Projection::Field(idx) => match self.program.types.get(cur_ty.0 as usize) {
                    Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                        cur_ty = *fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!(
                                "Field .{idx} out of bounds on '{}'",
                                self.program.type_label(cur_ty)
                            ))?;
                    }
                    _ => {
                        return Err(format!(
                            "Cannot access field on non-struct/overlay type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    }
                },
                Projection::Variant(v_idx) => {
                    let Some(Type::Union { variants, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot access variant .v{v_idx} on non-union type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    };
                    cur_ty = *variants
                        .get(*v_idx as usize)
                        .ok_or_else(|| format!(
                            "Variant .v{v_idx} out of bounds on '{}'",
                            self.program.type_label(cur_ty)
                        ))?;
                }
                Projection::Index(_) => {
                    let Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) =
                        self.program.types.get(cur_ty.0 as usize)
                    else {
                        return Err(format!(
                            "Cannot index non-array/simd type '{}'",
                            self.program.type_label(cur_ty)
                        ));
                    };
                    cur_ty = *elem;
                }
            }
        }
        Ok(cur_ty)
    }

    /// Resolves any `Projection::Deref` indirections in `place` to a concrete `(PtrTarget, Vec<ResolvedProj>)`.
    fn resolve_place(&self, place: &Place) -> Result<(PtrTarget, Vec<ResolvedProj>), String> {
        let caller_frame = self.frames.len() - 1;
        let func_id = self.frames[caller_frame].func_id;
        let caller_id = self.sched.running * FRAME_STRIDE + caller_frame;
        let mut cur_ty = self
            .fn_cache
            .get(&func_id)
            .and_then(|f| f.locals.get(place.local.0 as usize).copied())
            .or_else(|| {
                self.program
                    .functions
                    .iter()
                    .find(|f| f.id == func_id)
                    .and_then(|f| f.locals.get(place.local.0 as usize).copied())
            });
        let mut cur_target = PtrTarget::Local {
            frame: caller_id,
            local: place.local,
            epoch: self.local_epoch(caller_id, place.local),
        };
        let mut cur_projs: Vec<ResolvedProj> = Vec::new();
        self.last_via.set(Via::Owner);

        for proj in &place.projections {
            match proj {
                Projection::Deref => {
                    let pointee_ty = cur_ty.and_then(|t| match self.program.types.get(t.0 as usize) {
                        Some(Type::Ptr { pointee, .. }) => Some(*pointee),
                        _ => None,
                    });
                    cur_ty = pointee_ty;
                    let ptr_val = self.read_resolved(&cur_target, &cur_projs)?;
                    match ptr_val {
                        Value::Ptr {
                            target,
                            projections,
                            tag,
                        } => {
                            if tag.0 == 0 {
                                self.last_via.set(Via::Raw);
                            } else {
                                self.last_via.set(Via::Reference(tag.0));
                                if let Some(aliasing) = self.aliasing.borrow().as_ref()
                                    && !aliasing.borrow(tag.0).live
                                {
                                    return Err(format!(
                                        "{UB_PREFIX}use of a reference to {} after a conflicting access invalidated it",
                                        self.describe_target(&target)
                                    ));
                                }
                            }
                            cur_target = target;
                            cur_projs = projections;
                        }
                        Value::Str(s) => {
                            cur_target = PtrTarget::Str(s);
                            cur_projs = Vec::new();
                        }
                        Value::Int(addr) => {
                            if let Some(pty) = pointee_ty
                                && let Ok((0, align)) = self.program.type_size_align(pty)
                                && addr > 0
                                && (addr as u128).is_multiple_of(u128::from(align))
                            {
                                cur_target = PtrTarget::Dangling { addr, ty: pty };
                                cur_projs = Vec::new();
                            } else {
                                return Err(format!(
                                    "Cannot dereference non-pointer value {ptr_val:?}"
                                ));
                            }
                        }
                        _ => {
                            return Err(format!(
                                "Cannot dereference non-pointer value {ptr_val:?}"
                            ));
                        }
                    }
                }
                Projection::Field(idx) => {
                    cur_ty = cur_ty.and_then(|t| match self.program.types.get(t.0 as usize) {
                        Some(Type::Struct(fs) | Type::Overlay(fs)) => fs.get(*idx as usize).copied(),
                        _ => None,
                    });
                    cur_projs.push(ResolvedProj::Field(*idx));
                }
                Projection::Variant(v_idx) => {
                    cur_ty = cur_ty.and_then(|t| match self.program.types.get(t.0 as usize) {
                        Some(Type::Union { variants, .. }) => variants.get(*v_idx as usize).copied(),
                        _ => None,
                    });
                    cur_projs.push(ResolvedProj::Variant(*v_idx));
                }
                Projection::Index(idx_local) => {
                    // A slice's data pointer has type `[T; 0]` and reaches element 0 of what it
                    // views: an index into it moves along those elements.
                    let slice_data = cur_ty.is_some_and(|t| {
                        matches!(self.program.types.get(t.0 as usize), Some(Type::Array { len: 0, .. }))
                    });
                    cur_ty = cur_ty.and_then(|t| match self.program.types.get(t.0 as usize) {
                        Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) => Some(*elem),
                        _ => None,
                    });
                    let idx_val = self.read_resolved(
                        &PtrTarget::Local {
                            frame: caller_id,
                            local: *idx_local,
                            epoch: self.local_epoch(caller_id, *idx_local),
                        },
                        &[],
                    )?;
                    let Value::Int(i) = idx_val else {
                        return Err(format!("Array index must be integer, got {idx_val:?}"));
                    };
                    if i < 0 {
                        return Err(format!("Negative array index {i}"));
                    }
                    if slice_data && let Some(ResolvedProj::Index(base)) = cur_projs.last_mut() {
                        *base += i as usize;
                        continue;
                    }
                    cur_projs.push(ResolvedProj::Index(i as usize));
                }
            }
        }

        Ok((cur_target, cur_projs))
    }

    fn local_epoch(&self, frame: usize, local: LocalId) -> u64 {
        self.frame_at(frame)
            .and_then(|f| f.epochs.get(local.0 as usize))
            .copied()
            .unwrap_or(0)
    }

    fn zero_sized_value(&self, ty_id: TypeId) -> Result<Value, String> {
        match self.program.types.get(ty_id.0 as usize) {
            Some(Type::Void | Type::Never) => Ok(Value::Void),
            Some(Type::Struct(fields)) => {
                let mut vals = Vec::with_capacity(fields.len());
                for &fty in fields {
                    vals.push(self.zero_sized_value(fty)?);
                }
                Ok(Value::Struct {
                    ty: ty_id,
                    fields: vals,
                })
            }
            Some(Type::Array { elem, len } | Type::Simd { elem, len }) => {
                if *len == 0 {
                    Ok(Value::Array(Vec::new()))
                } else {
                    let ev = self.zero_sized_value(*elem)?;
                    Ok(Value::Array(vec![ev; *len as usize]))
                }
            }
            Some(Type::Overlay(_)) => Ok(Value::Overlay {
                ty: ty_id,
                active_field: Some(0),
                val: Box::new(Value::Void),
            }),
            other => Err(format!(
                "Cannot synthesize zero-sized value for non-ZST type {other:?}"
            )),
        }
    }

    fn read_resolved(&self, target: &PtrTarget, projs: &[ResolvedProj]) -> Result<Value, String> {
        let val = self.read_resolved_raw(target, projs)?;
        if matches!(val, Value::Uninit) {
            return Err(format!("{UB_PREFIX}read of uninitialized or moved memory {target:?}"));
        }
        Ok(val)
    }

    /// Checks that references are used only while nothing has invalidated them.
    pub fn check_aliasing(&mut self) {
        *self.aliasing.get_mut() = Some(Aliasing::default());
    }

    fn is_raw_ptr_type(&self, ty: TypeId) -> bool {
        self.program.raw_ptr_types.contains(&ty)
    }

    /// Records an access to the place `resolve_place` just resolved.
    fn alias_access(&mut self, target: &PtrTarget, projs: &[ResolvedProj], write: bool) {
        let via = self.last_via.get();
        if let Some(aliasing) = self.aliasing.get_mut()
            && !matches!(target, PtrTarget::Str(_) | PtrTarget::Dangling { .. } | PtrTarget::Global(_))
        {
            aliasing.access(target, projs, via, write);
        }
    }

    /// The tag of a new `&place` or `&mut place` of type `ty`, resolved just now.
    fn retag(&mut self, target: &PtrTarget, projs: &[ResolvedProj], mutable: bool, ty: TypeId) -> Tag {
        let via = self.last_via.get();
        let raw = self.is_raw_ptr_type(ty);
        let Some(aliasing) = self.aliasing.get_mut() else {
            return Tag(0);
        };
        if raw || matches!(target, PtrTarget::Str(_) | PtrTarget::Dangling { .. } | PtrTarget::Global(_)) {
            return Tag(0);
        }
        // `&mut` of a `cell` field, through a shared reference: interior mutation.
        if let Via::Reference(t) = via
            && mutable
            && !aliasing.borrow(t).mutable
        {
            return Tag(0);
        }
        aliasing.access(target, projs, via, mutable);
        let parent = match via {
            Via::Reference(t) => t,
            _ => 0,
        };
        let from_raw = match via {
            Via::Reference(t) => aliasing.borrow(t).from_raw,
            Via::Raw => true,
            Via::Owner => false,
        };
        aliasing.borrows.push(Borrow {
            path: projs.to_vec(),
            mutable,
            parent,
            live: true,
            from_raw,
        });
        let tag = aliasing.borrows.len() as u64;
        let live = aliasing.by_target.entry(target.clone()).or_default();
        if mutable { &mut live.mutable } else { &mut live.shared }.push(tag);
        Tag(tag)
    }

    /// Names the memory a pointer reaches, for error messages.
    fn describe_target(&self, target: &PtrTarget) -> String {
        match target {
            PtrTarget::Local { frame, local, .. } => {
                let name = self
                    .frame_at(*frame)
                    .and_then(|f| self.fn_cache.get(&f.func_id))
                    .and_then(|f| f.local_names.iter().find(|(l, _)| l == local))
                    .map(|(_, n)| format!("local '{n}'"));
                name.unwrap_or_else(|| format!("local {local}"))
            }
            PtrTarget::Heap(_) => "a heap allocation".to_string(),
            PtrTarget::Global(_) => "a global".to_string(),
            other => format!("{other:?}"),
        }
    }

    /// Checks an access by the running thread against the accesses of other threads, for race
    /// detection (once a thread has been created).
    fn record_access(&self, target: &PtrTarget, projs: &[ResolvedProj], write: bool) -> Result<(), String> {
        if self.in_atomic.get() || matches!(target, PtrTarget::Str(_) | PtrTarget::Dangling { .. }) {
            return Ok(());
        }
        let mut guard = self.race.borrow_mut();
        let Some(race) = guard.as_mut() else {
            return Ok(());
        };
        let t = race.current;
        let vc = race.clocks[t].clone();
        let field = slot_field(projs);
        let fields = race.shadow.entry(slot_key(target, projs)).or_default();
        let unordered = |&(u, c): &(usize, u64)| u != t && c > clock(&vc, u);
        let what = if write { "writes" } else { "reads" };
        let report = |u: usize, other: &str| {
            Err(format!(
                "{UB_PREFIX}data race: thread {t} {what} {} concurrently with thread {u}'s {other} (no join, lock, or atomic operation orders them)",
                self.describe_target(target)
            ))
        };
        for (other, shadow) in fields.iter() {
            if field.is_some() && other.is_some() && *other != field {
                continue;
            }
            if let Some(w) = shadow.write.filter(unordered) {
                return report(w.0, "write");
            }
            if write && let Some(r) = shadow.reads.iter().find(|r| unordered(r)) {
                return report(r.0, "read");
            }
        }
        let shadow = fields.entry(field).or_default();
        if write {
            shadow.write = Some((t, clock(&vc, t)));
            shadow.reads.clear();
        } else {
            shadow.reads.retain(|(u, _)| *u != t);
            shadow.reads.push((t, clock(&vc, t)));
        }
        Ok(())
    }

    /// The value at `target` and `projs`, which may be uninitialized.
    fn read_resolved_raw(&self, target: &PtrTarget, projs: &[ResolvedProj]) -> Result<Value, String> {
        self.record_access(target, projs, false)?;
        if let PtrTarget::Dangling { ty, .. } = target {
            let mut cur_ty = *ty;
            for proj in projs {
                match proj {
                    ResolvedProj::Field(idx) => match self.program.types.get(cur_ty.0 as usize) {
                        Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                            cur_ty = *fields
                                .get(*idx as usize)
                                .ok_or_else(|| format!("Field .{idx} out of bounds"))?;
                        }
                        _ => return Err(format!("Cannot access field .{idx} on ZST {cur_ty}")),
                    },
                    ResolvedProj::Variant(v_idx) => {
                        let Some(Type::Union { variants, .. }) =
                            self.program.types.get(cur_ty.0 as usize)
                        else {
                            return Err(format!("Cannot access variant .v{v_idx} on ZST {cur_ty}"));
                        };
                        cur_ty = *variants
                            .get(*v_idx as usize)
                            .ok_or_else(|| format!("Variant .v{v_idx} out of bounds"))?;
                    }
                    ResolvedProj::Index(idx) => match self.program.types.get(cur_ty.0 as usize) {
                        Some(Type::Array { elem, len } | Type::Simd { elem, len }) => {
                            let (es, _) = self.program.type_size_align(*elem)?;
                            if es > 0 && (*idx as u64) >= *len {
                                return Err(format!(
                                    "Array index {idx} out of bounds (len {len})"
                                ));
                            }
                            cur_ty = *elem;
                        }
                        _ => return Err(format!("Cannot index non-array ZST {cur_ty}")),
                    },
                }
            }
            return self.zero_sized_value(cur_ty);
        }
        if let PtrTarget::Str(s) = target {
            if projs.is_empty() {
                return Ok(Value::Str(s.clone()));
            }
            if let [ResolvedProj::Index(idx)] = projs {
                let b = *s.as_bytes().get(*idx).ok_or_else(|| {
                    format!("String index {idx} out of bounds (len {})", s.len())
                })?;
                return Ok(Value::Int(i128::from(b)));
            }
            return Err(format!("Unsupported projections {projs:?} on string target"));
        }
        let mut cur = match target {
            PtrTarget::Local {
                frame,
                local,
                epoch,
            } => {
                self.check_local(*frame, *local, *epoch)?;
                self.frame_at(*frame)
                    .ok_or_else(|| format!("Undefined {local}"))?
                    .locals
                    .get(local.0 as usize)
                    .ok_or_else(|| format!("Undefined {local}"))?
            }
            PtrTarget::Heap(id) => &self.heap_block(*id)?.slots,
            PtrTarget::Global(gl_id) => self
                .globals
                .get(gl_id.0 as usize)
                .ok_or_else(|| format!("Undefined {gl_id}"))?,
            PtrTarget::ThreadLocal { thread, global } => self
                .sched
                .thread_locals
                .get(&(*thread, *global))
                .ok_or_else(|| format!("Undefined {global}"))?,
            PtrTarget::Str(_) | PtrTarget::Dangling { .. } => unreachable!(),
        };

        for proj in projs {
            match proj {
                ResolvedProj::Field(idx) => match cur {
                    Value::Struct { fields, .. } => {
                        cur = fields
                            .get(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds"))?;
                    }
                    Value::Overlay {
                        active_field, val, ..
                    } => {
                        if *active_field != Some(*idx) {
                            return Err(format!(
                                "Overlay read of inactive field .{idx} (active: {active_field:?})"
                            ));
                        }
                        cur = val;
                    }
                    _ => return Err(format!("Cannot access field .{idx} on {cur:?}")),
                },
                ResolvedProj::Variant(v_idx) => {
                    let Value::Union {
                        variant, payload, ..
                    } = cur
                    else {
                        return Err(format!("Cannot access variant .v{v_idx} on {cur:?}"));
                    };
                    if *variant != *v_idx {
                        return Err(format!(
                            "Union read of inactive variant .v{v_idx} (active: v{variant})"
                        ));
                    }
                    cur = payload;
                }
                ResolvedProj::Index(idx) => {
                    let Value::Array(elems) = cur else {
                        return Err(format!("Cannot index non-array value {cur:?}"));
                    };
                    cur = elems.get(*idx).ok_or_else(|| {
                        format!("{UB_PREFIX}index {idx} out of bounds (len {})", elems.len())
                    })?;
                }
            }
        }

        Ok(cur.clone())
    }

    fn write_resolved(
        &mut self,
        target: &PtrTarget,
        projs: &[ResolvedProj],
        new_val: Value,
    ) -> Result<(), String> {
        self.record_access(target, projs, true)?;
        if let PtrTarget::Local {
            frame,
            local,
            epoch,
        } = target
        {
            self.check_local(*frame, *local, *epoch)?;
        }
        if let PtrTarget::Heap(id) = target {
            self.heap_block(*id)?;
        }
        let mut cur = match target {
            PtrTarget::Local { frame, local, .. } => self
                .frame_at_mut(*frame)
                .ok_or_else(|| format!("Undefined {local}"))?
                .locals
                .get_mut(local.0 as usize)
                .ok_or_else(|| format!("Undefined {local}"))?,
            PtrTarget::Heap(id) => &mut self.heap[*id].slots,
            PtrTarget::Global(gl_id) => self
                .globals
                .get_mut(gl_id.0 as usize)
                .ok_or_else(|| format!("Undefined {gl_id}"))?,
            PtrTarget::ThreadLocal { thread, global } => self
                .sched
                .thread_locals
                .get_mut(&(*thread, *global))
                .ok_or_else(|| format!("Undefined {global}"))?,
            PtrTarget::Str(_) => {
                return Err("Cannot write to immutable string literal".to_string());
            }
            PtrTarget::Dangling { .. } => {
                return Ok(());
            }
        };

        for proj in projs {
            match proj {
                ResolvedProj::Field(idx) => match cur {
                    Value::Struct { fields, .. } => {
                        cur = fields
                            .get_mut(*idx as usize)
                            .ok_or_else(|| format!("Field .{idx} out of bounds"))?;
                    }
                    Value::Overlay {
                        active_field, val, ..
                    } => {
                        *active_field = Some(*idx);
                        cur = val;
                    }
                    _ => return Err(format!("Cannot write field .{idx} on {cur:?}")),
                },
                ResolvedProj::Variant(v_idx) => {
                    let Value::Union {
                        variant, payload, ..
                    } = cur
                    else {
                        return Err(format!("Cannot write variant .v{v_idx} on {cur:?}"));
                    };
                    *variant = *v_idx;
                    cur = payload;
                }
                ResolvedProj::Index(idx) => {
                    let Value::Array(elems) = cur else {
                        return Err(format!("Cannot index non-array value {cur:?}"));
                    };
                    let len = elems.len();
                    cur = elems
                        .get_mut(*idx)
                        .ok_or_else(|| format!("{UB_PREFIX}index {idx} out of bounds (len {len})"))?;
                }
            }
        }

        *cur = new_val;
        Ok(())
    }

    fn read_place(&mut self, place: &Place, is_move: bool) -> Result<Value, String> {
        let (target, projs) = self.resolve_place(place)?;
        self.alias_access(&target, &projs, is_move);
        let val = self.read_resolved(&target, &projs)?;
        if is_move {
            self.write_resolved(&target, &projs, Value::Uninit)?;
        }
        Ok(val)
    }

    /// `@atomic_<op>` at compile time: a plain read-modify-write, as compile-time code runs on
    /// one thread. Yields the previous value (`void` for `store`).
    fn eval_atomic(&mut self, op: &str, elem_ty: TypeId, args: &[Value]) -> Result<Value, String> {
        // Each atomic operation acquires and releases its location, so atomics on it are ordered
        // and order the plain accesses around them. A plain access they do not order is a race,
        // which the access recorded here reports.
        let Value::Ptr {
            target,
            projections,
            ..
        } = &args[0]
        else {
            return Err(format!("Atomic operation on a non-pointer {:?}", args[0]));
        };
        // A relaxed operation orders nothing, so it must not make a race look synchronized.
        if let Some(op) = op.strip_suffix("_relaxed") {
            self.in_atomic.set(true);
            let result = self.eval_atomic_unsynced(op, elem_ty, args);
            self.in_atomic.set(false);
            return result;
        }
        let key = slot_key(target, projections);
        if let Some(race) = self.race.get_mut().as_mut() {
            race.acquire(&key);
        }
        self.record_access(target, projections, op != "load")?;
        self.in_atomic.set(true);
        let result = self.eval_atomic_unsynced(op, elem_ty, args);
        self.in_atomic.set(false);
        if let Some(race) = self.race.get_mut().as_mut() {
            race.release(key);
        }
        result
    }

    fn eval_atomic_unsynced(&mut self, op: &str, elem_ty: TypeId, args: &[Value]) -> Result<Value, String> {
        let Value::Ptr {
            target,
            projections,
            ..
        } = &args[0]
        else {
            return Err(format!("'@atomic_{op}' expects a pointer, found {:?}", args[0]));
        };
        let Some(&Type::Int { signed, bits }) = self.program.types.get(elem_ty.0 as usize) else {
            return Err(format!("'@atomic_{op}' expects an integer pointee"));
        };
        let int = |v: &Value| match v {
            Value::Int(i) => Ok(*i),
            other => Err(format!("'@atomic_{op}' expects an integer, found {other:?}")),
        };
        let old = self.read_resolved(target, projections)?;
        let cur = int(&old)?;
        let arg = |i: usize| int(&args[i]);
        let wrap = |v: i128| Self::wrap_int_to_bits(v, bits as u32, !signed);
        let new = match op {
            "load" => None,
            "store" | "swap" => Some(arg(1)?),
            "cas" => (cur == arg(1)?).then(|| arg(2)).transpose()?,
            "add" => Some(wrap(cur.wrapping_add(arg(1)?))),
            "sub" => Some(wrap(cur.wrapping_sub(arg(1)?))),
            "and" => Some(cur & arg(1)?),
            "or" => Some(cur | arg(1)?),
            "xor" => Some(wrap(cur ^ arg(1)?)),
            _ => return Err(format!("Unknown atomic operation '{op}'")),
        };
        if let Some(v) = new {
            self.write_resolved(target, projections, Value::Int(v))?;
        }
        Ok(if op == "store" { Value::Void } else { old })
    }

    fn write_place(&mut self, place: &Place, val: Value) -> Result<(), String> {
        let (target, projs) = self.resolve_place(place)?;
        self.alias_access(&target, &projs, true);
        self.write_resolved(&target, &projs, val)
    }

    fn eval_operand(&mut self, op: &Operand) -> Result<Value, String> {
        if let (true, Operand::Const(ConstValue::Global(id))) = (self.pure, op)
            && self.program.globals.get(id.0 as usize).is_some_and(|g| g.mutable)
        {
            return Err("This expression reads a mutable static, so it is not constant".to_string());
        }
        match op {
            Operand::Copy(place) => self.read_place(place, false),
            Operand::Move(place) => self.read_place(place, true),
            Operand::Const(ConstValue::Global(id)) if self.program.thread_local_globals.contains(id) => {
                let thread = self.sched.os_thread(self.sched.running);
                let initial = self
                    .globals
                    .get(id.0 as usize)
                    .ok_or_else(|| format!("Undefined {id}"))?
                    .clone();
                self.sched.thread_locals.entry((thread, *id)).or_insert(initial);
                Ok(Value::Ptr {
                    target: PtrTarget::ThreadLocal { thread, global: *id },
                    projections: Vec::new(),
                    tag: Tag::default(),
                })
            }
            Operand::Const(cv) => Ok(Self::const_to_val(cv)),
        }
    }

    fn operand_type(&self, func: &Function, op: &Operand) -> Result<Option<TypeId>, String> {
        match op {
            Operand::Copy(place) | Operand::Move(place) => Ok(Some(self.place_type(func, place)?)),
            Operand::Const(_) => Ok(None),
        }
    }

    /// Byte offsets of `fields` laid out in order with natural alignment (as `type_size_align`).
    fn field_offsets(&self, fields: &[TypeId]) -> Result<Vec<u64>, String> {
        let mut offset = 0u64;
        let mut out = Vec::with_capacity(fields.len());
        for &f in fields {
            let (fs, fa) = self.program.type_size_align(f)?;
            offset = (offset + fa - 1) & !(fa - 1);
            out.push(offset);
            offset += fs;
        }
        Ok(out)
    }

    /// Byte offset of a tagged union's payload: the tag first, then the payload aligned to the
    /// largest variant alignment.
    fn union_payload_offset(&self, tag: TypeId, variants: &[TypeId]) -> Result<u64, String> {
        let (ts, _) = self.program.type_size_align(tag)?;
        let mut max_align = 1u64;
        for &v in variants {
            max_align = max_align.max(self.program.type_size_align(v)?.1);
        }
        Ok((ts + max_align - 1) & !(max_align - 1))
    }

    /// The in-memory bit pattern of `v` (of type `ty`) as laid out by compiled code, for
    /// `@transmute`. Supports scalars, optionals, unions, structs, arrays, and overlays up to 128
    /// bytes; pointers have no bit pattern in the VM.
    fn value_to_bits(&self, v: &Value, ty: TypeId) -> Result<crate::wide::Wide, String> {
        let (size, _) = self.program.type_size_align(ty)?;
        if size > 128 {
            return Err(format!(
                "'@transmute' of a {size}-byte value is not supported during compile-time evaluation"
            ));
        }
        let int_bits = |v: &Value| -> Result<Wide, String> {
            match v {
                Value::Int(n) => Ok(Wide::from_i128(*n)),
                Value::Wide(w) => Ok(**w),
                Value::Bool(b) => Ok(Wide::from_i128(i128::from(*b))),
                other => Err(format!("Expected an integer value for '@transmute', got {other:?}")),
            }
        };
        let place = |acc: Wide, field: Wide, offset: u64, bytes: u64| {
            acc.bitor(&field.wrap((bytes * 8) as u16, false).shl((offset * 8) as u32))
        };
        let ty_def = self
            .program
            .types
            .get(ty.0 as usize)
            .ok_or_else(|| format!("Undefined type {ty}"))?
            .clone();
        match ty_def {
            Type::Void | Type::Never => Ok(Wide::ZERO),
            Type::Bool | Type::Int { .. } | Type::Rune | Type::Pattern { .. } => {
                Ok(int_bits(v)?.wrap((size * 8) as u16, false))
            }
            Type::F32 => match v {
                Value::Float(b) => Ok(Wide::from_i128(i128::from(
                    (f64::from_bits(*b) as f32).to_bits(),
                ))),
                other => Err(format!("Expected a float value, got {other:?}")),
            },
            Type::F64 => match v {
                Value::Float(b) => Ok(Wide::from_i128(i128::from(*b))),
                other => Err(format!("Expected a float value, got {other:?}")),
            },
            Type::Union { tag, variants } => {
                let Value::Union { variant, payload, .. } = v else {
                    return Err(format!("Expected a union value, got {v:?}"));
                };
                let var_ty = variants[*variant as usize];
                if let Some(niche) = self.program.union_niche(ty) {
                    let (ns, _) = self.program.type_size_align(niche.scalar)?;
                    let null = Wide::from_i128(niche.null).wrap((ns * 8) as u16, false);
                    return Ok(if *variant == 0 {
                        null
                    } else {
                        self.value_to_bits(payload, niche.payload)?
                    });
                }
                let stored_tag = self
                    .program
                    .union_tag_values(ty)
                    .and_then(|vals| vals.get(*variant as usize).copied())
                    .unwrap_or(i128::from(*variant));
                let (ts, _) = self.program.type_size_align(tag)?;
                let off = self.union_payload_offset(tag, &variants)?;
                let (vs, _) = self.program.type_size_align(var_ty)?;
                let acc = place(Wide::ZERO, Wide::from_i128(stored_tag), 0, ts);
                Ok(place(acc, self.value_to_bits(payload, var_ty)?, off, vs))
            }
            Type::Struct(fields) => {
                let Value::Struct { fields: vals, .. } = v else {
                    return Err(format!("Expected a struct value, got {v:?}"));
                };
                let offsets = self.field_offsets(&fields)?;
                let mut acc = Wide::ZERO;
                for ((fty, off), fv) in fields.iter().zip(offsets).zip(vals) {
                    let (fs, _) = self.program.type_size_align(*fty)?;
                    acc = place(acc, self.value_to_bits(fv, *fty)?, off, fs);
                }
                Ok(acc)
            }
            Type::Array { elem, .. } => {
                let Value::Array(vals) = v else {
                    return Err(format!("Expected an array value, got {v:?}"));
                };
                let (es, _) = self.program.type_size_align(elem)?;
                let mut acc = Wide::ZERO;
                for (i, ev) in vals.iter().enumerate() {
                    acc = place(acc, self.value_to_bits(ev, elem)?, i as u64 * es, es);
                }
                Ok(acc)
            }
            Type::Overlay(fields) => match v {
                Value::Overlay {
                    active_field: Some(f),
                    val,
                    ..
                } => self.value_to_bits(val, fields[*f as usize]),
                _ => Ok(Wide::ZERO),
            },
            other => Err(format!(
                "'@transmute' of {other} values is not supported during compile-time evaluation"
            )),
        }
    }

    /// Decodes a bit pattern produced by `value_to_bits` as a value of type `ty`.
    fn bits_to_value(&self, bits: &crate::wide::Wide, ty: TypeId) -> Result<Value, String> {
        let slice = |offset: u64, bytes: u64| bits.shr((offset * 8) as u32).wrap((bytes * 8) as u16, false);
        let ty_def = self
            .program
            .types
            .get(ty.0 as usize)
            .ok_or_else(|| format!("Undefined type {ty}"))?
            .clone();
        match ty_def {
            Type::Void | Type::Never => Ok(Value::Void),
            Type::Bool => Ok(Value::Bool(!bits.wrap(8, false).is_zero())),
            Type::Int { signed, bits: n } => Ok(Value::from_wide(bits.wrap(n, signed))),
            Type::Rune => Ok(Value::from_wide(bits.wrap(32, false))),
            Type::Pattern { base, .. } => self.bits_to_value(bits, base),
            Type::F32 => {
                let raw = bits.wrap(32, false).to_i128().unwrap_or(0) as u32;
                Ok(Value::from_f64(f64::from(f32::from_bits(raw))))
            }
            Type::F64 => Ok(Value::Float(bits.wrap(64, false).to_i128().unwrap_or(0) as u64)),
            Type::Union { tag, variants } => {
                if let Some(niche) = self.program.union_niche(ty) {
                    let (ps, _) = self.program.type_size_align(niche.payload)?;
                    let (ns, _) = self.program.type_size_align(niche.scalar)?;
                    let raw = slice(0, ps);
                    let marker = slice(niche.offset, ns);
                    return Ok(if marker == Wide::from_i128(niche.null).wrap((ns * 8) as u16, false) {
                        Value::Union {
                            ty,
                            variant: 0,
                            payload: Box::new(Value::Void),
                        }
                    } else {
                        Value::Union {
                            ty,
                            variant: 1,
                            payload: Box::new(self.bits_to_value(&raw, niche.payload)?),
                        }
                    });
                }
                let (ts, _) = self.program.type_size_align(tag)?;
                let stored = slice(0, ts);
                let variant = match self.program.union_tag_values(ty) {
                    Some(vals) => vals
                        .iter()
                        .position(|v| Wide::from_i128(*v).wrap((ts * 8) as u16, false) == stored),
                    None => stored.to_i128().map(|i| i as usize),
                }
                .filter(|&i| i < variants.len())
                .ok_or_else(|| format!(
                    "'@transmute' produced an invalid tag {stored} for '{}'",
                    self.program.type_label(ty)
                ))?;
                let var_ty = variants[variant];
                let off = self.union_payload_offset(tag, &variants)?;
                let (vs, _) = self.program.type_size_align(var_ty)?;
                Ok(Value::Union {
                    ty,
                    variant: variant as u32,
                    payload: Box::new(self.bits_to_value(&slice(off, vs), var_ty)?),
                })
            }
            Type::Struct(fields) => {
                let offsets = self.field_offsets(&fields)?;
                let mut vals = Vec::with_capacity(fields.len());
                for (fty, off) in fields.iter().zip(offsets) {
                    let (fs, _) = self.program.type_size_align(*fty)?;
                    vals.push(self.bits_to_value(&slice(off, fs), *fty)?);
                }
                Ok(Value::Struct { ty, fields: vals })
            }
            Type::Array { elem, len } => {
                let (es, _) = self.program.type_size_align(elem)?;
                let mut vals = Vec::with_capacity(len as usize);
                for i in 0..len {
                    vals.push(self.bits_to_value(&slice(i * es, es), elem)?);
                }
                Ok(Value::Array(vals))
            }
            other => Err(format!(
                "'@transmute' to {other} is not supported during compile-time evaluation"
            )),
        }
    }

    /// `(bits, unsigned)` of an integer-like type (`isize`-like `i64` for anything else).
    fn int_width(ty: &Type) -> (u32, bool) {
        match ty {
            Type::Int { signed, bits } => (u32::from(*bits), !signed),
            Type::Rune => (32, true),
            _ => (64, false),
        }
    }

    pub(crate) fn wrap_int_to_bits(val: i128, bits: u32, unsigned: bool) -> i128 {
        if bits >= 128 {
            return val;
        }
        let mask: u128 = (1u128 << bits) - 1;
        let raw = (val as u128) & mask;
        if unsigned {
            raw as i128
        } else {
            let sign_bit = 1u128 << (bits - 1);
            if (raw & sign_bit) != 0 {
                (raw | !mask) as i128
            } else {
                raw as i128
            }
        }
    }

    pub(crate) fn bswap_int(val: i128, bits: u32, unsigned: bool) -> i128 {
        let byte_count = (bits / 8) as usize;
        if byte_count <= 1 {
            return Self::wrap_int_to_bits(val, bits, unsigned);
        }
        let raw = val as u128;
        let mut swapped = 0u128;
        for i in 0..byte_count {
            let b = (raw >> (i * 8)) & 0xFF;
            swapped |= b << ((byte_count - 1 - i) * 8);
        }
        Self::wrap_int_to_bits(swapped as i128, bits, unsigned)
    }

    fn eval_scalar_binop(
        inferred_ty: &Type,
        binop: BinOp,
        l_val: Value,
        r_val: Value,
    ) -> Result<Value, String> {
        // Integers use the exact semantics of compile-time folding (`wide::apply_binop`):
        // overflow, division, and shift-amount errors, wrapping and saturating operators.
        let (bits, unsigned) = Self::int_width(inferred_ty);
        let as_wide = |v: &Value| match v {
            Value::Int(n) => Some(Wide::from_i128(*n)),
            Value::Wide(w) => Some(**w),
            _ => None,
        };
        // A `bool` read as its storage byte (the C-value checks of export wrappers) compares
        // as 0 / 1.
        let byte = |v: Value, other: &Value| match v {
            Value::Bool(b) if matches!(other, Value::Int(_)) => Value::Int(i128::from(b)),
            v => v,
        };
        let l_val = byte(l_val, &r_val);
        let r_val = byte(r_val, &l_val);
        let (l_val, r_val) = match (as_wide(&l_val), as_wide(&r_val)) {
            (Some(l), Some(r)) => {
                // Older code paths may hold a `u128` as its `i128` bit pattern: normalize.
                let width = u16::try_from(bits).unwrap_or(512);
                let l = l.wrap(width, !unsigned);
                let r = r.wrap(width, !unsigned);
                return match crate::wide::apply_binop(binop, &l, &r, width, !unsigned)
                    .map_err(|e| format!("{e} (for type '{inferred_ty}')"))?
                {
                    crate::wide::BinResult::Bool(b) => Ok(Value::Bool(b)),
                    crate::wide::BinResult::Int(v) => Ok(Value::from_wide(v)),
                };
            }
            _ => (l_val, r_val),
        };
        match (l_val, r_val) {
            (Value::Float(ab), Value::Float(bb)) => {
                let a = f64::from_bits(ab);
                let b = f64::from_bits(bb);
                match binop {
                    BinOp::Add => Ok(Value::from_f64(a + b)),
                    BinOp::Sub => Ok(Value::from_f64(a - b)),
                    BinOp::Mul => Ok(Value::from_f64(a * b)),
                    BinOp::Div => Ok(Value::from_f64(a / b)),
                    BinOp::Rem => Ok(Value::from_f64(a % b)),
                    BinOp::Eq => Ok(Value::Bool(a == b)),
                    BinOp::Ne => Ok(Value::Bool(a != b)),
                    BinOp::Lt => Ok(Value::Bool(a < b)),
                    BinOp::Le => Ok(Value::Bool(a <= b)),
                    BinOp::Gt => Ok(Value::Bool(a > b)),
                    BinOp::Ge => Ok(Value::Bool(a >= b)),
                    _ => Err(format!("Unsupported BinOp {binop} on float")),
                }
            }
            (Value::Bool(a), Value::Bool(b)) => match binop {
                BinOp::BitAnd => Ok(Value::Bool(a & b)),
                BinOp::BitOr => Ok(Value::Bool(a | b)),
                BinOp::BitXor => Ok(Value::Bool(a ^ b)),
                BinOp::Eq => Ok(Value::Bool(a == b)),
                BinOp::Ne => Ok(Value::Bool(a != b)),
                _ => Err(format!("Unsupported BinOp {binop} on bool")),
            },
            (Value::Type(a), Value::Type(b)) => match binop {
                BinOp::Eq => Ok(Value::Bool(a == b)),
                BinOp::Ne => Ok(Value::Bool(a != b)),
                _ => Err(format!("Unsupported BinOp {binop} on type")),
            },
            (l, r) => Err(format!("Invalid operands for {binop}: {l:?} and {r:?}")),
        }
    }

    fn eval_rvalue(
        &mut self,
        func: &Function,
        rvalue: &Rvalue,
        dest_ty: TypeId,
    ) -> Result<Value, String> {
        match rvalue {
            Rvalue::Use(op) => {
                if let Operand::Const(cv) = op
                    && !matches!(cv, ConstValue::Global(_))
                {
                    Ok(Self::const_to_val_typed(cv, dest_ty, &self.program.types))
                } else {
                    self.eval_operand(op)
                }
            }
            Rvalue::UnaryOp(unop, op) => {
                let val = self.eval_operand(op)?;
                let dst_ty = self
                    .program
                    .types
                    .get(dest_ty.0 as usize)
                    .cloned()
                    .unwrap_or(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                let resolved_dst_ty = match &dst_ty {
                    Type::Pattern { base, .. } => self
                        .program
                        .types
                        .get(base.0 as usize)
                        .cloned()
                        .unwrap_or(dst_ty),
                    _ => dst_ty,
                };
                let (bits, unsigned) = Self::int_width(&resolved_dst_ty);
                match (unop, val) {
                    (UnOp::Neg, Value::Int(n)) => Ok(Value::Int(n.wrapping_neg())),
                    (UnOp::Neg, Value::Float(bits)) => Ok(Value::from_f64(-f64::from_bits(bits))),
                    (UnOp::Not, Value::Int(n)) => Ok(Value::Int(!n)),
                    (UnOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
                    (UnOp::Bswap, Value::Int(n)) => {
                        Ok(Value::Int(Self::bswap_int(n, bits, unsigned)))
                    }
                    (u, Value::Array(elems)) => {
                        let mut out = Vec::with_capacity(elems.len());
                        for e in elems {
                            let v = match (u, e) {
                                (UnOp::Neg, Value::Int(n)) => Value::Int(n.wrapping_neg()),
                                (UnOp::Neg, Value::Float(bits)) => {
                                    Value::from_f64(-f64::from_bits(bits))
                                }
                                (UnOp::Not, Value::Int(n)) => Value::Int(!n),
                                (UnOp::Not, Value::Bool(b)) => Value::Bool(!b),
                                (UnOp::Bswap, Value::Int(n)) => {
                                    Value::Int(Self::bswap_int(n, bits, unsigned))
                                }
                                (u, v) => {
                                    return Err(format!("Unsupported SIMD unary op {u} on {v:?}"));
                                }
                            };
                            out.push(v);
                        }
                        Ok(Value::Array(out))
                    }
                    (u, v) => Err(format!("Unsupported unary op {u} on {v:?}")),
                }
            }
            Rvalue::BinaryOp(binop, lhs, rhs) => {
                let l_val = self.eval_operand(lhs)?;
                let r_val = self.eval_operand(rhs)?;

                // Byte arithmetic, as `&rel` fields resolve to a pointer into their value.
                if *binop == BinOp::AddWrap
                    && let (Value::Ptr { .. }, Value::Int(n)) = (&l_val, &r_val)
                    && let Some(Type::Ptr { pointee, .. }) = self.program.types.get(dest_ty.0 as usize)
                {
                    let (n, pointee) = (*n, *pointee);
                    let addr = self.expose(l_val) + n;
                    return self.unexpose(addr, pointee).ok_or_else(|| {
                        format!("{UB_PREFIX}pointer arithmetic left the allocation")
                    });
                }

                if matches!(
                    binop,
                    BinOp::AddChecked | BinOp::SubChecked | BinOp::MulChecked
                ) {
                    let payload_ty_id = match self.program.types.get(dest_ty.0 as usize) {
                        Some(Type::Union { variants, .. }) if variants.len() == 2 => variants[1],
                        _ => dest_ty,
                    };
                    let inferred_ty_id = self
                        .operand_type(func, lhs)?
                        .or(self.operand_type(func, rhs)?)
                        .unwrap_or(payload_ty_id);
                    let raw_ty = self
                        .program
                        .types
                        .get(inferred_ty_id.0 as usize)
                        .cloned()
                        .unwrap_or(Type::Int {
                            signed: true,
                            bits: 64,
                        });
                    let inferred_ty = match &raw_ty {
                        Type::Pattern { base, .. } => self
                            .program
                            .types
                            .get(base.0 as usize)
                            .cloned()
                            .unwrap_or(raw_ty),
                        _ => raw_ty,
                    };
                    let checked_op = match binop {
                        BinOp::AddChecked => BinOp::Add,
                        BinOp::SubChecked => BinOp::Sub,
                        BinOp::MulChecked => BinOp::Mul,
                        _ => unreachable!(),
                    };
                    return match Self::eval_scalar_binop(&inferred_ty, checked_op, l_val, r_val) {
                        Ok(val) => Ok(Value::Union {
                            ty: dest_ty,
                            variant: 1,
                            payload: Box::new(val),
                        }),
                        Err(_) => Ok(Value::Union {
                            ty: dest_ty,
                            variant: 0,
                            payload: Box::new(Value::Void),
                        }),
                    };
                }

                let inferred_ty_id = self
                    .operand_type(func, lhs)?
                    .or(self.operand_type(func, rhs)?)
                    .unwrap_or(dest_ty);
                let raw_ty = self
                    .program
                    .types
                    .get(inferred_ty_id.0 as usize)
                    .cloned()
                    .unwrap_or(Type::Int {
                        signed: true,
                        bits: 64,
                    });
                let inferred_ty = match &raw_ty {
                    Type::Pattern { base, .. } => self
                        .program
                        .types
                        .get(base.0 as usize)
                        .cloned()
                        .unwrap_or(raw_ty),
                    _ => raw_ty,
                };

                if let (Value::Array(l_elems), Value::Array(r_elems)) = (&l_val, &r_val) {
                    if l_elems.len() != r_elems.len() {
                        return Err(format!(
                            "SIMD vector lane length mismatch: {} vs {}",
                            l_elems.len(),
                            r_elems.len()
                        ));
                    }
                    let elem_ty = match &inferred_ty {
                        Type::Simd { elem, .. } | Type::Array { elem, .. } => self
                            .program
                            .types
                            .get(elem.0 as usize)
                            .cloned()
                            .unwrap_or(Type::Int {
                                signed: true,
                                bits: 64,
                            }),
                        other => other.clone(),
                    };
                    let mut out = Vec::with_capacity(l_elems.len());
                    for (le, re) in l_elems.iter().cloned().zip(r_elems.iter().cloned()) {
                        out.push(Self::eval_scalar_binop(&elem_ty, *binop, le, re)?);
                    }
                    return Ok(Value::Array(out));
                }

                if let Type::Ptr { pointee, .. } = inferred_ty
                    && matches!(binop, BinOp::Add | BinOp::Sub)
                {
                    if let Ok((0, _)) = self.program.type_size_align(pointee) {
                        return Ok(l_val);
                    }
                    if let (
                        Value::Ptr {
                            target,
                            projections,
                            ..
                        },
                        Value::Int(off),
                    ) = (&l_val, &r_val)
                    {
                        let mut projections = projections.clone();
                        let delta = if *binop == BinOp::Sub { -*off } else { *off };
                        if delta == 0 {
                            return Ok(Value::Ptr {
                                target: target.clone(),
                                projections,
                                tag: Tag::default(),
                            });
                        }
                        if let Some(ResolvedProj::Index(idx)) = projections.last_mut() {
                            let next = (*idx as i128) + delta;
                            if next < 0 {
                                return Err(format!("Negative pointer index {next}"));
                            }
                            *idx = next as usize;
                            return Ok(Value::Ptr {
                                target: target.clone(),
                                projections,
                                tag: Tag::default(),
                            });
                        }
                    }
                }

                Self::eval_scalar_binop(&inferred_ty, *binop, l_val, r_val)
            }
            Rvalue::Transmute(op, target_ty_id)
                if self.operand_type(func, op)?.is_some() =>
            {
                // Bitwise reinterpretation with the compiled layout (see `value_to_bits`).
                let src_ty = self.operand_type(func, op)?.expect("checked above");
                let val = self.eval_operand(op)?;
                let bits = self.value_to_bits(&val, src_ty)?;
                self.bits_to_value(&bits, *target_ty_id)
            }
            Rvalue::Cast(op, target_ty_id) | Rvalue::Transmute(op, target_ty_id) => {
                let mut val = self.eval_operand(op)?;
                if let Value::Ptr { tag, .. } = &mut val
                    && self.is_raw_ptr_type(*target_ty_id)
                {
                    *tag = Tag(0);
                }
                let dst_ty = self
                    .program
                    .types
                    .get(target_ty_id.0 as usize)
                    .ok_or_else(|| format!("Undefined type {target_ty_id}"))?;
                let resolved_dst_ty = match dst_ty {
                    Type::Pattern { base, .. } => {
                        self.program.types.get(base.0 as usize).unwrap_or(dst_ty)
                    }
                    other => other,
                };
                match (val, resolved_dst_ty) {
                    (Value::Int(n), Type::F32 | Type::F64) => Ok(Value::from_f64(n as f64)),
                    (Value::Wide(w), Type::F32 | Type::F64) => {
                        Ok(Value::from_f64(w.to_string().parse::<f64>().unwrap_or(0.0)))
                    }
                    // Saturating float-to-int conversion (NaN converts to 0), as in compiled code.
                    (Value::Float(fbits), Type::Int { signed, bits }) => {
                        let f = f64::from_bits(fbits);
                        let truncated = if f.is_nan() {
                            crate::wide::Wide::ZERO
                        } else {
                            // Exact integer part (beyond `i128` for wide targets); values past
                            // the representable range saturate below.
                            let mag = crate::wide::Wide::from_str_radix(
                                &format!("{:.0}", f.trunc().abs()),
                                10,
                            )
                            .unwrap_or(crate::wide::Wide::max_value(1024, false));
                            if f < 0.0 { mag.neg() } else { mag }
                        };
                        Ok(Value::from_wide(
                            truncated
                                .max(crate::wide::Wide::min_value(*bits, *signed))
                                .min(crate::wide::Wide::max_value(*bits, *signed)),
                        ))
                    }
                    (Value::Float(bits), Type::Rune) => {
                        Ok(Value::Int((f64::from_bits(bits) as u32).into()))
                    }
                    (Value::Float(bits), Type::F32) => {
                        Ok(Value::from_f64(f64::from_bits(bits) as f32 as f64))
                    }
                    (Value::Float(bits), Type::F64) => Ok(Value::Float(bits)),
                    (Value::Bool(b), _) => Ok(Value::Int(i128::from(b))),
                    (Value::Int(n), Type::Bool) => Ok(Value::Bool(n != 0)),
                    (Value::Int(n), Type::Int { signed, bits }) => Ok(Value::from_wide(
                        crate::wide::Wide::from_i128(n).wrap(*bits, *signed),
                    )),
                    (Value::Wide(w), Type::Int { signed, bits }) => {
                        Ok(Value::from_wide(w.wrap(*bits, *signed)))
                    }
                    (Value::Wide(w), Type::Bool) => Ok(Value::Bool(!w.is_zero())),
                    (Value::Int(n), &Type::Ptr { pointee, .. })
                        if self.unexpose(n, pointee).is_some() =>
                    {
                        Ok(self.unexpose(n, pointee).expect("checked above"))
                    }
                    (Value::Int(n), _) => Ok(Value::Int(n)),
                    (
                        Value::Ptr {
                            target,
                            projections,
                            ..
                        },
                        &Type::Ptr { pointee, .. },
                    ) => {
                        let ptr = Value::Ptr {
                            target,
                            projections,
                            tag: Tag::default(),
                        };
                        self.retype_heap_block(&ptr, pointee)?;
                        Ok(ptr)
                    }
                    (Value::Str(s), Type::Ptr { .. }) => Ok(Value::Str(s)),
                    (
                        Value::Ptr {
                            target: PtrTarget::Dangling { addr, .. },
                            ..
                        },
                        Type::Int { signed, bits },
                    ) => Ok(Value::from_wide(
                        crate::wide::Wide::from_i128(addr).wrap(*bits, *signed),
                    )),
                    (ptr @ Value::Ptr { .. }, Type::Int { signed, bits }) => {
                        let (signed, bits) = (*signed, *bits);
                        let addr = self.expose(ptr);
                        Ok(Value::from_wide(crate::wide::Wide::from_i128(addr).wrap(bits, signed)))
                    }
                    (v, t) => Err(format!("Cannot cast {v:?} to {t}")),
                }
            }
            Rvalue::Ref { mutable, place } => {
                // Zig-style comptime: if the destination has type `type` (`MetaType`) and `place` holds a `Value::Type`,
                // `&place` / `&mut place` constructs a pointer TYPE `&T` / `&mut T`!
                if matches!(
                    self.program.types.get(dest_ty.0 as usize),
                    Some(Type::MetaType)
                ) {
                    let val = self.read_place(place, false)?;
                    if let Value::Type(pointee) = val {
                        let ptr_ty = self.program.intern_type(Type::Ptr {
                            mutable: *mutable,
                            pointee,
                        });
                        return Ok(Value::Type(ptr_ty));
                    }
                }
                let (target, projections) = self.resolve_place(place)?;
                let tag = self.retag(&target, &projections, *mutable, dest_ty);
                Ok(Value::Ptr {
                    target,
                    projections,
                    tag,
                })
            }
            Rvalue::Aggregate(agg_ty, ops) => {
                let mut vals = Vec::with_capacity(ops.len());
                for op in ops {
                    vals.push(self.eval_operand(op)?);
                }

                // Zig-style comptime: if `agg_ty` is `Type::MetaType` (`type`), aggregating `Value::Type`s
                // constructs and interns a new `Type::Struct(...)` in `Program`!
                match self.program.types.get(agg_ty.0 as usize) {
                    Some(Type::MetaType) => {
                        let mut field_types = Vec::with_capacity(vals.len());
                        for v in vals {
                            let Value::Type(ft) = v else {
                                return Err(format!(
                                    "Comptime struct type aggregate expected type operands, got {v:?}"
                                ));
                            };
                            field_types.push(ft);
                        }
                        let new_struct_ty = self.program.intern_type(Type::Struct(field_types));
                        Ok(Value::Type(new_struct_ty))
                    }
                    Some(Type::Array { elem, .. }) => {
                        for v in &mut vals {
                            if matches!(v, Value::Void) {
                                *v = Self::uninit_value_for_type(self.program, *elem);
                            }
                        }
                        Ok(Value::Array(vals))
                    }
                    Some(Type::Int { bits: 256, .. }) => Ok(Value::Array(vals)),
                    Some(Type::Simd { len, .. }) => {
                        if vals.len() == 1 && *len > 1 {
                            Ok(Value::Array(vec![vals[0].clone(); *len as usize]))
                        } else {
                            Ok(Value::Array(vals))
                        }
                    }
                    Some(Type::Struct(ftys)) => {
                        let ftys = ftys.clone();
                        for (v, fty) in vals.iter_mut().zip(ftys) {
                            if matches!(v, Value::Void) {
                                *v = Self::uninit_value_for_type(self.program, fty);
                            }
                        }
                        Ok(Value::Struct {
                            ty: *agg_ty,
                            fields: vals,
                        })
                    }
                    _ => Ok(Value::Struct {
                        ty: *agg_ty,
                        fields: vals,
                    }),
                }
            }
            Rvalue::Union {
                ty,
                variant,
                payload,
            } => {
                let p_val = self.eval_operand(payload)?;
                Ok(Value::Union {
                    ty: *ty,
                    variant: *variant,
                    payload: Box::new(p_val),
                })
            }
            Rvalue::Discriminant(place) => {
                let val = self.read_place(place, false)?;
                let Value::Union { variant, .. } = val else {
                    return Err(format!(
                        "Cannot read discriminant of non-union value {val:?}"
                    ));
                };
                Ok(Value::Int(i128::from(variant)))
            }
            Rvalue::ArrayType { elem, len } => {
                let elem_val = self.eval_operand(elem)?;
                let len_val = self.eval_operand(len)?;
                let Value::Type(elem_ty) = elem_val else {
                    return Err(format!(
                        "Comptime array type constructor expected type for element, got {elem_val:?}"
                    ));
                };
                let Value::Int(n) = len_val else {
                    return Err(format!(
                        "Comptime array type constructor expected integer for length, got {len_val:?}"
                    ));
                };
                if n < 0 {
                    return Err(format!("Comptime array length cannot be negative ({n})"));
                }
                let arr_ty = self.program.intern_type(Type::Array {
                    elem: elem_ty,
                    len: n as u64,
                });
                Ok(Value::Type(arr_ty))
            }
            Rvalue::SimdType { elem, len } => {
                let elem_val = self.eval_operand(elem)?;
                let len_val = self.eval_operand(len)?;
                let Value::Type(elem_ty) = elem_val else {
                    return Err(format!(
                        "Comptime SIMD type constructor expected type for element, got {elem_val:?}"
                    ));
                };
                let Value::Int(n) = len_val else {
                    return Err(format!(
                        "Comptime SIMD type constructor expected integer for lane count, got {len_val:?}"
                    ));
                };
                if n <= 0 {
                    return Err(format!("Comptime SIMD lane count must be positive ({n})"));
                }
                let simd_ty = self.program.intern_type(Type::Simd {
                    elem: elem_ty,
                    len: n as u64,
                });
                Ok(Value::Type(simd_ty))
            }
            Rvalue::OverlayType(ops) => {
                let mut field_types = Vec::with_capacity(ops.len());
                for op in ops {
                    let v = self.eval_operand(op)?;
                    let Value::Type(ft) = v else {
                        return Err(format!(
                            "Comptime overlay type constructor expected type operands, got {v:?}"
                        ));
                    };
                    field_types.push(ft);
                }
                let overlay_ty = self.program.intern_type(Type::Overlay(field_types));
                Ok(Value::Type(overlay_ty))
            }
            Rvalue::UnionType { tag, variants } => {
                let tag_val = self.eval_operand(tag)?;
                let Value::Type(tag_ty) = tag_val else {
                    return Err(format!(
                        "Comptime union type constructor expected type for tag, got {tag_val:?}"
                    ));
                };
                let mut var_types = Vec::with_capacity(variants.len());
                for op in variants {
                    let v = self.eval_operand(op)?;
                    let Value::Type(vt) = v else {
                        return Err(format!(
                            "Comptime union type constructor expected type operands for variants, got {v:?}"
                        ));
                    };
                    var_types.push(vt);
                }
                let union_ty = self.program.intern_type(Type::Union {
                    tag: tag_ty,
                    variants: var_types,
                });
                Ok(Value::Type(union_ty))
            }
            Rvalue::PatternType { base, ranges } => {
                let base_val = self.eval_operand(base)?;
                let Value::Type(base_ty) = base_val else {
                    return Err(format!(
                        "Comptime pattern type constructor expected base integer type, got {base_val:?}"
                    ));
                };
                let mut eval_ranges = Vec::with_capacity(ranges.len());
                for (lo_op, hi_op) in ranges {
                    let lo_val = self.eval_operand(lo_op)?;
                    let hi_val = self.eval_operand(hi_op)?;
                    let as_wide = |v: Value| match v {
                        Value::Int(n) => Some(Wide::from_i128(n)),
                        Value::Wide(w) => Some(*w),
                        _ => None,
                    };
                    let (Some(lo), Some(hi)) = (as_wide(lo_val), as_wide(hi_val)) else {
                        return Err(
                            "Comptime pattern type constructor expected integer range bounds"
                                .to_string(),
                        );
                    };
                    if lo > hi {
                        return Err(format!(
                            "Invalid pattern range {lo}..={hi}: lower bound exceeds upper bound"
                        ));
                    }
                    eval_ranges.push((lo, hi));
                }
                let pat_ty = self.program.intern_type(Type::Pattern {
                    base: base_ty,
                    ranges: eval_ranges,
                });
                Ok(Value::Type(pat_ty))
            }
        }
    }
}
