//! Bundled `core` (freestanding) and `std` (hosted) standard library modules and preludes.

pub const CORE_MEM_SRC: &str = "\
pub fn swap[T](a: &mut T, b: &mut T) borrows(a: b, b: a) {
    unsafe {
        let pa: *mut T = a as *mut T;
        let pb: *mut T = b as *mut T;
        let tmp = move *pa;
        *pa = move *pb;
        *pb = move tmp;
    }
}

pub fn replace[T](dest: &mut T, src: T) -> T borrows(*dest, dest: src) {
    unsafe {
        let p: *mut T = dest as *mut T;
        let old = move *p;
        *p = move src;
        return old;
    }
}
";

pub const CORE_CMP_SRC: &str = "\
pub fn min[N: number](a: N, b: N) -> N {
    if a < b {
        return a;
    }
    return b;
}

pub fn max[N: number](a: N, b: N) -> N {
    if a > b {
        return a;
    }
    return b;
}

pub fn clamp[N: number](self: N, lo: N, hi: N) -> N {
    if self < lo {
        return lo;
    }
    if self > hi {
        return hi;
    }
    return self;
}
";

pub const CORE_MATH_SRC: &str = "\
pub fn abs[S: signed](self: S) -> S {
    if self < 0 {
        return -self;
    }
    return self;
}

pub fn abs[F: float](self: F) -> F {
    if self < 0.0 {
        return -self;
    }
    return self;
}
";

pub const CORE_SLICE_SRC: &str = "\
pub fn is_empty[S: sequence](self: &S) -> bool {
    return self.len == 0;
}

pub fn first[T: copy](self: &[T]) -> ?T borrows(*self) {
    if self.len == 0 {
        return null;
    }
    return self[0];
}

pub fn last[T: copy](self: &[T]) -> ?T borrows(*self) {
    if self.len == 0 {
        return null;
    }
    return self[self.len - 1];
}
";

pub const CORE_OPTION_SRC: &str = "\
pub fn is_some[T](self: ?T) -> bool {
    if let _v = self {
        return true;
    }
    return false;
}

pub fn is_none[T](self: ?T) -> bool {
    if let _v = self {
        return false;
    }
    return true;
}
";

pub const CORE_FMT_SRC: &str = "\
pub opaque Formatter {
    buf: *mut u8,
    len: usize,
    cap: usize,
    /// What would have been written with room for it.
    wanted: usize,

    pub unsafe fn new(buf: *mut u8, cap: usize) -> Self {
        return Self {
            buf: buf,
            len: 0,
            cap: cap,
            wanted: 0,
        };
    }

    pub fn len(self: &Self) -> usize {
        return self.len;
    }

    pub fn is_truncated(self: &Self) -> bool {
        return self.wanted > self.cap;
    }

    /// The buffer size that would have held everything.
    pub fn wanted(self: &Self) -> usize {
        return self.wanted;
    }

    pub fn write_byte(self: &mut Self, b: u8) {
        self.wanted = self.wanted +% 1;
        if self.len < self.cap {
            let addr: usize = (self.buf as usize) +% self.len;
            let dst: *mut u8 = addr as *mut u8;
            unsafe {
                *dst = b;
            }
            self.len = self.len +% 1;
        }
    }

    pub fn write_str(self: &mut Self, s: &str) {
        let mut i: usize = 0;
        let n: usize = s.len;
        while i < n {
            self.write_byte(s[i]);
            i = i +% 1;
        }
    }

    pub fn write_quoted_str(self: &mut Self, s: &str) {
        self.write_byte(34);
        self.write_str(s);
        self.write_byte(34);
    }

    pub fn write_bool(self: &mut Self, val: bool) {
        if val {
            self.write_str(\"true\");
        } else {
            self.write_str(\"false\");
        }
    }

    pub fn write_rune(self: &mut Self, r: rune, quoted: bool) {
        if quoted {
            self.write_byte(39);
        }
        let cp: u32 = r as u32;
        if cp <= 0x7F {
            self.write_byte(cp as u8);
        } else if cp <= 0x7FF {
            self.write_byte(((cp >> 6) | 0xC0) as u8);
            self.write_byte(((cp & 0x3F) | 0x80) as u8);
        } else if cp <= 0xFFFF {
            self.write_byte(((cp >> 12) | 0xE0) as u8);
            self.write_byte((((cp >> 6) & 0x3F) | 0x80) as u8);
            self.write_byte(((cp & 0x3F) | 0x80) as u8);
        } else {
            self.write_byte(((cp >> 18) | 0xF0) as u8);
            self.write_byte((((cp >> 12) & 0x3F) | 0x80) as u8);
            self.write_byte((((cp >> 6) & 0x3F) | 0x80) as u8);
            self.write_byte(((cp & 0x3F) | 0x80) as u8);
        }
        if quoted {
            self.write_byte(39);
        }
    }

    pub fn write_int(
        self: &mut Self,
        val: i64,
        is_signed: bool,
        radix: u64,
        uppercase: bool,
        min_width: usize,
        pad_zero: bool
    ) {
        let mut neg: bool = false;
        let mut mag: u64 = val as u64;
        if is_signed && val < 0 {
            neg = true;
            let z: i64 = 0;
            mag = (z -% val) as u64;
        }
        let mut digits: [u8; 64] = @default([u8; 64]);
        let mut count: usize = 0;
        if mag == 0 {
            digits[0] = 48;
            count = 1;
        } else {
            while mag > 0 {
                let rem: u8 = (mag % radix) as u8;
                let mut ch: u8 = rem +% 87;
                if rem < 10 {
                    ch = rem +% 48;
                } else if uppercase {
                    ch = rem +% 55;
                }
                digits[count] = ch;
                count = count +% 1;
                mag = mag / radix;
            }
        }
        let mut total_len: usize = count;
        if neg {
            total_len = count +% 1;
        }
        if !pad_zero {
            let mut pad: usize = total_len;
            while pad < min_width {
                self.write_byte(32);
                pad = pad +% 1;
            }
        }
        if neg {
            self.write_byte(45);
        }
        if pad_zero {
            let mut pad: usize = total_len;
            while pad < min_width {
                self.write_byte(48);
                pad = pad +% 1;
            }
        }
        let mut idx: usize = count;
        while idx > 0 {
            idx = idx -% 1;
            self.write_byte(digits[idx]);
        }
    }

    pub fn write_f64(self: &mut Self, val: f64, precision: usize) {
        let mut v: f64 = val;
        if v < 0.0 {
            self.write_byte(45);
            v = -v;
        }
        let int_part: i64 = v as i64;
        self.write_int(int_part, false, 10, false, 0, false);
        if precision > 0 {
            self.write_byte(46);
            let mut frac: f64 = v - (int_part as f64);
            let mut p: usize = 0;
            while p < precision {
                frac = frac * 10.0;
                let d: u8 = (frac as i64) as u8;
                self.write_byte(d +% 48);
                frac = frac - ((d as i64) as f64);
                p = p +% 1;
            }
        }
    }

    pub fn write[T: format](self: &mut Self, val: T) {
        @format(self, val);
    }
}

pub fn str_eq(a: &str, b: &str) -> bool {
    if a.len != b.len {
        return false;
    }
    let mut i: usize = 0;
    while i < a.len {
        if a[i] != b[i] {
            return false;
        }
        i = i +% 1;
    }
    return true;
}

pub fn fmt_slice[T: format](buf: &mut [u8], val: T) -> &str borrows(buf) {
    let cap: usize = buf.len;
    let mut ptr: *mut u8 = 0 as *mut u8;
    if cap > 0 {
        ptr = &mut buf[0] as *mut u8;
    }
    let mut f = unsafe { Formatter::new(ptr, cap) };
    @format(&mut f, val);
    let n: usize = f.len();
    return buf[0..n];
}

pub fn fmt_buf[N: usize, T: format](buf: &mut [u8; N], val: T) -> &str borrows(buf) {
    let s: &mut [u8] = buf;
    return fmt_slice(s, val);
}
";

pub const CORE_META_SRC: &str = "\
pub struct FieldSpec {
    pub name: &str,
    pub ty: type,
}

pub struct EnumSpec {
    pub name: &str,
    pub value: i64,
}

pub struct UnionSpec {
    pub name: &str,
    pub payload: type = void,
}

pub struct ErrorSpec {
    pub name: &str,
    pub payload: type = void,
}

pub struct StructField {
    pub name: &str,
    pub ty: type,
    pub offset: usize,
    pub has_default: bool,
}

pub struct TupleField {
    pub name: &str,
    pub index: usize,
    pub ty: type,
    pub offset: usize,
}

pub struct OverlayField {
    pub name: &str,
    pub ty: type,
}

pub struct EnumVariant[T: enum] {
    pub name: &str,
    pub value: @backing_type(T),
    pub val: T,
}

pub struct UnionVariant[T: union] {
    pub name: &str,
    pub payload: type,
    pub tag: T::Tag,
}

pub struct ErrorVariant {
    pub error_name: &str,
    pub name: &str,
    pub payload: type,
}

pub struct FnInfo {
    pub params: &[type],
    pub ret: type,
}

pub fn TupleConcat[A, B] -> type {
    comptime let a = @fields(A);
    comptime let b = @fields(B);
    comptime let mut out: [type; a.len + b.len] = uninit;
    comptime for (f, i) in a { out[i] = f.ty; }
    comptime for (f, i) in b { out[a.len + i] = f.ty; }
    return @Tuple(&out);
}

pub fn TupleTake[T, N: usize] -> type {
    if N == 0 || N > @fields(T).len {
        return @compile_error(\"TupleTake: cannot take \", N, \" elements of \", T);
    } else {
        comptime let mut out: [type; N] = uninit;
        comptime for (f, i) in @fields(T) {
            if i < N { out[i] = f.ty; }
        }
        return @Tuple(&out);
    }
}

pub fn TupleSkip[T, N: usize] -> type {
    if N >= @fields(T).len {
        return @compile_error(\"TupleSkip: skipping \", N, \" elements of \", T, \" leaves none\");
    } else {
        comptime let src = @fields(T);
        comptime let mut out: [type; src.len - N] = uninit;
        comptime for (f, i) in src {
            if i >= N { out[i - N] = f.ty; }
        }
        return @Tuple(&out);
    }
}

pub fn tuple_concat[A: unchecked, B: unchecked](move a: A, move b: B) -> TupleConcat[A, B] {
    let mut out: TupleConcat[A, B];
    comptime for f in @fields(A) { @field(out, f.index) = move @field(a, f.index); }
    comptime for f in @fields(B) { @field(out, @fields(A).len + f.index) = move @field(b, f.index); }
    return out;
}

pub fn tuple_split[N: usize, T: unchecked](move t: T) -> tuple { TupleTake[T, N], TupleSkip[T, N] } {
    let mut head: TupleTake[T, N];
    let mut tail: TupleSkip[T, N];
    comptime for f in @fields(T) {
        if f.index < N {
            @field(head, f.index) = move @field(t, f.index);
        } else {
            @field(tail, f.index - N) = move @field(t, f.index);
        }
    }
    return { head, tail };
}

pub fn FieldAt[T, P: &[&str]] -> type {
    if P.len == 0 { return T; }
    comptime for f in @fields(T) {
        if f.name == P[0] { return FieldAt[f.ty, P[1..P.len]]; }
    }
    return @compile_error(\"FieldAt: \", T, \" has no field \", P[0]);
}
";

pub const CORE_PRELUDE_SRC: &str = "\
pub import core::mem::{swap, replace};
pub import core::cmp::{min, max, clamp};
pub import core::math::abs;
pub import core::slice::{is_empty, first, last};
pub import core::option::{is_some, is_none};
pub import core::fmt::{Formatter, str_eq, fmt_slice, fmt_buf};
pub import core::meta::{FieldSpec, EnumSpec, UnionSpec, ErrorSpec, StructField, TupleField, OverlayField, EnumVariant, UnionVariant, ErrorVariant, FnInfo, TupleConcat, TupleTake, TupleSkip, FieldAt, tuple_concat, tuple_split};
";

pub const CORE_ROOT_SRC: &str = "\
pub import core::prelude::*;
";

pub const STD_MEM_SRC: &str = "\
/// The program's allocator, named by `alias ProgramAllocator = A;` in the root module. `@alloc`,
/// `@realloc`, and `@dealloc` then call `A`, and a null result traps, as it does for the default.
/// `A` has no instance, so a call is direct.
///
/// An implementation promises what `Allocator` does, which is why it is `unsafe impl`.
pub unsafe trait GlobalAllocator {
    fn alloc(bytes: usize, align: usize) -> *mut u8;
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8;
    fn dealloc(ptr: *mut u8);
}

/// What a container allocates through: `Vec[i32, A]` holds an `A`. A type with no fields costs
/// nothing there, and `&Pool` holds a reference, so the borrow checker keeps the container
/// inside the pool's lifetime.
///
/// Safe code trusts what this returns, so an implementation is `unsafe impl` and promises: a
/// non-null result is `bytes` long, aligned to `align`, and used by nothing else until it is given
/// back through `dealloc` (or moved by `realloc`, which keeps the contents up to the smaller
/// size); `realloc` and `dealloc` are given only pointers this allocator returned. Null means
/// there is no memory, and the containers trap on it.
pub unsafe trait Allocator {
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8;
    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8;
    fn dealloc(self: &Self, ptr: *mut u8);
}

/// The program's allocator, as a value. The default for every container.
pub struct Global { }

unsafe impl Allocator for Global {
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 {
        return @raw_alloc(bytes);
    }

    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        return unsafe { @realloc(u8, ptr, bytes) };
    }

    fn dealloc(self: &Self, ptr: *mut u8) {
        unsafe { @dealloc(ptr); }
    }
}

unsafe impl[A: Allocator] Allocator for &A {
    fn alloc(self: &Self, bytes: usize, align: usize) -> *mut u8 {
        return (**self).alloc(bytes, align);
    }

    fn realloc(self: &Self, ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 {
        return (**self).realloc(ptr, bytes, align);
    }

    fn dealloc(self: &Self, ptr: *mut u8) {
        (**self).dealloc(ptr);
    }
}

/// Room for `len` values of `T` from `allocator`. Traps on overflow or if it has no memory, and
/// a zero-sized `T` allocates nothing, as for `@alloc`.
pub fn alloc_in[T, A: Allocator](allocator: &A, len: usize) -> *mut T {
    if @size_of(T) == 0 {
        return (@align_of(T) as usize) as *mut T;
    }
    let bytes: usize = (len *? @size_of(T)) orelse @trap();
    let raw = allocator.alloc(bytes, @align_of(T));
    if (raw as usize) == 0 {
        @trap();
    }
    return raw as *mut T;
}

pub fn realloc_in[T, A: Allocator](allocator: &A, ptr: *mut T, len: usize) -> *mut T {
    if @size_of(T) == 0 {
        return ptr;
    }
    let bytes: usize = (len *? @size_of(T)) orelse @trap();
    let raw = allocator.realloc(ptr as *mut u8, bytes, @align_of(T));
    if (raw as usize) == 0 {
        @trap();
    }
    return raw as *mut T;
}

pub fn dealloc_in[T, A: Allocator](allocator: &A, ptr: *mut T) {
    if @size_of(T) != 0 {
        allocator.dealloc(ptr as *mut u8);
    }
}

pub safe extern fn malloc(size: usize) -> *mut u8;
pub extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
pub extern fn free(ptr: *mut u8);

pub import core::mem::*;

/// Fallible counterpart of `@alloc`: returns `null` instead of trapping when `len * size_of(T)`
/// overflows `usize` or the allocator is out of memory. For zero-sized `T`, returns the aligned
/// null-page pointer `@align_of(T) as *mut T` without allocating.
pub fn try_alloc[T](len: usize) -> ?*mut T {
    if @size_of(T) == 0 {
        return (@align_of(T) as usize) as *mut T;
    }
    let mut bytes: usize = (len *? @size_of(T)) orelse return null;
    if bytes == 0 {
        bytes = 1;
    }
    let raw: *mut u8 = @raw_alloc(bytes);
    if (raw as usize) == 0 {
        return null;
    }
    return raw as *mut T;
}

/// How deeply boxes of a recursive type drop inside each other before the rest waits, which
/// keeps a list of any length from overflowing the stack.
const DROP_LIMIT: usize = 128;

/// A box that was too deep to drop where it was, and how to drop it.
struct DeferredDrop {
    next: usize,
    run: fn(usize),
    value: usize,
}

/// The nesting of recursive drops, and the first `DeferredDrop`. Both belong to the fiber.
thread_local static mut DROP_DEPTH: usize = 0;
thread_local static mut DROP_QUEUE: usize = 0;

/// Sets `DROP_DEPTH` and `DROP_QUEUE` for a fiber taking over, and returns what they were.
pub fn swap_drop_state(depth: usize, queue: usize) -> tuple { usize, usize } {
    unsafe {
        let old: tuple { usize, usize } = { DROP_DEPTH, DROP_QUEUE };
        DROP_DEPTH = depth;
        DROP_QUEUE = queue;
        return old;
    }
}

/// Whether a recursive drop may go deeper here.
fn enter_drop() -> bool {
    unsafe {
        if DROP_DEPTH == DROP_LIMIT {
            return false;
        }
        DROP_DEPTH = DROP_DEPTH + 1;
    }
    return true;
}

fn defer_drop(run: fn(usize), value: usize) {
    unsafe {
        let entry: *mut DeferredDrop = @alloc(DeferredDrop, 1) as *mut DeferredDrop;
        *entry = DeferredDrop { next: DROP_QUEUE, run: run, value: value };
        DROP_QUEUE = entry as usize;
    }
}

/// Ends a recursive drop. The outermost runs what went deeper than `DROP_LIMIT`, staying
/// the outermost while it does, so those drops only add to the queue it is emptying.
fn leave_drop() {
    unsafe {
        if DROP_DEPTH > 1 {
            DROP_DEPTH = DROP_DEPTH - 1;
            return;
        }
        while DROP_QUEUE != 0 {
            let entry = DROP_QUEUE as *mut DeferredDrop;
            DROP_QUEUE = (*entry).next;
            let run = (*entry).run;
            let value = (*entry).value;
            @dealloc(entry);
            run(value);
        }
        DROP_DEPTH = 0;
    }
}

pub opaque Box[T, A: Allocator + copy = Global] {
    ptr: *own T,
    allocator: A,

    unsafe impl drop(may_dangle T) where T: !linear, T: !recursive {
        fn drop(self: &mut Self) {
            unsafe {
                @drop(self.ptr);
                dealloc_in[T, A](&self.allocator, self.ptr);
            }
        }
    }

    unsafe impl drop(may_dangle T) where T: !linear, T: recursive {
        fn drop(self: &mut Self) {
            unsafe {
                if !enter_drop() {
                    let later: *own Self = @alloc(Self, 1) as *own Self;
                    let ptr: *mut T = self.ptr;
                    *later = Self { ptr: ptr as *own T, allocator: self.allocator };
                    defer_drop(fn(kept: usize) {
                        unsafe {
                            let kept = kept as *own Self;
                            let boxed = move *kept;
                            @dealloc(kept);
                        }
                    }, later as usize);
                    return;
                }
                @drop(self.ptr);
                dealloc_in[T, A](&self.allocator, self.ptr);
                leave_drop();
            }
        }
    }

    unsafe impl drop(may_dangle T) where T: linear {
        fn drop(self: &mut Self) {
            unsafe {
                dealloc_in[T, A](&self.allocator, self.ptr);
            }
        }
    }

    pub fn into_inner(move self) -> T {
        unsafe {
            let p: *mut T = self.ptr;
            let val = move *p;
            dealloc_in[T, A](&self.allocator, p);
            @forget(self);
            return val;
        }
    }

    pub fn new(val: T) -> Self where A: default {
        return Self::new_in(move val, @default(A));
    }

    pub fn new_in(val: T, allocator: A) -> Self borrows(val, allocator) {
        let typed_ptr: *own T = unsafe { alloc_in[T, A](&allocator, 1) as *own T };
        unsafe {
            *typed_ptr = move val;
        }
        return Self {
            ptr: typed_ptr,
            allocator: allocator,
        };
    }

    pub fn get(self: &Self) -> &T {
        unsafe {
            return &*self.ptr;
        }
    }

    pub fn get_mut(self: &mut Self) -> &mut T {
        unsafe {
            return &mut *self.ptr;
        }
    }
}
";

pub const STD_SYNC_SRC: &str = "\
import std::mem::swap_drop_state;

/// Why a cancellable operation stopped.
pub error CancelError { Cancelled, TimedOut }

/// The address of the running task's innermost cancel scope, or 0.
thread_local static mut CURRENT_SCOPE: usize = 0;

pub fn ResultOf[F] -> type {
    comptime let info = @fn_info(F);
    return info.ret;
}

/// A region of work that can be cancelled, from any thread. Code inside finds it through the
/// task, not a parameter, and scopes nest: cancelling one cancels those inside it. Cancellation
/// is delivered as an error from `check_cancelled`, so what is live is consumed the normal way.
pub opaque(unsafe sync) CancelScope {
    cell flag: u32,
    cell parent: usize,
    /// Tasks started inside this scope that have not finished.
    cell live: u32,
    /// Absolute, in `now_ms` time. Nested scopes each keep their own, so the earliest on the
    /// path is what takes effect.
    cell deadline: i64,

    pub fn new() -> Self {
        return Self { flag: 0, parent: 0, live: 0, deadline: NO_DEADLINE };
    }

    /// A task's own scope, inside the scope at address `outer`.
    pub fn nested_in(outer: usize) -> Self {
        return Self { flag: 0, parent: outer, live: 0, deadline: NO_DEADLINE };
    }

    /// A scope that cancels itself `ms` milliseconds from now, reporting `.TimedOut`.
    pub fn with_timeout_ms(ms: i64) -> Self {
        return Self { flag: 0, parent: 0, live: 0, deadline: now_ms() + ms };
    }

    pub fn cancel(self: &Self) {
        unsafe { @atomic_store(&raw mut self.flag, 1); }
    }

    /// Why this scope has stopped, or one around it: 0 if it has not, 1 cancelled, 2 timed out.
    /// An explicit cancel is reported over a deadline.
    pub(mod) fn stop_reason(self: &Self) -> i32 {
        if unsafe { @atomic_load(&raw mut self.flag) } != 0 {
            return 1;
        }
        let up = unsafe { @atomic_load(&raw mut self.parent) };
        let mut above = 0;
        if up != 0 {
            above = unsafe { (*(up as *const CancelScope)).stop_reason() };
        }
        if above == 1 {
            return 1;
        }
        let deadline = unsafe { @atomic_load(&raw mut self.deadline) };
        if deadline != NO_DEADLINE && now_ms() >= deadline {
            return 2;
        }
        return above;
    }

    /// Whether this scope, or one around it, was cancelled or timed out.
    pub fn is_cancelled(self: &Self) -> bool {
        return self.stop_reason() != 0;
    }

    /// Runs `f` inside this scope.
    pub fn run[F: callable](self: &Self, f: F) -> ResultOf[F] {
        unsafe {
            let outer = CURRENT_SCOPE;
            @atomic_store(&raw mut self.parent, outer);
            CURRENT_SCOPE = self as *const CancelScope as usize;
            let result = f();
            CURRENT_SCOPE = outer;
            self.wait_tasks();
            return result;
        }
    }

    /// Waits for the tasks started inside this scope. They read it through their parents, so a
    /// scope cannot end before they do, even if a handle to one escaped.
    pub fn wait_tasks(self: &Self) {
        while unsafe { @atomic_load(&raw mut self.live) } != 0 {
            if !fiber_park(self as *const CancelScope as usize, 0) {
                let _rc = usleep(100);
            }
        }
    }

    pub(mod) fn add_task(self: &Self) {
        let _old = unsafe { @atomic_add(&raw mut self.live, 1) };
    }

    pub(mod) fn end_task(self: &Self) {
        let _old = unsafe { @atomic_sub(&raw mut self.live, 1) };
        fiber_wake(self as *const CancelScope as usize);
    }

    /// Whether this scope, or one around it, stops by itself at some point.
    pub(mod) fn has_deadline(self: &Self) -> bool {
        if unsafe { @atomic_load(&raw mut self.deadline) } != NO_DEADLINE {
            return true;
        }
        let up = unsafe { @atomic_load(&raw mut self.parent) };
        return up != 0 && unsafe { (*(up as *const CancelScope)).has_deadline() };
    }
}

const NO_DEADLINE: i64 = 9223372036854775807;

/// Monotonic milliseconds.
pub fn now_ms() -> i64 {
    let mut time: [i64; 2] = { 0, 0 };
    let _rc = unsafe { clock_gettime(1, &raw mut time) };
    return time[0] * 1000 + time[1] / 1000000;
}

/// Why the running task should stop: 0 if it should not, as for `CancelScope::stop_reason`.
fn task_stop_reason() -> i32 {
    let current = unsafe { CURRENT_SCOPE };
    if current == 0 {
        return 0;
    }
    return unsafe { (*(current as *const CancelScope)).stop_reason() };
}

fn stop_error(reason: i32) -> CancelError!void {
    if reason == 2 {
        return .TimedOut;
    }
    if reason == 1 {
        return .Cancelled;
    }
}

/// The saved registers of a suspended fiber: glibc's `ucontext_t`, whose start is its stack.
struct UContext {
    flags: usize,
    link: usize,
    stack: *mut u8,
    stack_flags: usize,
    stack_size: usize,
    rest: [uninit u64; 1024],
}

/// A task with a stack of its own, which runs until it waits. Everything not running is ready,
/// parked, or finished. The thread's first fiber stands for its own stack.
struct Fiber {
    context: UContext,
    memory: *mut u8,
    entry: ?fn(*mut u8) -> *mut u8,
    arg: *mut u8,
    done: bool,
    scope: usize,
    /// Its `DROP_DEPTH` and `DROP_QUEUE` while it is not running.
    drop_depth: usize,
    drop_queue: usize,
    next: usize,
    /// While parked: what wakes it, and when to look again regardless (0 for never).
    key: usize,
    until: i64,
    /// Or the file descriptor it waits for, and the `poll` events, if `fd` is not -1.
    fd: i32,
    events: i16,
    /// The descriptor `epoll` has for this fiber, or -1. It stays there between waits, which
    /// makes waiting on the same one again a single call.
    watched: i32,
    /// The wait list it is in, or `NOT_PARKED`, and its neighbour there, after `next`.
    list: usize,
    previous: usize,
}

/// What a thread with fibers shares with the others, which is how they reach it. `busy` has a bit
/// for each key list in use, so that a wake bothers only schedulers that might care.
struct Scheduler {
    lock: [u64; 8],
    keys: [usize; 32],
    count: usize,
    overflowed: bool,
    sleeping: bool,
    busy: [u64; 4],
    wake_read: i32,
    wake_write: i32,
    next: usize,
}

/// What `poll` reads and fills in.
struct PollFd {
    fd: i32,
    events: i16,
    revents: i16,
}

pub const POLL_IN: i16 = 1;
pub const POLL_OUT: i16 = 4;

const IDLE_MS: i32 = 1;
/// How often fibers waiting on descriptors look for themselves, for those `epoll` is not watching:
/// it takes only one registration for a descriptor, and refuses regular files.
const SWEEP_MS: i64 = 50;
/// Wait lists by key, then one for descriptors. Each has a first and a last entry in the table.
const KEY_LISTS: usize = 256;
const FD_LIST: usize = 256;
const WAIT_LISTS: usize = 257;
const NOT_PARKED: usize = 18446744073709551615;
const EPOLL_ONESHOT: u32 = 1073741824;
const INBOX_SIZE: usize = 32;
const EPOLL_ADD: i32 = 1;
const EPOLL_DEL: i32 = 2;
const EPOLL_MOD: i32 = 3;
/// Events taken from `epoll` at a time. Each is three `u32`s on x86-64, where the struct is packed.
const EPOLL_BATCH: i32 = 32;
const FIBER_STACK: usize = 8388608;
const GUARD_PAGE: usize = 4096;

/// This thread's running fiber, or 0 if it has none.
thread_local static mut CURRENT_FIBER: usize = 0;
thread_local static mut QUEUE_FIRST: usize = 0;
thread_local static mut QUEUE_LAST: usize = 0;
thread_local static mut FIBERS_ALIVE: usize = 0;
/// Guards the list of schedulers, and is taken only while there are any.
static mut SCHEDULER_LOCK: [u64; 8] = { 0, 0, 0, 0, 0, 0, 0, 0 };
static mut SCHEDULERS: usize = 0;
static mut SCHEDULER_COUNT: usize = 0;
/// This thread's scheduler.
thread_local static mut MY_SCHEDULER: usize = 0;
/// This thread's wait lists.
thread_local static mut WAIT_TABLE: usize = 0;
thread_local static mut EPOLL_FD: i32 = -1;
thread_local static mut NEXT_SWEEP: i64 = 0;
/// When to next recheck what is parked. Another thread cannot wake a fiber, and nothing does
/// when a deadline passes or a scope is cancelled, so each is noticed here.
thread_local static mut NEXT_RECHECK: i64 = 0;

/// Threads other than the main one that are running, any of which might wake a fiber.
static mut THREADS_ALIVE: usize = 0;
/// How many have ended, as what one did last may have been for a fiber, which then needs a look.
static mut THREADS_ENDED: usize = 0;
thread_local static mut ENDED_SEEN: usize = 0;

pub fn thread_started() {
    let _old = unsafe { @atomic_add_relaxed(&raw mut THREADS_ALIVE, 1) };
}

pub fn thread_ended() {
    let _old = unsafe { @atomic_sub_relaxed(&raw mut THREADS_ALIVE, 1) };
    let _ended = unsafe { @atomic_add_relaxed(&raw mut THREADS_ENDED, 1) };
}

/// Whether a thread is running, or has ended since this thread last looked.
fn threads_matter() -> bool {
    unsafe {
        return @atomic_load_relaxed(&raw mut THREADS_ALIVE) != 0
            || @atomic_load_relaxed(&raw mut THREADS_ENDED) != ENDED_SEEN;
    }
}

fn enqueue_fiber(fiber: *mut Fiber) {
    unsafe {
        (*fiber).next = 0;
        if QUEUE_LAST == 0 {
            QUEUE_FIRST = fiber as usize;
        } else {
            (*(QUEUE_LAST as *mut Fiber)).next = fiber as usize;
        }
        QUEUE_LAST = fiber as usize;
    }
}

fn list_of(key: usize) -> usize {
    return ((key >> 4) ^ (key >> 12)) & (KEY_LISTS - 1);
}

fn table_slot(list: usize) -> *mut usize {
    return unsafe { (WAIT_TABLE as *mut usize) + list * 2 };
}

fn registry_lock() -> *mut u8 {
    return unsafe { &raw mut SCHEDULER_LOCK[0] as *mut u64 as *mut u8 };
}

fn scheduler_lock(scheduler: *mut Scheduler) -> *mut u8 {
    return unsafe { &raw mut (*scheduler).lock[0] as *mut u64 as *mut u8 };
}

/// Sets or clears the bit that says a key list is in use.
fn mark_busy(list: usize, used: bool) {
    unsafe {
        let scheduler = MY_SCHEDULER as *mut Scheduler;
        let word = &raw mut (*scheduler).busy[list / 64];
        let bit: u64 = 1 << (list % 64) as u64;
        if used {
            let _old = @atomic_or(word, bit);
        } else {
            let _old = @atomic_and(word, bit ^ 18446744073709551615);
        }
    }
}

/// Adds `fiber` to the end of a wait list, so that those woken together run in the order they came.
fn park_in(fiber: *mut Fiber, list: usize) {
    unsafe {
        let slot = table_slot(list);
        let last = *(slot + 1);
        (*fiber).list = list;
        (*fiber).next = 0;
        (*fiber).previous = last;
        if last == 0 {
            *slot = fiber as usize;
            if list != FD_LIST {
                mark_busy(list, true);
            }
        } else {
            (*(last as *mut Fiber)).next = fiber as usize;
        }
        *(slot + 1) = fiber as usize;
    }
}

/// Takes `fiber` off its wait list, and makes it ready.
fn unpark(fiber: *mut Fiber) {
    unsafe {
        let list = (*fiber).list;
        let slot = table_slot(list);
        let before = (*fiber).previous;
        let after = (*fiber).next;
        if before == 0 {
            *slot = after;
            if after == 0 && list != FD_LIST {
                mark_busy(list, false);
            }
        } else {
            (*(before as *mut Fiber)).next = after;
        }
        if after == 0 {
            *(slot + 1) = before;
        } else {
            (*(after as *mut Fiber)).previous = before;
        }
        (*fiber).list = NOT_PARKED;
        enqueue_fiber(fiber);
    }
}

fn wake_here(key: usize) {
    unsafe {
        let mut at = *table_slot(list_of(key));
        while at != 0 {
            let fiber = at as *mut Fiber;
            at = (*fiber).next;
            if (*fiber).key == key {
                unpark(fiber);
            }
        }
    }
}

/// Leaves `key` for the thread of `scheduler`, waking it if it is asleep.
fn wake_there(scheduler: *mut Scheduler, key: usize) {
    unsafe {
        let lock = scheduler_lock(scheduler);
        let _rc = pthread_mutex_lock(lock);
        if (*scheduler).count < INBOX_SIZE {
            (*scheduler).keys[(*scheduler).count] = key;
            (*scheduler).count = (*scheduler).count + 1;
        } else {
            (*scheduler).overflowed = true;
        }
        let asleep = (*scheduler).sleeping;
        (*scheduler).sleeping = false;
        if asleep {
            let byte: u8 = 1;
            let _n = write((*scheduler).wake_write, &raw const byte, 1);
        }
        let _unlocked = pthread_mutex_unlock(lock);
    }
}

/// Wakes the fibers parked on `key`, on any thread. They look again, so an extra wake is harmless.
pub fn fiber_wake(key: usize) {
    unsafe {
        if CURRENT_FIBER != 0 {
            wake_here(key);
        }
        let others = @atomic_load_relaxed(&raw mut SCHEDULER_COUNT);
        if others == 0 || (others == 1 && CURRENT_FIBER != 0) {
            return;
        }
        let list = list_of(key);
        let bit: u64 = 1 << (list % 64) as u64;
        let _rc = pthread_mutex_lock(registry_lock());
        let mut at = SCHEDULERS;
        while at != 0 {
            let scheduler = at as *mut Scheduler;
            at = (*scheduler).next;
            let in_use = @atomic_load(&raw mut (*scheduler).busy[list / 64]) & bit;
            if scheduler as usize != MY_SCHEDULER && in_use != 0 {
                wake_there(scheduler, key);
            }
        }
        let _unlocked = pthread_mutex_unlock(registry_lock());
    }
}

/// Acts on what other threads have left for this one.
fn drain_inbox() {
    unsafe {
        let scheduler = MY_SCHEDULER as *mut Scheduler;
        if @atomic_load_relaxed(&raw mut (*scheduler).count) == 0 && !(*scheduler).overflowed {
            return;
        }
        let mut keys: [usize; 32] = @default([usize; 32]);
        let lock = scheduler_lock(scheduler);
        let _rc = pthread_mutex_lock(lock);
        let count = (*scheduler).count;
        for i in 0..count {
            keys[i] = (*scheduler).keys[i];
        }
        let overflowed = (*scheduler).overflowed;
        (*scheduler).count = 0;
        (*scheduler).overflowed = false;
        let _unlocked = pthread_mutex_unlock(lock);
        for i in 0..count {
            wake_here(keys[i]);
        }
        if overflowed {
            for list in 0..KEY_LISTS {
                let mut at = *table_slot(list);
                while at != 0 {
                    let fiber = at as *mut Fiber;
                    at = (*fiber).next;
                    unpark(fiber);
                }
            }
        }
    }
}

/// Makes this thread's scheduler, and lets other threads find it.
fn start_scheduler() {
    unsafe {
        let scheduler: *mut Scheduler = @alloc(Scheduler, 1);
        let mut ends: [i32; 2] = { 0, 0 };
        let _rc = pipe(&raw mut ends);
        for i in 0..8 {
            (*scheduler).lock[i] = 0;
        }
        for i in 0..4 {
            (*scheduler).busy[i] = 0;
        }
        (*scheduler).count = 0;
        (*scheduler).overflowed = false;
        (*scheduler).sleeping = false;
        (*scheduler).wake_read = ends[0];
        (*scheduler).wake_write = ends[1];
        MY_SCHEDULER = scheduler as usize;
        EPOLL_FD = epoll_create1(0);
        // Zero is no fiber, so this reads as the thread being woken.
        let mut watch: [u32; 3] = { 1, 0, 0 };
        let _added = epoll_ctl(EPOLL_FD, EPOLL_ADD, ends[0], &mut watch[0] as *mut u32);
        let _locked = pthread_mutex_lock(registry_lock());
        (*scheduler).next = SCHEDULERS;
        SCHEDULERS = scheduler as usize;
        let _old = @atomic_add_relaxed(&raw mut SCHEDULER_COUNT, 1);
        let _unlocked = pthread_mutex_unlock(registry_lock());
    }
}

fn stop_scheduler() {
    unsafe {
        let scheduler = MY_SCHEDULER as *mut Scheduler;
        let _locked = pthread_mutex_lock(registry_lock());
        if SCHEDULERS == scheduler as usize {
            SCHEDULERS = (*scheduler).next;
        } else {
            let mut at = SCHEDULERS as *mut Scheduler;
            while (*at).next != scheduler as usize {
                at = (*at).next as *mut Scheduler;
            }
            (*at).next = (*scheduler).next;
        }
        let _old = @atomic_sub_relaxed(&raw mut SCHEDULER_COUNT, 1);
        let _unlocked = pthread_mutex_unlock(registry_lock());
        let _a = close(EPOLL_FD);
        let _b = close((*scheduler).wake_read);
        let _c = close((*scheduler).wake_write);
        EPOLL_FD = -1;
        MY_SCHEDULER = 0;
        @dealloc(scheduler);
    }
}

/// Whether a parked fiber has to look for itself, given what nothing wakes it for.
fn should_look(fiber: *const Fiber, now: i64, keys: bool, sweep: bool) -> bool {
    unsafe {
        if (*fiber).scope != 0 && (*((*fiber).scope as *const CancelScope)).is_cancelled() {
            return true;
        }
        if (*fiber).fd != -1 {
            return sweep;
        }
        if (*fiber).until != 0 {
            return now >= (*fiber).until;
        }
        return keys;
    }
}

/// Finds what needs another look, at most once a millisecond: nothing wakes a fiber when a deadline
/// passes or a scope is cancelled. A wake can also be missed by code that is not a fiber's, or by
/// a thread that ended, so fibers waiting on keys look too, but seldom.
fn recheck_parked() {
    unsafe {
        let now = now_ms();
        if now < NEXT_RECHECK {
            return;
        }
        NEXT_RECHECK = now + 1;
        let sweep = now >= NEXT_SWEEP;
        if sweep {
            NEXT_SWEEP = now + SWEEP_MS;
        }
        let ended = @atomic_load_relaxed(&raw mut THREADS_ENDED);
        let keys = ended != ENDED_SEEN || (sweep && threads_matter());
        ENDED_SEEN = ended;
        for list in 0..WAIT_LISTS {
            let mut at = *table_slot(list);
            while at != 0 {
                let fiber = at as *mut Fiber;
                at = (*fiber).next;
                if should_look(fiber, now, keys, sweep) {
                    unpark(fiber);
                }
            }
        }
    }
}

/// Whether anything other than a running fiber can still change: a thread, a clock, a descriptor,
/// or a scope already cancelled, which nothing woke its fiber for.
fn something_can_wake() -> bool {
    unsafe {
        if threads_matter() || *table_slot(FD_LIST) != 0 {
            return true;
        }
        for list in 0..KEY_LISTS {
            let mut at = *table_slot(list);
            while at != 0 {
                let fiber = at as *const Fiber;
                if (*fiber).until != 0 {
                    return true;
                }
                if (*fiber).scope != 0 {
                    let scope = (*fiber).scope as *const CancelScope;
                    if (*scope).has_deadline() || (*scope).is_cancelled() {
                        return true;
                    }
                }
                at = (*fiber).next;
            }
        }
        return false;
    }
}

/// Sleeps until a descriptor is ready, another thread wakes this one, or `IDLE_MS` passes.
fn wait_idle() {
    unsafe {
        let scheduler = MY_SCHEDULER as *mut Scheduler;
        let lock = scheduler_lock(scheduler);
        let _rc = pthread_mutex_lock(lock);
        let waiting = (*scheduler).count != 0 || (*scheduler).overflowed;
        (*scheduler).sleeping = !waiting;
        let _unlocked = pthread_mutex_unlock(lock);
        if waiting {
            return;
        }
        let mut events: [u32; 96] = @default([u32; 96]);
        let ready = epoll_wait(EPOLL_FD, &mut events[0] as *mut u32, EPOLL_BATCH, IDLE_MS);
        let _locked = pthread_mutex_lock(lock);
        (*scheduler).sleeping = false;
        let _released = pthread_mutex_unlock(lock);
        for i in 0..ready {
            let at = i as usize * 3;
            let address = (events[at + 1] as usize) | ((events[at + 2] as usize) << 32);
            if address == 0 {
                let mut bytes: [u8; 64] = @default([u8; 64]);
                let _n = read((*scheduler).wake_read, &mut bytes[0] as *mut u8, 64);
            } else {
                let fiber = address as *mut Fiber;
                if (*fiber).list != NOT_PARKED {
                    unpark(fiber);
                }
            }
        }
    }
}

/// Runs the next fiber, until `me` is resumed. With none ready, the thread sleeps until something
/// parked can go on, and if nothing ever can, every fiber is waiting for another: it traps.
fn switch_fiber(me: *mut Fiber) {
    unsafe {
        // A cancel scope belongs to its fiber.
        (*me).scope = CURRENT_SCOPE;
        drain_inbox();
        recheck_parked();
        while QUEUE_FIRST == 0 {
            if !something_can_wake() {
                @trap();
            }
            wait_idle();
            drain_inbox();
            recheck_parked();
        }
        let next = QUEUE_FIRST as *mut Fiber;
        QUEUE_FIRST = (*next).next;
        if QUEUE_FIRST == 0 {
            QUEUE_LAST = 0;
        }
        if next as usize == me as usize {
            return;
        }
        CURRENT_FIBER = next as usize;
        // So does a drop that parks: another fiber starts its own count.
        let drops = swap_drop_state((*next).drop_depth, (*next).drop_queue);
        (*me).drop_depth = drops.0;
        (*me).drop_queue = drops.1;
        let _rc = swapcontext(&raw mut (*me).context, &raw mut (*next).context);
        CURRENT_SCOPE = (*me).scope;
    }
}

/// Lets the other fibers on this thread run. False if there are none, so the caller must block.
pub fn fiber_yield() -> bool {
    unsafe {
        if CURRENT_FIBER == 0 {
            return false;
        }
        let me = CURRENT_FIBER as *mut Fiber;
        enqueue_fiber(me);
        switch_fiber(me);
        return true;
    }
}

/// Waits until `key` is woken, or `until` passes if it is not 0, or for no reason at all, so the
/// caller looks again. False if this thread has no fibers, so the caller must block.
pub fn fiber_park(key: usize, until: i64) -> bool {
    unsafe {
        if CURRENT_FIBER == 0 {
            return false;
        }
        let me = CURRENT_FIBER as *mut Fiber;
        (*me).key = key;
        (*me).until = until;
        (*me).fd = -1;
        park_in(me, list_of(key));
        switch_fiber(me);
        return true;
    }
}

/// Waits on `cond` as a fiber, with `mutex` held and released while it waits. It joins the wait
/// list first, so a wake from another thread after the unlock is not missed.
unsafe fn fiber_wait_cond(cond: *mut u8, mutex: *mut u8) {
    unsafe {
        let me = CURRENT_FIBER as *mut Fiber;
        let key = cond as usize;
        (*me).key = key;
        (*me).until = 0;
        (*me).fd = -1;
        park_in(me, list_of(key));
        let _rc1 = pthread_mutex_unlock(mutex);
        switch_fiber(me);
        let _rc2 = pthread_mutex_lock(mutex);
    }
}

/// Takes `mutex` as a fiber. As with a condition, it parks before trying a last time, so an
/// unlock on another thread is not missed.
unsafe fn fiber_lock(mutex: *mut u8) {
    unsafe {
        while pthread_mutex_trylock(mutex) != 0 {
            let me = CURRENT_FIBER as *mut Fiber;
            let key = mutex as usize;
            (*me).key = key;
            (*me).until = 0;
            (*me).fd = -1;
            park_in(me, list_of(key));
            if pthread_mutex_trylock(mutex) == 0 {
                unpark(me);
                switch_fiber(me);
                return;
            }
            switch_fiber(me);
        }
    }
}

/// Whether `fd` is ready now, or within `timeout_ms`.
fn fd_ready(fd: i32, events: i16, timeout_ms: i32) -> bool {
    unsafe {
        let mut one = PollFd { fd: fd, events: events, revents: 0 };
        return poll(&raw mut one, 1, timeout_ms) > 0;
    }
}

/// Has `epoll` tell this fiber when `fd` is ready, once.
unsafe fn watch_fd(me: *mut Fiber, fd: i32, events: i16) {
    unsafe {
        let address = me as usize;
        let mut watch: [u32; 3] = { events as u32 | EPOLL_ONESHOT, address as u32, (address >> 32) as u32 };
        let event = &mut watch[0] as *mut u32;
        if (*me).watched == fd && epoll_ctl(EPOLL_FD, EPOLL_MOD, fd, event) == 0 {
            return;
        }
        if (*me).watched != -1 && (*me).watched != fd {
            let _rc = epoll_ctl(EPOLL_FD, EPOLL_DEL, (*me).watched, event);
        }
        (*me).watched = -1;
        if epoll_ctl(EPOLL_FD, EPOLL_ADD, fd, event) == 0 {
            (*me).watched = fd;
        }
    }
}

/// Waits a while for `fd` to be ready for `events`, returning why the task should stop instead, or
/// 0. Other fibers run meanwhile. It may return early, so the caller tries again.
pub fn wait_fd_once(fd: i32, events: i16) -> i32 {
    unsafe {
        let reason = task_stop_reason();
        if reason != 0 {
            return reason;
        }
        if CURRENT_FIBER == 0 {
            let _ready = fd_ready(fd, events, IDLE_MS);
            return 0;
        }
        let me = CURRENT_FIBER as *mut Fiber;
        (*me).key = 0;
        (*me).until = 0;
        (*me).fd = fd;
        (*me).events = events;
        watch_fd(me, fd, events);
        park_in(me, FD_LIST);
        switch_fiber(me);
        return 0;
    }
}

/// Waits until `fd` is ready for `events`, returning why the task should stop instead, or 0.
/// Other fibers run meanwhile. Only here does the task notice a stop, as for `Channel::recv`.
pub fn wait_fd(fd: i32, events: i16) -> i32 {
    while true {
        let reason = task_stop_reason();
        if reason != 0 {
            return reason;
        }
        if fd_ready(fd, events, 0) {
            return 0;
        }
        let stopped = wait_fd_once(fd, events);
        if stopped != 0 {
            return stopped;
        }
    }
    return 0;
}

/// Gives a moment to anything else that can run, on this thread or another.
pub fn sleep_briefly() -> i32 {
    if !fiber_park(0, now_ms() + 1) {
        return usleep(50);
    }
    return 0;
}

/// Whether this thread has fibers, so that a blocking call would stop them.
pub fn on_fibers() -> bool {
    return unsafe { CURRENT_FIBER } != 0;
}

fn new_fiber(memory: *mut u8, entry: ?fn(*mut u8) -> *mut u8, arg: *mut u8) -> *mut Fiber {
    unsafe {
        let fiber: *mut Fiber = @alloc(Fiber, 1);
        (*fiber).memory = memory;
        (*fiber).entry = entry;
        (*fiber).arg = arg;
        (*fiber).done = false;
        (*fiber).scope = 0;
        (*fiber).drop_depth = 0;
        (*fiber).drop_queue = 0;
        (*fiber).next = 0;
        (*fiber).key = 0;
        (*fiber).until = 0;
        (*fiber).fd = -1;
        (*fiber).events = 0;
        (*fiber).watched = -1;
        (*fiber).list = NOT_PARKED;
        (*fiber).previous = 0;
        return fiber;
    }
}

fn fiber_main() {
    unsafe {
        let me = CURRENT_FIBER as *mut Fiber;
        let entry = (*me).entry orelse unreachable;
        let _none = entry((*me).arg);
        (*me).done = true;
        if (*me).watched != -1 {
            let _rc = epoll_ctl(EPOLL_FD, EPOLL_DEL, (*me).watched, 0 as *mut u32);
        }
        fiber_wake(me as usize);
        switch_fiber(me);
        @trap();
    }
}

/// A new fiber running `entry(arg)`, with a guard page below its stack.
pub fn fiber_start(entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> u64 {
    unsafe {
        if CURRENT_FIBER == 0 {
            CURRENT_FIBER = new_fiber(0 as *mut u8, null, 0 as *mut u8) as usize;
            let table: *mut usize = @alloc(usize, WAIT_LISTS * 2);
            WAIT_TABLE = table as usize;
            for i in 0..(WAIT_LISTS * 2) {
                *(table + i) = 0;
            }
            start_scheduler();
        }
        // `MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE`: only pages a fiber touches cost memory.
        let memory = mmap(0 as *mut u8, FIBER_STACK, 3, 16418, -1, 0);
        if (memory as usize) == 18446744073709551615 {
            @trap();
        }
        let _guard = mprotect(memory, GUARD_PAGE, 0);
        let fiber = new_fiber(memory, entry, arg);
        let _rc = getcontext(&raw mut (*fiber).context);
        (*fiber).context.link = 0;
        (*fiber).context.stack = memory;
        (*fiber).context.stack_flags = 0;
        (*fiber).context.stack_size = FIBER_STACK;
        makecontext(&raw mut (*fiber).context, fiber_main, 0);
        FIBERS_ALIVE = FIBERS_ALIVE + 1;
        enqueue_fiber(fiber);
        return fiber as usize as u64;
    }
}

/// Whether the fiber `id` has ended, so that `fiber_join` will not wait.
pub fn fiber_finished(id: u64) -> bool {
    return unsafe { (*(id as usize as *const Fiber)).done };
}

/// Runs other fibers until the fiber `id` ends, then frees it. It must be on this thread.
pub fn fiber_join(id: u64) {
    unsafe {
        if CURRENT_FIBER == 0 {
            @trap();
        }
        let fiber = id as usize as *mut Fiber;
        while !(*fiber).done {
            let _parked = fiber_park(fiber as usize, 0);
        }
        let _rc = munmap((*fiber).memory, FIBER_STACK);
        @dealloc(fiber);
        FIBERS_ALIVE = FIBERS_ALIVE - 1;
        if FIBERS_ALIVE == 0 {
            @dealloc(CURRENT_FIBER as *mut Fiber);
            CURRENT_FIBER = 0;
            @dealloc(WAIT_TABLE as *mut usize);
            WAIT_TABLE = 0;
            stop_scheduler();
        }
    }
}

/// Waits on `cond` as `pthread_cond_wait` does, returning why the task should stop, or 0. In a
/// scope, the wait is bounded so that a cancel from elsewhere, or a deadline, is noticed; outside
/// one, nothing can stop it and it costs nothing extra.
unsafe fn wait_cancellable(cond: *mut u8, mutex: *mut u8) -> i32 {
    unsafe {
        if CURRENT_FIBER != 0 {
            fiber_wait_cond(cond, mutex);
            return task_stop_reason();
        }
        if CURRENT_SCOPE == 0 {
            let _rc = pthread_cond_wait(cond, mutex);
            return 0;
        }
        let reason = task_stop_reason();
        if reason != 0 {
            return reason;
        }
        let mut deadline: [i64; 2] = { 0, 0 };
        let _rc = clock_gettime(0, &raw mut deadline);
        deadline[1] = deadline[1] + 1000000;
        if deadline[1] >= 1000000000 {
            deadline[0] = deadline[0] + 1;
            deadline[1] = deadline[1] - 1000000000;
        }
        let _timed = pthread_cond_timedwait(cond, mutex, &raw const deadline);
        return 0;
    }
}

/// Sleeps for `ms` milliseconds, unless the task is stopped first.
pub fn sleep_ms(ms: i64) -> CancelError!void {
    let end = now_ms() + ms;
    while now_ms() < end {
        try stop_error(task_stop_reason());
        if !fiber_park(0, end) {
            let _rc = usleep(1000);
        }
    }
    try stop_error(task_stop_reason());
}

/// The task's current scope, for a thread starting inside it.
pub fn current_scope() -> usize {
    return unsafe { CURRENT_SCOPE };
}

pub fn set_current_scope(scope: usize) {
    unsafe { CURRENT_SCOPE = scope; }
}

/// Counts a task started inside the scope at address `scope`, if there is one.
pub fn scope_add_task(scope: usize) {
    if scope != 0 {
        unsafe { (*(scope as *const CancelScope)).add_task(); }
    }
}

pub fn scope_end_task(scope: usize) {
    if scope != 0 {
        unsafe { (*(scope as *const CancelScope)).end_task(); }
    }
}

/// `.Cancelled` if the running task's scope, or one around it, was cancelled.
pub fn check_cancelled() -> CancelError!void {
    try stop_error(task_stop_reason());
}

safe extern fn usleep(usec: u32) -> i32;
extern fn getcontext(context: *mut UContext) -> i32;
extern fn makecontext(context: *mut UContext, entry: fn(), argc: i32);
extern fn swapcontext(from: *mut UContext, to: *mut UContext) -> i32;
extern fn poll(fds: *mut PollFd, count: usize, timeout_ms: i32) -> i32;
extern fn epoll_create1(flags: i32) -> i32;
extern fn epoll_ctl(epoll: i32, operation: i32, fd: i32, event: *mut u32) -> i32;
extern fn epoll_wait(epoll: i32, events: *mut u32, count: i32, timeout_ms: i32) -> i32;
extern fn close(fd: i32) -> i32;
extern fn pipe(fds: *mut [i32; 2]) -> i32;
extern fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
extern fn write(fd: i32, buf: *const u8, count: usize) -> isize;
extern fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, offset: i64) -> *mut u8;
extern fn mprotect(addr: *mut u8, len: usize, prot: i32) -> i32;
extern fn munmap(addr: *mut u8, len: usize) -> i32;
extern fn pthread_mutex_trylock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_init(mutex: *mut u8, attr: *const u8) -> i32;
extern fn pthread_mutex_lock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_unlock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_destroy(mutex: *mut u8) -> i32;
extern fn pthread_cond_init(cond: *mut u8, attr: *const u8) -> i32;
extern fn pthread_cond_wait(cond: *mut u8, mutex: *mut u8) -> i32;
extern fn pthread_cond_timedwait(cond: *mut u8, mutex: *mut u8, deadline: *const [i64; 2]) -> i32;
extern fn clock_gettime(clock: i32, time: *mut [i64; 2]) -> i32;
extern fn pthread_cond_signal(cond: *mut u8) -> i32;
extern fn pthread_cond_broadcast(cond: *mut u8) -> i32;
extern fn pthread_cond_destroy(cond: *mut u8) -> i32;

/// Asserts that a value may move to another thread although its type is not `send` (one raw
/// pointer handed to a worker, say). `new` is `unsafe`: the caller vouches for that one value.
pub opaque(unsafe send) UnsafeSend[T] {
    value: T,

    pub unsafe fn new(value: T) -> Self {
        return Self { value: value };
    }

    pub fn get(self: &Self) -> &T {
        return &self.value;
    }

    pub fn into_inner(move self) -> T {
        return self.value;
    }
}

/// Asserts that a value may be shared between threads although its type is not `sync`. `new`
/// is `unsafe`: the caller vouches that every access to that one value is synchronized.
pub opaque(unsafe sync) UnsafeSync[T] {
    value: T,

    pub unsafe fn new(value: T) -> Self {
        return Self { value: value };
    }

    pub fn get(self: &Self) -> &T {
        return &self.value;
    }

    pub fn into_inner(move self) -> T {
        return self.value;
    }
}

pub opaque(linear) MutexGuard[T: send] {
    raw_mtx: *mut u8,
    data_ptr: *ref mut T,

    pub(mod) fn create(raw_mtx: *mut u8, data_ptr: *ref mut T) -> Self {
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
        fiber_wake(self.raw_mtx as usize);
    }
}

pub opaque(unsafe send, unsafe sync) Mutex[T: send] {
    raw: [u64; 6],
    raw_handle: *mut u8,
    data: T,

    unsafe impl drop(may_dangle T) where T: !linear {
        fn drop(self: &mut Self) {
            unsafe {
                let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
                let _rc = pthread_mutex_destroy(ptr);
            }
        }
    }

    unsafe impl drop(may_dangle T) where T: linear {
        fn drop(self: &mut Self) {
            unsafe {
                let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
                let _rc = pthread_mutex_destroy(ptr);
            }
        }
    }

    pub fn into_inner(move mut self) -> T {
        unsafe {
            let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
            let _rc = pthread_mutex_destroy(ptr);
            let data_ptr: *mut T = &raw mut self.data;
            let val = move *data_ptr;
            @forget(self);
            return val;
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

    pub fn lock(self: &Self) -> MutexGuard[T] {
        let self_mut = self as *mut Self;
        unsafe {
            let raw_ptr = &mut (*self_mut).raw[0] as *mut u64 as *mut u8;
            let data_ptr = &mut (*self_mut).data as *ref mut T;
            if CURRENT_FIBER != 0 {
                // A fiber on this thread may hold it, and needs a turn to let go.
                fiber_lock(raw_ptr);
            } else {
                let _rc = pthread_mutex_lock(raw_ptr);
            }
            return MutexGuard[T]::create(raw_ptr, data_ptr);
        }
    }

    pub fn with_lock[F: callable](self: &Self, f: F) -> i32 {
        let mut guard = self.lock();
        let out: i32 = f(guard.get_mut());
        guard.unlock();
        return out;
    }
}

pub opaque(unsafe sync) Waiter {
    raw_mtx: [u64; 6],
    raw_cv: [u64; 6],
    state: i32,
    timeout_us: u64,
    timeout_branch: i32,

    impl drop {
        fn drop(self: &mut Self) {
            unsafe {
                let cv_ptr = (&mut self.raw_cv[0] as *mut u64 as usize) as *mut u8;
                let mtx_ptr = (&mut self.raw_mtx[0] as *mut u64 as usize) as *mut u8;
                let _rc1 = pthread_cond_destroy(cv_ptr);
                let _rc2 = pthread_mutex_destroy(mtx_ptr);
            }
        }
    }

    pub fn new() -> Self {
        let mut w = Self {
            raw_mtx: { 0, 0, 0, 0, 0, 0 },
            raw_cv: { 0, 0, 0, 0, 0, 0 },
            state: -1,
            timeout_us: 0,
            timeout_branch: -1,
        };
        unsafe {
            let mtx_ptr = (&mut w.raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let cv_ptr = (&mut w.raw_cv[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_init(mtx_ptr, 0 as *const u8);
            let _rc2 = pthread_cond_init(cv_ptr, 0 as *const u8);
        }
        return w;
    }

    pub(mod) fn try_claim(self: &Self, branch_idx: i32) -> bool {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let cv_ptr = (&mut (*self_mut).raw_cv[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            if (*self_mut).state < 0 {
                (*self_mut).state = branch_idx;
                let _rc2 = pthread_cond_signal(cv_ptr);
                fiber_wake(cv_ptr as usize);
                let _rc3 = pthread_mutex_unlock(mtx_ptr);
                return true;
            }
            let _rc4 = pthread_mutex_unlock(mtx_ptr);
            return false;
        }
    }

    pub(mod) fn set_timeout(self: &Self, delay_us: u64, branch_idx: i32) {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            if (*self_mut).timeout_branch < 0 || delay_us < (*self_mut).timeout_us {
                (*self_mut).timeout_us = delay_us;
                (*self_mut).timeout_branch = branch_idx;
            }
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
        }
    }

    pub fn winner(self: &Self) -> i32 {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let w = (*self_mut).state;
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return w;
        }
    }

    pub fn park(self: &Self) -> i32 {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let cv_ptr = (&mut (*self_mut).raw_cv[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            if (*self_mut).timeout_branch >= 0 {
                let mut rem: u64 = (*self_mut).timeout_us;
                let t_branch: i32 = (*self_mut).timeout_branch;
                while (*self_mut).state < 0 && rem > 0 {
                    let mut step: u64 = rem;
                    if step > 1000 {
                        step = 1000;
                    }
                    let _rc_u = pthread_mutex_unlock(mtx_ptr);
                    let _yielded = fiber_yield();
                    let _rc_s = usleep(step as u32);
                    let _rc_l = pthread_mutex_lock(mtx_ptr);
                    if rem >= step {
                        rem -= step;
                    } else {
                        rem = 0;
                    }
                }
                if (*self_mut).state < 0 {
                    (*self_mut).state = t_branch;
                }
                let w = (*self_mut).state;
                let _rc2 = pthread_mutex_unlock(mtx_ptr);
                return w;
            }
            while (*self_mut).state < 0 {
                if CURRENT_FIBER != 0 {
                    fiber_wait_cond(cv_ptr, mtx_ptr);
                } else {
                    let _rc_w = pthread_cond_wait(cv_ptr, mtx_ptr);
                }
            }
            let w = (*self_mut).state;
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return w;
        }
    }
}

pub opaque(copy, unsafe sync) WaitNode {
    waiter: *const Waiter,
    branch_idx: i32,
    val_ptr: *mut u8,
    active: bool,

    pub fn new() -> Self {
        return Self {
            waiter: 0 as *const Waiter,
            branch_idx: -1,
            val_ptr: 0 as *mut u8,
            active: false,
        };
    }

    pub(mod) fn init(self: &mut Self, waiter: *const Waiter, branch_idx: i32, val_ptr: *mut u8) {
        self.waiter = waiter;
        self.branch_idx = branch_idx;
        self.val_ptr = val_ptr;
        self.active = true;
    }

    pub(mod) fn deactivate(self: &mut Self) {
        self.active = false;
    }

    pub(mod) fn is_active(self: &Self) -> bool {
        return self.active;
    }

    pub(mod) fn get_waiter(self: &Self) -> *const Waiter {
        return self.waiter;
    }

    pub(mod) fn get_branch_idx(self: &Self) -> i32 {
        return self.branch_idx;
    }

    pub(mod) fn get_val_ptr(self: &Self) -> *mut u8 {
        return self.val_ptr;
    }
}

pub struct Timer {
    pub delay_us: u64,

    pub fn after_us(delay_us: u64) -> Self {
        return Self {
            delay_us: delay_us,
        };
    }

    pub fn ready() -> Self {
        return Self {
            delay_us: 0,
        };
    }

    pub fn wait(self: &Self) -> i32 {
        if self.delay_us > 0 {
            let _rc = usleep(self.delay_us as u32);
        }
        return 1;
    }

    pub fn recv(self: &Self) -> i32 {
        return self.wait();
    }

    pub unsafe fn select_fast_recv(self: &Self, out_ptr: *mut i32) -> bool {
        if self.delay_us == 0 {
            unsafe {
                *out_ptr = 1;
            }
            return true;
        }
        return false;
    }

    pub unsafe fn select_register_recv(
        self: &Self,
        node: *mut WaitNode,
        waiter: *const Waiter,
        branch_idx: i32,
        out_ptr: *mut i32
    ) -> bool {
        unsafe {
            *out_ptr = 1;
            if self.delay_us == 0 {
                return (*waiter).try_claim(branch_idx);
            }
            (*node).init(waiter, branch_idx, out_ptr as *mut u8);
            (*waiter).set_timeout(self.delay_us, branch_idx);
            return false;
        }
    }

    pub unsafe fn select_unregister(self: &Self, node: *mut WaitNode) {
        unsafe {
            (*node).deactivate();
        }
    }
}

pub opaque(unsafe send, unsafe sync) Channel[T: send] {
    raw_mtx: [u64; 6],
    not_empty_cv: [u64; 6],
    not_full_cv: [u64; 6],
    buf: *own [uninit T; 64],
    cap: usize,
    head: usize,
    tail: usize,
    count: usize,
    recv_waiters: [*mut WaitNode; 8],
    send_waiters: [*mut WaitNode; 8],

    unsafe impl drop(may_dangle T) where T: !linear {
        fn drop(self: &mut Self) {
            unsafe {
                while self.count > 0 {
                    let h_idx: usize = self.head;
                    let slot_ptr: *mut T = (&mut (*self.buf)[h_idx] as *mut uninit T as usize) as *mut T;
                    @drop(slot_ptr);
                    self.head = (h_idx +% 1) % self.cap;
                    self.count = self.count -% 1;
                }
                Self::destroy_raw(self);
            }
        }
    }

    unsafe impl drop(may_dangle T) where T: linear {
        fn drop(self: &mut Self) {
            unsafe {
                Self::destroy_raw(self);
            }
        }
    }

    fn destroy_raw(self: &mut Self) {
        unsafe {
            let ne_ptr = (&mut self.not_empty_cv[0] as *mut u64 as usize) as *mut u8;
            let nf_ptr = (&mut self.not_full_cv[0] as *mut u64 as usize) as *mut u8;
            let mtx_ptr = (&mut self.raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_cond_destroy(ne_ptr);
            let _rc2 = pthread_cond_destroy(nf_ptr);
            let _rc3 = pthread_mutex_destroy(mtx_ptr);
            @dealloc(self.buf);
        }
    }

    pub fn close_and_drain[F: callable](move mut self, f: F) {
        unsafe {
            while self.count > 0 {
                let h_idx: usize = self.head;
                let slot_ptr: *mut T = (&mut (*self.buf)[h_idx] as *mut uninit T as usize) as *mut T;
                self.head = (h_idx +% 1) % self.cap;
                self.count = self.count -% 1;
                f(move *slot_ptr);
            }
        }
    }

    pub fn with_capacity(cap: usize) -> Self {
        let mut real_cap: usize = cap;
        if real_cap == 0 {
            real_cap = 1;
        }
        if real_cap > 64 {
            real_cap = 64;
        }
        let buf_ptr: *own [uninit T; 64] = unsafe { @alloc([uninit T; 64], 1) as *own [uninit T; 64] };
        let mut ch = Self {
            raw_mtx: { 0, 0, 0, 0, 0, 0 },
            not_empty_cv: { 0, 0, 0, 0, 0, 0 },
            not_full_cv: { 0, 0, 0, 0, 0, 0 },
            buf: buf_ptr,
            cap: real_cap,
            head: 0,
            tail: 0,
            count: 0,
            recv_waiters: {
                0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode,
                0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode
            },
            send_waiters: {
                0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode,
                0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode, 0 as *mut WaitNode
            },
        };
        unsafe {
            let mtx_ptr = (&mut ch.raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let ne_ptr = (&mut ch.not_empty_cv[0] as *mut u64 as usize) as *mut u8;
            let nf_ptr = (&mut ch.not_full_cv[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_init(mtx_ptr, 0 as *const u8);
            let _rc2 = pthread_cond_init(ne_ptr, 0 as *const u8);
            let _rc3 = pthread_cond_init(nf_ptr, 0 as *const u8);
        }
        return ch;
    }

    pub fn new() -> Self {
        return Self::with_capacity(16);
    }

    fn try_push_locked(self_mut: *mut Self, val_ptr: *const T) -> bool {
        unsafe {
            let mut i: usize = 0;
            while i < 8 {
                let node: *mut WaitNode = (*self_mut).recv_waiters[i];
                if (node as usize) != 0 {
                    (*self_mut).recv_waiters[i] = 0 as *mut WaitNode;
                    if (*node).is_active() {
                        (*node).deactivate();
                        let w: *const Waiter = (*node).get_waiter();
                        if (*w).try_claim((*node).get_branch_idx()) {
                            @memcpy((*node).get_val_ptr() as *mut T, val_ptr, 1);
                            return true;
                        }
                    }
                }
                i = i +% 1;
            }
            if (*self_mut).count < (*self_mut).cap {
                let t_idx: usize = (*self_mut).tail;
                let slot_ptr: *mut T = (&mut (*(*self_mut).buf)[t_idx] as *mut uninit T as usize) as *mut T;
                @memcpy(slot_ptr, val_ptr, 1);
                (*self_mut).tail = (t_idx +% 1) % (*self_mut).cap;
                (*self_mut).count = (*self_mut).count +% 1;
                let ne_ptr = (&mut (*self_mut).not_empty_cv[0] as *mut u64 as usize) as *mut u8;
                let _rc = pthread_cond_signal(ne_ptr);
                fiber_wake(ne_ptr as usize);
                return true;
            }
            return false;
        }
    }

    fn try_pop_locked(self_mut: *mut Self, out_ptr: *mut T) -> bool {
        unsafe {
            if (*self_mut).count > 0 {
                let h_idx: usize = (*self_mut).head;
                let slot_ptr: *const T = (&mut (*(*self_mut).buf)[h_idx] as *mut uninit T as usize) as *const T;
                @memcpy(out_ptr, slot_ptr, 1);
                (*self_mut).head = (h_idx +% 1) % (*self_mut).cap;
                (*self_mut).count = (*self_mut).count -% 1;
                let mut i: usize = 0;
                while i < 8 {
                    let snode: *mut WaitNode = (*self_mut).send_waiters[i];
                    if (snode as usize) != 0 {
                        (*self_mut).send_waiters[i] = 0 as *mut WaitNode;
                        if (*snode).is_active() {
                            (*snode).deactivate();
                            let sw: *const Waiter = (*snode).get_waiter();
                            if (*sw).try_claim((*snode).get_branch_idx()) {
                                let t_idx: usize = (*self_mut).tail;
                                let dst_slot: *mut T = (&mut (*(*self_mut).buf)[t_idx] as *mut uninit T as usize) as *mut T;
                                @memcpy(dst_slot, (*snode).get_val_ptr() as *const T, 1);
                                (*self_mut).tail = (t_idx +% 1) % (*self_mut).cap;
                                (*self_mut).count = (*self_mut).count +% 1;
                                i = 8;
                            }
                        }
                    }
                    if i < 8 {
                        i = i +% 1;
                    }
                }
                let nf_ptr = (&mut (*self_mut).not_full_cv[0] as *mut u64 as usize) as *mut u8;
                let _rc = pthread_cond_signal(nf_ptr);
                fiber_wake(nf_ptr as usize);
                return true;
            }
            let mut j: usize = 0;
            while j < 8 {
                let snode: *mut WaitNode = (*self_mut).send_waiters[j];
                if (snode as usize) != 0 {
                    (*self_mut).send_waiters[j] = 0 as *mut WaitNode;
                    if (*snode).is_active() {
                        (*snode).deactivate();
                        let sw: *const Waiter = (*snode).get_waiter();
                        if (*sw).try_claim((*snode).get_branch_idx()) {
                            @memcpy(out_ptr, (*snode).get_val_ptr() as *const T, 1);
                            return true;
                        }
                    }
                }
                j = j +% 1;
            }
            return false;
        }
    }

    pub fn try_send(self: &Self, val: T) -> ?T borrows(val, self: val) {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let val_ptr = (&val as *const T as usize) as *const T;
            let ok: bool = Self::try_push_locked(self_mut, val_ptr);
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            if ok {
                @forget(val);
                return null;
            }
            return move val;
        }
    }

    /// Sends `val`, waiting while the channel is full. Yields null, or `val` back if the
    /// task is cancelled first, so a linear value is not lost.
    pub fn send(self: &Self, val: T) -> ?T borrows(val, self: val) {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let nf_ptr = (&mut (*self_mut).not_full_cv[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let val_ptr = (&val as *const T as usize) as *const T;
            while !Self::try_push_locked(self_mut, val_ptr) {
                if wait_cancellable(nf_ptr, mtx_ptr) != 0 {
                    let _rc3 = pthread_mutex_unlock(mtx_ptr);
                    return val;
                }
            }
            @forget(val);
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return null;
        }
    }

    pub fn try_recv(self: &Self) -> ?T borrows(*self) {
        let self_mut = self as *mut Self;
        let mut slot: uninit T = uninit;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let slot_ptr = (&mut slot as *mut uninit T as usize) as *mut T;
            let ok: bool = Self::try_pop_locked(self_mut, slot_ptr);
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            if ok {
                return move *slot_ptr;
            }
            return null;
        }
    }

    /// The next value, waiting while the channel is empty, unless the task is cancelled
    /// first. A value that arrived wins over cancellation.
    pub fn recv(self: &Self) -> CancelError!T borrows(*self) {
        let self_mut = self as *mut Self;
        let mut slot: uninit T = uninit;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let ne_ptr = (&mut (*self_mut).not_empty_cv[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let slot_ptr = (&mut slot as *mut uninit T as usize) as *mut T;
            while !Self::try_pop_locked(self_mut, slot_ptr) {
                let reason = wait_cancellable(ne_ptr, mtx_ptr);
                if reason != 0 {
                    let _rc3 = pthread_mutex_unlock(mtx_ptr);
                    if reason == 2 {
                        return .TimedOut;
                    }
                    return .Cancelled;
                }
            }
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return move *slot_ptr;
        }
    }

    pub unsafe fn select_fast_recv(self: &Self, out_ptr: *mut T) -> bool {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let ok: bool = Self::try_pop_locked(self_mut, out_ptr);
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return ok;
        }
    }

    pub unsafe fn select_fast_send(self: &Self, val_ptr: *mut T) -> bool {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            let ok: bool = Self::try_push_locked(self_mut, val_ptr as *const T);
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return ok;
        }
    }

    pub unsafe fn select_register_recv(
        self: &Self,
        node: *mut WaitNode,
        waiter: *const Waiter,
        branch_idx: i32,
        out_ptr: *mut T
    ) -> bool {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            if (*waiter).winner() >= 0 {
                let _rc_u = pthread_mutex_unlock(mtx_ptr);
                return false;
            }
            if (*self_mut).count > 0 {
                if (*waiter).try_claim(branch_idx) {
                    let _ok = Self::try_pop_locked(self_mut, out_ptr);
                    let _rc_u = pthread_mutex_unlock(mtx_ptr);
                    return true;
                }
            }
            (*node).init(waiter, branch_idx, out_ptr as *mut u8);
            let mut i: usize = 0;
            while i < 8 {
                if ((*self_mut).recv_waiters[i] as usize) == 0 {
                    (*self_mut).recv_waiters[i] = node;
                    i = 8;
                } else {
                    i = i +% 1;
                }
            }
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return false;
        }
    }

    pub unsafe fn select_register_send(
        self: &Self,
        node: *mut WaitNode,
        waiter: *const Waiter,
        branch_idx: i32,
        val_ptr: *mut T
    ) -> bool {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            if (*waiter).winner() >= 0 {
                let _rc_u = pthread_mutex_unlock(mtx_ptr);
                return false;
            }
            if (*self_mut).count < (*self_mut).cap {
                if (*waiter).try_claim(branch_idx) {
                    let _ok = Self::try_push_locked(self_mut, val_ptr as *const T);
                    let _rc_u = pthread_mutex_unlock(mtx_ptr);
                    return true;
                }
            }
            (*node).init(waiter, branch_idx, val_ptr as *mut u8);
            let mut i: usize = 0;
            while i < 8 {
                if ((*self_mut).send_waiters[i] as usize) == 0 {
                    (*self_mut).send_waiters[i] = node;
                    i = 8;
                } else {
                    i = i +% 1;
                }
            }
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
            return false;
        }
    }

    pub unsafe fn select_unregister(self: &Self, node: *mut WaitNode) {
        let self_mut = self as *mut Self;
        unsafe {
            let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_mutex_lock(mtx_ptr);
            (*node).deactivate();
            let mut i: usize = 0;
            while i < 8 {
                if ((*self_mut).recv_waiters[i] as usize) == (node as usize) {
                    (*self_mut).recv_waiters[i] = 0 as *mut WaitNode;
                }
                if ((*self_mut).send_waiters[i] as usize) == (node as usize) {
                    (*self_mut).send_waiters[i] = 0 as *mut WaitNode;
                }
                i = i +% 1;
            }
            let _rc2 = pthread_mutex_unlock(mtx_ptr);
        }
    }
}
";

pub const STD_THREAD_SRC: &str = "\
import std::sync::{CancelScope, ResultOf, current_scope, set_current_scope, scope_add_task, scope_end_task, fiber_start, fiber_join, fiber_finished, thread_started, thread_ended, sleep_briefly, Channel};
import std::collections::Vec;
safe extern fn malloc(size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
extern fn pthread_create(
    thread: *mut u64,
    attr: *const u8,
    start_routine: fn(*mut u8) -> *mut u8,
    arg: *mut u8
) -> i32;
extern fn pthread_join(thread: u64, retval: *mut *mut u8) -> i32;
extern fn pthread_detach(thread: u64) -> i32;

/// A handle to work that finishes later, with a result of type `T`. What implements it depends on
/// the execution policy; waiting for one is an ordinary call.
pub fn Future[T] -> trait {
    return trait {
        fn await(move self) -> T;
    };
}

struct TaskStart[F, R] { f: F, scope: *mut CancelScope, outer: usize, result: *mut ?R }

/// Where tasks run. What a program's `async f(x)` uses is chosen by `alias ProgramExecutor = E;`
/// in the root module, and `async(e) f(x)` names another. `async` only promises that the work
/// happens, so code must not depend on a task overlapping with its caller.
pub trait Executor {
    /// Runs `entry(arg)` until it returns, as `wait` will see. No result means this executor did
    /// not take it, and the task runs on the caller.
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64;
    fn wait(self: &Self, id: u64);
}

impl[E: Executor] Executor for &E {
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
        return (**self).start(entry, arg);
    }

    fn wait(self: &Self, id: u64) {
        (**self).wait(id);
    }
}

/// One thread for each task.
pub struct Threads { }

impl Executor for Threads {
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
        let mut tid: u64 = 0;
        thread_started();
        if unsafe { pthread_create(&mut tid, 0 as *const u8, entry, arg) } != 0 {
            thread_ended();
            return null;
        }
        return tid;
    }

    fn wait(self: &Self, id: u64) {
        let mut raw_ret: *mut u8 = 0 as *mut u8;
        let _rc = unsafe { pthread_join(id, &mut raw_ret) };
        thread_ended();
    }
}

/// Every task runs on its caller, to the end, before `async` returns.
pub struct Inline { }

impl Executor for Inline {
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
        return null;
    }

    fn wait(self: &Self, id: u64) {
    }
}

/// Tasks with stacks of their own, taking turns on the thread that started them. A task runs
/// until it waits, so nothing else changes in between, and a blocking call stops them all. A
/// handle must be awaited on that thread.
pub struct Fibers { }

impl Executor for Fibers {
    fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
        return fiber_start(entry, arg);
    }

    fn wait(self: &Self, id: u64) {
        fiber_join(id);
    }
}

/// A task on a worker, which a `Task` waits for through `done`.
struct Job {
    entry: fn(*mut u8) -> *mut u8,
    arg: *mut u8,
    done: Channel[i32],
}

fn run_job(raw: *mut u8) -> *mut u8 {
    let job = raw as *mut Job;
    unsafe {
        let _none = ((*job).entry)((*job).arg);
        let _sent = (*job).done.send(1);
    }
    return 0 as *mut u8;
}

/// Waits for `job`, or until its waiter is told to stop.
fn job_finished(job: *mut Job) -> bool {
    let _done = unsafe { (*job).done.recv() } catch |e| return false;
    return true;
}

/// A worker's life: fibers for what it is sent, until it is sent 0, and then until they are done.
fn run_worker(raw: *mut u8) -> *mut u8 {
    let jobs = raw as *const Channel[usize];
    let mut running = Vec[u64]::new();
    while true {
        let job = unsafe { (*jobs).recv() } catch |e| 0;
        if job == 0 {
            break;
        }
        running.push(fiber_start(run_job, job as *mut u8));
        let mut i: usize = 0;
        while i < running.len() {
            let id = *(running.get(i) orelse unreachable);
            if fiber_finished(id) {
                fiber_join(id);
                let last = running.len() - 1;
                running.swap(i, last);
                let _gone = running.pop();
            } else {
                i = i + 1;
            }
        }
    }
    while let id = running.pop() {
        fiber_join(id);
    }
    thread_ended();
    return 0 as *mut u8;
}

/// Worker threads, each with fibers of its own. A task stays on the worker it is given to, so
/// `thread_local` statics stay the same across its waits, and tasks on different workers really do
/// run at once. Tasks go to workers in turn. Dropping the pool lets what it was given finish.
pub opaque(unsafe send, unsafe sync) WorkerPool {
    queues: Vec[Channel[usize]],
    threads: Vec[u64],
    cell turn: usize,

    pub fn new(workers: usize) -> Self {
        let mut queues = Vec[Channel[usize]]::new();
        for i in 0..workers {
            queues.push(Channel[usize]::new());
        }
        let mut threads = Vec[u64]::new();
        for i in 0..workers {
            let queue = queues.get(i) orelse unreachable;
            let mut tid: u64 = 0;
            thread_started();
            let arg = queue as *const Channel[usize] as *mut u8;
            let _rc = unsafe { pthread_create(&mut tid, 0 as *const u8, run_worker, arg) };
            threads.push(tid);
        }
        return Self { queues: move queues, threads: move threads, turn: 0 };
    }

    pub fn workers(self: &Self) -> usize {
        return self.queues.len();
    }

    impl Executor {
        fn start(self: &Self, entry: fn(*mut u8) -> *mut u8, arg: *mut u8) -> ?u64 {
            if self.queues.len() == 0 {
                return null;
            }
            let job: *own Job = unsafe { @alloc(Job, 1) as *own Job };
            unsafe {
                *job = Job { entry: entry, arg: arg, done: Channel[i32]::new() };
            }
            let turn = unsafe { @atomic_add_relaxed(&raw mut self.turn, 1) };
            let queue = self.queues.get(turn % self.queues.len()) orelse unreachable;
            let _sent = queue.send(job as usize);
            return job as usize as u64;
        }

        fn wait(self: &Self, id: u64) {
            let job = id as usize as *mut Job;
            // Being cancelled does not end the wait: the task is cancelled with its waiter.
            while !job_finished(job) {
                let _r = sleep_briefly();
            }
            unsafe {
                @drop(job);
                @dealloc(job);
            }
        }
    }

    impl drop {
        fn drop(self: &mut Self) {
            for queue in self.queues.iter() {
                let _sent = queue.send(0);
            }
            for tid in self.threads.iter() {
                let mut raw_ret: *mut u8 = 0 as *mut u8;
                let _rc = unsafe { pthread_join(*tid, &mut raw_ret) };
            }
        }
    }
}

/// The program's executor: the root module's `ProgramExecutor` if it has one.
pub alias DefaultExecutor = Threads;

/// A task started by `async`. Dropping the handle cancels the task and waits for it, so a task
/// cannot outlive what it borrows. If `R` is linear the handle is too, so a result is not lost.
pub opaque(owns R, unsafe send) Task[R: send, E: Executor + copy + send = DefaultExecutor] {
    // Set if the executor took the task, for `wait`.
    id: ?u64,
    executor: E,
    // Apart, because the scope is shared with the running task and the result is not.
    scope: *own CancelScope,
    result: *own ?R,

    pub(mod) fn create(id: ?u64, executor: E, scope: *own CancelScope, result: *own ?R) -> Self borrows(executor) {
        return Self { id: id, executor: executor, scope: scope, result: result };
    }

    pub(mod) fn box_scope(outer: usize) -> *own CancelScope {
        let scope: *own CancelScope = unsafe { @alloc(CancelScope, 1) as *own CancelScope };
        unsafe {
            *scope = CancelScope::nested_in(outer);
        }
        return scope;
    }

    pub(mod) fn box_result() -> *own ?R {
        let result: *own ?R = unsafe { @alloc(?R, 1) as *own ?R };
        unsafe {
            *result = null;
        }
        return result;
    }

    fn take_result(self: &Self) -> R {
        if let id = self.id {
            self.executor.wait(id);
        }
        unsafe {
            let slot: *mut ?R = self.result;
            let taken = move *slot;
            @dealloc(slot);
            @dealloc(self.scope);
            if let r = taken {
                return move r;
            }
        }
        @trap();
    }

    /// Asks the task to stop, then waits for it. The task decides what that means, and its
    /// result is still returned, so a value it already produced is not lost.
    pub fn cancel(move self) -> R {
        unsafe {
            (*self.scope).cancel();
        }
        return self.await();
    }

    impl drop where R: !linear {
        fn drop(self: &mut Self) {
            unsafe {
                (*self.scope).cancel();
            }
            let _result = self.take_result();
        }
    }

    // A handle to a linear result cannot be dropped, so this never runs.
    impl drop where R: linear {
        fn drop(self: &mut Self) {
        }
    }

    impl Future[R] {
        fn await(move self) -> R {
            let result = self.take_result();
            unsafe {
                @forget(self);
            }
            return result;
        }
    }
}

/// Starts `f` as a task on the program's executor, which `async f(x)` lowers to.
pub fn start_task[F: send + callable](f: F) -> Task[ResultOf[F]] borrows(f) {
    return start_task_on(move f, @default(DefaultExecutor));
}

/// Starts `f` as a task on `executor`, which `async(e) f(x)` lowers to. Waiting for the task, or
/// dropping its handle, is what ends it, so the handle holds whatever `f` and `executor` borrow.
pub fn start_task_on[F: send + callable, E: Executor + copy + send](f: F, executor: E) -> Task[ResultOf[F], E] borrows(f, executor) {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let start = raw_ctx as *mut TaskStart[F, ResultOf[F]];
        unsafe {
            let mut local_f = move (*start).f;
            let scope = (*start).scope;
            let outer = (*start).outer;
            let result = (*start).result;
            @dealloc(start);
            set_current_scope(scope as usize);
            let slot = result as *own ?ResultOf[F];
            *slot = local_f();
            (*scope).wait_tasks();
            scope_end_task(outer);
            return 0 as *mut u8;
        }
    };
    let outer = current_scope();
    scope_add_task(outer);
    let scope = Task[ResultOf[F], E]::box_scope(outer);
    let result = Task[ResultOf[F], E]::box_result();
    let start: *own TaskStart[F, ResultOf[F]] = unsafe {
        @alloc(TaskStart[F, ResultOf[F]], 1) as *own TaskStart[F, ResultOf[F]]
    };
    unsafe {
        *start = TaskStart[F, ResultOf[F]] {
            f: move f,
            scope: scope as *mut CancelScope,
            outer: outer,
            result: result as *mut ?ResultOf[F],
        };
    }
    let id = executor.start(entry, start as *mut u8);
    let mut taken = false;
    if let _id = id {
        taken = true;
    }
    if !taken {
        // Nothing took it, so it runs here: `async` promises the work happens.
        let _none = entry(start as *mut u8);
        set_current_scope(outer);
    }
    return Task[ResultOf[F], E]::create(id, executor, scope, result);
}

/// What a scoped thread starts from: its closure, and its creator's cancel scope.
struct ThreadStart[F] { f: F, scope: usize }

pub opaque(linear) ScopedHandle[F: send] {
    tid: u64,
    anchor: *own F,

    pub(mod) fn create(tid: u64, anchor: *own F) -> Self {
        return Self {
            tid: tid,
            anchor: anchor,
        };
    }

    // Stores the closure for the new thread; only a linear owner may keep a (possibly
    // linear) `F` behind a raw pointer.
    pub(mod) fn box_closure(f: F) -> *mut ThreadStart[F] {
        let start: *own ThreadStart[F] = unsafe { @alloc(ThreadStart[F], 1) as *own ThreadStart[F] };
        unsafe {
            *start = ThreadStart[F] { f: move f, scope: current_scope() };
        }
        scope_add_task(current_scope());
        return start;
    }

    pub fn join(move self) -> i32 {
        let mut raw_ret: *mut u8 = 0 as *mut u8;
        let _rc = unsafe { pthread_join(self.tid, &mut raw_ret) };
        return raw_ret as usize as i32;
    }

    impl Future[i32] {
        fn await(move self) -> i32 {
            return self.join();
        }
    }
}

pub fn spawn_scoped[F: send + callable](f: F) -> ScopedHandle[F] {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let start = raw_ctx as *mut ThreadStart[F];
        unsafe {
            let mut local_f = move (*start).f;
            let scope = (*start).scope;
            set_current_scope(scope);
            @dealloc(start);
            let res: i32 = local_f();
            scope_end_task(scope);
            thread_ended();
            return res as usize as *mut u8;
        }
    };
    let start = ScopedHandle[F]::box_closure(move f);
    let box_ptr = start as *mut u8;
    let mut tid: u64 = 0;
    thread_started();
    let _rc = unsafe { pthread_create(&mut tid, 0 as *const u8, entry, box_ptr) };
    return ScopedHandle[F]::create(tid, unsafe { start as *own F });
}

pub opaque(linear, owns R, unsafe sync) JoinHandle[R: send] {
    tid: u64,

    pub(mod) fn create(tid: u64) -> Self {
        return Self {
            tid: tid,
        };
    }

    // Stores the closure for the new thread; only a linear owner may keep a (possibly
    // linear) closure behind a raw pointer.
    pub(mod) fn box_closure[F](f: F) -> *mut F {
        let p: *own F = unsafe { @alloc(F, 1) as *own F };
        unsafe {
            *p = move f;
        }
        return p;
    }

    /// A thread's result travels in the pointer it exits with, or behind it if too big.
    pub(mod) fn pack_ret(val: R) -> *mut u8 {
        let mut raw_ret: *mut u8 = 0 as *mut u8;
        unsafe {
            if @size_of(R) > @size_of(*mut u8) {
                let boxed: *own R = @alloc(R, 1) as *own R;
                *boxed = move val;
                return boxed as *mut u8;
            }
            let dst_ptr = (&mut raw_ret as *mut *mut u8 as usize) as *own R;
            *dst_ptr = move val;
        }
        return raw_ret;
    }

    pub fn join(move self) -> R {
        let mut raw_ret: *mut u8 = 0 as *mut u8;
        let _rc = unsafe { pthread_join(self.tid, &mut raw_ret) };
        unsafe {
            if @size_of(R) > @size_of(*mut u8) {
                let boxed = raw_ret as *mut R;
                let val = move *boxed;
                @dealloc(boxed);
                return val;
            }
            let res_ptr = (&mut raw_ret as *mut *mut u8 as usize) as *mut R;
            return move *res_ptr;
        }
    }

    pub fn detach(move self) where R: !linear {
        let _rc = unsafe { pthread_detach(self.tid) };
    }

    impl Future[R] {
        fn await(move self) -> R {
            return self.join();
        }
    }
}

pub fn spawn[F: send + callable](f: F) -> JoinHandle[F] {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let f_ptr = raw_ctx as *mut F;
        unsafe {
            let mut local_f = move *f_ptr;
            @dealloc(f_ptr);
            let res = local_f();
            thread_ended();
            return JoinHandle[F]::pack_ret(res);
        }
    };
    let box_f: *mut F = JoinHandle[F]::box_closure[F](move f);
    let mut tid: u64 = 0;
    thread_started();
    let _rc = unsafe { pthread_create(&mut tid, 0 as *const u8, entry, box_f as *mut u8) };
    return JoinHandle[F]::create(tid);
}
";

pub const STD_FMT_SRC: &str = "\
safe extern fn malloc(size: usize) -> *mut u8;
extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);

pub import core::fmt::*;

/// A growable, heap-allocated UTF-8 string.
pub opaque String {
    ptr: ?*own u8,
    len: usize,
    cap: usize,

    impl drop {
        fn drop(self: &mut Self) {
            if let p = self.ptr {
                unsafe {
                    @dealloc(p);
                }
            }
        }
    }

    impl clone {
        fn clone(self: &Self) -> Self {
            return String::from(self.as_str());
        }
    }

    impl format {
        fn format(self: &Self, f: &mut Formatter) {
            f.write_str(self.as_str());
        }
    }

    pub fn new() -> Self {
        return Self { ptr: null, len: 0, cap: 0 };
    }

    pub fn with_capacity(cap: usize) -> Self {
        let mut s = Self::new();
        s.reserve(cap);
        return s;
    }

    pub fn from(text: &str) -> Self {
        let mut s = Self::with_capacity(text.len);
        s.push_str(text);
        return s;
    }

    /// A string taking ownership of `len` bytes at `ptr`, from `@alloc`.
    pub unsafe fn from_raw(ptr: *mut u8, len: usize) -> Self {
        return Self { ptr: unsafe { ptr as *own u8 }, len: len, cap: len };
    }

    pub fn len(self: &Self) -> usize {
        return self.len;
    }

    pub fn capacity(self: &Self) -> usize {
        return self.cap;
    }

    pub fn is_empty(self: &Self) -> bool {
        return self.len == 0;
    }

    /// Makes room for at least `extra` more bytes.
    pub fn reserve(self: &mut Self, extra: usize) {
        let need = self.len + extra;
        if need <= self.cap {
            return;
        }
        let mut new_cap: usize = 16;
        if self.cap > 0 {
            new_cap = self.cap * 2;
        }
        while new_cap < need {
            new_cap = new_cap * 2;
        }
        if let old_ptr = self.ptr {
            unsafe {
                self.ptr = @realloc(u8, old_ptr, new_cap) as *own u8;
            }
        } else {
            self.ptr = unsafe { @alloc(u8, new_cap) as *own u8 };
        }
        self.cap = new_cap;
    }

    pub fn push_byte(self: &mut Self, b: u8) {
        self.reserve(1);
        let p = self.ptr orelse unreachable;
        unsafe {
            *(p + self.len) = b;
        }
        self.len += 1;
    }

    pub fn push_str(self: &mut Self, text: &str) {
        self.reserve(text.len);
        if text.len == 0 {
            return;
        }
        let p = self.ptr orelse unreachable;
        for (b, i) in text {
            unsafe {
                *(p + self.len + i) = b;
            }
        }
        self.len += text.len;
    }

    /// Appends `c` encoded as UTF-8.
    pub fn push(self: &mut Self, c: rune) {
        let v = c as u32;
        if v < 128 {
            self.push_byte(v as u8);
        } else if v < 2048 {
            self.push_byte((192 | (v >> 6)) as u8);
            self.push_byte((128 | (v & 63)) as u8);
        } else if v < 65536 {
            self.push_byte((224 | (v >> 12)) as u8);
            self.push_byte((128 | ((v >> 6) & 63)) as u8);
            self.push_byte((128 | (v & 63)) as u8);
        } else {
            self.push_byte((240 | (v >> 18)) as u8);
            self.push_byte((128 | ((v >> 12) & 63)) as u8);
            self.push_byte((128 | ((v >> 6) & 63)) as u8);
            self.push_byte((128 | (v & 63)) as u8);
        }
    }

    pub fn clear(self: &mut Self) {
        self.len = 0;
    }

    pub fn as_str(self: &Self) -> &str {
        // An empty string may have no buffer: a zero length never dereferences the pointer.
        let mut p: *mut u8 = 1 as *mut u8;
        if let ptr = self.ptr {
            p = ptr;
        }
        unsafe {
            let arr_ref: &[u8; 0] = &*(p as *const [u8; 0]);
            return arr_ref[0..self.len];
        }
    }
}

pub fn format[T: format](val: T) -> String {
    let cap: usize = 512;
    let raw: *mut u8 = unsafe { @alloc(u8, cap) };
    let mut f = unsafe { Formatter::new(raw, cap) };
    @format(&mut f, val);
    if !f.is_truncated() {
        return unsafe { String::from_raw(raw, f.len()) };
    }
    // Now the size is known. Formatting twice runs a `format` hook twice.
    unsafe { @dealloc(raw); }
    let size = f.wanted();
    let whole: *mut u8 = unsafe { @alloc(u8, size) };
    let mut g = unsafe { Formatter::new(whole, size) };
    @format(&mut g, val);
    return unsafe { String::from_raw(whole, g.len()) };
}
";

pub const STD_IO_SRC: &str = "\
pub extern fn puts(s: *const u8) -> i32;
pub extern fn write(fd: i32, buf: *const u8, count: usize) -> isize;
pub extern fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
extern fn fopen(path: *const u8, mode: *const u8) -> ?*mut u8;
extern fn fread(buf: *mut u8, size: usize, count: usize, f: *mut u8) -> usize;
extern fn fwrite(buf: *const u8, size: usize, count: usize, f: *mut u8) -> usize;
extern fn fclose(f: *mut u8) -> i32;

extern fn pipe(fds: *mut [i32; 2]) -> i32;
extern fn close(fd: i32) -> i32;
extern fn socket(domain: i32, kind: i32, protocol: i32) -> i32;
extern fn setsockopt(fd: i32, level: i32, name: i32, value: *const i32, len: u32) -> i32;
extern fn bind(fd: i32, addr: *const SocketAddress, len: u32) -> i32;
extern fn listen(fd: i32, backlog: i32) -> i32;
extern fn connect(fd: i32, addr: *const SocketAddress, len: u32) -> i32;
extern fn getsockname(fd: i32, addr: *mut SocketAddress, len: *mut u32) -> i32;
extern fn getsockopt(fd: i32, level: i32, name: i32, value: *mut i32, len: *mut u32) -> i32;
extern fn accept4(fd: i32, addr: *mut u8, len: *mut u32, flags: i32) -> i32;
extern fn fcntl(fd: i32, command: i32, arg: i32) -> i32;
extern fn signal(number: i32, handler: usize) -> usize;
extern fn __errno_location() -> *mut i32;

pub import core::fmt::Formatter;
pub import std::fmt::{String, format};
import std::sync::{wait_fd, wait_fd_once, on_fibers, POLL_IN, POLL_OUT};

/// Why reading or writing stopped.
pub error IoError { Cancelled, TimedOut, Failed }

/// `poll` promises this much room in a pipe, so a descriptor that blocks can take it at once.
const WRITE_CHUNK: usize = 4096;

const EINTR: i32 = 4;
const EAGAIN: i32 = 11;
const O_NONBLOCK: i32 = 2048;
const ECONNABORTED: i32 = 103;
const EINPROGRESS: i32 = 115;

fn os_error() -> i32 {
    return unsafe { *__errno_location() };
}

fn stopped(reason: i32) -> IoError!void {
    if reason == 1 {
        return .Cancelled;
    }
    if reason == 2 {
        return .TimedOut;
    }
}

/// An open file descriptor, closed on drop.
pub opaque Fd {
    raw: i32,
    /// Made here, and non-blocking, so a read or write can be tried at once. A descriptor from
    /// elsewhere keeps its flags, which it may share, and is asked about first.
    own_flags: bool,

    /// Takes ownership of `raw`. Writing to something with no reader is then an error from
    /// `write_all`, not `SIGPIPE`, whose default ends the process: this ignores it for the whole
    /// process, which any C code in it will see.
    pub fn from_raw(raw: i32) -> Self {
        let _old = unsafe { signal(13, 1) };
        return Self { raw: raw, own_flags: false };
    }

    /// Takes ownership of `raw`, already non-blocking.
    pub(mod) fn nonblocking(raw: i32) -> Self {
        let _old = unsafe { signal(13, 1) };
        return Self { raw: raw, own_flags: true };
    }

    /// Waits as `events` says, with nothing to wait for unless the descriptor is one that blocks.
    fn before_io(self: &Self, events: i16) -> IoError!void {
        if !self.own_flags {
            try stopped(wait_fd(self.raw, events));
        }
    }

    /// What to do about a read or write that failed.
    fn after_failure(self: &Self, events: i16) -> IoError!void {
        let error = os_error();
        if error == EAGAIN && self.own_flags {
            try stopped(wait_fd_once(self.raw, events));
        } else if error != EINTR {
            return .Failed;
        }
    }

    pub fn raw(self: &Self) -> i32 {
        return self.raw;
    }

    /// Reads what is available into `buf`, up to its length. 0 means the end of the stream.
    pub fn read(self: &Self, buf: &mut [u8]) -> IoError!usize {
        if buf.len == 0 {
            return 0;
        }
        while true {
            try self.before_io(POLL_IN);
            let n = unsafe { read(self.raw, &mut buf[0] as *mut u8, buf.len) };
            if n >= 0 {
                return n as usize;
            }
            try self.after_failure(POLL_IN);
        }
        return .Failed;
    }

    /// Writes all of `data`. With no reader left this is `.Failed`.
    pub fn write_all(self: &Self, data: &str) -> IoError!void {
        let mut done: usize = 0;
        while done < data.len {
            try self.before_io(POLL_OUT);
            let mut chunk = data.len - done;
            if chunk > WRITE_CHUNK {
                chunk = WRITE_CHUNK;
            }
            let n = unsafe { write(self.raw, &data[done] as *const u8, chunk) };
            if n >= 0 {
                done = done + n as usize;
            } else {
                try self.after_failure(POLL_OUT);
            }
        }
    }

    impl drop {
        fn drop(self: &mut Self) {
            let _rc = unsafe { close(self.raw) };
        }
    }
}

/// The two ends of a pipe.
pub struct Pipe {
    reader: Fd,
    writer: Fd,
}

pub fn open_pipe() -> ?Pipe {
    let mut fds: [i32; 2] = { 0, 0 };
    if unsafe { pipe(&raw mut fds) } != 0 {
        return null;
    }
    let _a = unsafe { fcntl(fds[0], 4, O_NONBLOCK) };
    let _b = unsafe { fcntl(fds[1], 4, O_NONBLOCK) };
    return Pipe { reader: Fd::nonblocking(fds[0]), writer: Fd::nonblocking(fds[1]) };
}

/// `sockaddr_in`.
struct SocketAddress {
    family: u16,
    port: u16,
    host: u32,
    zero: u64,
}

fn swap_bytes(port: u16) -> u16 {
    return (port >> 8) | (port << 8);
}

/// The dotted form of an IPv4 address, in the order the bytes have in memory, or null.
pub fn parse_ipv4(text: &str) -> ?u32 {
    let mut address: u32 = 0;
    let mut part: u32 = 0;
    let mut digits: usize = 0;
    let mut dots: u32 = 0;
    let mut at: usize = 0;
    while at <= text.len {
        if at == text.len || text[at] == 46 {
            if digits == 0 {
                return null;
            }
            address = address | (part << (dots * 8));
            part = 0;
            digits = 0;
            if at < text.len {
                dots = dots + 1;
                if dots > 3 {
                    return null;
                }
            }
        } else {
            if text[at] < 48 || text[at] > 57 {
                return null;
            }
            part = part * 10 + (text[at] - 48) as u32;
            digits = digits + 1;
            if part > 255 || digits > 3 {
                return null;
            }
        }
        at = at + 1;
    }
    if dots != 3 {
        return null;
    }
    return address;
}

fn address_of(host: &str, port: u16) -> ?SocketAddress {
    let parsed = parse_ipv4(host) orelse return null;
    return SocketAddress { family: 2, port: swap_bytes(port), host: parsed, zero: 0 };
}

/// A TCP socket listening for connections.
pub opaque TcpListener {
    socket: Fd,

    /// Listens on `host`, an IPv4 address such as `127.0.0.1`. Port 0 picks a free one, which
    /// `port` then reports.
    pub fn bind(host: &str, port: u16) -> ?Self {
        let address = address_of(host, port) orelse return null;
        let raw = unsafe { socket(2, 1, 0) };
        if raw < 0 {
            return null;
        }
        let fd = Fd::from_raw(raw);
        let on: i32 = 1;
        let _rc = unsafe { setsockopt(raw, 1, 2, &raw const on, 4) };
        if unsafe { bind(raw, &raw const address, 16) } != 0 || unsafe { listen(raw, 128) } != 0 {
            return null;
        }
        return Self { socket: fd };
    }

    pub fn port(self: &Self) -> u16 {
        let mut address = SocketAddress { family: 0, port: 0, host: 0, zero: 0 };
        let mut len: u32 = 16;
        let _rc = unsafe { getsockname(self.socket.raw(), &raw mut address, &raw mut len) };
        return swap_bytes(address.port);
    }

    /// Waits for a connection.
    pub fn accept(self: &Self) -> IoError!Fd {
        while true {
            try stopped(wait_fd(self.socket.raw(), POLL_IN));
            let raw = unsafe { accept4(self.socket.raw(), 0 as *mut u8, 0 as *mut u32, O_NONBLOCK) };
            if raw >= 0 {
                return Fd::nonblocking(raw);
            }
            let error = os_error();
            if error != EINTR && error != ECONNABORTED {
                return .Failed;
            }
        }
        return .Failed;
    }
}

/// Connects to `port` on `host`, an IPv4 address. Other fibers run meanwhile, and a task can be
/// cancelled or reach its deadline, which is how to give this a timeout.
pub fn connect_to(host: &str, port: u16) -> IoError!Fd {
    let address = address_of(host, port) orelse return .Failed;
    let raw = unsafe { socket(2, 1, 0) };
    if raw < 0 {
        return .Failed;
    }
    let fd = Fd::nonblocking(raw);
    let flags = unsafe { fcntl(raw, 3, 0) };
    let _set = unsafe { fcntl(raw, 4, flags | O_NONBLOCK) };
    if unsafe { connect(raw, &raw const address, 16) } != 0 {
        if os_error() != EINPROGRESS {
            return .Failed;
        }
        try stopped(wait_fd(raw, POLL_OUT));
        let mut failure: i32 = 0;
        let mut len: u32 = 4;
        let _rc = unsafe { getsockopt(raw, 1, 4, &raw mut failure, &raw mut len) };
        if failure != 0 {
            return .Failed;
        }
    }
    return fd;
}

/// Writes `count` bytes to `fd`, however many calls that takes, returning how many it managed.
fn write_fully(fd: i32, ptr: *const u8, count: usize) -> isize {
    let mut done: usize = 0;
    while done < count {
        let n = unsafe { write(fd, ptr + done, count - done) };
        if n >= 0 {
            done = done + n as usize;
        } else if os_error() != EINTR {
            break;
        }
    }
    return done as isize;
}

pub fn print_str(s: &str) -> isize {
    if s.len == 0 {
        return 0;
    }
    return write_fully(1, &s[0] as *const u8, s.len);
}

/// Most output fits the buffer on the stack, and what does not goes through `format`.
fn emit[T: format](fd: i32, val: T, newline: bool) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = unsafe { Formatter::new(ptr, 512) };
    @format(&mut f, val);
    if newline {
        f.write_byte(10);
    }
    if !f.is_truncated() {
        return write_fully(fd, ptr as *const u8, f.len());
    }
    let mut text = format(val);
    if newline {
        text.push_byte(10);
    }
    let bytes = text.as_str();
    return write_fully(fd, &bytes[0] as *const u8, bytes.len);
}

pub fn print[T: format](val: T) -> isize {
    return emit(1, val, false);
}

pub fn println[T: format](val: T) -> isize {
    return emit(1, val, true);
}

pub fn eprint[T: format](val: T) -> isize {
    return emit(2, val, false);
}

pub fn eprintln[T: format](val: T) -> isize {
    return emit(2, val, true);
}

/// One line from standard input without its newline, or `null` at end of input.
pub fn read_line() -> ?String {
    let mut line = String::new();
    let mut b: u8 = 0;
    let mut got_any = false;
    while true {
        if on_fibers() && wait_fd(0, POLL_IN) != 0 {
            break;
        }
        let n = unsafe { read(0, &mut b as *mut u8, 1) };
        if n <= 0 {
            break;
        }
        got_any = true;
        if b == 10 {
            break;
        }
        line.push_byte(b);
    }
    if !got_any {
        return null;
    }
    return line;
}

/// `path` as a NUL-terminated C string.
fn c_path(path: &str) -> String {
    let mut p = String::from(path);
    p.push_byte(0);
    return p;
}

/// The whole contents of the file at `path`, or `null` if it cannot be read.
pub fn read_file(path: &str) -> ?String {
    let p = c_path(path);
    let f = unsafe { fopen(&p.as_str()[0] as *const u8, \"rb\" as *const u8) } orelse return null;
    let mut out = String::new();
    let mut buf: [u8; 4096] = @default([u8; 4096]);
    while true {
        let n = unsafe { fread(&mut buf[0] as *mut u8, 1, 4096, f) };
        if n == 0 {
            break;
        }
        for i in 0..n {
            out.push_byte(buf[i]);
        }
    }
    let _ = unsafe { fclose(f) };
    return out;
}

/// Replaces the file at `path` with `contents`; `false` if it cannot be written.
pub fn write_file(path: &str, contents: &str) -> bool {
    let p = c_path(path);
    let f = unsafe { fopen(&p.as_str()[0] as *const u8, \"wb\" as *const u8) } orelse return false;
    let mut ok = true;
    if contents.len > 0 {
        ok = unsafe { fwrite(&contents[0] as *const u8, 1, contents.len, f) } == contents.len;
    }
    return unsafe { fclose(f) } == 0 && ok;
}
";

pub const STD_BUILD_SRC: &str = "\
pub enum OptimizeMode {
    Debug,
    ReleaseSafe,
    ReleaseFast,
    ReleaseSmall,
}

pub struct Target {
    pub enum Os {
        Linux,
        MacOs,
        Windows,
        FreeBsd,
        Freestanding,
    }

    pub enum Arch {
        X86_64,
        Aarch64,
        Riscv64,
        Wasm32,
    }

    pub os: Os,
    pub arch: Arch,
    pub optimize: OptimizeMode = OptimizeMode::Debug,
}

pub struct Dependency {
    pub name: &str,
    pub url: &str,
    pub sha256: u256,
}

pub struct Package {
    pub name: &str,
    pub version: tuple { u32, u32, u32 } = { 0, 1, 0 },
    pub root: &str = \"src/main.slop\",
    pub no_std: bool = false,
    pub deps: &[Dependency] = &[],
    pub system_libs: &[&str] = &[],
}
";

pub const STD_COLLECTIONS_SRC: &str = "\
import std::mem::{Allocator, Global, alloc_in, realloc_in, dealloc_in};
import std::fmt::String;
/// A growable heap array. It owns its elements (`owns T`): with a linear `T` the vector itself is
/// linear and is consumed with `drain`, `pop`, or `into_...`; otherwise it drops its elements.
/// A borrowing iterator over a sequence's elements, yielding `&T`. Each item borrows the iterator,
/// which in turn borrows the sequence.
pub opaque Iter[T] {
    p: *ref T,
    left: usize,

    /// An iterator over the `len` elements at `p`, which must be valid for as long as the
    /// borrow `p` carries.
    pub unsafe fn from_raw(p: *ref T, len: usize) -> Self {
        return Self { p: p, left: len };
    }

    /// The next item. It borrows the sequence, not the iterator, so items may be held across
    /// further calls.
    pub fn next(self: &mut Self) -> ?&T borrows(*self) {
        if self.left == 0 {
            return null;
        }
        self.left -= 1;
        let cur = self.p;
        self.p = cur + 1;
        unsafe {
            return &*cur;
        }
    }
}

/// A borrowing iterator over a sequence's elements, yielding `&mut T`.
pub opaque IterMut[T] {
    p: *ref mut T,
    left: usize,

    /// An iterator over the `len` elements at `p`, which must be valid and unaliased for as
    /// long as the borrow `p` carries.
    pub unsafe fn from_raw(p: *ref mut T, len: usize) -> Self {
        return Self { p: p, left: len };
    }

    /// The next item, distinct from every other item this iterator yields.
    pub fn next(self: &mut Self) -> ?&mut T borrows(*self) {
        if self.left == 0 {
            return null;
        }
        self.left -= 1;
        let cur = self.p;
        self.p = cur + 1;
        unsafe {
            return &mut *cur;
        }
    }
}

pub opaque Vec[T, A: Allocator + copy = Global] {
    ptr: ?*own T,
    len: usize,
    cap: usize,
    allocator: A,

    pub fn new() -> Self where A: default {
        return Self::new_in(@default(A));
    }

    pub fn new_in(allocator: A) -> Self borrows(allocator) {
        return Self { ptr: null, len: 0, cap: 0, allocator: allocator };
    }

    pub fn with_capacity(cap: usize) -> Self where A: default {
        return Self::with_capacity_in(cap, @default(A));
    }

    pub fn with_capacity_in(cap: usize, allocator: A) -> Self borrows(allocator) {
        if cap == 0 {
            return Self::new_in(allocator);
        }
        let p: *own T = unsafe { alloc_in[T, A](&allocator, cap) as *own T };
        return Self { ptr: p, len: 0, cap: cap, allocator: allocator };
    }

    pub fn len(self: &Self) -> usize {
        return self.len;
    }

    pub fn capacity(self: &Self) -> usize {
        return self.cap;
    }

    pub fn is_empty(self: &Self) -> bool {
        return self.len == 0;
    }

    fn grow(self: &mut Self) -> *own T {
        if @size_of(T) == 0 {
            self.cap = 18446744073709551615;
            let p: *own T = unsafe { alloc_in[T, A](&self.allocator, 1) as *own T };
            self.ptr = p;
            return p;
        }
        let mut new_cap: usize = 4;
        if self.cap > 0 {
            new_cap = self.cap * 2;
        }
        self.cap = new_cap;
        if let old_ptr = self.ptr {
            let p: *own T = unsafe { realloc_in[T, A](&self.allocator, old_ptr, new_cap) as *own T };
            self.ptr = p;
            return p;
        }
        let p: *own T = unsafe { alloc_in[T, A](&self.allocator, new_cap) as *own T };
        self.ptr = p;
        return p;
    }

    pub fn push(self: &mut Self, value: T) borrows(self: value) {
        let p: *own T = if self.len == self.cap {
            self.grow()
        } else {
            self.ptr orelse unreachable
        };
        unsafe {
            *(p + self.len) = move value;
        }
        self.len += 1;
    }

    pub fn pop(self: &mut Self) -> ?T borrows(*self) {
        if self.len == 0 {
            return null;
        }
        self.len -= 1;
        let p = self.ptr orelse unreachable;
        unsafe {
            return move *(p + self.len);
        }
    }

    /// Puts `value` at `index`, moving the elements from there on up by one. An `index` past the
    /// length traps.
    pub fn insert(self: &mut Self, index: usize, value: T) borrows(self: value) {
        if index > self.len {
            @trap();
        }
        let p: *own T = if self.len == self.cap {
            self.grow()
        } else {
            self.ptr orelse unreachable
        };
        let mut i = self.len;
        while i > index {
            unsafe {
                *(p + i) = move *(p + (i - 1));
            }
            i -= 1;
        }
        unsafe {
            *(p + index) = move value;
        }
        self.len += 1;
    }

    /// Takes out the element at `index`, moving those after it down by one, or null past the end.
    pub fn remove(self: &mut Self, index: usize) -> ?T borrows(*self) {
        if index >= self.len {
            return null;
        }
        let p = self.ptr orelse unreachable;
        let taken = unsafe { move *(p + index) };
        for i in index..(self.len - 1) {
            unsafe {
                *(p + i) = move *(p + (i + 1));
            }
        }
        self.len -= 1;
        return taken;
    }

    pub fn get(self: &Self, index: usize) -> ?&T {
        if index >= self.len {
            return null;
        }
        let p = self.ptr orelse unreachable;
        unsafe {
            return &*(p + index);
        }
    }

    pub fn get_mut(self: &mut Self, index: usize) -> ?&mut T {
        if index >= self.len {
            return null;
        }
        let p = self.ptr orelse unreachable;
        unsafe {
            return &mut *(p + index);
        }
    }

    /// The elements as a slice (`for x in v.as_slice()`).
    /// Sorts by `before(a, b)`, which says whether `a` goes first. Elements it does not order
    /// keep their order. It takes room for a copy of the elements.
    pub fn sort_by[F: callable](self: &mut Self, before: F) {
        if self.len < 2 || @size_of(T) == 0 {
            return;
        }
        let n = self.len;
        let start: *mut T = (self.ptr orelse unreachable) as *mut T;
        let spare: *mut T = alloc_in[T, A](&self.allocator, n);
        let mut from = start;
        let mut to = spare;
        let mut width: usize = 1;
        while width < n {
            let mut low: usize = 0;
            while low < n {
                let mut middle = low + width;
                if middle > n {
                    middle = n;
                }
                let mut high = middle + width;
                if high > n {
                    high = n;
                }
                let mut left = low;
                let mut right = middle;
                for k in low..high {
                    let take_right = right < high
                        && (left == middle || before(unsafe { &*(from + right) }, unsafe { &*(from + left) }));
                    unsafe {
                        let slot = (to + k) as *own T;
                        if take_right {
                            *slot = move *(from + right);
                            right = right + 1;
                        } else {
                            *slot = move *(from + left);
                            left = left + 1;
                        }
                    }
                }
                low = high;
            }
            let done = to;
            to = from;
            from = done;
            width = width * 2;
        }
        if from as usize != start as usize {
            for i in 0..n {
                unsafe {
                    let slot = (start + i) as *own T;
                    *slot = move *(from + i);
                }
            }
        }
        dealloc_in[T, A](&self.allocator, spare);
    }

    /// Sorts numbers, smallest first.
    pub fn sort(self: &mut Self) where T: number {
        self.sort_by(fn(a: &T, b: &T) -> bool { return *a < *b; });
    }

    /// Exchanges two elements, which is how to reorder what cannot be copied.
    pub fn swap(self: &mut Self, a: usize, b: usize) {
        if a >= self.len || b >= self.len {
            @trap();
        }
        if a == b {
            return;
        }
        let base: *mut T = (self.ptr orelse unreachable) as *mut T;
        unsafe {
            let x = move *(base + a);
            let y = move *(base + b);
            let first = (base + a) as *own T;
            let second = (base + b) as *own T;
            *first = move y;
            *second = move x;
        }
    }

    pub fn as_slice(self: &Self) -> &[T] {
        // An empty vector has no allocation: its slice uses a dangling, aligned pointer that
        // a zero length never dereferences.
        let p: *mut T = self.data_ptr();
        unsafe {
            return &(*(p as *const [T; 0]))[0..self.len];
        }
    }

    pub fn as_mut_slice(self: &mut Self) -> &mut [T] {
        let p: *mut T = self.data_ptr();
        unsafe {
            return &mut (*(p as *mut [T; 0]))[0..self.len];
        }
    }

    /// The elements' address: the allocation, or for an empty vector (which has none) a
    /// dangling, aligned pointer that a zero length never dereferences.
    fn data_ptr(self: &Self) -> *mut T {
        if let p = self.ptr {
            return p;
        }
        return (@align_of(T) as usize) as *mut T;
    }

    /// Iterates over the elements by reference (`for x in v.iter()`).
    pub fn iter(self: &Self) -> Iter[T] {
        unsafe {
            return Iter[T]::from_raw(self.data_ptr() as *ref T, self.len);
        }
    }

    /// Iterates over the elements by mutable reference (`for x in v.iter_mut()`).
    pub fn iter_mut(self: &mut Self) -> IterMut[T] {
        unsafe {
            return IterMut[T]::from_raw(self.data_ptr() as *ref mut T, self.len);
        }
    }

    /// Drops the elements past `new_len`.
    pub fn truncate(self: &mut Self, new_len: usize) where T: !linear {
        if new_len >= self.len {
            return;
        }
        let p = self.ptr orelse unreachable;
        let mut i: usize = new_len;
        while i < self.len {
            unsafe {
                @drop(p + i);
            }
            i += 1;
        }
        self.len = new_len;
    }

    pub fn clear(self: &mut Self) where T: !linear {
        self.truncate(0);
    }

    /// Consumes the vector, passing each element to `f` in order.
    pub fn drain[F: callable](move mut self, f: F) {
        let p = self.ptr orelse return;
        let n = self.len;
        self.len = 0;
        let mut i: usize = 0;
        while i < n {
            unsafe {
                f(move *(p + i));
            }
            i += 1;
        }
    }

    impl default where A: default {
        fn default() -> Self {
            return Self::new();
        }
    }

    impl clone where T: clone {
        fn clone(self: &Self) -> Self {
            let src_ptr = self.ptr orelse return Self::new_in(self.allocator);
            if self.len == 0 {
                return Self::new_in(self.allocator);
            }
            let new_ptr: *own T = unsafe { alloc_in[T, A](&self.allocator, self.len) as *own T };
            let mut i: usize = 0;
            while i < self.len {
                unsafe {
                    *(new_ptr + i) = @clone(&*(src_ptr + i));
                }
                i += 1;
            }
            return Self { ptr: new_ptr, len: self.len, cap: self.len, allocator: self.allocator };
        }
    }

    unsafe impl drop(may_dangle T) where T: !linear {
        fn drop(self: &mut Self) {
            if let p = self.ptr {
                let mut i: usize = 0;
                while i < self.len {
                    unsafe {
                        @drop(p + i);
                    }
                    i += 1;
                }
                unsafe {
                    dealloc_in[T, A](&self.allocator, p);
                }
            }
        }
    }

    unsafe impl drop(may_dangle T) where T: linear {
        fn drop(self: &mut Self) {
            if let p = self.ptr {
                unsafe {
                    dealloc_in[T, A](&self.allocator, p);
                }
            }
        }
    }
}

fn is_space(b: u8) -> bool {
    return b == 32 || (b >= 9 && b <= 13);
}

/// `self` without the whitespace at either end.
pub fn trim(self: &str) -> &str borrows(self) {
    let mut start: usize = 0;
    let mut end = self.len;
    while start < end && is_space(self[start]) {
        start = start + 1;
    }
    while end > start && is_space(self[end - 1]) {
        end = end - 1;
    }
    return self[start..end];
}

pub fn starts_with(self: &str, prefix: &str) -> bool {
    return prefix.len <= self.len && self[0..prefix.len] == prefix;
}

pub fn ends_with(self: &str, suffix: &str) -> bool {
    return suffix.len <= self.len && self[(self.len - suffix.len)..] == suffix;
}

/// Where `needle` first appears. An empty one is found at the start.
pub fn find_str(self: &str, needle: &str) -> ?usize {
    if needle.len > self.len {
        return null;
    }
    for i in 0..(self.len - needle.len + 1) {
        if self[i..(i + needle.len)] == needle {
            return i;
        }
    }
    return null;
}

/// The parts of `self` between each `separator`, which must not be empty. Two in a row have an
/// empty part between them, so `a,,b` has three parts.
pub fn split(self: &str, separator: &str) -> Vec[&str] borrows(self) {
    if separator.len == 0 {
        @trap();
    }
    let mut parts = Vec[&str]::new();
    let mut start: usize = 0;
    let mut at: usize = 0;
    while at + separator.len <= self.len {
        if self[at..(at + separator.len)] == separator {
            parts.push(self[start..at]);
            at = at + separator.len;
            start = at;
        } else {
            at = at + 1;
        }
    }
    parts.push(self[start..]);
    return parts;
}

/// The runs of `self` between whitespace.
pub fn words(self: &str) -> Vec[&str] borrows(self) {
    let mut parts = Vec[&str]::new();
    let mut start: usize = 0;
    let mut inside = false;
    for i in 0..self.len {
        if is_space(self[i]) {
            if inside {
                parts.push(self[start..i]);
                inside = false;
            }
        } else if !inside {
            start = i;
            inside = true;
        }
    }
    if inside {
        parts.push(self[start..]);
    }
    return parts;
}

/// The decimal integer `self` is, with an optional sign, or null if it is not one or does not fit.
pub fn parse_int(self: &str) -> ?i64 {
    let mut at: usize = 0;
    let negative = self.len > 0 && self[0] == 45;
    if self.len > 0 && (self[0] == 45 || self[0] == 43) {
        at = 1;
    }
    if at == self.len {
        return null;
    }
    let mut value: i64 = 0;
    while at < self.len {
        if self[at] < 48 || self[at] > 57 {
            return null;
        }
        // Built negative, as the most negative value has no positive counterpart.
        value = (value *? 10) orelse return null;
        value = (value -? (self[at] - 48) as i64) orelse return null;
        at = at + 1;
    }
    if negative {
        return value;
    }
    return (0 -? value) orelse null;
}

/// Whether `self` sorts before `other`, byte by byte.
pub fn str_before(self: &str, other: &str) -> bool {
    let mut i: usize = 0;
    while i < self.len && i < other.len {
        if self[i] != other[i] {
            return self[i] < other[i];
        }
        i = i + 1;
    }
    return self.len < other.len;
}

/// Hash of an integer key (Fibonacci hashing).
pub fn hash_key[K: integer](k: K) -> u64 {
    return ((k as i64) as u64) *% 11400714819323198485;
}

/// Hash of a byte-sequence key such as `&str` (FNV-1a).
pub fn hash_key[K: sequence](k: K) -> u64 {
    let mut h: u64 = 14695981039346656037;
    for b in k {
        h = (h ^ (b as u64)) *% 1099511628211;
    }
    return h;
}

/// A key's hash, for a type that is not an integer or a string.
pub trait Hash {
    fn hash(self: &Self) -> u64;
}

/// Whether two keys are the same, for a type that is not an integer or a string.
pub trait Eq {
    fn eq(self: &Self, other: &Self) -> bool;
}

/// How a `HashMap[K, V]` key is looked up: a `String` by `&str`, so that a lookup need not make one,
/// a `copy` key by value, and anything else by reference.
pub fn Lookup[K] -> type {
    if K == String {
        return &str;
    } else if @satisfies(K, copy) {
        return K;
    } else {
        return &K;
    }
}

fn view_key[K](key: &K) -> Lookup[K] borrows(key) {
    if K == String {
        return key.as_str();
    } else if @satisfies(K, copy) {
        return *key;
    } else {
        return key;
    }
}

/// `view_key` of a key in the map, whose `borrows` says what the result holds.
fn view_stored[K](key: *const K) -> Lookup[K] {
    if K == String {
        return unsafe { (*key).as_str() };
    } else if @satisfies(K, copy) {
        return unsafe { *key };
    } else {
        return unsafe { &*key };
    }
}

fn hash_lookup[K: unchecked](key: Lookup[K]) -> u64 {
    if K == String {
        return hash_key[&str](key);
    } else if @satisfies(K, Hash) {
        return key.hash();
    } else {
        return hash_key[K](key);
    }
}

fn same_key[K: unchecked](stored: &K, key: Lookup[K]) -> bool {
    if K == String {
        return stored.as_str() == key;
    } else if @satisfies(K, Eq) {
        if @satisfies(K, copy) {
            return stored.eq(&key);
        } else {
            return stored.eq(key);
        }
    } else {
        return *stored == key;
    }
}

/// A hash map with open addressing, which owns its keys and values. A key is an integer, `&str`,
/// `String`, or a type implementing `Hash` and `Eq`. With a linear `V` it is linear, and is consumed
/// with `drain`. `K` is `unchecked` because which of those it is decides how a key is hashed and
/// compared (see `Lookup`), so a key is checked where a map of it is used.
pub opaque HashMap[K: unchecked, V, A: Allocator + copy = Global] {
    keys: ?*own K,
    vals: ?*own V,
    // Slot states: 0 empty, 1 full, 2 removed.
    states: ?*own u8,
    len: usize,
    used: usize,
    cap: usize,
    allocator: A,

    pub fn new() -> Self where A: default {
        return Self::new_in(@default(A));
    }

    pub fn new_in(allocator: A) -> Self borrows(allocator) {
        return Self { keys: null, vals: null, states: null, len: 0, used: 0, cap: 0, allocator: allocator };
    }

    pub fn len(self: &Self) -> usize {
        return self.len;
    }

    pub fn is_empty(self: &Self) -> bool {
        return self.len == 0;
    }

    /// The slot holding `key`, if any.
    fn find(self: &Self, key: Lookup[K]) -> ?usize {
        if self.cap == 0 {
            return null;
        }
        let st = self.states orelse unreachable;
        let ks = self.keys orelse unreachable;
        let mask = self.cap - 1;
        let mut i = (hash_lookup[K](key) as usize) & mask;
        while true {
            let s = unsafe { *(st + i) };
            if s == 0 {
                return null;
            }
            if s == 1 && same_key[K](unsafe { &*(ks + i) }, key) {
                return i;
            }
            i = (i + 1) & mask;
        }
        return null;
    }

    /// Places `key` / `value` in the first free slot of its probe sequence (`key` absent).
    fn place(self: &mut Self, key: K, value: V) borrows(self: key, self: value) {
        let st = self.states orelse unreachable;
        let ks = self.keys orelse unreachable;
        let vs = self.vals orelse unreachable;
        let mask = self.cap - 1;
        let mut i = (hash_lookup[K](view_key[K](&key)) as usize) & mask;
        while unsafe { *(st + i) } == 1 {
            i = (i + 1) & mask;
        }
        if unsafe { *(st + i) } == 0 {
            self.used += 1;
        }
        unsafe {
            *(st + i) = 1;
            *(ks + i) = move key;
            *(vs + i) = move value;
        }
        self.len += 1;
    }

    /// Grows (and drops removed slots) when one more entry would pass 3/4 occupancy.
    fn reserve_one(self: &mut Self) {
        if (self.used + 1) * 4 <= self.cap * 3 {
            return;
        }
        let old_cap = self.cap;
        let old_states = self.states;
        let old_keys = self.keys;
        let old_vals = self.vals;
        let mut new_cap: usize = 8;
        while new_cap * 3 < (self.len + 1) * 4 * 2 {
            new_cap = new_cap * 2;
        }
        let st: *own u8 = unsafe { alloc_in[u8, A](&self.allocator, new_cap) as *own u8 };
        for i in 0..new_cap {
            unsafe {
                *(st + i) = 0;
            }
        }
        self.states = st;
        self.keys = unsafe { alloc_in[K, A](&self.allocator, new_cap) as *own K };
        self.vals = unsafe { alloc_in[V, A](&self.allocator, new_cap) as *own V };
        self.cap = new_cap;
        self.len = 0;
        self.used = 0;
        if let ost = old_states {
            let ok = old_keys orelse unreachable;
            let ov = old_vals orelse unreachable;
            for i in 0..old_cap {
                if unsafe { *(ost + i) } == 1 {
                    let k = unsafe { move *(ok + i) };
                    let v = unsafe { move *(ov + i) };
                    self.place(move k, v);
                }
            }
            unsafe {
                dealloc_in[u8, A](&self.allocator, ost);
                dealloc_in[K, A](&self.allocator, ok);
                dealloc_in[V, A](&self.allocator, ov);
            }
        }
    }

    /// Inserts `value` for `key`, returning the value it replaces.
    pub fn insert(self: &mut Self, key: K, value: V) -> ?V borrows(*self, self: key, self: value) {
        if let i = self.find(view_key[K](&key)) {
            let vs = self.vals orelse unreachable;
            let old = unsafe { move *(vs + i) };
            unsafe {
                *(vs + i) = move value;
            }
            return old;
        }
        self.reserve_one();
        self.place(move key, value);
        return null;
    }

    pub fn get(self: &Self, key: Lookup[K]) -> ?&V borrows(self) {
        let i = self.find(key) orelse return null;
        let vs = self.vals orelse unreachable;
        unsafe {
            return &*(vs + i);
        }
    }

    pub fn get_mut(self: &mut Self, key: Lookup[K]) -> ?&mut V borrows(self) {
        let i = self.find(key) orelse return null;
        let vs = self.vals orelse unreachable;
        unsafe {
            return &mut *(vs + i);
        }
    }

    pub fn contains_key(self: &Self, key: Lookup[K]) -> bool {
        if let i = self.find(key) {
            return true;
        }
        return false;
    }

    /// Removes `key`, returning its value.
    pub fn remove(self: &mut Self, key: Lookup[K]) -> ?V borrows(*self) {
        let i = self.find(key) orelse return null;
        let st = self.states orelse unreachable;
        let ks = self.keys orelse unreachable;
        let vs = self.vals orelse unreachable;
        unsafe {
            *(st + i) = 2;
            @drop(ks + i);
        }
        self.len -= 1;
        unsafe {
            return move *(vs + i);
        }
    }

    /// The keys, in slot order, as they are looked up.
    pub fn keys(self: &Self) -> Vec[Lookup[K]] borrows(self) {
        let mut out = Vec[Lookup[K]]::with_capacity(self.len);
        if let st = self.states {
            let ks = self.keys orelse unreachable;
            for i in 0..self.cap {
                if unsafe { *(st + i) } == 1 {
                    out.push(view_stored[K]((ks + i) as *const K));
                }
            }
        }
        return out;
    }

    /// Consumes the map, passing each key and value to `f`.
    pub fn drain[F: callable](move mut self, f: F) {
        let st = self.states orelse return;
        let ks = self.keys orelse unreachable;
        let vs = self.vals orelse unreachable;
        for i in 0..self.cap {
            if unsafe { *(st + i) } == 1 {
                unsafe {
                    *(st + i) = 2;
                    f(move *(ks + i), move *(vs + i));
                }
            }
        }
        self.len = 0;
    }

    impl default where A: default {
        fn default() -> Self {
            return Self::new();
        }
    }

    unsafe impl drop(may_dangle K, V) where V: !linear {
        fn drop(self: &mut Self) {
            if let st = self.states {
                let ks = self.keys orelse unreachable;
                let vs = self.vals orelse unreachable;
                for i in 0..self.cap {
                    if unsafe { *(st + i) } == 1 {
                        unsafe {
                            @drop(ks + i);
                            @drop(vs + i);
                        }
                    }
                }
                unsafe {
                    dealloc_in[u8, A](&self.allocator, st);
                    dealloc_in[K, A](&self.allocator, ks);
                    dealloc_in[V, A](&self.allocator, vs);
                }
            }
        }
    }

    unsafe impl drop(may_dangle K, V) where V: linear {
        fn drop(self: &mut Self) {
            if let st = self.states {
                let ks = self.keys orelse unreachable;
                let vs = self.vals orelse unreachable;
                for i in 0..self.cap {
                    if unsafe { *(st + i) } == 1 {
                        unsafe {
                            @drop(ks + i);
                        }
                    }
                }
                unsafe {
                    dealloc_in[u8, A](&self.allocator, st);
                    dealloc_in[K, A](&self.allocator, ks);
                    dealloc_in[V, A](&self.allocator, vs);
                }
            }
        }
    }
}
";

pub const STD_PRELUDE_SRC: &str = "\
pub import core::prelude::*;
pub import std::mem::{Allocator, GlobalAllocator, Global};
pub import std::mem::Box;
pub import std::collections::{Vec, HashMap, Iter, IterMut, Hash, Eq, trim, starts_with, ends_with, find_str, split, words, parse_int, str_before};
pub import std::sync::{CancelError, CancelScope, check_cancelled, now_ms, sleep_ms, Mutex, MutexGuard, Channel, Waiter, WaitNode, Timer, UnsafeSend, UnsafeSync};
pub import std::thread::{Future, Task, Executor, Threads, Inline, Fibers, WorkerPool, ScopedHandle, spawn_scoped, JoinHandle, spawn};
pub import std::fmt::{String, format};
pub import std::io::{print, println, eprint, eprintln, read_line, read_file, write_file, Fd, Pipe, IoError, open_pipe, TcpListener, connect_to, parse_ipv4};
";

pub const STD_ROOT_SRC: &str = "\
pub import std::prelude::*;
";

pub const CORE_MODULES: &[(&str, &str)] = &[
    ("core", CORE_ROOT_SRC),
    ("core::prelude", CORE_PRELUDE_SRC),
    ("core::mem", CORE_MEM_SRC),
    ("core::cmp", CORE_CMP_SRC),
    ("core::math", CORE_MATH_SRC),
    ("core::slice", CORE_SLICE_SRC),
    ("core::option", CORE_OPTION_SRC),
    ("core::fmt", CORE_FMT_SRC),
    ("core::meta", CORE_META_SRC),
];

pub const STD_MODULES: &[(&str, &str)] = &[
    ("std", STD_ROOT_SRC),
    ("std::prelude", STD_PRELUDE_SRC),
    ("std::mem", STD_MEM_SRC),
    ("std::collections", STD_COLLECTIONS_SRC),
    ("std::sync", STD_SYNC_SRC),
    ("std::thread", STD_THREAD_SRC),
    ("std::fmt", STD_FMT_SRC),
    ("std::io", STD_IO_SRC),
    ("std::build", STD_BUILD_SRC),
];

pub fn is_stdlib_module(mod_path: &str) -> bool {
    mod_path == "core"
        || mod_path.starts_with("core::")
        || mod_path == "std"
        || mod_path.starts_with("std::")
}
