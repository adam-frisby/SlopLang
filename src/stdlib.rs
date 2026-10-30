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

pub fn replace[T](dest: &mut T, src: T) -> T borrows(dest, dest: src) {
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

pub fn first[T](self: &[T]) -> ?T {
    if self.len == 0 {
        return null;
    }
    return self[0];
}

pub fn last[T](self: &[T]) -> ?T {
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
    truncated: bool,

    pub unsafe fn new(buf: *mut u8, cap: usize) -> Self {
        return Self {
            buf: buf,
            len: 0,
            cap: cap,
            truncated: false,
        };
    }

    pub fn len(self: &Self) -> usize {
        return self.len;
    }

    pub fn is_truncated(self: &Self) -> bool {
        return self.truncated;
    }

    pub fn write_byte(self: &mut Self, b: u8) {
        if self.len < self.cap {
            let addr: usize = (self.buf as usize) +% self.len;
            let dst: *mut u8 = addr as *mut u8;
            unsafe {
                *dst = b;
            }
            self.len = self.len +% 1;
        } else {
            self.truncated = true;
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
    pub index: usize,
    pub ty: type,
    pub offset: usize,
}

pub struct OverlayField {
    pub name: &str,
    pub ty: type,
}

pub fn EnumVariant[T: enum] -> type {
    return struct {
        pub name: &str,
        pub value: @backing_type(T),
        pub val: T,
    };
}

pub fn UnionVariant[T: union] -> type {
    return struct {
        pub name: &str,
        pub payload: type,
        pub tag: T::Tag,
    };
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
";

pub const CORE_PRELUDE_SRC: &str = "\
pub import core::mem::{swap, replace};
pub import core::cmp::{min, max, clamp};
pub import core::math::abs;
pub import core::slice::{is_empty, first, last};
pub import core::option::{is_some, is_none};
pub import core::fmt::{Formatter, str_eq, fmt_slice, fmt_buf};
pub import core::meta::{FieldSpec, EnumSpec, UnionSpec, ErrorSpec, StructField, TupleField, OverlayField, EnumVariant, UnionVariant, ErrorVariant, FnInfo};
";

pub const CORE_ROOT_SRC: &str = "\
pub import core::prelude::*;
";

pub const STD_MEM_SRC: &str = "\
pub safe extern fn malloc(size: usize) -> *mut u8;
pub extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
pub extern fn free(ptr: *mut u8);

pub import core::mem::*;

/// Fallible counterpart of `@alloc`: returns `null` instead of trapping when `len * size_of(T)`
/// overflows `usize` or the allocator is out of memory.
pub fn try_alloc[T](len: usize) -> ?*mut T {
    let mut bytes: usize = (len *? @size_of(T)) orelse return null;
    if bytes == 0 {
        bytes = 1;
    }
    let raw: *mut u8 = malloc(bytes);
    if (raw as usize) == 0 {
        return null;
    }
    return raw as *mut T;
}

pub fn Box[T] -> type {
    return opaque {
        ptr: *own T,

        unsafe impl drop(may_dangle T) where T: !linear {
            fn drop(self: &mut Self) {
                unsafe {
                    @drop(self.ptr);
                    @dealloc(self.ptr);
                }
            }
        }

        unsafe impl drop(may_dangle T) where T: linear {
            fn drop(self: &mut Self) {
                unsafe {
                    @dealloc(self.ptr);
                }
            }
        }

        pub fn into_inner(move self) -> T {
            unsafe {
                let p: *mut T = self.ptr;
                let val = move *p;
                @dealloc(p);
                @forget(self);
                return val;
            }
        }

        pub fn new(val: T) -> Self {
            let typed_ptr: *own T = unsafe { @alloc(T, 1) as *own T };
            unsafe {
                *typed_ptr = move val;
            }
            return Self {
                ptr: typed_ptr,
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
    };
}
";

pub const STD_SYNC_SRC: &str = "\
safe extern fn usleep(usec: u32) -> i32;
extern fn pthread_mutex_init(mutex: *mut u8, attr: *const u8) -> i32;
extern fn pthread_mutex_lock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_unlock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_destroy(mutex: *mut u8) -> i32;
extern fn pthread_cond_init(cond: *mut u8, attr: *const u8) -> i32;
extern fn pthread_cond_wait(cond: *mut u8, mutex: *mut u8) -> i32;
extern fn pthread_cond_signal(cond: *mut u8) -> i32;
extern fn pthread_cond_broadcast(cond: *mut u8) -> i32;
extern fn pthread_cond_destroy(cond: *mut u8) -> i32;

/// Asserts that a value may move to another thread although its type is not `send` (one raw
/// pointer handed to a worker, say). `new` is `unsafe`: the caller vouches for that one value.
pub fn UnsafeSend[T] -> type {
    return opaque(unsafe send) {
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
    };
}

/// Asserts that a value may be shared between threads although its type is not `sync`. `new`
/// is `unsafe`: the caller vouches that every access to that one value is synchronized.
pub fn UnsafeSync[T] -> type {
    return opaque(unsafe sync) {
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
    };
}

pub fn MutexGuard[T: send] -> type {
    return opaque(linear) {
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
        }
    };
}

pub fn Mutex[T: send] -> type {
    return opaque(unsafe send, unsafe sync) {
        raw: [u64; 6],
        raw_handle: *mut u8,
        data: T,

        unsafe impl drop(may_dangle T) where T: !linear {
            fn drop(self: &mut Self) {
                unsafe {
                    let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
                    let _rc = pthread_mutex_destroy(ptr);
                    @drop(&mut self.data);
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
                let _rc = pthread_mutex_lock(raw_ptr);
                return MutexGuard[T]::create(raw_ptr, data_ptr);
            }
        }

        pub fn with_lock[F: callable](self: &Self, f: F) -> i32 {
            let mut guard = self.lock();
            let out: i32 = f(guard.get_mut());
            guard.unlock();
            return out;
        }
    };
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
                let _rc_w = pthread_cond_wait(cv_ptr, mtx_ptr);
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

pub fn Channel[T: send] -> type {
    return opaque(unsafe send, unsafe sync) {
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

        pub fn send(self: &Self, val: T) borrows(self: val) {
            let self_mut = self as *mut Self;
            unsafe {
                let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
                let nf_ptr = (&mut (*self_mut).not_full_cv[0] as *mut u64 as usize) as *mut u8;
                let _rc1 = pthread_mutex_lock(mtx_ptr);
                let val_ptr = (&val as *const T as usize) as *const T;
                while !Self::try_push_locked(self_mut, val_ptr) {
                    let _rc_w = pthread_cond_wait(nf_ptr, mtx_ptr);
                }
                @forget(val);
                let _rc2 = pthread_mutex_unlock(mtx_ptr);
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

        pub fn recv(self: &Self) -> T borrows(*self) {
            let self_mut = self as *mut Self;
            let mut slot: uninit T = uninit;
            unsafe {
                let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
                let ne_ptr = (&mut (*self_mut).not_empty_cv[0] as *mut u64 as usize) as *mut u8;
                let _rc1 = pthread_mutex_lock(mtx_ptr);
                let slot_ptr = (&mut slot as *mut uninit T as usize) as *mut T;
                while !Self::try_pop_locked(self_mut, slot_ptr) {
                    let _rc_w = pthread_cond_wait(ne_ptr, mtx_ptr);
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
    };
}
";

pub const STD_THREAD_SRC: &str = "\
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

pub fn ScopedHandle[F: send] -> type {
    return opaque(linear) {
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
        pub(mod) fn box_closure(f: F) -> *own F {
            let box_f = unsafe { malloc(64) as *own F };
            unsafe {
                *box_f = move f;
            }
            return box_f;
        }

        pub fn join(move self) -> i32 {
            let mut raw_ret: *mut u8 = 0 as *mut u8;
            let _rc = unsafe { pthread_join(self.tid, &mut raw_ret) };
            return raw_ret as usize as i32;
        }
    };
}

pub fn spawn_scoped[F: send](f: F) -> ScopedHandle[F] {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let f_ptr = raw_ctx as *mut F;
        unsafe {
            let mut local_f = move *f_ptr;
            free(raw_ctx);
            let res: i32 = local_f();
            return res as usize as *mut u8;
        }
    };
    let box_f = ScopedHandle[F]::box_closure(move f);
    let box_ptr = box_f as *mut u8;
    let mut tid: u64 = 0;
    let _rc = unsafe { pthread_create(&mut tid, 0 as *const u8, entry, box_ptr) };
    return ScopedHandle[F]::create(tid, box_f);
}

pub fn JoinHandle[R: send] -> type {
    return opaque(linear, owns R, unsafe sync) {
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

        pub(mod) fn pack_ret(val: R) -> *mut u8 {
            let mut raw_ret: *mut u8 = 0 as *mut u8;
            unsafe {
                let dst_ptr = (&mut raw_ret as *mut *mut u8 as usize) as *own R;
                *dst_ptr = move val;
            }
            return raw_ret;
        }

        pub fn join(move self) -> R {
            let mut raw_ret: *mut u8 = 0 as *mut u8;
            let _rc = unsafe { pthread_join(self.tid, &mut raw_ret) };
            unsafe {
                let res_ptr = (&mut raw_ret as *mut *mut u8 as usize) as *mut R;
                return move *res_ptr;
            }
        }

        pub fn detach(move self) where R: !linear {
            let _rc = unsafe { pthread_detach(self.tid) };
        }
    };
}

pub fn spawn[F: send](f: F) -> JoinHandle[F] {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let f_ptr = raw_ctx as *mut F;
        unsafe {
            let mut local_f = move *f_ptr;
            @dealloc(f_ptr);
            let res = local_f();
            return JoinHandle[F]::pack_ret(res);
        }
    };
    let box_f: *mut F = JoinHandle[F]::box_closure[F](move f);
    let mut tid: u64 = 0;
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
    ptr: *own u8,
    len: usize,
    cap: usize,

    impl drop {
        fn drop(self: &mut Self) {
            if (self.ptr as usize) != 0 {
                unsafe {
                    free(self.ptr);
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
        return Self { ptr: unsafe { 0 as *own u8 }, len: 0, cap: 0 };
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

    /// A string taking ownership of `len` bytes at `ptr`, which `malloc` allocated.
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
        if (self.ptr as usize) == 0 {
            self.ptr = unsafe { malloc(new_cap) as *own u8 };
        } else {
            unsafe {
                self.ptr = realloc(self.ptr, new_cap) as *own u8;
            }
        }
        self.cap = new_cap;
    }

    pub fn push_byte(self: &mut Self, b: u8) {
        self.reserve(1);
        unsafe {
            *(self.ptr + self.len) = b;
        }
        self.len += 1;
    }

    pub fn push_str(self: &mut Self, text: &str) {
        self.reserve(text.len);
        for (b, i) in text {
            unsafe {
                *(self.ptr + self.len + i) = b;
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
        let mut p: *mut u8 = self.ptr;
        if (p as usize) == 0 {
            p = 1 as *mut u8;
        }
        unsafe {
            let arr_ref: &[u8; 0] = &*(p as *const [u8; 0]);
            return arr_ref[0..self.len];
        }
    }
}

pub fn format[T: format](val: T) -> String {
    let cap: usize = 512;
    let raw: *mut u8 = malloc(cap);
    let mut f = unsafe { Formatter::new(raw, cap) };
    @format(&mut f, val);
    return unsafe { String::from_raw(raw, f.len()) };
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

pub import core::fmt::Formatter;
pub import std::fmt::String;

pub fn print_str(s: &str) -> isize {
    if s.len == 0 {
        return 0;
    }
    let ptr = &s[0] as *const u8;
    return unsafe { write[1](ptr, s.len) };
}

pub fn print[T: format](val: T) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = unsafe { Formatter::new(ptr, 512) };
    @format(&mut f, val);
    return unsafe { write[1](ptr as *const u8, f.len()) };
}

pub fn println[T: format](val: T) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = unsafe { Formatter::new(ptr, 512) };
    @format(&mut f, val);
    f.write_byte(10);
    return unsafe { write[1](ptr as *const u8, f.len()) };
}

pub fn eprint[T: format](val: T) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = unsafe { Formatter::new(ptr, 512) };
    @format(&mut f, val);
    return unsafe { write[2](ptr as *const u8, f.len()) };
}

pub fn eprintln[T: format](val: T) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = unsafe { Formatter::new(ptr, 512) };
    @format(&mut f, val);
    f.write_byte(10);
    return unsafe { write[2](ptr as *const u8, f.len()) };
}

/// One line from standard input without its newline, or `null` at end of input.
pub fn read_line() -> ?String {
    let mut line = String::new();
    let mut b: u8 = 0;
    let mut got_any = false;
    while true {
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
    pub root: &str = \"src/main.lrrr\",
    pub no_std: bool = false,
    pub deps: &[Dependency] = &[],
    pub system_libs: &[&str] = &[],
}
";

pub const STD_COLLECTIONS_SRC: &str = "\
/// A growable heap array. It owns its elements (`owns T`): with a linear `T` the vector itself is
/// linear and is consumed with `drain`, `pop`, or `into_...`; otherwise it drops its elements.
/// A borrowing iterator over a sequence's elements, yielding `&T`. Each item borrows the iterator,
/// which in turn borrows the sequence.
pub fn Iter[T] -> type {
    return opaque {
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
    };
}

/// A borrowing iterator over a sequence's elements, yielding `&mut T`.
pub fn IterMut[T] -> type {
    return opaque {
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
    };
}

pub fn Vec[T] -> type {
    return opaque {
        ptr: ?*own T,
        len: usize,
        cap: usize,

        pub fn new() -> Self {
            return Self { ptr: null, len: 0, cap: 0 };
        }

        pub fn with_capacity(cap: usize) -> Self {
            if cap == 0 {
                return Self::new();
            }
            let p: *own T = unsafe { @alloc(T, cap) as *own T };
            return Self { ptr: p, len: 0, cap: cap };
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
            let mut new_cap: usize = 4;
            if self.cap > 0 {
                new_cap = self.cap * 2;
            }
            self.cap = new_cap;
            if let old_ptr = self.ptr {
                let p: *own T = unsafe { @realloc(T, old_ptr, new_cap) as *own T };
                self.ptr = p;
                return p;
            }
            let p: *own T = unsafe { @alloc(T, new_cap) as *own T };
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

        pub fn pop(self: &mut Self) -> ?T {
            if self.len == 0 {
                return null;
            }
            self.len -= 1;
            let p = self.ptr orelse unreachable;
            unsafe {
                return move *(p + self.len);
            }
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

        impl default {
            fn default() -> Self {
                return Self::new();
            }
        }

        impl clone where T: clone {
            fn clone(self: &Self) -> Self {
                let src_ptr = self.ptr orelse return @default(Self);
                if self.len == 0 {
                    return @default(Self);
                }
                let new_ptr: *own T = unsafe { @alloc(T, self.len) as *own T };
                let mut i: usize = 0;
                while i < self.len {
                    unsafe {
                        *(new_ptr + i) = @clone(&*(src_ptr + i));
                    }
                    i += 1;
                }
                return Self { ptr: new_ptr, len: self.len, cap: self.len };
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
                        @dealloc(p);
                    }
                }
            }
        }

        unsafe impl drop(may_dangle T) where T: linear {
            fn drop(self: &mut Self) {
                if let p = self.ptr {
                    unsafe {
                        @dealloc(p);
                    }
                }
            }
        }
    };
}

/// Hash of an integer key (Fibonacci hashing).
pub fn hash_key[K: integer](k: K) -> u64 {
    return ((k as i64) as u64) *% 11400714819323198485;
}

/// Hash of a byte-sequence key such as `&str` (FNV-1a).
pub fn hash_key[K](k: K) -> u64 {
    let mut h: u64 = 14695981039346656037;
    for b in k {
        h = (h ^ (b as u64)) *% 1099511628211;
    }
    return h;
}

/// A hash map from `copy` keys (integers or `&str`) to values, with open addressing. It owns its
/// values: with a linear `V` it is linear and is consumed with `drain`.
pub fn HashMap[K: copy, V] -> type {
    return opaque {
        keys: ?*own K,
        vals: ?*own V,
        // Slot states: 0 empty, 1 full, 2 removed.
        states: ?*mut u8,
        len: usize,
        used: usize,
        cap: usize,

        pub fn new() -> Self {
            return Self { keys: null, vals: null, states: null, len: 0, used: 0, cap: 0 };
        }

        pub fn len(self: &Self) -> usize {
            return self.len;
        }

        pub fn is_empty(self: &Self) -> bool {
            return self.len == 0;
        }

        /// The slot holding `key`, if any.
        fn find(self: &Self, key: K) -> ?usize {
            if self.cap == 0 {
                return null;
            }
            let st = self.states orelse unreachable;
            let ks = self.keys orelse unreachable;
            let mask = self.cap - 1;
            let mut i = (hash_key[K](key) as usize) & mask;
            while true {
                let s = unsafe { *(st + i) };
                if s == 0 {
                    return null;
                }
                if s == 1 && unsafe { *(ks + i) } == key {
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
            let mut i = (hash_key[K](key) as usize) & mask;
            while unsafe { *(st + i) } == 1 {
                i = (i + 1) & mask;
            }
            if unsafe { *(st + i) } == 0 {
                self.used += 1;
            }
            unsafe {
                *(st + i) = 1;
                *(ks + i) = key;
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
            let st: *mut u8 = @alloc(u8, new_cap);
            for i in 0..new_cap {
                unsafe {
                    *(st + i) = 0;
                }
            }
            self.states = st;
            self.keys = unsafe { @alloc(K, new_cap) as *own K };
            self.vals = unsafe { @alloc(V, new_cap) as *own V };
            self.cap = new_cap;
            self.len = 0;
            self.used = 0;
            if let ost = old_states {
                let ok = old_keys orelse unreachable;
                let ov = old_vals orelse unreachable;
                for i in 0..old_cap {
                    if unsafe { *(ost + i) } == 1 {
                        let k = unsafe { *(ok + i) };
                        let v = unsafe { move *(ov + i) };
                        self.place(k, v);
                    }
                }
                unsafe {
                    @dealloc(ost);
                    @dealloc(ok);
                    @dealloc(ov);
                }
            }
        }

        /// Inserts `value` for `key`, returning the value it replaces.
        pub fn insert(self: &mut Self, key: K, value: V) -> ?V borrows(self: key, self: value) {
            if let i = self.find(key) {
                let vs = self.vals orelse unreachable;
                let old = unsafe { move *(vs + i) };
                unsafe {
                    *(vs + i) = move value;
                }
                return old;
            }
            self.reserve_one();
            self.place(key, value);
            return null;
        }

        pub fn get(self: &Self, key: K) -> ?&V {
            let i = self.find(key) orelse return null;
            let vs = self.vals orelse unreachable;
            unsafe {
                return &*(vs + i);
            }
        }

        pub fn get_mut(self: &mut Self, key: K) -> ?&mut V {
            let i = self.find(key) orelse return null;
            let vs = self.vals orelse unreachable;
            unsafe {
                return &mut *(vs + i);
            }
        }

        pub fn contains_key(self: &Self, key: K) -> bool {
            if let i = self.find(key) {
                return true;
            }
            return false;
        }

        /// Removes `key`, returning its value.
        pub fn remove(self: &mut Self, key: K) -> ?V {
            let i = self.find(key) orelse return null;
            let st = self.states orelse unreachable;
            let vs = self.vals orelse unreachable;
            unsafe {
                *(st + i) = 2;
            }
            self.len -= 1;
            unsafe {
                return move *(vs + i);
            }
        }

        /// The keys, in slot order.
        pub fn keys(self: &Self) -> Vec[K] {
            let mut out = Vec[K]::with_capacity(self.len);
            if let st = self.states {
                let ks = self.keys orelse unreachable;
                for i in 0..self.cap {
                    if unsafe { *(st + i) } == 1 {
                        out.push(unsafe { *(ks + i) });
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
                        f(*(ks + i), move *(vs + i));
                    }
                }
            }
            self.len = 0;
        }

        impl default {
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
                                @drop(vs + i);
                            }
                        }
                    }
                    unsafe {
                        @dealloc(st);
                        @dealloc(ks);
                        @dealloc(vs);
                    }
                }
            }
        }

        unsafe impl drop(may_dangle K, V) where V: linear {
            fn drop(self: &mut Self) {
                if let st = self.states {
                    let ks = self.keys orelse unreachable;
                    let vs = self.vals orelse unreachable;
                    unsafe {
                        @dealloc(st);
                        @dealloc(ks);
                        @dealloc(vs);
                    }
                }
            }
        }
    };
}
";

pub const STD_PRELUDE_SRC: &str = "\
pub import core::prelude::*;
pub import std::mem::Box;
pub import std::collections::{Vec, HashMap, Iter, IterMut};
pub import std::sync::{Mutex, MutexGuard, Channel, Waiter, WaitNode, Timer, UnsafeSend, UnsafeSync};
pub import std::thread::{ScopedHandle, spawn_scoped, JoinHandle, spawn};
pub import std::fmt::{String, format};
pub import std::io::{print, println, eprint, eprintln, read_line, read_file, write_file};
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
