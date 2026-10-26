//! Bundled `core` (freestanding) and `std` (hosted) standard library modules and preludes.

pub const CORE_MEM_SRC: &str = "\
pub fn swap(comptime T: type, a: &mut T, b: &mut T) borrows(a: b, b: a) {
    unsafe {
        let pa: *mut T = a as *mut T;
        let pb: *mut T = b as *mut T;
        let tmp = move *pa;
        *pa = move *pb;
        *pb = move tmp;
    }
}

pub fn replace(comptime T: type, dest: &mut T, src: T) -> T borrows(dest, dest: src) {
    unsafe {
        let p: *mut T = dest as *mut T;
        let old = move *p;
        *p = move src;
        return old;
    }
}
";

pub const CORE_CMP_SRC: &str = "\
pub fn min(comptime N: number, a: N, b: N) -> N {
    if a < b {
        return a;
    }
    return b;
}

pub fn max(comptime N: number, a: N, b: N) -> N {
    if a > b {
        return a;
    }
    return b;
}

pub fn clamp(comptime N: number, self: N, lo: N, hi: N) -> N {
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
pub fn abs(comptime S: signed, self: S) -> S {
    if self < 0 {
        return -self;
    }
    return self;
}

pub fn abs(comptime F: float, self: F) -> F {
    if self < 0.0 {
        return -self;
    }
    return self;
}
";

pub const CORE_SLICE_SRC: &str = "\
pub fn is_empty(comptime S: sequence, self: &S) -> bool {
    return self.len == 0;
}

pub fn first(comptime T: type, self: &[T]) -> ?T {
    if self.len == 0 {
        return null;
    }
    return self[0];
}

pub fn last(comptime T: type, self: &[T]) -> ?T {
    if self.len == 0 {
        return null;
    }
    return self[self.len - 1];
}
";

pub const CORE_OPTION_SRC: &str = "\
pub fn is_some(comptime T: type, self: ?T) -> bool {
    if let _v = self {
        return true;
    }
    return false;
}

pub fn is_none(comptime T: type, self: ?T) -> bool {
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

    pub fn new(buf: *mut u8, cap: usize) -> Self {
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

    pub fn write(comptime T: format, self: &mut Self, val: T) {
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

pub fn fmt_slice(comptime T: format, buf: &mut [u8], val: T) -> &str borrows(buf) {
    let cap: usize = buf.len;
    let mut ptr: *mut u8 = 0 as *mut u8;
    if cap > 0 {
        ptr = &mut buf[0] as *mut u8;
    }
    let mut f = Formatter::new(ptr, cap);
    @format(&mut f, val);
    let n: usize = f.len();
    return buf[0..n];
}

pub fn fmt_buf(comptime N: usize, comptime T: format, buf: &mut [u8; N], val: T) -> &str borrows(buf) {
    let s: &mut [u8] = buf;
    return fmt_slice(s, val);
}
";

pub const CORE_PRELUDE_SRC: &str = "\
pub import core::mem::{swap, replace};
pub import core::cmp::{min, max, clamp};
pub import core::math::abs;
pub import core::slice::{is_empty, first, last};
pub import core::option::{is_some, is_none};
pub import core::fmt::{Formatter, str_eq, fmt_slice, fmt_buf};
";

pub const CORE_ROOT_SRC: &str = "\
pub import core::prelude::*;
";

pub const STD_MEM_SRC: &str = "\
pub extern fn malloc(size: usize) -> *mut u8;
pub extern fn realloc(ptr: *mut u8, size: usize) -> *mut u8;
pub extern fn free(ptr: *mut u8);

pub import core::mem::*;

/// Fallible counterpart of `@alloc`: returns `null` instead of trapping when `len * size_of(T)`
/// overflows `usize` or the allocator is out of memory.
pub fn try_alloc(comptime T: type, len: usize) -> ?*mut T {
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

pub fn Box(comptime T: type) -> type {
    return opaque(owns T) {
        ptr: *mut T,

        drop(self: &mut Self) where T: !linear {
            unsafe {
                @drop(self.ptr);
                @dealloc(self.ptr);
            }
        }

        drop(self: &mut Self) where T: linear {
            unsafe {
                @dealloc(self.ptr);
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
            let typed_ptr: *mut T = @alloc(T, 1);
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
extern fn usleep(usec: u32) -> i32;
extern fn pthread_mutex_init(mutex: *mut u8, attr: *const u8) -> i32;
extern fn pthread_mutex_lock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_unlock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_destroy(mutex: *mut u8) -> i32;
extern fn pthread_cond_init(cond: *mut u8, attr: *const u8) -> i32;
extern fn pthread_cond_wait(cond: *mut u8, mutex: *mut u8) -> i32;
extern fn pthread_cond_signal(cond: *mut u8) -> i32;
extern fn pthread_cond_broadcast(cond: *mut u8) -> i32;
extern fn pthread_cond_destroy(cond: *mut u8) -> i32;

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

pub fn Mutex(comptime T: send) -> type {
    return opaque(owns T, unsafe sync) {
        raw: [u64; 6],
        raw_handle: *mut u8,
        data: T,

        drop(self: &mut Self) where T: !linear {
            unsafe {
                let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
                let _rc = pthread_mutex_destroy(ptr);
                @drop(&mut self.data);
            }
        }

        drop(self: &mut Self) where T: linear {
            unsafe {
                let ptr = &mut self.raw[0] as *mut u64 as *mut u8;
                let _rc = pthread_mutex_destroy(ptr);
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

pub opaque(unsafe sync) Waiter {
    raw_mtx: [u64; 6],
    raw_cv: [u64; 6],
    state: i32,
    timeout_us: u64,
    timeout_branch: i32,

    drop(self: &mut Self) {
        unsafe {
            let cv_ptr = (&mut self.raw_cv[0] as *mut u64 as usize) as *mut u8;
            let mtx_ptr = (&mut self.raw_mtx[0] as *mut u64 as usize) as *mut u8;
            let _rc1 = pthread_cond_destroy(cv_ptr);
            let _rc2 = pthread_mutex_destroy(mtx_ptr);
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

    pub fn try_claim(self: &Self, branch_idx: i32) -> bool {
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

    pub fn set_timeout(self: &Self, delay_us: u64, branch_idx: i32) {
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

    pub fn init(self: &mut Self, waiter: *const Waiter, branch_idx: i32, val_ptr: *mut u8) {
        self.waiter = waiter;
        self.branch_idx = branch_idx;
        self.val_ptr = val_ptr;
        self.active = true;
    }

    pub fn deactivate(self: &mut Self) {
        self.active = false;
    }

    pub fn is_active(self: &Self) -> bool {
        return self.active;
    }

    pub fn get_waiter(self: &Self) -> *const Waiter {
        return self.waiter;
    }

    pub fn get_branch_idx(self: &Self) -> i32 {
        return self.branch_idx;
    }

    pub fn get_val_ptr(self: &Self) -> *mut u8 {
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

    pub fn select_fast_recv(self: &Self, out_ptr: *mut i32) -> bool {
        if self.delay_us == 0 {
            unsafe {
                *out_ptr = 1;
            }
            return true;
        }
        return false;
    }

    pub fn select_register_recv(
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

    pub fn select_unregister(self: &Self, node: *mut WaitNode) {
        unsafe {
            (*node).deactivate();
        }
    }
}

pub fn Channel(comptime T: send) -> type {
    return opaque(owns T, unsafe sync) {
        raw_mtx: [u64; 6],
        not_empty_cv: [u64; 6],
        not_full_cv: [u64; 6],
        buf: *mut [uninit T; 64],
        cap: usize,
        head: usize,
        tail: usize,
        count: usize,
        recv_waiters: [*mut WaitNode; 8],
        send_waiters: [*mut WaitNode; 8],

        drop(self: &mut Self) where T: !linear {
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

        drop(self: &mut Self) where T: linear {
            unsafe {
                Self::destroy_raw(self);
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

        pub fn close_and_drain(comptime F: callable, move mut self, f: F) {
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
            let buf_ptr: *mut [uninit T; 64] = @alloc([uninit T; 64], 1);
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

        pub fn try_send(self: &Self, val: T) -> ?T {
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

        pub fn send(self: &Self, val: T) {
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

        pub fn try_recv(self: &Self) -> ?T {
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

        pub fn recv(self: &Self) -> T {
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

        pub fn select_fast_recv(self: &Self, out_ptr: *mut T) -> bool {
            let self_mut = self as *mut Self;
            unsafe {
                let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
                let _rc1 = pthread_mutex_lock(mtx_ptr);
                let ok: bool = Self::try_pop_locked(self_mut, out_ptr);
                let _rc2 = pthread_mutex_unlock(mtx_ptr);
                return ok;
            }
        }

        pub fn select_fast_send(self: &Self, val_ptr: *mut T) -> bool {
            let self_mut = self as *mut Self;
            unsafe {
                let mtx_ptr = (&mut (*self_mut).raw_mtx[0] as *mut u64 as usize) as *mut u8;
                let _rc1 = pthread_mutex_lock(mtx_ptr);
                let ok: bool = Self::try_push_locked(self_mut, val_ptr as *const T);
                let _rc2 = pthread_mutex_unlock(mtx_ptr);
                return ok;
            }
        }

        pub fn select_register_recv(
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

        pub fn select_register_send(
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

        pub fn select_unregister(self: &Self, node: *mut WaitNode) {
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
extern fn malloc(size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);
extern fn pthread_create(
    thread: *mut u64,
    attr: *const u8,
    start_routine: fn(*mut u8) -> *mut u8,
    arg: *mut u8
) -> i32;
extern fn pthread_join(thread: u64, retval: *mut *mut u8) -> i32;
extern fn pthread_detach(thread: u64) -> i32;

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

pub fn JoinHandle(comptime R: send) -> type {
    return opaque(linear, owns R, unsafe sync) {
        tid: u64,

        pub fn create(tid: u64) -> Self {
            return Self {
                tid: tid,
            };
        }

        pub fn pack_ret(val: R) -> *mut u8 {
            let mut raw_ret: *mut u8 = 0 as *mut u8;
            unsafe {
                let dst_ptr = (&mut raw_ret as *mut *mut u8 as usize) as *mut R;
                *dst_ptr = move val;
            }
            return raw_ret;
        }

        pub fn join(move self) -> R {
            let mut raw_ret: *mut u8 = 0 as *mut u8;
            let _rc = pthread_join(self.tid, &mut raw_ret);
            unsafe {
                let res_ptr = (&mut raw_ret as *mut *mut u8 as usize) as *mut R;
                return move *res_ptr;
            }
        }

        pub fn detach(move self) where R: !linear {
            let _rc = pthread_detach(self.tid);
        }
    };
}

pub fn spawn(comptime F: send, f: F) -> JoinHandle(F) {
    let entry = fn(raw_ctx: *mut u8) -> *mut u8 {
        let f_ptr = raw_ctx as *mut F;
        unsafe {
            let mut local_f = move *f_ptr;
            @dealloc(f_ptr);
            let res = local_f();
            return JoinHandle(F)::pack_ret(res);
        }
    };
    let box_f: *mut F = @alloc(F, 1);
    unsafe {
        *box_f = move f;
    }
    let mut tid: u64 = 0;
    let _rc = pthread_create(&mut tid, 0 as *const u8, entry, box_f as *mut u8);
    return JoinHandle(F)::create(tid);
}
";

pub const STD_FMT_SRC: &str = "\
extern fn malloc(size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);

pub import core::fmt::*;

pub opaque String {
    ptr: *mut u8,
    len: usize,

    drop(self: &mut Self) {
        if (self.ptr as usize) != 0 {
            unsafe {
                free(self.ptr);
            }
        }
    }

    format(self: &Self, f: &mut Formatter) {
        f.write_str(self.as_str());
    }

    pub fn from_raw(ptr: *mut u8, len: usize) -> Self {
        return Self {
            ptr: ptr,
            len: len,
        };
    }

    pub fn len(self: &Self) -> usize {
        return self.len;
    }

    pub fn as_str(self: &Self) -> &str {
        unsafe {
            let arr_ptr = self.ptr as *const [u8; 0];
            let arr_ref: &[u8; 0] = &*arr_ptr;
            return arr_ref[0..self.len];
        }
    }
}

pub fn format(comptime T: format, val: T) -> String {
    let cap: usize = 512;
    let raw: *mut u8 = malloc(cap);
    let mut f = Formatter::new(raw, cap);
    @format(&mut f, val);
    return String::from_raw(raw, f.len());
}
";

pub const STD_IO_SRC: &str = "\
pub extern fn puts(s: *const u8) -> i32;
pub extern fn write(fd: i32, buf: *const u8, count: usize) -> isize;
pub extern fn read(fd: i32, buf: *mut u8, count: usize) -> isize;

pub import core::fmt::Formatter;

pub fn print_str(s: &str) -> isize {
    if s.len == 0 {
        return 0;
    }
    let ptr = &s[0] as *const u8;
    return write(1, ptr, s.len);
}

pub fn print(comptime T: format, val: T) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = Formatter::new(ptr, 512);
    @format(&mut f, val);
    return write(1, ptr as *const u8, f.len());
}

pub fn println(comptime T: format, val: T) -> isize {
    let mut buf: [u8; 512] = @default([u8; 512]);
    let ptr = &mut buf[0] as *mut u8;
    let mut f = Formatter::new(ptr, 512);
    @format(&mut f, val);
    f.write_byte(10);
    return write(1, ptr as *const u8, f.len());
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

pub const STD_PRELUDE_SRC: &str = "\
pub import core::prelude::*;
pub import std::mem::Box;
pub import std::sync::{Mutex, MutexGuard, Channel, Waiter, WaitNode, Timer};
pub import std::thread::{ScopedHandle, spawn_scoped, JoinHandle, spawn};
pub import std::fmt::{String, format};
pub import std::io::{print, println};
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
];

pub const STD_MODULES: &[(&str, &str)] = &[
    ("std", STD_ROOT_SRC),
    ("std::prelude", STD_PRELUDE_SRC),
    ("std::mem", STD_MEM_SRC),
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
