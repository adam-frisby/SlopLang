//! Bundled `core` (freestanding) and `std` (hosted) standard library modules and preludes.

pub const CORE_MEM_SRC: &str = "\
pub fn swap(comptime T: type, a: &mut T, b: &mut T) {
    let tmp: T = *a;
    *a = *b;
    *b = tmp;
}

pub fn replace(comptime T: type, dest: &mut T, src: T) -> T {
    let old: T = *dest;
    *dest = move src;
    return old;
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
pub struct Formatter {
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
pub extern fn free(ptr: *mut u8);

pub import core::mem::*;

pub fn Box(comptime T: type) -> type {
    return struct {
        ptr: *mut T,

        drop(self: &mut Self) {
            unsafe {
                free(self.ptr as *mut u8);
            }
        }

        pub fn new(val: T) -> Self {
            let raw = malloc(64);
            let typed_ptr = raw as *mut T;
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
extern fn pthread_mutex_init(mutex: *mut u8, attr: *const u8) -> i32;
extern fn pthread_mutex_lock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_unlock(mutex: *mut u8) -> i32;
extern fn pthread_mutex_destroy(mutex: *mut u8) -> i32;

pub fn MutexGuard(comptime T: send) -> type {
    return struct(linear) {
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
    return struct(unsafe sync) {
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

pub fn ScopedHandle(comptime F: send) -> type {
    return struct(linear) {
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
";

pub const STD_FMT_SRC: &str = "\
extern fn malloc(size: usize) -> *mut u8;
extern fn free(ptr: *mut u8);

pub import core::fmt::*;

pub struct String {
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

pub const STD_PRELUDE_SRC: &str = "\
pub import core::prelude::*;
pub import std::mem::Box;
pub import std::sync::{Mutex, MutexGuard};
pub import std::thread::{ScopedHandle, spawn_scoped};
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
];

pub fn is_stdlib_module(mod_path: &str) -> bool {
    mod_path == "core"
        || mod_path.starts_with("core::")
        || mod_path == "std"
        || mod_path.starts_with("std::")
}

