use std::io::Write;
use std::process::{Command, Stdio};

use crate::llvm::LlvmLowering;
use crate::lower::Compiler;
use crate::vm::{Value, Vm};

#[test]
fn test_c_ffi_integer_types_and_opaque_pointers() {
    let src = r#"
// 1. Distinct C-compatible integer types (`c_*`) and `opaque` pointers in extern & export-ready signatures:
extern fn memcmp(s1: *const opaque, s2: *const opaque, n: usize) -> c_int;

// Distinct overloads on `c_int` vs `i32` and `c_long` vs `c_longlong`:
pub fn classify(self: i32) -> i32 {
    return 1;
}
pub fn classify(self: c_int) -> i32 {
    return 2;
}
pub fn classify(self: c_long) -> i32 {
    return 3;
}
pub fn classify(self: c_longlong) -> i32 {
    return 4;
}

// Generic meta-type constraints (`signed`, `unsigned`, `integer`) work on `c_*` types:
pub fn double_signed(comptime S: signed, x: S) -> S {
    return x + x;
}
pub fn bump_unsigned(comptime U: unsigned, x: U) -> U {
    return x + 1;
}

// Type-erased raw pointer (`*const opaque`, `*mut opaque`) and safe reference (`&opaque`, `&mut opaque`) helpers:
pub fn write_i32_via_opaque_raw(dst: *mut opaque, src: *const opaque) {
    let typed_dst = dst as *mut i32;
    let typed_src = src as *const i32;
    unsafe {
        *typed_dst = *typed_src + 5;
    }
}

pub fn read_i32_via_opaque_ref(r: &opaque) -> i32 {
    let raw = r as *const opaque;
    let typed = raw as *const i32;
    unsafe {
        return *typed;
    }
}

pub fn mutate_i32_via_opaque_mut_ref(r: &mut opaque, delta: i32) {
    let raw = r as *mut opaque;
    let typed = raw as *mut i32;
    unsafe {
        *typed = *typed + delta;
    }
}

pub fn main() -> i32 {
    // All 11 distinct C integer types:
    let cc: c_char = 65;
    let csc: c_schar = -5;
    let cuc: c_uchar = 200;
    let cs: c_short = -100;
    let cus: c_ushort = 500;
    let ci: c_int = 21;
    let cui: c_uint = 9;
    let cl: c_long = 1000;
    let cul: c_ulong = 2000;
    let cll: c_longlong = -3000;
    let cull: c_ulonglong = 4000;

    let doubled_ci: c_int = double_signed(c_int, ci); // 42
    let bumped_cui: c_uint = bump_unsigned(c_uint, cui); // 10

    let native_i32: i32 = 7;
    let tag_sum = native_i32.classify() + ci.classify() + cl.classify() + cll.classify(); // 1 + 2 + 3 + 4 = 10

    let c_arith = (cc as i32) + (csc as i32) + (cuc as i32) + (cs as i32) + (cus as i32)
        + (cl as i32) + (cul as i32) + (cll as i32) + (cull as i32);
    // 65 - 5 + 200 - 100 + 500 + 1000 + 2000 - 3000 + 4000 = 4660
    if c_arith != 4660 {
        return 1;
    }

    // Implicit coercion of `&T` / `&mut T` to `*const opaque` / `*mut opaque`:
    let src_val: i32 = 15;
    let mut dst_val: i32 = 0;
    write_i32_via_opaque_raw(&mut dst_val, &src_val); // dst_val becomes 20

    // Safe `&opaque` and `&mut opaque` references with automatic reborrowing:
    let mut box_val: i32 = 30;
    let mut op_mut_ref: &mut opaque = &mut box_val;
    mutate_i32_via_opaque_mut_ref(op_mut_ref, 7); // reborrows `op_mut_ref` -> box_val becomes 37
    let read_back = read_i32_via_opaque_ref(op_mut_ref); // reborrows `&mut opaque` as `&opaque` -> 37

    // Expected: 42 + 10 + 10 + 20 + 37 = 119
    return (doubled_ci as i32) + (bumped_cui as i32) + tag_sum + dst_val + read_back;
}
"#;
    let mut program = Compiler::compile_source(src)
        .expect("Failed to compile C FFI integer types and opaque pointers test");

    // Verify in Stage 3 VM:
    let main_id = program
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_res = Vm::eval(&mut program, main_id, vec![]).expect("VM execution failed");
    assert_eq!(vm_res, Value::Int(119));

    // Verify in Stage 4 LLVM (`lli`):
    let llvm_ir = LlvmLowering::lower(&program).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(119),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Negative 1: Implicitly mixing `c_int` with `i32` without `as` is rejected:
    let err_mix_let = Compiler::compile_source(
        "pub fn main() -> i32 { let x: c_int = 10; let y: i32 = x; return y; }",
    )
    .expect_err("Expected implicit conversion from `c_int` to `i32` to be rejected");
    assert!(
        err_mix_let.contains("cannot implicitly convert 'c_int' to 'i32'"),
        "Unexpected error: {err_mix_let}"
    );

    let err_mix_bin = Compiler::compile_source(
        "pub fn main() -> i32 { let x: c_int = 10; let y: i32 = 20; let z = x + y; return 0; }",
    )
    .expect_err("Expected binary `+` mixing `c_int` and `i32` to be rejected");
    assert!(
        err_mix_bin.contains("cannot mix 'c_int' and 'i32' without an explicit 'as' cast"),
        "Unexpected error: {err_mix_bin}"
    );

    let err_mix_long = Compiler::compile_source(
        "pub fn main() -> i32 { let x: c_long = 10; let y: c_longlong = x; return 0; }",
    )
    .expect_err("Expected implicit conversion from `c_long` to `c_longlong` to be rejected");
    assert!(
        err_mix_long.contains("cannot implicitly convert 'c_long' to 'c_longlong'"),
        "Unexpected error: {err_mix_long}"
    );

    // Negative 2: Using `opaque` by value (variable, parameter, return, field, array) is rejected:
    let err_opaque_let =
        Compiler::compile_source("pub fn main() -> i32 { let x: opaque = 0; return 0; }")
            .expect_err("Expected `let x: opaque` to be rejected");
    assert!(
        err_opaque_let.contains("Unsized type 'opaque' cannot be bound by value"),
        "Unexpected error: {err_opaque_let}"
    );

    let err_opaque_param =
        Compiler::compile_source("pub fn bad(x: opaque) {} pub fn main() -> i32 { return 0; }")
            .expect_err("Expected parameter `x: opaque` by value to be rejected");
    assert!(
        err_opaque_param.contains("Unsized type 'opaque' cannot be passed by value"),
        "Unexpected error: {err_opaque_param}"
    );

    let err_opaque_field =
        Compiler::compile_source("pub struct Bad { f: opaque } pub fn main() -> i32 { return 0; }")
            .expect_err("Expected field `f: opaque` by value to be rejected");
    assert!(
        err_opaque_field.contains("Unsized type 'opaque' cannot be stored by value in field"),
        "Unexpected error: {err_opaque_field}"
    );

    let err_opaque_arr = Compiler::compile_source(
        "pub fn main() -> i32 { let a: [opaque; 4] = {0, 0, 0, 0}; return 0; }",
    )
    .expect_err("Expected `[opaque; 4]` to be rejected");
    assert!(
        err_opaque_arr
            .contains("Unsized type 'opaque' has unknown size and cannot be an array element"),
        "Unexpected error: {err_opaque_arr}"
    );

    // Negative 3: Dereferencing `*const opaque`, `*mut opaque`, or `&opaque` is rejected:
    let err_deref_opaque = Compiler::compile_source(
            "pub fn main() -> i32 { let x: i32 = 5; let p: *const opaque = &x; unsafe { let y = *p; } return 0; }",
        )
        .expect_err("Expected dereferencing `*const opaque` to be rejected");
    assert!(
        err_deref_opaque.contains("Cannot dereference pointer of type '*const opaque'"),
        "Unexpected error: {err_deref_opaque}"
    );

    // Negative 4: Element-scaled pointer arithmetic on `*const opaque` or `*mut opaque` is rejected:
    let err_ptr_arith = Compiler::compile_source(
            "pub fn main() -> i32 { let mut x: i32 = 5; let p: *mut opaque = &mut x; let q = p + 1; return 0; }",
        )
        .expect_err("Expected pointer arithmetic `p + 1` on `*mut opaque` to be rejected");
    assert!(
        err_ptr_arith.contains("Cannot perform element-scaled pointer arithmetic on '*mut opaque'"),
        "Unexpected error: {err_ptr_arith}"
    );

    // Negative 5: Mutability and concrete pointer safety (`&T` -> `*mut opaque` and `*mut opaque` -> `*mut i32` without `as` rejected):
    let err_const_to_mut = Compiler::compile_source(
        "pub fn main() -> i32 { let x: i32 = 5; let p: *mut opaque = &x; return 0; }",
    )
    .expect_err("Expected coercing `&i32` to `*mut opaque` to be rejected");
    assert!(
        err_const_to_mut.contains("cannot implicitly convert '&i32' to '*mut opaque'"),
        "Unexpected error: {err_const_to_mut}"
    );

    let err_opaque_to_typed = Compiler::compile_source(
            "pub fn main() -> i32 { let mut x: i32 = 5; let p: *mut opaque = &mut x; let q: *mut i32 = p; return 0; }",
        )
        .expect_err("Expected implicit conversion from `*mut opaque` to `*mut i32` without `as` to be rejected");
    assert!(
        err_opaque_to_typed.contains("cannot implicitly convert '*mut opaque' to '*mut i32'"),
        "Unexpected error: {err_opaque_to_typed}"
    );

    // Negative 6: NLL borrow checker tracks loans through `&opaque`:
    let err_nll_opaque = Compiler::compile_source(
        r#"
pub fn inspect(p: &opaque) -> i32 { return 0; }
pub fn main() -> i32 {
    let mut x: i32 = 10;
    let r: &opaque = &x;
    x = 20;
    return inspect(r);
}
"#,
    )
    .expect_err("Expected NLL borrow checker to reject mutating `x` while `r: &opaque` is live");
    assert!(
        err_nll_opaque.contains("because it is currently borrowed"),
        "Unexpected error: {err_nll_opaque}"
    );

    // Negative 7: Reserved floating-point types `c_longdouble` and `f128` are rejected with clear diagnostics:
    let err_cld =
        Compiler::compile_source("pub fn main() -> i32 { let x: c_longdouble = 0.0; return 0; }")
            .expect_err("Expected `c_longdouble` to be rejected as reserved");
    assert!(
        err_cld.contains("Type 'c_longdouble' is reserved"),
        "Unexpected error: {err_cld}"
    );

    let err_f128 =
        Compiler::compile_source("pub fn main() -> i32 { let x: f128 = 0.0; return 0; }")
            .expect_err("Expected `f128` to be rejected as reserved");
    assert!(
        err_f128.contains("Type 'f128' is reserved"),
        "Unexpected error: {err_f128}"
    );
}

#[test]
fn test_named_opaque_ffi_opaque_newtypes_and_existential_return_types() {
    use crate::llvm::LlvmLowering;
    use crate::lower::Compiler;
    use std::io::Write;
    use std::process::{Command, Stdio};

    // 1. End-to-end compilation & execution covering:
    //    - Named Opaque FFI Types (`pub type Sqlite3 = opaque { ... };`, `pub opaque CFile;`, inherent & extension methods on `*mut Sqlite3`, universal `*mut opaque` coercion)
    //    - Opaque Newtypes (`pub type UserId = opaque u64 { ... };`, `pub opaque OrderId = u64 { ... };`, transparent inside defining module, opaque outside defining module)
    //    - Existential Return Types (`-> opaque Counter`, `-> opaque Counter + Resettable`, trait method calls, generic `comptime T: Counter`, `&Counter` borrowing)
    let ids_src = r#"
pub type UserId = opaque u64 {
    pub fn new(raw: u64) -> Self {
        // Inside defining module `ids`, `UserId` and `u64` coerce transparently and support operators/literals
        return raw + 1000;
    }

    pub fn raw(self: Self) -> u64 {
        return self - 1000;
    }

    pub fn next(self: Self) -> Self {
        return self + 1;
    }
};

pub opaque OrderId = u64 {
    pub fn from_user(u: UserId, seq: u64) -> Self {
        return (u as u64) * 10 + seq;
    }

    pub fn raw(self: Self) -> u64 {
        return self;
    }
};
"#;
    let root_src = r#"
import root::ids::UserId;
import root::ids::OrderId;

// Named Opaque FFI Types (`Sqlite3` vs `CFile`)
pub type Sqlite3 = extern opaque {
    pub fn from_addr(addr: usize) -> *mut Self {
        return addr as *mut Self;
    }

    pub fn tag(self: *const Self) -> i32 {
        return (self as usize) as i32;
    }
};

pub extern opaque CFile {
    pub fn from_addr(addr: usize) -> *mut Self {
        return addr as *mut Self;
    }
}

pub fn ping_db(self: *mut Sqlite3, delta: i32) -> i32 {
    return self.tag() + delta;
}

pub fn addr_of_any(p: *const opaque) -> usize {
    return p as usize;
}

// Existential Return Types (`-> opaque Counter` and `-> opaque Counter + Resettable`)
pub trait Counter {
    fn get(self: &Self) -> i32;
    fn add(self: &mut Self, delta: i32);
}

pub trait Resettable {
    fn reset(self: &mut Self);
}

pub struct StepCounter {
    val: i32,
    step: i32,

    pub fn get(self: &Self) -> i32 {
        return self.val;
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.val = self.val + delta * self.step;
    }

    pub fn reset(self: &mut Self) {
        self.val = 0;
    }

    pub fn secret_step(self: &Self) -> i32 {
        return self.step;
    }
}

pub fn make_counter(start: i32, step: i32) -> opaque Counter {
    return StepCounter { val: start, step: step };
}

pub fn make_resettable_counter(start: i32) -> opaque Counter + Resettable {
    return StepCounter { val: start, step: 1 };
}

pub fn bump_generic(comptime T: Counter, c: &mut T, amount: i32) -> i32 {
    c.add(amount);
    return c.get();
}

pub fn read_dyn(c: &Counter) -> i32 {
    return c.get();
}

pub fn main() -> i32 {
    // A. Named Opaque FFI handles
    let db: *mut Sqlite3 = Sqlite3.from_addr(40);
    let file: *mut CFile = CFile.from_addr(80);
    if db.tag() != 40 {
        return 1;
    }
    if db.ping_db(2) != 42 {
        return 2;
    }
    // Both `*mut Sqlite3` and `*mut CFile` coerce to universal `*const opaque`
    if addr_of_any(db) != 40 || addr_of_any(file) != 80 {
        return 3;
    }

    // B. Opaque Newtypes (`UserId` and `OrderId` from module `ids`)
    let uid1: UserId = UserId.new(7);
    let uid2: UserId = uid1.next();
    if uid1.raw() != 7 || uid2.raw() != 8 {
        return 4;
    }
    // Explicit `as` cast works outside defining module
    if (uid1 as u64) != 1007 {
        return 5;
    }
    let ord: OrderId = OrderId.from_user(uid1, 3);
    if ord.raw() != 10073 {
        return 6;
    }

    // C. Existential Return Types (`-> opaque Counter` and `-> opaque Counter + Resettable`)
    let mut c1 = make_counter(10, 3);
    c1.add(4); // 10 + 4 * 3 = 22
    if c1.get() != 22 {
        return 7;
    }
    if bump_generic(&mut c1, 2) != 28 {
        return 8;
    }
    if read_dyn(&c1) != 28 {
        return 9;
    }

    let mut c2 = make_resettable_counter(50);
    c2.add(5);
    if c2.get() != 55 {
        return 10;
    }
    c2.reset();
    if c2.get() != 0 {
        return 11;
    }

    return 42;
}
"#;

    let prog = Compiler::compile_package(&[("root::ids", ids_src), ("root", root_src)])
        .expect("Failed to compile named opaques, opaque newtypes, and existential return types");
    let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
    let mut child = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn lli");
    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let output = child.wait_with_output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(42),
        "lli stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );

    // Negative 1: Distinct named opaque pointers (`*mut Sqlite3` vs `*mut CFile`) do NOT implicitly coerce to each other,
    // and concrete pointers (`*mut i32`) do NOT implicitly coerce to `*mut Sqlite3`.
    let err_cross_opaque = Compiler::compile_source(
        r#"
pub extern opaque Sqlite3;
pub extern opaque CFile;
pub fn main() -> i32 {
    let db: *mut Sqlite3 = 40 as *mut Sqlite3;
    let f: *mut CFile = db;
    return 0;
}
"#,
    )
    .expect_err("Expected implicit conversion from `*mut Sqlite3` to `*mut CFile` to be rejected");
    assert!(
        err_cross_opaque.contains("cannot implicitly convert '*mut Sqlite3' to '*mut CFile'"),
        "Unexpected error: {err_cross_opaque}"
    );

    let err_concrete_to_named_opaque = Compiler::compile_source(
        r#"
pub extern opaque Sqlite3;
pub fn main() -> i32 {
    let mut x: i32 = 10;
    let db: *mut Sqlite3 = &mut x;
    return 0;
}
"#,
    )
    .expect_err("Expected implicit conversion from `&mut i32` to `*mut Sqlite3` to be rejected");
    assert!(
        err_concrete_to_named_opaque
            .contains("cannot implicitly convert '&mut i32' to '*mut Sqlite3'"),
        "Unexpected error: {err_concrete_to_named_opaque}"
    );

    let err_deref_named_opaque = Compiler::compile_source(
        r#"
pub extern opaque Sqlite3;
pub fn main() -> i32 {
    let db: *const Sqlite3 = 40 as *const Sqlite3;
    unsafe { let v = *db; }
    return 0;
}
"#,
    )
    .expect_err("Expected dereferencing `*const Sqlite3` to be rejected");
    assert!(
        err_deref_named_opaque.contains("Cannot dereference pointer of type '*const Sqlite3'"),
        "Unexpected error: {err_deref_named_opaque}"
    );

    // Negative 2: Opaque Newtype encapsulation outside defining module:
    //    - Raw literal initialization (`let u: UserId = 42;`) is rejected outside defining module
    //    - Implicit conversion to/from underlying type (`let raw: u64 = u;`) is rejected outside defining module
    //    - Arithmetic operators (`u + u`) are rejected outside defining module
    let err_nt_lit = Compiler::compile_package(&[
            ("root::ids", ids_src),
            (
                "root",
                r#"
import root::ids::UserId;
pub fn main() -> i32 {
    let u: UserId = 42;
    return 0;
}
"#,
            ),
        ])
        .expect_err("Expected raw integer literal assignment to `UserId` outside defining module to be rejected");
    assert!(
            err_nt_lit.contains("Cannot initialize opaque newtype 'UserId' directly from an integer literal outside module 'root::ids'"),
            "Unexpected error: {err_nt_lit}"
        );

    let err_nt_implicit = Compiler::compile_package(&[
            ("root::ids", ids_src),
            (
                "root",
                r#"
import root::ids::UserId;
pub fn main() -> i32 {
    let u: UserId = UserId.new(7);
    let raw: u64 = u;
    return 0;
}
"#,
            ),
        ])
        .expect_err("Expected implicit conversion from `UserId` to `u64` outside defining module to be rejected");
    assert!(
            err_nt_implicit.contains("is an opaque newtype outside module 'root::ids' and cannot be implicitly converted to 'u64'"),
            "Unexpected error: {err_nt_implicit}"
        );

    let err_nt_arith = Compiler::compile_package(&[
        ("root::ids", ids_src),
        (
            "root",
            r#"
import root::ids::UserId;
pub fn main() -> i32 {
    let uid: UserId = UserId.new(7);
    let uid_b = uid + uid;
    return 0;
}
"#,
        ),
    ])
    .expect_err("Expected raw arithmetic on `UserId` outside defining module to be rejected");
    assert!(
            err_nt_arith.contains("Cannot perform binary operator 'add' directly on opaque newtype 'UserId' outside module 'root::ids'"),
            "Unexpected error: {err_nt_arith}"
        );

    // Negative 3: Existential Return Type (`-> opaque Counter`) encapsulation:
    //    - Cannot bind to explicit concrete type (`let c: StepCounter = make_counter(1, 1);`)
    //    - Cannot access concrete fields (`c.val`)
    //    - Cannot call inherent methods not in the trait bound (`c.secret_step()`)
    //    - Cannot return a type that does not satisfy the bound
    let err_exist_concrete_annot = Compiler::compile_source(
            r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub struct StepCounter {
    val: i32,
    pub fn get(self: &Self) -> i32 { return self.val; }
}
pub fn make_counter(v: i32) -> opaque Counter {
    return StepCounter { val: v };
}
pub fn main() -> i32 {
    let c: StepCounter = make_counter(10);
    return c.get();
}
"#,
        )
        .expect_err("Expected binding `-> opaque Counter` to explicit concrete type `StepCounter` to be rejected");
    assert!(
        err_exist_concrete_annot
            .contains("return value to explicit concrete type 'StepCounter' in 'let c'"),
        "Unexpected error: {err_exist_concrete_annot}"
    );

    let err_exist_field = Compiler::compile_source(
        r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub struct StepCounter {
    val: i32,
    pub fn get(self: &Self) -> i32 { return self.val; }
}
pub fn make_counter(v: i32) -> opaque Counter {
    return StepCounter { val: v };
}
pub fn main() -> i32 {
    let c = make_counter(10);
    return c.val;
}
"#,
    )
    .expect_err(
        "Expected direct field access `c.val` on `-> opaque Counter` variable to be rejected",
    );
    assert!(
        err_exist_field.contains("Cannot access concrete field 'val' on existential"),
        "Unexpected error: {err_exist_field}"
    );

    let err_exist_method = Compiler::compile_source(
            r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub struct StepCounter {
    val: i32,
    pub fn get(self: &Self) -> i32 { return self.val; }
    pub fn secret(self: &Self) -> i32 { return 99; }
}
pub fn make_counter(v: i32) -> opaque Counter {
    return StepCounter { val: v };
}
pub fn main() -> i32 {
    let c = make_counter(10);
    return c.secret();
}
"#,
        )
        .expect_err("Expected calling non-trait method `c.secret()` on `-> opaque Counter` variable to be rejected");
    assert!(
            err_exist_method.contains("Cannot call method 'secret' on opaque return value 'c': method 'secret' is not declared in its trait bound"),
            "Unexpected error: {err_exist_method}"
        );

    let err_exist_unsatisfied = Compiler::compile_source(
        r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub struct NotACounter { val: i32 }
pub fn make_counter(v: i32) -> opaque Counter {
    return NotACounter { val: v };
}
pub fn main() -> i32 {
    let c = make_counter(10);
    return 0;
}
"#,
    )
    .expect_err("Expected returning `NotACounter` from `-> opaque Counter` to be rejected");
    assert!(
        err_exist_unsatisfied.contains(
            "Return type 'NotACounter' in 'make_counter' does not satisfy 'opaque' return bound"
        ),
        "Unexpected error: {err_exist_unsatisfied}"
    );

    let err_exist_conflict = Compiler::compile_source(
        r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub struct CounterA {
    val: i32,
    pub fn get(self: &Self) -> i32 { return self.val; }
}
pub struct CounterB {
    val: i32,
    pub fn get(self: &Self) -> i32 { return self.val; }
}
pub fn make_counter(flag: bool) -> opaque Counter {
    if flag {
        return CounterA { val: 1 };
    }
    return CounterB { val: 2 };
}
pub fn main() -> i32 {
    let c = make_counter(true);
    return c.get();
}
"#,
    )
    .expect_err("Expected conflicting concrete return types in `-> opaque Counter` to be rejected");
    assert!(
        err_exist_conflict.contains(
            "Conflicting concrete return types in '-> opaque ...' function 'make_counter'"
        ),
        "Unexpected error: {err_exist_conflict}"
    );
}

#[test]
fn test_export_types_functions_null_checks_and_c_header() {
    let src = r#"
export enum Mode {
    Fast = 0,
    Safe = 1,
}

export error MathErr {
    DivByZero,
    NegativeInput,
}

export type HandleId = opaque u64 {
    pub fn new(raw: u64) -> HandleId {
        return raw as HandleId;
    }
}

export struct Point {
    x: c_int,
    y: c_int,
    coords: [i32; 2],
}

export opaque Counter {
    val: c_int,

    pub fn new(v: c_int) -> Self {
        return Self { val: v };
    }

    pub fn add(c: *mut Self, delta: c_int) -> c_int {
        unsafe {
            (*c).val = (*c).val + delta;
            return (*c).val;
        }
    }

    pub fn get(c: *const Self) -> c_int {
        unsafe {
            return (*c).val;
        }
    }
}

export fn counter_add(c: *mut Counter, delta: c_int) -> c_int {
    return Counter::add(c, delta);
}

export fn counter_try_get(c: ?*const Counter, fallback: c_int) -> c_int {
    let ptr = c orelse return fallback;
    return Counter::get(ptr);
}

export fn counter_nonnull_if_positive(c: *mut Counter) -> ?*mut Counter {
    if Counter::get(c as *const Counter) > (0 as c_int) {
        return c;
    }
    return null;
}

export fn make_point_if_valid(x: c_int, y: c_int, ok: bool) -> ?Point {
    if !ok {
        return null;
    }
    return Point { x: x, y: y, coords: [i32; 2] { 10, 20 } };
}

export fn checked_div(a: c_int, b: c_int) -> MathErr!c_int {
    if b == (0 as c_int) {
        return MathErr::DivByZero;
    }
    if a < (0 as c_int) {
        return MathErr::NegativeInput;
    }
    return a / b;
}

export fn check_mode(m: Mode) -> MathErr!void {
    match m {
        Mode::Fast => return,
        Mode::Safe => return MathErr::NegativeInput,
    }
}

pub fn main() -> i32 {
    let mut cnt = Counter::new(5 as c_int);
    let v1 = counter_add(&mut cnt, 7 as c_int);
    if v1 != (12 as c_int) { return 1; }

    let v2 = counter_try_get(&cnt, 99 as c_int);
    if v2 != (12 as c_int) { return 2; }
    let v3 = counter_try_get(null, 99 as c_int);
    if v3 != (99 as c_int) { return 3; }

    // Calling `export fn` via internal lrrr signature (`-> ?Point`, `-> MathErr!c_int`)
    let pt_opt = make_point_if_valid(3 as c_int, 4 as c_int, true);
    let pt = pt_opt orelse return 4;
    if pt.x != (3 as c_int) || pt.coords[1] != 20 { return 5; }

    let q_ok = checked_div(24 as c_int, 6 as c_int) catch 0 as c_int;
    if q_ok != (4 as c_int) { return 6; }

    // Calling `export fn` via lowered C ABI out-pointer signature (`bool ...(..., *mut E, *mut T)`)
    let mut out_pt = Point { x: 0 as c_int, y: 0 as c_int, coords: [i32; 2] { 0, 0 } };
    let ok_pt = make_point_if_valid(8 as c_int, 9 as c_int, true, &mut out_pt);
    if !ok_pt || out_pt.x != (8 as c_int) || out_pt.y != (9 as c_int) { return 7; }
    let fail_pt = make_point_if_valid(8 as c_int, 9 as c_int, false, null);
    if fail_pt { return 8; }

    let mut out_err: MathErr = MathErr::NegativeInput;
    let mut out_div: c_int = 0 as c_int;
    let div_ok = checked_div(30 as c_int, 5 as c_int, &mut out_err, &mut out_div);
    if !div_ok || out_div != (6 as c_int) { return 9; }

    let div_fail = checked_div(30 as c_int, 0 as c_int, &mut out_err, null);
    if div_fail { return 10; }
    match out_err {
        MathErr::DivByZero => {},
        MathErr::NegativeInput => return 11,
    }

    let mode_ok = check_mode(Mode::Fast, null);
    if !mode_ok { return 12; }
    let mode_fail = check_mode(Mode::Safe, &mut out_err);
    if mode_fail { return 13; }

    return 42;
}
"#;
    let (mut prog, header) =
        Compiler::compile_source_with_c_header(src).expect("Failed to compile export program");

    assert!(header.contains("#include <stdbool.h>"), "Header:\n{header}");
    assert!(
        header.contains("typedef struct Counter Counter;"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("typedef enum MathErr {"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("MathErr_DivByZero = 0,"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("typedef uint64_t HandleId;"),
        "Header:\n{header}"
    );
    assert!(header.contains("int32_t coords[2];"), "Header:\n{header}");
    assert!(
        header.contains("int counter_add(Counter* c, int delta);"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("int counter_try_get(const Counter* c, int fallback);"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("Counter* counter_nonnull_if_positive(Counter* c);"),
        "Header:\n{header}"
    );
    assert!(
        header
            .contains("bool make_point_if_valid(int x, int y, bool ok, /* out */ Point* out_val);"),
        "Header:\n{header}"
    );
    assert!(
        header.contains(
            "bool checked_div(int a, int b, /* out */ MathErr* out_err, /* out */ int* out_val);"
        ),
        "Header:\n{header}"
    );
    assert!(
        header.contains("bool check_mode(Mode m, /* out */ MathErr* out_err);"),
        "Header:\n{header}"
    );

    let main_id = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let vm_val = Vm::eval(&mut prog, main_id, vec![]).expect("VM execution failed");
    assert_eq!(vm_val, Value::Int(42));

    let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
    if let Ok(mut child) = Command::new("lli")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
    {
        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(llvm_ir.as_bytes())
            .unwrap();
        let output = child.wait_with_output().unwrap();
        assert_eq!(output.status.code(), Some(42));
    }

    // Verify automatic panicking null check on bare `*mut Counter` in `export fn`:
    let null_trap_src = r#"
export opaque Counter {
    val: i32,
    pub fn inc(c: *mut Self) -> i32 {
        unsafe {
            (*c).val = (*c).val + 1;
            return (*c).val;
        }
    }
}
export fn counter_inc(c: *mut Counter) -> i32 {
    return Counter::inc(c);
}
pub fn main() -> i32 {
    let null_ptr: *mut Counter = 0 as *mut Counter;
    return counter_inc(null_ptr);
}
"#;
    let mut trap_prog = Compiler::compile_source(null_trap_src).expect("Should compile");
    let trap_main = trap_prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let trap_res = Vm::eval(&mut trap_prog, trap_main, vec![]);
    assert!(
        trap_res.is_err(),
        "Expected passing null raw pointer to bare `*mut Counter` parameter of `export fn` to trap at entry"
    );

    // Negative tests:
    // 1. Passing `export opaque` by value in `export fn`
    let err_struct_val = Compiler::compile_source(
        r#"
export opaque Engine { x: i32 }
export fn take_engine(e: Engine) -> i32 { return 0; }
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected passing `export opaque` by value in `export fn` to be rejected");
    assert!(
        err_struct_val.contains("is an opaque handle type and must be passed behind a raw pointer"),
        "Unexpected error: {err_struct_val}"
    );

    // 2. Passing safe reference `&i32` or `&str` in `export fn`
    let err_safe_ref = Compiler::compile_source(
        r#"
export fn bad_ref(x: &i32) -> i32 { return *x; }
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected safe reference `&i32` in `export fn` to be rejected");
    assert!(
        err_safe_ref.contains("Safe reference '&i32' is forbidden across FFI"),
        "Unexpected error: {err_safe_ref}"
    );

    // 3. Bare array by value in `export fn`
    let err_bare_arr = Compiler::compile_source(
        r#"
export fn bad_arr(a: [i32; 4]) -> i32 { return a[0]; }
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected bare array by value in `export fn` to be rejected");
    assert!(
        err_bare_arr
            .contains("Bare fixed-size array '[i32; 4]' cannot be passed or returned by value"),
        "Unexpected error: {err_bare_arr}"
    );

    // 4. `export error` with payload variant
    let err_payload_error = Compiler::compile_source(
        r#"
export error BadErr {
    Code(i32),
}
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected `export error` with payload variant to be rejected");
    assert!(
        err_payload_error.contains("'export error' is restricted to unit variants"),
        "Unexpected error: {err_payload_error}"
    );

    // 5. `export union`
    let err_export_union = Compiler::compile_source(
        r#"
export union BadUnion {
    A(i32),
    B(f64),
}
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected `export union` to be rejected");
    assert!(
        err_export_union.contains("Tagged 'union' types cannot be declared 'export'"),
        "Unexpected error: {err_export_union}"
    );

    // 6. `pub` field on `opaque` is rejected at compile time (all fields in `opaque { ... }` are strictly private):
    let err_pub_field_in_opaque = Compiler::compile_source(
        r#"
pub opaque BadOpaque {
    pub x: i32,
}
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected `pub` field inside `opaque { ... }` to be rejected");
    assert!(
        err_pub_field_in_opaque.contains("Field 'x' of 'opaque' type cannot be declared 'pub'"),
        "Unexpected error: {err_pub_field_in_opaque}"
    );

    // 7. Zero-field `opaque Token {}` is a sized ZST (can be passed by value), whereas `extern opaque CHandle;` is unsized:
    let zst_opaque_src = r#"
pub opaque Token {
    pub fn new() -> Self {
        return Self {};
    }
}
pub fn consume_token(t: Token) -> i32 {
    return 42;
}
pub fn main() -> i32 {
    let tok = Token::new();
    return consume_token(tok);
}
"#;
    let mut zst_prog = Compiler::compile_source(zst_opaque_src)
        .expect("Expected zero-field `opaque Token` to compile as a sized ZST");
    let zst_main = zst_prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    assert_eq!(
        Vm::eval(&mut zst_prog, zst_main, vec![]).unwrap(),
        Value::Int(42)
    );

    let err_zst_outside = Compiler::compile_source(
        r#"
pub opaque Token {}
pub fn main() -> i32 {
    let t = Token {};
    return 0;
}
"#,
    )
    .expect_err(
        "Expected constructing zero-field `opaque Token {}` outside its block to be rejected",
    );
    assert!(
        err_zst_outside
            .contains("Cannot construct opaque type 'Token' outside its 'opaque { ... }' block"),
        "Unexpected error: {err_zst_outside}"
    );
}

#[test]
fn test_static_and_static_mut_unsafe_and_sync_rules() {
    let src = r#"
pub const BASE_VAL: i32 = 100;
pub comptime FACTOR = 3;

pub struct Config {
pub limit: i32,
pub scale: i32,
}

pub static GLOBAL_CFG: Config = Config { limit: BASE_VAL, scale: FACTOR };
pub static mut GLOBAL_COUNTER: i32 = 10;
pub static mut GLOBAL_ARR: [i32; 3] = { 1, 2, 3 };

pub opaque IdGen {
pub const START_ID: i32 = 50;
const SECRET_OFFSET: i32 = 7;
static mut NEXT_ID: i32 = 50;
pub static MAX_ID: i32 = 1000;

pub fn next() -> i32 {
    let ptr: *mut i32 = &raw mut Self::NEXT_ID;
    unsafe {
        let cur = *ptr;
        Self::NEXT_ID = cur + Self::SECRET_OFFSET;
        return cur;
    }
}
}

pub fn read_cfg_ref() -> &Config {
return &GLOBAL_CFG;
}

pub fn main() -> i32 {
// 1. Safe read & shared borrow of immutable `static`:
let cfg_ref = read_cfg_ref();
let base = cfg_ref.limit * GLOBAL_CFG.scale; // 100 * 3 = 300

// 2. Taking `&raw const` and `&raw mut` of `static mut` is safe outside `unsafe`:
let raw_cnt_const: *const i32 = &raw const GLOBAL_COUNTER;
let raw_cnt_mut: *mut i32 = &raw mut GLOBAL_COUNTER;
let raw_elem_mut: *mut i32 = &raw mut GLOBAL_ARR[1];

// 3. Reading/writing `static mut` or dereferencing `*const T` / `*mut T` inside `unsafe`:
let mutated_sum: i32 = unsafe {
    *raw_cnt_mut = *raw_cnt_const + 5; // GLOBAL_COUNTER = 15
    GLOBAL_COUNTER += 5;               // GLOBAL_COUNTER = 20
    *raw_elem_mut = 20;                // GLOBAL_ARR[1] = 20
    GLOBAL_ARR[2] = 30;                // GLOBAL_ARR[2] = 30
    GLOBAL_COUNTER + GLOBAL_ARR[0] + GLOBAL_ARR[1] + GLOBAL_ARR[2] // 20 + 1 + 20 + 30 = 71
};

// 4. Associated `const` and `static` on `opaque`:
let id1 = IdGen::next(); // 50
let id2 = IdGen::next(); // 57
let max_id = IdGen::MAX_ID; // 1000
let start_id = IdGen::START_ID; // 50

// 300 + 71 + 50 + 57 + 1000 - 50 = 1428
return base + mutated_sum + id1 + id2 + max_id - start_id;
}
"#;
    let mut prog = Compiler::compile_source(src)
        .expect("Expected valid static / static mut / const / &raw program to compile");
    let main_id = prog
        .functions
        .iter()
        .find(|f| f.export.as_deref() == Some("main"))
        .unwrap()
        .id;
    let res = Vm::eval(&mut prog, main_id, vec![]).expect("VM eval failed");
    assert_eq!(res, Value::Int(1428));

    let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
    assert!(llvm_ir.contains("= constant { i32, i32 } { i32 100, i32 3 }"));
    assert!(llvm_ir.contains("= global i32 10"));

    // Negative 1: Reading `static mut` outside `unsafe` is rejected:
    let err_read_mut = Compiler::compile_source(
        r#"
pub static mut COUNTER: i32 = 0;
pub fn main() -> i32 {
return COUNTER;
}
"#,
    )
    .expect_err("Expected reading `static mut` outside `unsafe` to be rejected");
    assert!(
        err_read_mut.contains(
            "Use of mutable static 'COUNTER' is unsafe and requires an 'unsafe { ... }' block"
        ),
        "Unexpected error: {err_read_mut}"
    );

    // Negative 2: Mutating `static mut` outside `unsafe` is rejected:
    let err_write_mut = Compiler::compile_source(
        r#"
pub static mut COUNTER: i32 = 0;
pub fn main() -> i32 {
COUNTER = 5;
return 0;
}
"#,
    )
    .expect_err("Expected writing `static mut` outside `unsafe` to be rejected");
    assert!(
        err_write_mut.contains(
            "Use of mutable static 'COUNTER' is unsafe and requires an 'unsafe { ... }' block"
        ),
        "Unexpected error: {err_write_mut}"
    );

    // Negative 3: Taking `&STATIC_MUT` or `&mut STATIC_MUT` is strictly forbidden even inside `unsafe`:
    let err_safe_ref_mut = Compiler::compile_source(
        r#"
pub static mut COUNTER: i32 = 0;
pub fn main() -> i32 {
unsafe {
    let r: &i32 = &COUNTER;
    return *r;
}
}
"#,
    )
    .expect_err("Expected `&COUNTER` on `static mut` to be rejected even in `unsafe`");
    assert!(
        err_safe_ref_mut.contains("Taking a safe reference ('&' or '&mut') to mutable static 'COUNTER' is forbidden; use '&raw const' or '&raw mut' instead"),
        "Unexpected error: {err_safe_ref_mut}"
    );

    let err_safe_mut_ref_mut = Compiler::compile_source(
        r#"
pub static mut COUNTER: i32 = 0;
pub fn main() -> i32 {
unsafe {
    let r: &mut i32 = &mut COUNTER;
    *r = 1;
    return *r;
}
}
"#,
    )
    .expect_err("Expected `&mut COUNTER` on `static mut` to be rejected even in `unsafe`");
    assert!(
        err_safe_mut_ref_mut.contains("Taking a safe reference ('&' or '&mut') to mutable static 'COUNTER' is forbidden; use '&raw const' or '&raw mut' instead"),
        "Unexpected error: {err_safe_mut_ref_mut}"
    );

    // Negative 4: Auto-borrowing `static mut` for a `&self` or `&mut self` method call is rejected even in `unsafe`:
    let err_method_borrow_mut = Compiler::compile_source(
        r#"
pub opaque Boxed {
x: i32,
pub fn get(self: &Self) -> i32 { return self.x; }
pub static mut INST: Boxed = Boxed { x: 7 };
}
pub fn main() -> i32 {
unsafe {
    return Boxed::INST.get();
}
}
"#,
    )
    .expect_err("Expected auto-borrowing `static mut` for `&Self` method to be rejected");
    assert!(
        err_method_borrow_mut
            .contains("Cannot auto-borrow mutable static 'Boxed::INST' as a safe reference"),
        "Unexpected error: {err_method_borrow_mut}"
    );

    // Negative 5: Dereferencing raw pointer `*const T` or `*mut T` outside `unsafe` is rejected:
    let err_deref_raw = Compiler::compile_source(
        r#"
pub static mut COUNTER: i32 = 0;
pub fn main() -> i32 {
let p: *const i32 = &raw const COUNTER;
return *p;
}
"#,
    )
    .expect_err("Expected dereferencing `*const i32` outside `unsafe` to be rejected");
    assert!(
        err_deref_raw.contains("Dereferencing raw pointer of type '*const i32' is unsafe and requires an 'unsafe { ... }' block"),
        "Unexpected error: {err_deref_raw}"
    );

    // Negative 6: Immutable `static` requires `T: sync`:
    let err_unsync_static = Compiler::compile_source(
        r#"
pub opaque UnsyncCell {
ptr: *mut i32,
pub static BAD: UnsyncCell = UnsyncCell { ptr: 0 as *mut i32 };
}
pub fn main() -> i32 {
let _x = &UnsyncCell::BAD;
return 0;
}
"#,
    )
    .expect_err("Expected immutable `static` of `!sync` type to be rejected");
    assert!(
        err_unsync_static.contains("requires 'UnsyncCell: sync'"),
        "Unexpected error: {err_unsync_static}"
    );

    // Negative 7: Mutating or taking `&raw mut` of immutable `static` is rejected:
    let err_mutate_immut_static = Compiler::compile_source(
        r#"
pub static IMMUT: i32 = 10;
pub fn main() -> i32 {
IMMUT = 20;
return IMMUT;
}
"#,
    )
    .expect_err("Expected mutating immutable `static` to be rejected");
    assert!(
        err_mutate_immut_static
            .contains("Cannot mutate or mutably borrow immutable static variable 'IMMUT'"),
        "Unexpected error: {err_mutate_immut_static}"
    );

    let err_raw_mut_immut_static = Compiler::compile_source(
        r#"
pub static IMMUT: i32 = 10;
pub fn main() -> i32 {
let p: *mut i32 = &raw mut IMMUT;
return 0;
}
"#,
    )
    .expect_err("Expected `&raw mut` of immutable `static` to be rejected");
    assert!(
        err_raw_mut_immut_static.contains(
            "Cannot take mutable raw pointer '&raw mut' to immutable static variable 'IMMUT'"
        ),
        "Unexpected error: {err_raw_mut_immut_static}"
    );

    // Negative 8: Reading `static mut` inside an index expression of `&raw const ARR[IDX]` outside `unsafe` is rejected:
    let err_raw_index_mut = Compiler::compile_source(
        r#"
pub static ARR: [i32; 4] = { 10, 20, 30, 40 };
pub static mut IDX: usize = 1;
pub fn main() -> i32 {
let p: *const i32 = &raw const ARR[IDX];
return 0;
}
"#,
    )
    .expect_err("Expected reading `static mut IDX` inside `&raw const ARR[IDX]` outside `unsafe` to be rejected");
    assert!(
        err_raw_index_mut.contains(
            "Use of mutable static 'IDX' is unsafe and requires an 'unsafe { ... }' block"
        ),
        "Unexpected error: {err_raw_index_mut}"
    );

    // Negative 9: `static` or `const` inside transparent `struct { ... }` is rejected:
    let err_struct_static = Compiler::compile_source(
        r#"
pub struct Point {
pub x: i32,
pub static ORIGIN_X: i32 = 0;
}
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected `static` inside transparent `struct` to be rejected");
    assert!(
        err_struct_static.contains("Associated 'static' or 'const'/'comptime' declarations are forbidden inside transparent 'struct' blocks"),
        "Unexpected error: {err_struct_static}"
    );
}

#[test]
fn test_memory_intrinsics_alloc_realloc_dealloc_memcpy_memmove_transmute_forget() {
    let src = r#"
pub static mut DROP_COUNTER: i32 = 0;

pub opaque TrackedGuard {
    tag: i32,

    pub fn new(tag: i32) -> Self {
        return Self { tag: tag };
    }

    pub fn tag(self: &Self) -> i32 {
        return self.tag;
    }

    drop(self: &mut Self) {
        unsafe {
            DROP_COUNTER += self.tag;
        }
    }
}

pub opaque(linear) LinearTicket {
    code: i64,

    pub fn new(code: i64) -> Self {
        return Self { code: code };
    }

    pub fn redeem(move self) -> i64 {
        return self.code;
    }
}

pub struct SplitU64 {
    pub lo: u32,
    pub hi: u32,
}

pub fn Vec(comptime T: type) -> type {
    return opaque {
        ptr: ?*mut T,
        len: usize,
        cap: usize,

        pub fn new() -> Self {
            return Self { ptr: null, len: 0, cap: 0 };
        }

        fn grow(self: &mut Self) -> *mut T {
            let mut new_cap: usize = 2;
            if self.cap != 0 {
                new_cap = self.cap * 2;
            }
            if let old_ptr = self.ptr {
                let new_ptr: *mut T = @realloc(T, old_ptr, new_cap);
                self.ptr = new_ptr;
                self.cap = new_cap;
                return new_ptr;
            } else {
                let new_ptr: *mut T = @alloc(T, new_cap);
                self.ptr = new_ptr;
                self.cap = new_cap;
                return new_ptr;
            }
        }

        pub fn push(self: &mut Self, value: T) {
            if self.len == self.cap {
                let _ = self.grow();
            }
            let p: *mut T = self.ptr orelse unreachable;
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

        pub fn len(self: &Self) -> usize {
            return self.len;
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

        default() -> Self {
            return Self::new();
        }

        clone(self: &Self) -> Self where T: clone {
            let src_ptr = self.ptr orelse return @default(Self);
            if self.len == 0 {
                return @default(Self);
            }
            let new_ptr: *mut T = @alloc(T, self.len);
            let mut i: usize = 0;
            while i < self.len {
                unsafe {
                    *(new_ptr + i) = @clone(&*(src_ptr + i));
                }
                i += 1;
            }
            return Self {
                ptr: new_ptr,
                len: self.len,
                cap: self.len,
            };
        }

        drop(self: &mut Self) where T: !linear {
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
    };
}

pub fn main() -> i32 {
    // 1. Test `Vec(i32)` using `@alloc`, `@realloc`, `@dealloc`, `@default`, `@clone`, `@drop`:
    let mut v = Vec(i32)::new();
    v.push(10);
    v.push(20);
    v.push(30); // triggers `@realloc` from cap 2 -> 4
    v.push(40);
    v.push(50); // triggers `@realloc` from cap 4 -> 8
    let mut v_copy = @clone(&v);
    let popped: i32 = v_copy.pop() orelse 0;
    if popped != 50 || v.len() != 5 || v_copy.len() != 4 {
        return 1;
    }

    // 2. Test `@memcpy` and `@memmove`:
    let src_arr: [i32; 5] = { 1, 2, 3, 4, 5 };
    let mut dst_arr: [i32; 5] = { 0, 0, 0, 0, 0 };
    unsafe {
        let base: *mut i32 = &raw mut dst_arr[0];
        @memcpy(base, &raw const src_arr[0], 5);
        // Overlapping shift right by 1 (`dst_arr[1..5] = dst_arr[0..4]` -> `{ 1, 1, 2, 3, 4 }`):
        @memmove(base + 1, base, 4);
    }
    if dst_arr[0] != 1 || dst_arr[1] != 1 || dst_arr[2] != 2 || dst_arr[3] != 3 || dst_arr[4] != 4 {
        return 2;
    }

    // 3. Test `@transmute`:
    let one_f32: f32 = 1.0;
    let bits_u32: u32 = unsafe { @transmute(u32, one_f32) };
    if bits_u32 != 0x3F800000 {
        return 3;
    }
    let split = SplitU64 { lo: 0x11223344, hi: 0x55667788 };
    let combined: u64 = unsafe { @transmute(u64, split) };
    let split_back: SplitU64 = unsafe { @transmute(SplitU64, combined) };
    if split_back.lo != 0x11223344 || split_back.hi != 0x55667788 {
        return 4;
    }

    // `@transmute` consumes affine/linear values without running their destructors:
    let g_transmuted = TrackedGuard::new(100);
    let raw_tag: i32 = unsafe { @transmute(i32, g_transmuted) };
    if raw_tag != 100 {
        return 5;
    }
    let ticket_transmuted = LinearTicket::new(77);
    let raw_code: i64 = unsafe { @transmute(i64, ticket_transmuted) };
    if raw_code != 77 {
        return 6;
    }

    // 4. Test `@forget`:
    if true {
        let g_dropped = TrackedGuard::new(7);
        let g_forgotten = TrackedGuard::new(1000);
        let lin_forgotten = LinearTicket::new(999);
        unsafe {
            @forget(g_forgotten);
            @forget(lin_forgotten);
        }
        let _ = g_dropped.tag();
    }
    // Only `g_dropped` (7) should have run its destructor; `g_transmuted` (100) and `g_forgotten` (1000) were suppressed!
    let drops: i32 = unsafe { DROP_COUNTER };
    if drops != 7 {
        return 7;
    }

    return 42;
}
"#;

    let prog = Compiler::compile_source(src)
        .expect("Expected memory intrinsics program to compile cleanly");
    let llvm_ir = LlvmLowering::lower(&prog).expect("Expected LLVM lowering to succeed");
    assert!(
        llvm_ir.contains("@llvm.memcpy.p0.p0.i64") && llvm_ir.contains("@llvm.memmove.p0.p0.i64"),
        "Expected LLVM IR to contain `@llvm.memcpy.p0.p0.i64` and `@llvm.memmove.p0.p0.i64`, got:\n{llvm_ir}"
    );

    let bin_path = "/tmp/lrrr_test_memory_intrinsics_bin";
    let mut clang = Command::new("clang")
        .args(["-x", "ir", "-", "-o", bin_path, "-Wno-override-module"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn clang");
    clang
        .stdin
        .as_mut()
        .unwrap()
        .write_all(llvm_ir.as_bytes())
        .unwrap();
    let clang_out = clang.wait_with_output().unwrap();
    assert!(
        clang_out.status.success(),
        "clang failed: {}",
        String::from_utf8_lossy(&clang_out.stderr)
    );
    let run_out = Command::new(bin_path).output().unwrap();
    let _ = std::fs::remove_file(bin_path);
    assert_eq!(run_out.status.code(), Some(42));

    // Negative 1: `@dealloc` outside `unsafe` is rejected:
    let err_dealloc = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let p: *mut i32 = @alloc(i32, 4);
    @dealloc(p);
    return 0;
}
"#,
    )
    .expect_err("Expected `@dealloc` outside `unsafe` to be rejected");
    assert!(
        err_dealloc.contains("'@dealloc' is unsafe and requires an 'unsafe { ... }' block"),
        "Unexpected error: {err_dealloc}"
    );

    // Negative 2: `@memcpy` outside `unsafe` is rejected:
    let err_memcpy = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let mut a: i32 = 1;
    let b: i32 = 2;
    @memcpy(&raw mut a, &raw const b, 1);
    return 0;
}
"#,
    )
    .expect_err("Expected `@memcpy` outside `unsafe` to be rejected");
    assert!(
        err_memcpy.contains("'@memcpy' is unsafe and requires an 'unsafe { ... }' block"),
        "Unexpected error: {err_memcpy}"
    );

    // Negative 3: `@transmute` outside `unsafe` is rejected:
    let err_transmute_unsafe = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let x: f32 = 1.0;
    let y: u32 = @transmute(u32, x);
    return y as i32;
}
"#,
    )
    .expect_err("Expected `@transmute` outside `unsafe` to be rejected");
    assert!(
        err_transmute_unsafe
            .contains("'@transmute' is unsafe and requires an 'unsafe { ... }' block"),
        "Unexpected error: {err_transmute_unsafe}"
    );

    // Negative 4: `@transmute` with mismatched sizes is rejected at compile time:
    let err_transmute_size = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let x: u32 = 1;
    let y: u64 = unsafe { @transmute(u64, x) };
    return y as i32;
}
"#,
    )
    .expect_err("Expected `@transmute` between `u32` and `u64` to be rejected");
    assert!(
        err_transmute_size
            .contains("Cannot '@transmute' from 'u32' (4 bytes) to 'u64' (8 bytes): types must have identical size"),
        "Unexpected error: {err_transmute_size}"
    );

    // Negative 5: `@forget` outside `unsafe` is rejected:
    let err_forget_unsafe = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let x: i32 = 1;
    @forget(x);
    return 0;
}
"#,
    )
    .expect_err("Expected `@forget` outside `unsafe` to be rejected");
    assert!(
        err_forget_unsafe.contains("'@forget' is unsafe and requires an 'unsafe { ... }' block"),
        "Unexpected error: {err_forget_unsafe}"
    );

    // Negative 6: Using a variable after `@forget` is rejected by move analysis (`src/drop.rs`):
    let err_use_after_forget = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let x: i32 = 10;
    unsafe {
        @forget(x);
    }
    return x;
}
"#,
    )
    .expect_err("Expected reading `x` after `@forget(x)` to be rejected");
    assert!(
        err_use_after_forget.contains("Use of moved or uninitialized value"),
        "Unexpected error: {err_use_after_forget}"
    );

    // Negative 7: Calling `@forget(x)` while `x` is borrowed by a live reference is rejected by `src/borrowck.rs`:
    let err_forget_borrowed = Compiler::compile_source(
        r#"
pub fn main() -> i32 {
    let x: i32 = 10;
    let r: &i32 = &x;
    unsafe {
        @forget(x);
    }
    return *r;
}
"#,
    )
    .expect_err("Expected `@forget(x)` while `r = &x` is still live to be rejected");
    assert!(
        err_forget_borrowed.contains("Borrow check error"),
        "Unexpected error: {err_forget_borrowed}"
    );
}
