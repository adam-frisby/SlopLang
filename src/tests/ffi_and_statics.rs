
use crate::llvm::LlvmLowering;
use crate::lower::Compiler;
use crate::vm::{Value, Vm};
use super::{lli, link_ir, link_with_c, TRAP_EXIT};

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
pub fn double_signed[S: signed](x: S) -> S {
    return x + x;
}
pub fn bump_unsigned[U: unsigned](x: U) -> U {
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

    let doubled_ci: c_int = double_signed[c_int](ci); // 42
    let bumped_cui: c_uint = bump_unsigned[c_uint](cui); // 10

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
    let output = lli(&llvm_ir);
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
        err_mix_bin.contains("cannot implicitly convert 'i32' to 'c_int'"),
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
    
    

    // 1. End-to-end compilation & execution covering:
    //    - Named Opaque FFI Types (`pub extern opaque Sqlite3 { ... }`, `pub extern opaque CFile`,
    //      inherent & extension methods on `*mut Sqlite3`, universal `*mut opaque` coercion)
    //    - Distinct types (`pub type UserId = distinct u64 { ... };`): nominal, same layout,
    //      converted with `as` in every module, literals and same-type operators allowed
    //    - Existential Return Types (`-> opaque Counter`, `-> opaque Counter + Resettable`, trait method calls, generic `comptime T: Counter`, `&Counter` borrowing)
    let ids_src = r#"
pub type UserId = distinct u64 {
    pub fn new(raw: u64) -> Self {
        // Conversion to and from `u64` is explicit, in the defining module too.
        return (raw + 1000) as UserId;
    }

    pub fn raw(self: Self) -> u64 {
        return (self as u64) - 1000;
    }

    pub fn next(self: Self) -> Self {
        return self + 1;
    }
};

pub type OrderId = distinct u64 {
    pub fn from_user(u: UserId, seq: u64) -> Self {
        return ((u as u64) * 10 + seq) as OrderId;
    }

    pub fn raw(self: Self) -> u64 {
        return self as u64;
    }
};
"#;
    let root_src = r#"
import root::ids::UserId;
import root::ids::OrderId;

// Named Opaque FFI Types (`Sqlite3` vs `CFile`)
pub extern opaque Sqlite3 {
    pub fn from_addr(addr: usize) -> *mut Self {
        return addr as *mut Self;
    }

    pub fn tag(self: *const Self) -> i32 {
        return (self as usize) as i32;
    }
}

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

    impl Counter {
        fn get(self: &Self) -> i32 {
            return self.val;
        }

        fn add(self: &mut Self, delta: i32) {
            self.val = self.val + delta * self.step;
        }
    }

    impl Resettable {
        fn reset(self: &mut Self) {
            self.val = 0;
        }
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

pub fn bump_generic[T: Counter](c: &mut T, amount: i32) -> i32 {
    c.add(amount);
    return c.get();
}

pub fn read_dyn(c: &Counter) -> i32 {
    return c.get();
}

pub fn main() -> i32 {
    // A. Named Opaque FFI handles
    let db: *mut Sqlite3 = Sqlite3::from_addr(40);
    let file: *mut CFile = CFile::from_addr(80);
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

    // B. Distinct types (`UserId` and `OrderId` from module `ids`)
    let uid1: UserId = UserId::new(7);
    let uid2: UserId = uid1.next();
    if uid1.raw() != 7 || uid2.raw() != 8 {
        return 4;
    }
    // `as` converts in every module, and literals and same-type operators apply
    let lit: UserId = 1009;
    if (uid1 as u64) != 1007 || ((uid2 + 1) as u64) != (lit as u64) {
        return 5;
    }
    let ord: OrderId = OrderId::from_user(uid1, 3);
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
        .expect("Failed to compile named opaques, distinct types, and existential return types");
    let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
    let output = lli(&llvm_ir);
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

    // Negative 2: a distinct type never converts implicitly, in any module, and does not mix
    // with its underlying type or with another distinct type in operators.
    let rejected = |src: &str| {
        Compiler::compile_package(&[("root::ids", ids_src), ("root", src)])
            .expect_err("expected a type error")
    };
    let err = rejected(
        "import root::ids::UserId;
pub fn main() -> i32 { let u: UserId = UserId::new(7); let raw: u64 = u; return 0; }",
    );
    assert!(
        err.contains("'UserId' is a distinct type and does not convert implicitly to 'u64'"),
        "Unexpected error: {err}"
    );
    let err = rejected(
        "import root::ids::UserId;
pub fn main() -> i32 { let u: UserId = UserId::new(7); let n: u64 = 1; let v = u + n; return 0; }",
    );
    assert!(err.contains("does not convert implicitly"), "Unexpected error: {err}");
    let err = rejected(
        "import root::ids::{UserId, OrderId};
pub fn main() -> i32 { let u = UserId::new(7); let o = OrderId::from_user(u, 1); let v = u + o; return 0; }",
    );
    assert!(err.contains("UserId") && err.contains("OrderId"), "Unexpected error: {err}");
    let err = Compiler::compile_source(
        "type Id = distinct u64 { pub fn of(r: u64) -> Self { return r; } };
pub fn main() -> i32 { return 0; }",
    )
    .expect_err("implicit conversion inside the defining module");
    assert!(
        err.contains("'Id' is a distinct type and does not convert implicitly from 'u64'"),
        "Unexpected error: {err}"
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
    impl Counter { fn get(self: &Self) -> i32 { return self.val; } }
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
    impl Counter { fn get(self: &Self) -> i32 { return self.val; } }
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
    impl Counter { fn get(self: &Self) -> i32 { return self.val; } }
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
    impl Counter { fn get(self: &Self) -> i32 { return self.val; } }
}
pub struct CounterB {
    val: i32,
    impl Counter { fn get(self: &Self) -> i32 { return self.val; } }
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

export type HandleId = distinct u64 {
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

    // The lowered C ABI signatures (`bool ...(..., *mut T)` for `?T`, and `E ...(..., *mut T)` for
    // `E!T`) are reachable from Lrrr only as C function pointers obtained with `@c_abi(...)`.
    let make_c = @c_abi(make_point_if_valid);
    let div_c = @c_abi(checked_div);
    let mode_c = @c_abi(check_mode);
    let mut out_pt = Point { x: 0 as c_int, y: 0 as c_int, coords: [i32; 2] { 0, 0 } };
    let ok_pt = make_c(8 as c_int, 9 as c_int, true, &raw mut out_pt);
    if !ok_pt || out_pt.x != (8 as c_int) || out_pt.y != (9 as c_int) { return 7; }
    let fail_pt = make_c(8 as c_int, 9 as c_int, false, 0 as *mut Point);
    if fail_pt { return 8; }

    let mut out_div: c_int = 0 as c_int;
    let div_ok = div_c(30 as c_int, 5 as c_int, &raw mut out_div);
    if div_ok != (0 as c_int) || out_div != (6 as c_int) { return 9; }

    let div_fail = div_c(30 as c_int, 0 as c_int, 0 as *mut c_int);
    if div_fail != (1 as c_int) { return 10; }
    let div_neg = div_c(-5 as c_int, 2 as c_int, 0 as *mut c_int);
    if div_neg != (2 as c_int) { return 11; }

    let mode_ok = mode_c(Mode::Fast);
    if mode_ok != (0 as c_int) { return 12; }
    let mode_fail = mode_c(Mode::Safe);
    if mode_fail != (2 as c_int) { return 13; }

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
        header.contains("MathErr_Ok = 0,"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("MathErr_DivByZero = 1,"),
        "Header:\n{header}"
    );
    assert!(
        header.contains("MathErr_NegativeInput = 2,"),
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
            "MathErr checked_div(int a, int b, /* out */ int* out_val);"
        ),
        "Header:\n{header}"
    );
    assert!(
        header.contains("MathErr check_mode(Mode m);"),
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
    let output = lli(&llvm_ir);
    assert_eq!(output.status.code(), Some(42));

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
        err_struct_val.contains("an 'export opaque' is a handle type and must be passed behind a raw pointer"),
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

    // 4. `export error` embedding another error set or passed by value when payload-carrying is forbidden
    let err_export_embedded = Compiler::compile_source(
        r#"
error Inner { A }
export error Outer {
    Inner,
    B,
}
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected `export error` with embedded error to be rejected");
    assert!(
        err_export_embedded.contains("Exported error 'Outer' cannot embed other error sets"),
        "Unexpected error: {err_export_embedded}"
    );

    let err_payload_error = Compiler::compile_source(
        r#"
export error BadErr {
    Code: i32,
}
export fn take_err(e: BadErr) -> i32 { return 0; }
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected payload-carrying `export error` passed by value to be rejected");
    assert!(
        err_payload_error.contains("Payload-carrying error 'BadErr' cannot be passed or embedded by value across FFI"),
        "Unexpected error: {err_payload_error}"
    );

    // 5. `export union` payloads must be FFI-safe
    let err_export_union = Compiler::compile_source(
        r#"
export union BadUnion {
    A(&str),
    B(f64),
}
pub fn main() -> i32 { return 0; }
"#,
    )
    .expect_err("Expected an `export union` with a `&str` payload to be rejected");
    assert!(
        err_export_union.contains("forbidden across FFI in payload of variant 'BadUnion::A'"),
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

    impl drop {
        fn drop(self: &mut Self) {
            unsafe {
                DROP_COUNTER += self.tag;
            }
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

pub fn Vec[T] -> type {
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
        }

        impl drop where T: !linear {
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
    };
}

pub fn main() -> i32 {
    // 1. Test `Vec[i32]` using `@alloc`, `@realloc`, `@dealloc`, `@default`, `@clone`, `@drop`:
    let mut v = Vec[i32]::new();
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

    let run_out = link_ir("memory_intrinsics", &llvm_ir).run(&[]);
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

#[test]
fn test_export_error_explicit_c_values() {
    // Unit-only `export error` returns its error code directly in C (reserving `Ok = 0` by default or
    // custom `<ident> = <value>`), while payload-carrying `export error` returns `<Name>_Tag` and
    // writes the payload to `<Name>* err_out`. Unioning/embedding errors creates a composed `error`
    // union without flattening their numeric values.
    let src = r#"
export error DbError { NotFound = 404, Busy = -1, Aborted = 7 }
export error(c_int) ExplicitCInt { ok Ok = 1, Zero = 0, Neg = -5 }
export error(u8) SmallErr { ok Success = 255, Low = 0, High = 200 }
export error Plain { First, Mid }
export error RichErr {
    Bad: i32,
    Coords: struct { x: i32, y: i32 },
    Empty,
}
error Wider { DbError, SmallErr, Other }
alias Combined = DbError || SmallErr;
fn widen(e: DbError) -> Wider!i32 { return e; }
fn widen_small(e: SmallErr) -> Wider!i32 { return e; }
fn combine_both(which: i32) -> Combined!i32 {
    if which == 1 { return DbError::Busy; }
    if which == 2 { return SmallErr::Low; }
    return 100;
}
export fn fail(code: i32) -> DbError!i32 {
    if code == 1 { return DbError::NotFound; }
    if code == 2 { return DbError::Busy; }
    return 7;
}
export fn fail_small(code: i32) -> SmallErr!i32 {
    if code == 1 { return SmallErr::Low; }
    if code == 2 { return SmallErr::High; }
    return 9;
}
export fn fail_cint(code: i32) -> ExplicitCInt!void {
    if code == 1 { return ExplicitCInt::Zero; }
    if code == 2 { return ExplicitCInt::Neg; }
    return;
}
export fn fail_rich(code: i32) -> RichErr!c_int {
    if code == 1 { return RichErr::Bad(42); }
    if code == 2 { return RichErr::Coords({ x: 10, y: 20 }); }
    if code == 3 { return RichErr::Empty; }
    return 99 as c_int;
}
export fn fail_rich_void(code: i32) -> RichErr!void {
    if code == 1 { return RichErr::Bad(-7); }
    if code == 2 { return RichErr::Empty; }
    return;
}
export fn classify(e: DbError) -> i32 {
    let w = widen(e) catch |err| {
        match err {
            DbError::NotFound => { return 10; }
            DbError::Busy => { return 20; }
            DbError::Aborted => { return 30; }
            SmallErr::Low => { return 50; }
            SmallErr::High => { return 60; }
            Wider::Other => { return 40; }
        }
    };
    return w;
}
export fn classify_small(e: SmallErr) -> i32 {
    let w = widen_small(e) catch |err| {
        match err {
            SmallErr::Low => { return 50; }
            SmallErr::High => { return 60; }
            _ => { return 99; }
        }
    };
    return w;
}
export fn check_combined() -> i32 {
    if !@satisfies(DbError, error) || !@satisfies(RichErr, error) { return -1; }
    if !@satisfies(Combined, error) { return -2; }
    let a = combine_both(1) catch |err| {
        match err {
            DbError::Busy => -10,
            _ => 0,
        }
    };
    let b = combine_both(2) catch |err| {
        match err {
            SmallErr::Low => 25,
            _ => 0,
        }
    };
    return a + b;
}
export fn check_cint(e: ExplicitCInt) -> i32 {
    match e {
        ExplicitCInt::Zero => { return 100; }
        ExplicitCInt::Neg => { return 200; }
    }
}
export fn read_ptr(p: *const DbError) -> i32 { let e = unsafe { *p }; return classify(e); }
export fn write_ptr(p: *mut DbError) { unsafe { *p = DbError::Aborted; } }
export fn plain() -> Plain!void { return Plain::Mid; }
"#;
    let (prog, header) = Compiler::compile_source_with_c_header(src).expect("compiles");
    assert!(
        header.contains("    DbError_Ok = 0,\n    DbError_Busy = -1,\n    DbError_Aborted = 7,\n    DbError_NotFound = 404,"),
        "explicit values with Ok = 0 first, then variants in value order:\n{header}"
    );
    assert!(
        header.contains("typedef enum ExplicitCInt {\n    ExplicitCInt_Ok = 1,\n    ExplicitCInt_Neg = -5,\n    ExplicitCInt_Zero = 0,\n} ExplicitCInt;"),
        "export error(c_int) with `ok Ok = 1` emits standard enum with custom Ok = 1:\n{header}"
    );
    assert!(
        header.contains("typedef enum SmallErr : uint8_t {\n    SmallErr_Success = 255,\n    SmallErr_Low = 0,\n    SmallErr_High = 200,\n} SmallErr;"),
        "export error(u8) with `ok Success = 255` emits fixed-underlying-type enum:\n{header}"
    );
    assert!(
        header.contains("    Plain_Ok = 0,\n    Plain_First = 1,\n    Plain_Mid = 2,"),
        "declaration order starting at 1 without explicit values:\n{header}"
    );
    assert!(
        header.contains("typedef union RichErr RichErr;")
            && header.contains("typedef enum RichErr_Tag {\n    RichErr_Ok = 0,\n    RichErr_Bad = 1,\n    RichErr_Coords = 2,\n    RichErr_Empty = 3,\n} RichErr_Tag;")
            && header.contains("union RichErr {\n    int32_t Bad;\n    struct {\n        int32_t x;\n        int32_t y;\n    } Coords;\n};")
            && header.contains("RichErr_Tag fail_rich(int32_t code, /* out */ int* out_val, /* out */ RichErr* err_out);")
            && header.contains("RichErr_Tag fail_rich_void(int32_t code, /* out */ RichErr* err_out);"),
        "payload-carrying export error emits RichErr_Tag, union RichErr, and err_out parameter:\n{header}"
    );
    let ir = LlvmLowering::lower_with_trap_exit(&prog, TRAP_EXIT).expect("lowers");
    let bin = link_with_c(
        "export_errorcode",
        &ir,
        &header,
        r#"#include <stdlib.h>
#include "lib.h"
int main(int argc, char **argv) {
    if (argc == 2) return classify((DbError)5); /* not a variant: traps */
    if (argc == 3) return classify_small((SmallErr)1); /* not a variant of SmallErr: traps */
    DbError e = DbError_Aborted; int v = 0;
    if (sizeof(SmallErr) != 1) return 10;
    if (fail(1, &v) != DbError_NotFound) return 1;
    if (fail(2, &v) != DbError_Busy) return 2;
    if (fail(3, &v) != DbError_Ok || v != 7) return 3;
    if (classify(DbError_NotFound) != 10 || classify(DbError_Busy) != 20) return 4;
    if (classify(DbError_Aborted) != 30) return 5;
    e = DbError_Busy;
    if (read_ptr(&e) != 20) return 6;
    write_ptr(&e);
    if (e != DbError_Aborted) return 7;
    if (plain() != Plain_Mid) return 8;
    if (check_combined() != 15) return 9;
    if (fail_small(1, &v) != SmallErr_Low) return 11;
    if (fail_small(2, &v) != SmallErr_High) return 12;
    if (fail_small(3, &v) != SmallErr_Success || v != 9) return 15;
    if (classify_small(SmallErr_Low) != 50 || classify_small(SmallErr_High) != 60) return 13;
    if (check_cint(ExplicitCInt_Zero) != 100 || check_cint(ExplicitCInt_Neg) != 200) return 14;
    if (fail_cint(1) != ExplicitCInt_Zero || fail_cint(2) != ExplicitCInt_Neg || fail_cint(3) != ExplicitCInt_Ok) return 16;
    RichErr r_err = {0};
    int r_val = 0;
    if (fail_rich(0, &r_val, &r_err) != RichErr_Ok || r_val != 99) return 17;
    if (fail_rich(1, &r_val, &r_err) != RichErr_Bad || r_err.Bad != 42 || r_val != 99) return 18;
    if (fail_rich(2, &r_val, &r_err) != RichErr_Coords || r_err.Coords.x != 10 || r_err.Coords.y != 20) return 19;
    if (fail_rich(3, &r_val, &r_err) != RichErr_Empty) return 20;
    if (fail_rich(1, NULL, NULL) != RichErr_Bad) return 21;
    if (fail_rich_void(0, &r_err) != RichErr_Ok) return 22;
    if (fail_rich_void(1, &r_err) != RichErr_Bad || r_err.Bad != -7) return 23;
    if (fail_rich_void(2, NULL) != RichErr_Empty) return 24;
    return 42;
}
"#,
    );
    let ok = bin.run(&[]);
    let bad = bin.run(&["bad"]);
    let bad_small = bin.run(&["a", "b"]);
    assert_eq!(ok.status.code(), Some(42));
    assert_eq!(bad.status.code(), Some(TRAP_EXIT), "an unknown error value from C traps");
    assert_eq!(bad_small.status.code(), Some(TRAP_EXIT), "an unknown u8 error value from C traps");

    for (src, expected) in [
        (
            "export error E { A = 1, B }\nexport fn f() -> E!void { return E::A; }",
            "Variant 'E::B' needs an explicit value",
        ),
        (
            "error C { X }\nerror E { A = 1, C }\npub fn main() -> i32 { return 0; }",
            "cannot mix embedded error sets with explicit",
        ),
        (
            "export error E { A = 1, B = 1 }\nexport fn f() -> E!void { return E::A; }",
            "have the same value 1",
        ),
        (
            "export error E { A = 0 }\nexport fn f() -> E!void { return E::A; }",
            "reserved for the success flag",
        ),
        (
            "export error E { ok Ok = 5, A = 5 }\nexport fn f() -> E!void { return E::A; }",
            "reserved for the success flag",
        ),
        (
            "export error E { Ok = 1 }\nexport fn f() -> E!void { return E::Ok; }",
            "conflicts with reserved success flag",
        ),
        (
            "export error E { A = 4294967296 }\nexport fn f() -> E!void { return E::A; }",
            "does not fit a C enum",
        ),
        (
            "export error(u8) E { A = 300 }\nexport fn f() -> E!void { return E::A; }",
            "does not fit backing type 'u8'",
        ),
        (
            "export error E { A = -1, B = 0x80004005 }\nexport fn f() -> E!void { return E::A; }",
            "mix negative values with values above INT_MAX",
        ),
    ] {
        let err = Compiler::compile_source_with_c_header(src)
            .err()
            .unwrap_or_else(|| panic!("expected rejection of:\n{src}"));
        assert!(err.contains(expected), "Unexpected error for:\n{src}\n{err}");
    }
    // Unsigned codes above INT_MAX (HRESULT-style) are fine when none is negative.
    let (_, header) = Compiler::compile_source_with_c_header(
        "export error E { A = 0x80004005 }\nexport fn f() -> E!void { return E::A; }",
    )
    .expect("unsigned C values compile");
    assert!(header.contains("E_A = 2147500037,"), "{header}");
}

#[test]
fn test_c_abi_aggregates_cross_in_both_directions() {
    // Each shape is passed and returned by value between C (clang) and Lrrr in both directions:
    // C calls `export fn`s, and Lrrr calls C `extern fn`s. The shapes cover each x86-64 System V
    // case: odd-sized integer eightbytes, float pairs, mixed integer/float eightbytes, and
    // aggregates over 16 bytes (`byval` / `sret`).
    let shapes: [(&str, &[(&str, &str)]); 10] = [
        ("B3", &[("u8", "uint8_t"); 3]),
        ("F2", &[("f32", "float"); 2]),
        ("F3", &[("f32", "float"); 3]),
        ("D2", &[("f64", "double"); 2]),
        ("IF", &[("i32", "int32_t"), ("f32", "float")]),
        ("FID", &[("f32", "float"), ("i32", "int32_t"), ("f64", "double")]),
        ("DI", &[("f64", "double"), ("i64", "int64_t")]),
        ("L3", &[("i64", "int64_t"); 3]),
        ("H5", &[("i16", "int16_t"); 5]),
        ("BIG", &[("f64", "double"), ("f64", "double"), ("f32", "float"), ("u8", "uint8_t")]),
    ];
    let mut lr = String::new();
    let mut c = String::from("#include <stdio.h>\n#include \"lib.h\"\n");
    let mut checks = String::new();
    for (name, fields) in shapes {
        let f = |i: usize| ((b'a' + i as u8) as char).to_string();
        let decl: Vec<String> =
            fields.iter().enumerate().map(|(i, (t, _))| format!("{}: {t}", f(i))).collect();
        let lit: Vec<String> = fields
            .iter()
            .enumerate()
            .map(|(i, (t, _))| format!("{}: {} as {t}", f(i), i + 1))
            .collect();
        let sum: Vec<String> = (0..fields.len()).map(|i| format!("(s.{} as f64)", f(i))).collect();
        let csum: Vec<String> = (0..fields.len()).map(|i| format!("(double)s.{}", f(i))).collect();
        let msum: Vec<String> = (0..fields.len()).map(|i| format!("(double)m.{}", f(i))).collect();
        let init: Vec<String> = (1..=fields.len()).map(|i| i.to_string()).collect();
        let (sum, csum, init) = (sum.join(" + "), csum.join(" + "), init.join(", "));
        let total: usize = (1..=fields.len()).sum();
        lr += &format!(
            "export struct {name} {{ {} }}
export fn lr_sum_{name}(k: i32, s: {name}) -> f64 {{ return {sum} + (k as f64); }}
export fn lr_mk_{name}() -> {name} {{ return {name} {{ {} }}; }}
extern fn c_sum_{name}(k: i32, s: {name}) -> f64;
extern fn c_mk_{name}() -> {name};
export fn lr_calls_c_{name}() -> i32 {{
    let s = unsafe {{ c_mk_{name}() }};
    if unsafe {{ c_sum_{name}(100, s) }} != {}.0 {{ return 1; }}
    if ({sum}) != {total}.0 {{ return 2; }}
    return 0;
}}
",
            decl.join(", "),
            lit.join(", "),
            total + 100
        );
        c += &format!(
            "double c_sum_{name}(int32_t k, {name} s) {{ return {csum} + k; }}
{name} c_mk_{name}(void) {{ {name} s = {{ {init} }}; return s; }}
"
        );
        checks += &format!(
            "    {{ {name} s = {{ {init} }}; if (lr_sum_{name}(1000, s) != {}.0) return 1;
      {name} m = lr_mk_{name}(); if ({} != {total}.0) return 2;
      if (lr_calls_c_{name}()) return 3; }}
",
            total + 1000,
            msum.join(" + ")
        );
    }
    // Register exhaustion (seven 16-byte structs fill the integer registers; the rest go on the
    // stack) and the zero / sign extension of narrow integer arguments.
    lr += "export struct P2 { a: i64, b: i64 }
export fn lr_many(a: P2, b: P2, c: P2, d: P2, e: P2, f: P2, g: P2, h: D2) -> i64 {
    return a.a + b.b + c.a + d.b + e.a + f.b + g.a + g.b + (h.a as i64) + (h.b as i64);
}
extern fn c_many(a: P2, b: P2, c: P2, d: P2, e: P2, f: P2, g: P2, h: D2) -> i64;
export fn lr_calls_c_many() -> i64 {
    let p = P2 { a: 1, b: 2 };
    return unsafe { c_many(p, p, p, p, p, p, p, D2 { a: 10.0, b: 20.0 }) };
}
export fn lr_small(a: i8, b: u8, c: bool, d: i16) -> i32 {
    let mut r: i32 = (a as i32) + (b as i32) + (d as i32);
    if c { r = r + 1000; }
    return r;
}
extern fn c_small(a: i8, b: u8, c: bool, d: i16) -> i32;
export fn lr_calls_c_small() -> i32 { return unsafe { c_small(-5, 250, true, -300) }; }
";
    c += "int64_t c_many(P2 a, P2 b, P2 c, P2 d, P2 e, P2 f, P2 g, D2 h) {
    return a.a + b.b + c.a + d.b + e.a + f.b + g.a + g.b + (int64_t)h.a + (int64_t)h.b;
}
int32_t c_small(int8_t a, uint8_t b, bool c, int16_t d) { return a + b + d + (c ? 1000 : 0); }
int main(void) {
";
    c += &checks;
    c += "    P2 p = {1, 2}; D2 h = {10.0, 20.0};
    if (lr_many(p, p, p, p, p, p, p, h) != 42 || lr_calls_c_many() != 42) return 4;
    if (lr_small(-5, 250, true, -300) != 945 || lr_calls_c_small() != 945) return 5;
    return 42;
}
";
    let (prog, header) = Compiler::compile_source_with_c_header(&lr).expect("compiles");
    let ir = LlvmLowering::lower(&prog).expect("lowers");
    let out = link_with_c("c_abi_aggregates", &ir, &header, &c).run(&[]);
    assert_eq!(out.status.code(), Some(42), "{}", String::from_utf8_lossy(&out.stdout));
}

#[test]
fn test_export_union_is_a_c_tagged_struct() {
    // An exported union is C's `struct { Tag tag; union { ... } payload; }`: it crosses by
    // value in both directions, nests in `export struct`s, takes explicit `= N` values and an
    // optional backing integer type (`union(Int)`), and a tag naming no variant traps.
    let src = r#"
export struct Point { x: i32, y: i32 }
export union Msg {
    Quit,
    Ping(i32),
    Move: struct { dx: i32, dy: i32 },
    Pair(tuple { i64, f64 }),
    At(Point),
    Scale(f64),
}
export union(c_int) Instr { Push: i64 = 10, Pop = 20, Nop = 30 }
export struct Frame { id: u8, msg: Msg }
fn score(m: Msg) -> i32 {
    match m {
        Msg::Quit => { return 1; }
        Msg::Ping(n) => { return n; }
        Msg::Move(d) => { return d.dx * 10 + d.dy; }
        Msg::Pair(p) => { return (p.0 as i32) + (p.1 as i32); }
        Msg::At(p) => { return p.x + p.y; }
        Msg::Scale(s) => { return (s * 2.0) as i32; }
    }
}
export fn lr_score(m: Msg) -> i32 { return score(m); }
export fn lr_make(k: i32) -> Msg {
    if k == 0 { return Msg::Quit; }
    if k == 1 { return Msg::Ping(77); }
    if k == 2 { return Msg::Move { dx: 3, dy: 4 }; }
    if k == 3 { return Msg::Pair({ 40, 2.5 }); }
    if k == 4 { return Msg::At(Point { x: 5, y: 6 }); }
    return Msg::Scale(10.5);
}
export fn lr_frame(f: *const Frame) -> i32 {
    let m = unsafe { (*f).msg };
    return score(m) + (unsafe { (*f).id } as i32);
}
export fn lr_instr(i: Instr) -> i64 {
    match i { Instr::Push(v) => { return v; } Instr::Pop => { return -1; } Instr::Nop => { return 0; } }
}
extern fn c_make(k: i32) -> Msg;
extern fn c_score(m: Msg) -> i32;
export fn lr_round_trip() -> i32 {
    let mut total: i32 = 0;
    let mut k: i32 = 0;
    while k < 6 { total = total + score(unsafe { c_make(k) }) + unsafe { c_score(lr_make(k)) }; k = k + 1; }
    return total;
}
"#;
    let c_main = r#"#include <string.h>
#include "lib.h"
static int score(Msg m) {
    switch (m.tag) {
    case Msg_Quit: return 1;
    case Msg_Ping: return m.payload.Ping;
    case Msg_Move: return m.payload.Move.dx * 10 + m.payload.Move.dy;
    case Msg_Pair: return (int)m.payload.Pair._0 + (int)m.payload.Pair._1;
    case Msg_At: return m.payload.At.x + m.payload.At.y;
    case Msg_Scale: return (int)(m.payload.Scale * 2.0);
    }
    return -1000;
}
Msg c_make(int32_t k) {
    Msg m;
    memset(&m, 0, sizeof m);
    switch (k) {
    case 0: m.tag = Msg_Quit; break;
    case 1: m.tag = Msg_Ping; m.payload.Ping = 77; break;
    case 2: m.tag = Msg_Move; m.payload.Move.dx = 3; m.payload.Move.dy = 4; break;
    case 3: m.tag = Msg_Pair; m.payload.Pair._0 = 40; m.payload.Pair._1 = 2.5; break;
    case 4: m.tag = Msg_At; m.payload.At.x = 5; m.payload.At.y = 6; break;
    default: m.tag = Msg_Scale; m.payload.Scale = 10.5;
    }
    return m;
}
int32_t c_score(Msg m) { return score(m); }
int main(int argc, char **argv) {
    (void)argv;
    if (argc > 1) { Msg bad; memset(&bad, 0, sizeof bad); bad.tag = (Msg_Tag)9; return lr_score(bad); }
    for (int k = 0; k < 6; k++) {
        Msg m = c_make(k);
        if (lr_score(m) != score(m) || score(lr_make(k)) != score(m)) return 1;
    }
    Frame f;
    memset(&f, 0, sizeof f);
    f.id = 3;
    f.msg = c_make(2);
    if (lr_frame(&f) != 37) return 2;
    Instr i; i.tag = Instr_Push; i.payload.Push = 123456789012LL;
    Instr j; j.tag = Instr_Pop;
    if (lr_instr(i) != 123456789012LL || lr_instr(j) != -1) return 3;
    if (lr_round_trip() != 2 * (1 + 77 + 34 + 42 + 11 + 21)) return 4;
    return 42;
}
"#;
    let (prog, header) = Compiler::compile_source_with_c_header(src).expect("compiles");
    let tuple_member = "        struct {\n            int64_t _0;\n            double _1;\n        } Pair;";
    assert!(
        header.contains("typedef enum Msg_Tag {\n    Msg_Quit = 0,")
            && header.contains("typedef enum Instr_Tag {\n    Instr_Push = 10,\n    Instr_Pop = 20,\n    Instr_Nop = 30,\n} Instr_Tag;")
            && header.contains("struct Instr {\n    Instr_Tag tag;")
            && header.contains(tuple_member),
        "{header}"
    );
    let ir = LlvmLowering::lower_with_trap_exit(&prog, TRAP_EXIT).expect("lowers");
    let bin = link_with_c("export_union", &ir, &header, c_main);
    assert_eq!(bin.run(&[]).status.code(), Some(42));
    assert_eq!(bin.run(&["bad"]).status.code(), Some(TRAP_EXIT), "an unknown tag from C traps");

    let err = Compiler::compile_source(
        "struct Inner { x: i32 }\nexport union U { A(i32), B(Inner) }\npub fn main() -> i32 { return 0; }",
    )
    .expect_err("an export union payload must be FFI-safe");
    assert!(err.contains("variant 'U::B'"), "{err}");
}

#[test]
fn test_c_function_pointers() {
    // `extern fn(...)` pointers use the C calling convention: callbacks from C, pointers returned
    // by C, and `@c_abi` pointers handed to C all pass aggregates by value correctly.
    let src = r#"
export struct Big { a: i64, b: i64, c: i64 }
export struct Pair { x: i32, y: f64 }
export fn apply(f: extern fn(Big) -> Big, v: i64) -> i64 {
    let r = f(Big { a: v, b: v + 1, c: v + 2 });
    return r.a + r.b + r.c;
}
export fn lr_scale(p: Pair) -> Pair { return Pair { x: p.x * 2, y: p.y * 2.0 }; }
extern fn c_get_doubler() -> extern fn(Big) -> Big;
extern fn c_run(f: extern fn(Pair) -> Pair) -> i32;
export fn lr_round() -> i32 {
    let d = unsafe { c_get_doubler() };
    let r = d(Big { a: 1, b: 2, c: 3 });
    return (r.a + r.b + r.c) as i32 + unsafe { c_run(@c_abi(lr_scale)) };
}
"#;
    let c_main = r#"#include "lib.h"
static Big triple(Big b) { Big r = { b.a * 3, b.b * 3, b.c * 3 }; return r; }
static Big doubler(Big b) { Big r = { b.a * 2, b.b * 2, b.c * 2 }; return r; }
Big (*c_get_doubler(void))(Big) { return doubler; }
int32_t c_run(Pair (*f)(Pair)) { Pair r = f((Pair){ 10, 1.5 }); return r.x + (int32_t)r.y; }
int main(void) {
    if (apply(triple, 1) != 18) return 1;
    if (lr_round() != 12 + 23) return 2;
    return 42;
}
"#;
    let (prog, header) = Compiler::compile_source_with_c_header(src).expect("compiles");
    assert!(header.contains("int64_t apply(Big (*f)(Big), int64_t v);"), "{header}");
    let ir = LlvmLowering::lower(&prog).expect("lowers");
    assert_eq!(link_with_c("c_fn_ptrs", &ir, &header, c_main).run(&[]).status.code(), Some(42));
    let err = Compiler::compile_source(
        "fn lr(x: i32) -> i32 { return x; }\nextern fn takes(f: extern fn(i32) -> i32) -> i32;\npub fn main() -> i32 { return takes(lr); }",
    )
    .expect_err("a Lrrr fn is not a C function pointer");
    assert!(err.contains("use different calling conventions"), "{err}");
}

/// The `define` / `declare` signatures in LLVM IR, keyed by symbol, as `ret (params)` with value
/// names and attributes that do not affect the calling convention removed, and named struct
/// types replaced by their bodies.
fn ir_signatures(ir: &str) -> std::collections::HashMap<String, String> {
    let mut structs = Vec::new();
    for line in ir.lines() {
        if let Some((name, body)) = line.split_once(" = type ") {
            structs.push((name.to_string(), body.to_string()));
        }
    }
    let mut sigs = std::collections::HashMap::new();
    for line in ir.lines() {
        let Some(rest) = line.strip_prefix("define ").or_else(|| line.strip_prefix("declare "))
        else {
            continue;
        };
        let at = rest.find('@').unwrap();
        let open = rest[at..].find('(').unwrap() + at;
        let close = rest.rfind(')').unwrap();
        let symbol = rest[at + 1..open].to_string();
        let clean = |s: &str| {
            let mut s = s.to_string();
            for (name, body) in &structs {
                s = s.replace(name.as_str(), body);
            }
            s.split_whitespace()
                .filter(|w| {
                    !w.starts_with('%')
                        && !matches!(
                            *w,
                            "dso_local" | "noundef" | "noalias" | "readonly" | "dead_on_unwind"
                                | "writable"
                                | "local_unnamed_addr" | "returned" | "internal"
                        )
                })
                .collect::<Vec<_>>()
                .join(" ")
        };
        let params: Vec<String> = rest[open + 1..close].split(", ").map(clean).collect();
        // A floating-point block returned as `[3 x float]` is returned in the same registers as
        // clang's `{ float, float, float }`.
        let mut ret = clean(&rest[..at]);
        if let Some(arr) = ret.strip_prefix('[')
            && let Some((n, elem)) = arr.trim_end_matches(']').split_once(" x ")
            && matches!(elem, "float" | "double")
        {
            ret = format!("{{ {} }}", vec![elem; n.parse().unwrap()].join(", "));
        }
        sigs.insert(symbol, format!("{ret} ({})", params.join(", ")));
    }
    sigs
}

#[test]
fn test_c_abi_aarch64_signatures_match_clang() {
    // No AArch64 machine runs the tests, so the signatures Lrrr emits for AArch64 (AAPCS64) are
    // checked against clang's for the same C declarations, both for `export fn` definitions and
    // `extern fn` declarations, and `llc` must accept the module.
    let shapes: [(&str, &[&str]); 15] = [
        ("B3", &["u8"; 3]),
        ("F2", &["f32"; 2]),
        ("F3", &["f32"; 3]),
        ("F4", &["f32"; 4]),
        ("F5", &["f32"; 5]),
        ("D2", &["f64"; 2]),
        ("D4", &["f64"; 4]),
        ("IF", &["i32", "f32"]),
        ("FID", &["f32", "i32", "f64"]),
        ("DI", &["f64", "i64"]),
        ("L1", &["i64"]),
        ("I1", &["i32"]),
        ("S12", &["i32"; 3]),
        ("H5", &["i16"; 5]),
        ("L3", &["i64"; 3]),
    ];
    let mut lr = String::new();
    let mut c = String::new();
    for (name, fields) in shapes {
        let decl: Vec<String> = fields
            .iter()
            .enumerate()
            .map(|(i, t)| format!("{}: {t}", (b'a' + i as u8) as char))
            .collect();
        lr += &format!(
            "export struct {name} {{ {} }}
export fn lr_id_{name}(k: i32, s: {name}) -> {name} {{ return s; }}
extern fn c_id_{name}(k: i32, s: {name}) -> {name};
export fn lr_calls_{name}(s: {name}) -> {name} {{ return unsafe {{ c_id_{name}(0, s) }}; }}
",
            decl.join(", ")
        );
        c += &format!(
            "{name} lr_id_{name}(int32_t k, {name} s) {{ return s; }}
{name} c_id_{name}(int32_t k, {name} s) {{ return s; }}
"
        );
    }
    lr += "export fn lr_small(a: i8, b: u8, c: bool, d: i16) -> i8 { return a; }\n";
    c += "int8_t lr_small(int8_t a, uint8_t b, bool c, int16_t d) { return a; }\n";
    let (prog, header) = Compiler::compile_source_with_c_header(&lr).expect("compiles");
    let dir = std::env::temp_dir().join(format!("lrrr_aarch64_abi_{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.h"), &header).unwrap();
    std::fs::write(dir.join("ref.c"), format!("#include \"lib.h\"\n{c}")).unwrap();
    for (apple, triple) in [(false, "aarch64-unknown-linux-gnu"), (true, "arm64-apple-macosx")] {
        let target = crate::c_abi::Target::Aarch64 { apple };
        let ir = LlvmLowering::lower_for_target(&prog, target).expect("lowers");
        let clang = std::process::Command::new("clang")
            .current_dir(&dir)
            .args(["-S", "-emit-llvm", "-O0", "-ffreestanding", &format!("--target={triple}")])
            .args(["ref.c", "-o", "-"])
            .output()
            .expect("Failed to spawn clang");
        assert!(clang.status.success(), "{}", String::from_utf8_lossy(&clang.stderr));
        let want = ir_signatures(&String::from_utf8_lossy(&clang.stdout));
        let got = ir_signatures(&ir);
        let mut symbols: Vec<&String> = want.keys().filter(|s| !s.starts_with("llvm.")).collect();
        symbols.sort();
        for sym in symbols {
            // `extern fn` declarations are checked against clang's definitions of the same C
            // signature.
            assert_eq!(got.get(sym), Some(&want[sym]), "{triple}: signature of {sym}");
        }
        std::fs::write(dir.join("lib.ll"), &ir).unwrap();
        let llc = std::process::Command::new("llc")
            .current_dir(&dir)
            .args(["lib.ll", "-o", "/dev/null"])
            .output()
            .expect("Failed to spawn llc");
        assert!(llc.status.success(), "{triple}: {}", String::from_utf8_lossy(&llc.stderr));
    }
}

#[test]
fn test_export_wrappers_trap_on_invalid_c_values() {
    // C can put any bits in a `bool` in memory, an enum, or a `rune`, a `NULL` in a non-optional
    // pointer, and any tag in a union. The C-ABI wrapper of an `export fn` checks every such
    // value in its parameters, including inside structs, arrays, and union payloads, and traps
    // on an invalid one before Lrrr code sees it; so do calls to C, on the values C returns. (A
    // `bool` parameter itself arrives as an `i1`, which the C ABI already normalizes.)
    let lr = r#"
export enum Color { Red = 1, Green = 2, Blue = 4 }
export struct Flags { on: bool, color: Color, pct: u8, r: rune }
export struct Palette { c: [Color; 4] }
export union Shape { Dot, Tagged(Flags) }
export fn lr_bool(b: bool) -> i32 { if b { return 1; } return 0; }
export fn lr_flags(f: Flags) -> i32 { return f.pct as i32; }
export fn lr_palette(p: Palette) -> i32 { return p.c[3] as i32; }
export fn lr_shape(s: Shape) -> i32 {
    match s { Shape::Dot => { return 0; } Shape::Tagged(f) => { return f.pct as i32; } }
}
export fn lr_ptr(p: *const i32) -> i32 { return unsafe { *p }; }
extern fn c_flags(k: i32) -> Flags;
export fn lr_from_c(k: i32) -> i32 { return unsafe { c_flags(k) }.pct as i32; }
export fn lr_via_ptr(f: extern fn(i32) -> Flags, k: i32) -> i32 { return f(k).pct as i32; }
"#;
    let c_main = r#"#include <stdlib.h>
#include <string.h>
#include "lib.h"
Flags c_flags(int32_t k) {
    Flags f = { true, Color_Green, 40, 0x1F600 };
    if (k == 1) f.color = (Color)3;
    return f;
}
int main(int argc, char **argv) {
    int which = atoi(argv[1]);
    Flags f = { true, Color_Green, 40, 0x1F600 };
    Palette p = { { Color_Red, Color_Green, Color_Blue, Color_Red } };
    Shape s; memset(&s, 0, sizeof s); s.tag = Shape_Tagged; s.payload.Tagged = f;
    int32_t v = 2;
    unsigned char two = 2;
    switch (which) {
    case 0:
        return lr_bool(true) + lr_flags(f) + lr_palette(p) + lr_shape(s) + lr_ptr(&v) - 84 + 42;
    case 1: f.pct = 0; f.r = 0x10FFFF; return lr_flags(f) + 42;
    case 2: memcpy(&f.on, &two, 1); return lr_flags(f);
    case 3: f.color = (Color)3; return lr_flags(f);
    case 4: f.r = 0xD800; return lr_flags(f);
    case 5: f.r = 0x110000; return lr_flags(f);
    case 6: p.c[3] = (Color)0; return lr_palette(p);
    case 7: s.tag = (Shape_Tag)2; return lr_shape(s);
    case 8: memcpy(&s.payload.Tagged.on, &two, 1); return lr_shape(s);
    case 9: return lr_ptr(NULL);
    case 10: return lr_from_c(0) + lr_via_ptr(c_flags, 0) - 80 + 42;
    case 11: return lr_from_c(1);
    case 12: return lr_via_ptr(c_flags, 1);
    }
    return 1;
}
"#;
    let (prog, header) = Compiler::compile_source_with_c_header(lr).expect("compiles");
    let ir = LlvmLowering::lower_with_trap_exit(&prog, TRAP_EXIT).expect("lowers");
    let bin = link_with_c("c_value_checks", &ir, &header, c_main);
    assert_eq!(bin.run(&["0"]).status.code(), Some(42), "valid values pass");
    assert_eq!(bin.run(&["1"]).status.code(), Some(42), "extreme valid values pass");
    assert_eq!(bin.run(&["10"]).status.code(), Some(42), "valid values from C pass");
    for case in [2, 3, 4, 5, 6, 7, 8, 9, 11, 12] {
        let code = bin.run(&[&case.to_string()]).status.code();
        assert_eq!(code, Some(TRAP_EXIT), "invalid value {case} traps");
    }
}
