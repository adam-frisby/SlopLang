pub mod ast;
pub mod borrowck;
pub mod drop;
pub mod frontend;
pub mod ir;
pub mod lexer;
pub mod llvm;
pub mod lower;
pub mod parser;
pub mod stdlib;
pub mod vm;

#[cfg(test)]
mod tests {
    use std::io::Write;
    use std::process::{Command, Stdio};

    use crate::borrowck::check_borrows;
    use crate::drop::elaborate_drops;
    use crate::ir::{FuncId, Type, TypeId};
    use crate::llvm::LlvmLowering;
    use crate::lower::Compiler;
    use crate::parser::Parser;
    use crate::vm::{Value, Vm};

    #[test]
    fn test_parse_and_roundtrip_ir() {
        let src = "\
ty0 = i64;
ty1 = { ty0, ty0 };
ty2 = &mut ty0;

fn0 = \"main\" {
    let _0: ty0;
    let _1: ty1;
    let _2: ty0;
    let _3: ty2;
    bb0: {
        StorageLive(_1);
        _1 = aggregate ty1(const 10, const 20);
        _2 = move _1.0;
        _3 = &mut _1.1;
        (*_3) = add(copy _2, const 5);
        _0 = call const fn1(move _1.1) -> bb1;
    }
    bb1: {
        StorageDead(_1);
        switchInt(copy _0) -> [25: bb2, otherwise: bb3];
    }
    bb2: {
        goto -> bb4;
    }
    bb3: {
        unreachable;
    }
    bb4: {
        return;
    }
}

fn1(1) {
    let _0: ty0;
    let _1: ty0;
    bb0: {
        _0 = add(copy _1, const 10);
        return;
    }
}
";

        let prog = Parser::parse_program(src).expect("Failed to parse low-level IR program");
        assert_eq!(prog.types.len(), 3);
        assert_eq!(prog.functions.len(), 2);

        // Verify round-trip Display -> Parser produces identical Program
        let printed = format!("{prog}");
        assert_eq!(printed, src);
        let reparsed = Parser::parse_program(&printed).expect("Failed to re-parse printed IR");
        assert_eq!(prog, reparsed);
    }

    #[test]
    fn test_llvm_lowering_and_execution() {
        let src = "\
ty0 = i64;
ty1 = { ty0, ty0 };
ty2 = &mut ty0;

fn0 = \"main\" {
    let _0: ty0;
    let _1: ty1;
    let _2: ty0;
    let _3: ty2;
    bb0: {
        StorageLive(_1);
        _1 = aggregate ty1(const 10, const 20);
        _2 = move _1.0;
        _3 = &mut _1.1;
        (*_3) = add(copy _2, const 15);
        _0 = call const fn1(move _1.1) -> bb1;
    }
    bb1: {
        StorageDead(_1);
        switchInt(copy _0) -> [35: bb2, otherwise: bb3];
    }
    bb2: {
        goto -> bb4;
    }
    bb3: {
        unreachable;
    }
    bb4: {
        return;
    }
}

fn1(1) {
    let _0: ty0;
    let _1: ty0;
    bb0: {
        _0 = add(copy _1, const 10);
        return;
    }
}
";

        let prog = Parser::parse_program(src).expect("Failed to parse IR");
        let llvm_ir = LlvmLowering::lower(&prog).expect("Failed to lower to LLVM IR");

        let mut child = Command::new("lli")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("Failed to spawn `lli`");

        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(llvm_ir.as_bytes())
            .unwrap();

        let output = child.wait_with_output().expect("Failed to wait on `lli`");
        if !output.status.success() && output.status.code() != Some(35) {
            panic!(
                "lli failed: {}\nGenerated LLVM IR:\n{}",
                String::from_utf8_lossy(&output.stderr),
                llvm_ir
            );
        }
        assert_eq!(output.status.code(), Some(35));
    }

    #[test]
    fn test_hello_world() {
        let src = "\
ty0 = i32;
ty1 = u8;
ty2 = &ty1;

extern fn0(ty2) -> ty0 = \"puts\";

fn1 = \"main\" {
    let _0: ty0;
    let _1: ty2;
    bb0: {
        _1 = const \"Hello, World!\";
        _0 = call const fn0(copy _1) -> bb1;
    }
    bb1: {
        _0 = const 0;
        return;
    }
}
";

        let prog = Parser::parse_program(src).expect("Failed to parse Hello World IR");
        assert_eq!(format!("{prog}"), src);

        let llvm_ir = LlvmLowering::lower(&prog).expect("Failed to lower to LLVM IR");

        let mut child = Command::new("lli")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("Failed to spawn `lli`");

        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(llvm_ir.as_bytes())
            .unwrap();

        let output = child.wait_with_output().expect("Failed to wait on `lli`");
        assert!(
            output.status.success(),
            "lli failed: {}\nGenerated LLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(stdout, "Hello, World!\n");
    }

    #[test]
    fn test_integer_types() {
        let src = "\
ty0 = i8;
ty1 = i16;
ty2 = i32;
ty3 = i64;
ty4 = i128;
ty5 = u8;
ty6 = u16;
ty7 = u32;
ty8 = u64;
ty9 = u128;
ty10 = rune;

fn0 {
    let _0: ty9;
    let _1: ty9;
    let _2: ty10;
    let _3: ty4;
    bb0: {
        _1 = const 34028236692093846346337460743176821145;
        _2 = const 129408;
        _3 = const -17014118346046923173168730371588410572;
        _0 = div(copy _1, const 5);
        return;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse integer types IR");
        assert_eq!(format!("{prog}"), src);
        let vm_res = Vm::eval(&mut prog, FuncId(0), vec![]).expect("Failed to eval u128 in VM");
        assert_eq!(
            vm_res,
            Value::Int(6805647338418769269267492148635364229)
        );
        let llvm_ir = LlvmLowering::lower(&prog).expect("Failed to lower integer types IR");
        assert!(llvm_ir.contains("udiv i128"));
    }

    #[test]
    fn test_read_line_echo() {
        let src = "\
ty0 = i32;

extern fn0() -> ty0 = \"getchar\";
extern fn1(ty0) -> ty0 = \"putchar\";

fn2 = \"main\" {
    let _0: ty0;
    let _1: ty0;
    let _2: ty0;
    bb0: {
        _1 = call const fn0() -> bb1;
    }
    bb1: {
        switchInt(copy _1) -> [-1: bb4, otherwise: bb2];
    }
    bb2: {
        _2 = call const fn1(copy _1) -> bb3;
    }
    bb3: {
        switchInt(copy _1) -> [10: bb4, otherwise: bb0];
    }
    bb4: {
        _0 = const 0;
        return;
    }
}
";

        let prog = Parser::parse_program(src).expect("Failed to parse read_line_echo IR");
        assert_eq!(format!("{prog}"), src);

        let llvm_ir = LlvmLowering::lower(&prog).expect("Failed to lower to LLVM IR");
        let ll_path = "/tmp/lrrr_read_line_echo.ll";
        std::fs::write(ll_path, &llvm_ir).expect("Failed to write temporary .ll file");

        let mut child = Command::new("lli")
            .arg(ll_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("Failed to spawn `lli`");

        child
            .stdin
            .as_mut()
            .unwrap()
            .write_all(b"Hello from stdin!\nIgnored second line\n")
            .unwrap();

        let output = child.wait_with_output().expect("Failed to wait on `lli`");
        let _ = std::fs::remove_file(ll_path);

        assert!(
            output.status.success(),
            "lli failed: {}\nGenerated LLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(stdout, "Hello from stdin!\n");
    }

    #[test]
    fn test_vm_comptime_value_and_type_functions() {
        // `fn0(1)` is a Zig-style comptime type function:
        // Given a type `T` (`_1: type`), it constructs `&mut T` (`_2`) and returns
        // the struct type `{ T, &mut T }` (`_0: type`).
        // `fn1` is a comptime value function computing `(10 + 15) + 10 = 35`.
        let src = "\
ty0 = type;
ty1 = i64;
ty2 = u32;

fn0(1) {
    let _0: ty0;
    let _1: ty0;
    let _2: ty0;
    bb0: {
        _2 = &mut _1;
        _0 = aggregate ty0(copy _1, copy _2);
        return;
    }
}

fn1(1) {
    let _0: ty1;
    let _1: ty1;
    bb0: {
        _0 = mul(copy _1, const 7);
        return;
    }
}
";

        let mut prog = Parser::parse_program(src).expect("Failed to parse comptime IR");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate `fn1(5)` at comptime -> Value::Int(35)
        let val = Vm::eval(&mut prog, FuncId(1), vec![Value::Int(5)])
            .expect("Comptime value evaluation failed");
        assert_eq!(val, Value::Int(35));

        // 2. Evaluate `fn0(ty1)` (where ty1 = i64) at comptime -> constructs `{ i64, &mut i64 }`!
        let pair_i64 = Vm::eval(&mut prog, FuncId(0), vec![Value::Type(TypeId(1))])
            .expect("Comptime type evaluation failed");
        let Value::Type(new_struct_ty_id) = pair_i64 else {
            panic!("Expected Value::Type, got {pair_i64:?}");
        };
        assert_eq!(
            prog.types[new_struct_ty_id.0 as usize],
            Type::Struct(vec![TypeId(1), TypeId(3)])
        );
        assert_eq!(
            prog.types[3],
            Type::Ptr {
                mutable: true,
                pointee: TypeId(1)
            }
        );

        // 3. Lower the program to LLVM IR (comptime-only `fn0` is automatically skipped, `fn1` is emitted)
        let llvm_ir = LlvmLowering::lower(&prog).expect("Failed to lower to LLVM IR");
        assert!(!llvm_ir.contains("@fn0"));
        assert!(llvm_ir.contains("define internal i64 @fn1"));
    }

    #[test]
    fn test_union_and_overlay_types() {
        let src = "\
ty0 = u8;
ty1 = void;
ty2 = i64;
ty3 = { ty2, ty2 };
ty4 = union ty0 { ty1, ty2, ty3 };
ty5 = overlay { ty2, ty3 };

fn0 = \"main\" {
    let _0: ty2;
    let _1: ty4;
    let _2: ty0;
    let _3: ty5;
    bb0: {
        StorageLive(_1);
        _1 = union ty4(v1, const 42);
        _2 = discriminant(_1);
        switchInt(copy _2) -> [1: bb1, otherwise: bb2];
    }
    bb1: {
        StorageLive(_3);
        _3.0 = copy _1.v1;
        _0 = copy _3.0;
        StorageDead(_3);
        StorageDead(_1);
        return;
    }
    bb2: {
        unreachable;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse union/overlay IR");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate in VM
        let vm_res = Vm::eval(&mut prog, FuncId(0), vec![]).expect("VM eval failed");
        assert_eq!(vm_res, Value::Int(42));

        // 2. Lower to LLVM IR and execute via `lli`
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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        assert_eq!(
            output.status.code(),
            Some(42),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
    }

    #[test]
    fn test_arrays_floats_casts_ops_and_globals() {
        let src = "\
ty0 = i64;
ty1 = [ty0; 3];
ty2 = f64;
ty3 = &mut ty0;
ty4 = fn(ty0) -> ty0;

global mut gl0: ty0 = const 10;

fn0 = \"main\" {
    let _0: ty0;
    let _1: ty1;
    let _2: ty0;
    let _3: ty2;
    let _4: ty2;
    let _5: ty0;
    let _6: ty3;
    let _7: ty0;
    bb0: {
        StorageLive(_1);
        _1 = aggregate ty1(const 10, const 20, const 30);
        _2 = const 1;
        _3 = cast(copy _1[_2], ty2);
        _4 = mul(copy _3, const 1.5);
        _5 = cast(copy _4, ty0);
        _6 = const gl0;
        _7 = copy (*_6);
        _0 = add(copy _5, copy _7);
        StorageDead(_1);
        return;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse arrays/floats/globals IR");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate in VM: _1[1] is 20 -> 20.0 * 1.5 = 30.0 -> 30 + gl0(10) = 40
        let vm_res = Vm::eval(&mut prog, FuncId(0), vec![]).expect("VM eval failed");
        assert_eq!(vm_res, Value::Int(40));

        // 2. Lower to LLVM IR and execute via `lli`
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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        assert_eq!(
            output.status.code(),
            Some(40),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
    }

    #[test]
    fn test_stage3_drop_elaboration_and_move_checking() {
        // `ty2` has a registered destructor `fn1(&mut ty2)` that increments `gl0` by the field value!
        // `ty3 = { ty2, ty2 }` is a pair of droppable `ty2`s.
        // In `fn0`:
        // - `_1: ty3` is initialized with `(10, 25)`
        // - `_1.0` is MOVED into `_2`, and `_2` is explicitly dropped (+10 to `gl0`)
        // - Then `_1` is dropped at the end of scope: because `_1.0` was already moved,
        //   Stage 3 Drop Elaboration must ONLY drop `_1.1` (+25 to `gl0`), resulting in `gl0 = 35`!
        let src = "\
ty0 = void;
ty1 = i64;
ty2 = { ty1 };
ty3 = { ty2, ty2 };
ty4 = &mut ty2;
ty5 = &mut ty1;

drop ty2 = fn1;

global mut gl0: ty1 = const 0;

fn0 = \"main\" {
    let _0: ty1;
    let _1: ty3;
    let _2: ty2;
    let _3: ty2;
    let _4: ty2;
    let _5: ty5;
    bb0: {
        StorageLive(_1);
        _3 = aggregate ty2(const 10);
        _4 = aggregate ty2(const 25);
        _1 = aggregate ty3(move _3, move _4);
        _2 = move _1.0;
        drop(_2) -> bb1;
    }
    bb1: {
        drop(_1) -> bb2;
    }
    bb2: {
        _5 = const gl0;
        _0 = copy (*_5);
        return;
    }
}

fn1(1) {
    let _0: ty0;
    let _1: ty4;
    let _2: ty5;
    let _3: ty1;
    let _4: ty1;
    bb0: {
        _2 = const gl0;
        _3 = copy (*_2);
        _4 = copy (*_1).0;
        (*_2) = add(copy _3, copy _4);
        _0 = const void;
        return;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse drop IR");
        assert_eq!(format!("{prog}"), src);

        // Elaborate drops (Stage 3 pass)
        elaborate_drops(&mut prog).expect("Drop elaboration failed");

        // Verify in VM
        let vm_res = Vm::eval(&mut prog, FuncId(0), vec![]).expect("VM eval failed");
        assert_eq!(vm_res, Value::Int(35));

        // Verify in LLVM via `lli`
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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        assert_eq!(
            output.status.code(),
            Some(35),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );

        // Verify use-after-move is rejected by `elaborate_drops`
        let bad_src = "\
ty0 = i64;
ty1 = { ty0 };

fn0 {
    let _0: ty1;
    let _1: ty1;
    let _2: ty1;
    bb0: {
        _1 = aggregate ty1(const 1);
        _2 = move _1;
        _0 = move _1;
        return;
    }
}
";
        let mut bad_prog = Parser::parse_program(bad_src).unwrap();
        let err = elaborate_drops(&mut bad_prog).unwrap_err();
        assert!(err.contains("Use of moved or uninitialized value '_1'"));
    }

    #[test]
    fn test_nll_borrow_checker() {
        // 1. Valid NLL & Disjoint Field Borrows:
        // - `_2 = &mut _1.0` and `_3 = &mut _1.1` are simultaneously live (disjoint fields -> OK!)
        // - After `_2` and `_3` are last used, `_1` is mutated directly (`_1.0 = const 100`) -> OK under NLL!
        let valid_src = "\
ty0 = i64;
ty1 = { ty0, ty0 };
ty2 = &mut ty0;

fn0 {
    let _0: ty0;
    let _1: ty1;
    let _2: ty2;
    let _3: ty2;
    bb0: {
        StorageLive(_1);
        _1 = aggregate ty1(const 10, const 20);
        _2 = &mut _1.0;
        _3 = &mut _1.1;
        (*_2) = const 30;
        (*_3) = const 40;
        _1.0 = const 50;
        _0 = add(copy _1.0, copy _1.1);
        StorageDead(_1);
        return;
    }
}
";
        let mut valid_prog = Parser::parse_program(valid_src).unwrap();
        elaborate_drops(&mut valid_prog).expect("Move check failed on valid program");
        check_borrows(&valid_prog).expect("Borrow check failed on valid NLL program");

        // 2. Reject conflicting mutable borrows (`&mut _1.0` while `&mut _1` is still live)
        let conflict_src = "\
ty0 = i64;
ty1 = { ty0, ty0 };
ty2 = &mut ty1;
ty3 = &mut ty0;

fn0 {
    let _0: ty0;
    let _1: ty1;
    let _2: ty2;
    let _3: ty3;
    bb0: {
        _1 = aggregate ty1(const 1, const 2);
        _2 = &mut _1;
        _3 = &mut _1.0;
        (*_2).1 = const 10;
        (*_3) = const 20;
        _0 = copy _1.0;
        return;
    }
}
";
        let conflict_prog = Parser::parse_program(conflict_src).unwrap();
        let err = check_borrows(&conflict_prog).unwrap_err();
        assert!(err.contains("cannot borrow '_1.0' as mutable because '_1' is already borrowed as mutable"));

        // 3. Reject mutation of `_1` while shared borrow `_2 = &_1` is still live
        let mutate_while_borrowed_src = "\
ty0 = i64;
ty1 = &ty0;

fn0 {
    let _0: ty0;
    let _1: ty0;
    let _2: ty1;
    bb0: {
        _1 = const 10;
        _2 = &_1;
        _1 = const 20;
        _0 = copy (*_2);
        return;
    }
}
";
        let mutate_prog = Parser::parse_program(mutate_while_borrowed_src).unwrap();
        let err = check_borrows(&mutate_prog).unwrap_err();
        assert!(err.contains("cannot mutate or move '_1' because it is currently borrowed"));

        // 4. Reject `StorageDead(_1)` while `_2 = &_1` is still live
        let dangling_storage_dead_src = "\
ty0 = i64;
ty1 = &ty0;

fn0 {
    let _0: ty0;
    let _1: ty0;
    let _2: ty1;
    bb0: {
        StorageLive(_1);
        _1 = const 10;
        _2 = &_1;
        StorageDead(_1);
        _0 = copy (*_2);
        return;
    }
}
";
        let dangling_prog = Parser::parse_program(dangling_storage_dead_src).unwrap();
        let err = check_borrows(&dangling_prog).unwrap_err();
        assert!(err.contains("goes out of scope (StorageDead) while still borrowed"));

        // 5. Reject returning a reference to a local stack variable (`_0 = &_1`)
        let return_local_ref_src = "\
ty0 = i64;
ty1 = &ty0;

fn0 {
    let _0: ty1;
    let _1: ty0;
    bb0: {
        _1 = const 42;
        _0 = &_1;
        return;
    }
}
";
        let return_local_prog = Parser::parse_program(return_local_ref_src).unwrap();
        let err = check_borrows(&return_local_prog).unwrap_err();
        assert!(err.contains("cannot return reference to local variable '_1'"));

        // 6. Reject mutating through an immutable reference (`(*_2) = const 99` where `_2: &ty0`)
        let immut_write_src = "\
ty0 = i64;
ty1 = &ty0;

fn0 {
    let _0: ty0;
    let _1: ty0;
    let _2: ty1;
    bb0: {
        _1 = const 10;
        _2 = &_1;
        (*_2) = const 99;
        _0 = copy _1;
        return;
    }
}
";
        let immut_prog = Parser::parse_program(immut_write_src).unwrap();
        let err = check_borrows(&immut_prog).unwrap_err();
        assert!(err.contains("through an immutable reference"));
    }

    #[test]
    fn test_interprocedural_borrow_inference_and_contracts() {
        // 1. Unannotated internal `foobar(a: &mut u8, b: &u8) -> &u8` (`fn1(2)`)
        //    `check_borrows` infers that `_0` only borrows from `_1` (`a`), NOT `_2` (`b`).
        //    Therefore, in `fn0`, `_2` (`y`) can be freed (`StorageDead(_2)`) immediately after the call
        //    even while `_5` (the returned reference) is still live and dereferenced later!
        let inferred_src = "\
ty0 = u8;
ty1 = &mut ty0;
ty2 = &ty0;

fn0 = \"main\" {
    let _0: ty0;
    let _1: ty0;
    let _2: ty0;
    let _3: ty1;
    let _4: ty2;
    let _5: ty2;
    bb0: {
        StorageLive(_1);
        _1 = const 10;
        StorageLive(_2);
        _2 = const 5;
        _3 = &mut _1;
        _4 = &_2;
        _5 = call const fn1(move _3, move _4) -> bb1;
    }
    bb1: {
        StorageDead(_2);
        _0 = copy (*_5);
        StorageDead(_1);
        return;
    }
}

fn1(2) {
    let _0: ty2;
    let _1: ty1;
    let _2: ty2;
    let _3: ty0;
    let _4: ty0;
    bb0: {
        _3 = copy (*_1);
        _4 = copy (*_2);
        (*_1) = add(copy _3, copy _4);
        _0 = &(*_1);
        return;
    }
}
";
        let mut inferred_prog = Parser::parse_program(inferred_src).unwrap();
        assert_eq!(format!("{inferred_prog}"), inferred_src);
        elaborate_drops(&mut inferred_prog).unwrap();
        check_borrows(&inferred_prog).expect("Inferred interprocedural borrow check should succeed");
        let vm_val = Vm::eval(&mut inferred_prog, FuncId(0), vec![]).unwrap();
        assert_eq!(vm_val, Value::Int(15));

        // 2. Explicitly annotated `fn1(2) borrows(_1)` round-trips and verifies when returning `&(*_1)`
        let explicit_ok_src = inferred_src.replace("fn1(2) {", "fn1(2) borrows(_1) {");
        let explicit_ok_prog = Parser::parse_program(&explicit_ok_src).unwrap();
        assert_eq!(format!("{explicit_ok_prog}"), explicit_ok_src);
        check_borrows(&explicit_ok_prog).expect("Explicit borrows(_1) contract should pass");

        // 3. Violating `fn1(2) borrows(_1)` by returning `_2` (`b`) instead of `_1` (`a`) is caught locally inside `fn1`!
        let explicit_bad_src = "\
ty0 = u8;
ty1 = &mut ty0;
ty2 = &ty0;

fn0(2) borrows(_1) {
    let _0: ty2;
    let _1: ty1;
    let _2: ty2;
    bb0: {
        _0 = copy _2;
        return;
    }
}
";
        let explicit_bad_prog = Parser::parse_program(explicit_bad_src).unwrap();
        assert_eq!(format!("{explicit_bad_prog}"), explicit_bad_src);
        let err = check_borrows(&explicit_bad_prog).unwrap_err();
        assert!(err.contains(
            "Borrow check error in fn0: return value borrows from parameter '_2', which is not permitted by explicit contract borrows(_1)"
        ));
    }

    #[test]
    fn test_comptime_array_union_and_overlay_type_constructors() {
        // - `fn0(2)` is `fn Array(comptime T: type, comptime len: u64) -> type`:
        //   constructs `[T; len]` and wraps it in a struct `{ [T; len] }`.
        // - `fn1(2)` is `fn Result(comptime T: type, comptime E: type) -> type`:
        //   constructs `union u8 { T, E }`.
        // - `fn2(2)` is `fn RawOverlay(comptime A: type, comptime B: type) -> type`:
        //   constructs `overlay { A, B }`.
        let src = "\
ty0 = type;
ty1 = u8;
ty2 = i32;
ty3 = u64;

fn0(2) {
    let _0: ty0;
    let _1: ty0;
    let _2: ty3;
    let _3: ty0;
    bb0: {
        _3 = [copy _1; copy _2];
        _0 = aggregate ty0(copy _3);
        return;
    }
}

fn1(2) {
    let _0: ty0;
    let _1: ty0;
    let _2: ty0;
    bb0: {
        _0 = union(const ty1, copy _1, copy _2);
        return;
    }
}

fn2(2) {
    let _0: ty0;
    let _1: ty0;
    let _2: ty0;
    bb0: {
        _0 = overlay(copy _1, copy _2);
        return;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse comptime type constructors");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate `Array(i32, 10)` (`fn0(ty2, 10)`)
        let arr_struct_val = Vm::eval(
            &mut prog,
            FuncId(0),
            vec![Value::Type(TypeId(2)), Value::Int(10)],
        )
        .expect("Comptime Array(i32, 10) failed");
        let Value::Type(arr_struct_ty_id) = arr_struct_val else {
            panic!("Expected Value::Type, got {arr_struct_val:?}");
        };
        assert_eq!(
            prog.types[4],
            Type::Array {
                elem: TypeId(2),
                len: 10
            }
        );
        assert_eq!(
            prog.types[arr_struct_ty_id.0 as usize],
            Type::Struct(vec![TypeId(4)])
        );

        // 2. Evaluate `Result(i32, u64)` (`fn1(ty2, ty3)`)
        let res_ty_val = Vm::eval(
            &mut prog,
            FuncId(1),
            vec![Value::Type(TypeId(2)), Value::Type(TypeId(3))],
        )
        .expect("Comptime Result(i32, u64) failed");
        let Value::Type(res_ty_id) = res_ty_val else {
            panic!("Expected Value::Type, got {res_ty_val:?}");
        };
        assert_eq!(
            prog.types[res_ty_id.0 as usize],
            Type::Union {
                tag: TypeId(1),
                variants: vec![TypeId(2), TypeId(3)]
            }
        );

        // 3. Evaluate `RawOverlay(i32, u64)` (`fn2(ty2, ty3)`)
        let overlay_ty_val = Vm::eval(
            &mut prog,
            FuncId(2),
            vec![Value::Type(TypeId(2)), Value::Type(TypeId(3))],
        )
        .expect("Comptime RawOverlay(i32, u64) failed");
        let Value::Type(overlay_ty_id) = overlay_ty_val else {
            panic!("Expected Value::Type, got {overlay_ty_val:?}");
        };
        assert_eq!(
            prog.types[overlay_ty_id.0 as usize],
            Type::Overlay(vec![TypeId(2), TypeId(3)])
        );
    }

    #[test]
    fn test_integer_overflow_checked_wrapping_saturating_unchecked() {
        let src = "\
ty0 = u8;
ty1 = i8;

fn0 = \"main\" {
    let _0: ty0;
    let _1: ty0;
    let _2: ty0;
    let _3: ty0;
    let _4: ty1;
    let _5: ty1;
    bb0: {
        _1 = const 250;
        _2 = add_wrap(copy _1, const 10);
        _3 = add_sat(copy _1, const 10);
        _4 = const 100;
        _5 = mul_sat(copy _4, const 2);
        _0 = add_unchecked(copy _2, const 30);
        return;
    }
}

fn1(1) {
    let _0: ty0;
    let _1: ty0;
    bb0: {
        _0 = add(copy _1, const 10);
        return;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse overflow ops IR");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate `fn0` in VM:
        // _2 = 250 +% 10 = 4 (u8)
        // _3 = 250 +| 10 = 255 (u8)
        // _5 = 100 *| 2 = 127 (i8)
        // _0 = 4 + 30 = 34
        let vm_res = Vm::eval(&mut prog, FuncId(0), vec![]).expect("VM eval of fn0 failed");
        assert_eq!(vm_res, Value::Int(34));

        // 2. Evaluate `fn1(250)` in VM: checked `add(250u8, 10)` must report overflow!
        let ovf_err = Vm::eval(&mut prog, FuncId(1), vec![Value::Int(250)])
            .expect_err("Expected u8 overflow error in checked add");
        assert!(ovf_err.contains("Integer overflow"));

        // 3. Lower to LLVM IR and verify intrinsics & `lli` execution
        let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
        assert!(llvm_ir.contains("@llvm.uadd.with.overflow.i8"));
        assert!(llvm_ir.contains("@llvm.uadd.sat.i8"));
        assert!(llvm_ir.contains("@llvm.smul.with.overflow.i8"));
        assert!(llvm_ir.contains("add nuw i8"));

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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        assert_eq!(
            output.status.code(),
            Some(34),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
    }

    #[test]
    fn test_scalar_pattern_types_comptime_and_llvm_range_metadata() {
        // - `ty1 = ty0 in 0..=100;` (`Percent`)
        // - `ty3 = ty2 in 0..=55295 | 57344..=1114111;` (`rune`-like multi-range pattern)
        // - `fn0(2)` is `fn Index(comptime Int: type, comptime len: u64) -> type`:
        //   constructs `Int in 0..=(len - 1)` at comptime!
        // - `fn1` loads a `Percent` value and returns it (emitting LLVM `!range !0` metadata).
        let src = "\
ty0 = u8;
ty1 = ty0 in 0..=100;
ty2 = u32;
ty3 = ty2 in 0..=55295 | 57344..=1114111;
ty4 = type;
ty5 = u64;

fn0(2) {
    let _0: ty4;
    let _1: ty4;
    let _2: ty5;
    let _3: ty5;
    bb0: {
        _3 = sub(copy _2, const 1);
        _0 = copy _1 in const 0..=copy _3;
        return;
    }
}

fn1 = \"main\" {
    let _0: ty0;
    let _1: ty1;
    bb0: {
        _1 = const 85;
        _0 = cast(copy _1, ty0);
        return;
    }
}

fn2(1) {
    let _0: ty1;
    let _1: ty0;
    bb0: {
        _0 = cast(copy _1, ty1);
        return;
    }
}
";
        let mut prog = Parser::parse_program(src).expect("Failed to parse pattern types IR");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate comptime `Index(u64, 64)` (`fn0(ty5, 64)`) -> `ty5 in 0..=63`
        let idx_ty_val = Vm::eval(
            &mut prog,
            FuncId(0),
            vec![Value::Type(TypeId(5)), Value::Int(64)],
        )
        .expect("Comptime Index(u64, 64) failed");
        let Value::Type(idx_ty_id) = idx_ty_val else {
            panic!("Expected Value::Type, got {idx_ty_val:?}");
        };
        assert_eq!(
            prog.types[idx_ty_id.0 as usize],
            Type::Pattern {
                base: TypeId(5),
                ranges: vec![(0, 63)],
            }
        );

        // 2. Evaluate `fn1` in VM -> 85 (within `0..=100`)
        let main_val = Vm::eval(&mut prog, FuncId(1), vec![]).expect("VM eval of fn1 failed");
        assert_eq!(main_val, Value::Int(85));

        // 3. Evaluate `fn2(150)` in VM -> must reject 150 as outside `0..=100`!
        let bad_err = Vm::eval(&mut prog, FuncId(2), vec![Value::Int(150)])
            .expect_err("Expected out-of-range error when casting 150 to ty0 in 0..=100");
        assert!(bad_err.contains("outside valid pattern ranges"));

        // 4. Lower to LLVM IR, verify `!range !0` metadata, and execute via `lli`
        let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
        assert!(llvm_ir.contains("!range !0"));
        assert!(llvm_ir.contains("!0 = !{i8 0, i8 101}"));

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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        assert_eq!(
            output.status.code(),
            Some(85),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
    }

    #[test]
    fn test_arbitrary_width_integers_and_simd_vectors() {
        use std::io::Write;
        use std::process::{Command, Stdio};

        let src = "\
ty0 = i24;
ty1 = u48;
ty2 = u256;
ty3 = u512;
ty4 = i32;
ty5 = simd[ty4; 4];
ty6 = type;
ty7 = u64;

fn0(2) {
    let _0: ty6;
    let _1: ty6;
    let _2: ty7;
    bb0: {
        _0 = simd[copy _1; copy _2];
        return;
    }
}

fn1 = \"main\" {
    let _0: ty4;
    let _1: ty0;
    let _2: ty0;
    let _3: ty1;
    let _4: ty2;
    let _5: ty3;
    let _6: ty5;
    let _7: ty5;
    let _8: ty5;
    let _9: ty4;
    let _10: ty7;
    let _11: ty4;
    let _12: ty3;
    let _13: ty3;
    let _14: ty4;
    bb0: {
        _1 = const 8388600;
        _2 = add_sat(copy _1, const 100);
        _3 = cast(copy _2, ty1);
        _4 = cast(copy _3, ty2);
        _12 = cast(copy _4, ty3);
        _5 = add_wrap(copy _12, const 3);
        _9 = const 10;
        _6 = aggregate ty5(copy _9);
        _7 = aggregate ty5(const 1, const 2, const 3, const 4);
        _8 = add(copy _6, copy _7);
        _10 = const 2;
        _11 = copy _8[_10];
        _13 = sub_wrap(copy _5, copy _12);
        _14 = cast(copy _13, ty4);
        _0 = add(copy _11, copy _14);
        return;
    }
}

fn2(1) {
    let _0: ty0;
    let _1: ty0;
    bb0: {
        _0 = add(copy _1, const 1);
        return;
    }
}
";
        let mut prog =
            Parser::parse_program(src).expect("Failed to parse arbitrary-width & SIMD IR");
        assert_eq!(format!("{prog}"), src);

        // 1. Evaluate comptime `fn0(i32, 4)` -> `simd[i32; 4]` (`ty5`)
        let simd_ty_val = Vm::eval(
            &mut prog,
            FuncId(0),
            vec![Value::Type(TypeId(4)), Value::Int(4)],
        )
        .expect("Comptime simd[T; N] constructor failed");
        assert_eq!(simd_ty_val, Value::Type(TypeId(5)));

        // 2. Evaluate `fn1` in VM:
        //    - `_2` = saturating i24 `8388600 + 100` -> `8388607` (`i24::MAX`)
        //    - `_5` = `8388607 + 3` in `u512`
        //    - `_6` = splat `simd[i32; 4](10)` -> `<10, 10, 10, 10>`
        //    - `_7` = `<1, 2, 3, 4>`
        //    - `_8` = `_6 + _7` -> `<11, 12, 13, 14>`
        //    - `_11` = `_8[2]` -> `13`
        //    - `_0` = `13 + 3` -> `16`
        let main_val = Vm::eval(&mut prog, FuncId(1), vec![]).expect("VM eval of fn1 failed");
        assert_eq!(main_val, Value::Int(16));

        // 3. Evaluate `fn2(8388607)` (`i24::MAX + 1`) -> must trap on signed 24-bit overflow!
        let ovf_err = Vm::eval(&mut prog, FuncId(2), vec![Value::Int(8_388_607)])
            .expect_err("Expected i24 overflow trap on 8388607 + 1");
        assert!(ovf_err.contains("Integer overflow"));

        // 4. Lower to LLVM IR and execute via `lli`
        let llvm_ir = LlvmLowering::lower(&prog).expect("LLVM lowering failed");
        assert!(llvm_ir.contains("i24"));
        assert!(llvm_ir.contains("i48"));
        assert!(llvm_ir.contains("i256"));
        assert!(llvm_ir.contains("i512"));
        assert!(llvm_ir.contains("<4 x i32>"));
        assert!(llvm_ir.contains("@llvm.sadd.sat.i24"));
        assert!(llvm_ir.contains("@llvm.sadd.with.overflow.v4i32"));

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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        assert_eq!(
            output.status.code(),
            Some(16),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
    }

    #[test]
    fn test_end_to_end_surface_language_comptime_structs_and_llvm() {
        let geom_mod = "\
pub record Point {
    x: i32,
    y: i32 = 10,

    pub fn sum(self: &Self) -> i32 {
        return self.x + self.y;
    }
}

pub fn Pair(comptime T: type) -> type {
    return record {
        first: T,
        second: T,
    };
}
";

        let root_mod = "\
import root::geom::{Point, Pair};

type Percent = i32 in 0..=100;

struct Counter {
    val: i32,

    fn secret_bonus(self: &Self) -> i32 {
        return 5;
    }

    pub fn new(start: i32) -> Self {
        return Self { val: start };
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.val += delta + self.secret_bonus();
    }

    pub fn get(self: &Self) -> &i32 {
        return &self.val;
    }

    default() -> Self {
        return Self { val: 2 };
    }

    clone(self: &Self) -> Self {
        return Self { val: self.val };
    }

    drop(self: &mut Self) {
        self.val = 0;
    }
}

fn maybe_val(flag: bool) -> ?i32 {
    if flag {
        return 7;
    } else {
        return null;
    }
}

pub fn main() -> i32 {
    let p = Point { x: 15 };
    let pair = Pair(i32) { first: p.sum(), second: 5 };
    let mut c = @default(Counter);
    c.add(pair.first + pair.second);
    let c2 = @clone(c);
    let r: &i32 = c2.get();
    let v_opt: ?i32 = maybe_val(true);
    let v_unwrapped: i32 = v_opt orelse 0;
    let pct: Percent = 10;
    let vec = simd[i32; 4] { 1, 2, 3, 4 };
    let idx: usize = 3;
    return (*r) + v_unwrapped + (pct as i32) + vec[idx];
}
";

        let prog = Compiler::compile_package(&[("root::geom", geom_mod), ("root", root_mod)])
            .expect("Failed to compile multi-module surface package");

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
        let output = child.wait_with_output().expect("Failed to wait on lli");
        // Expected:
        // p.sum() = 15 + 10 = 25
        // pair.first + pair.second = 25 + 5 = 30
        // c starts at 2 (`@default(Counter)`), `c.add(30)` adds `30 + 5` = 37
        // c2 = `@clone(c)` -> 37
        // v_unwrapped = 7
        // pct = 10
        // vec[3] = 4
        // total = 37 + 7 + 10 + 4 = 58
        assert_eq!(
            output.status.code(),
            Some(58),
            "lli stderr: {}\nLLVM IR:\n{}",
            String::from_utf8_lossy(&output.stderr),
            llvm_ir
        );
    }

    #[test]
    fn test_struct_block_privacy_and_module_visibility() {
        // 1. Accessing a private struct field from a free function in the SAME file must be rejected!
        let bad_field_src = "\
struct Secret {
    hidden: i32,

    pub fn new(v: i32) -> Self {
        return Self { hidden: v };
    }
}

pub fn main() -> i32 {
    let s = Secret::new(42);
    return s.hidden;
}
";
        let err = Compiler::compile_source(bad_field_src)
            .expect_err("Expected private struct field access outside struct block to fail");
        assert!(
            err.contains("Cannot access private field 'hidden' of struct 'Secret' outside its 'struct { ... }' block"),
            "Unexpected error: {err}"
        );

        // 2. Constructing a struct with private fields outside its `struct { ... }` block must be rejected!
        let bad_lit_src = "\
struct Secret {
    hidden: i32,
}

pub fn main() -> i32 {
    let s = Secret { hidden: 10 };
    return 0;
}
";
        let err = Compiler::compile_source(bad_lit_src)
            .expect_err("Expected struct literal with private field outside struct block to fail");
        assert!(
            err.contains("Cannot construct struct 'Secret' with private field 'hidden' outside its 'struct { ... }' block"),
            "Unexpected error: {err}"
        );

        // 3. Calling a private struct method outside its `struct { ... }` block must be rejected!
        let bad_method_src = "\
struct Secret {
    hidden: i32,

    pub fn new(v: i32) -> Self {
        return Self { hidden: v };
    }

    fn internal_only(self: &Self) -> i32 {
        return self.hidden;
    }
}

pub fn main() -> i32 {
    let s = Secret::new(42);
    return s.internal_only();
}
";
        let err = Compiler::compile_source(bad_method_src)
            .expect_err("Expected private struct method call outside struct block to fail");
        assert!(
            err.contains("Cannot call private method 'internal_only' of struct 'Secret' outside its 'struct { ... }' block"),
            "Unexpected error: {err}"
        );

        // 4. Cross-module private item access must be rejected!
        let mod_a = "\
fn helper() -> i32 {
    return 1;
}
";
        let mod_b = "\
import root::a;

pub fn main() -> i32 {
    return a::helper();
}
";
        let err = Compiler::compile_package(&[("root::a", mod_a), ("root", mod_b)])
            .expect_err("Expected cross-module private function call to fail");
        assert!(
            err.contains("Item 'helper' in module 'root::a' is private"),
            "Unexpected error: {err}"
        );

        // 5. Out-of-range compile-time constant assigned to a Pattern type must be rejected!
        let bad_pattern_src = "\
type Percent = u8 in 0..=100;

pub fn main() -> i32 {
    let p: Percent = 150;
    return p as i32;
}
";
        let err = Compiler::compile_source(bad_pattern_src)
            .expect_err("Expected out-of-range pattern constant to fail");
        assert!(
            err.contains("outside valid pattern ranges"),
            "Unexpected error: {err}"
        );
    }

    #[test]
    fn test_extension_methods_comptime_receivers_and_coherence() {
        use crate::lower::Compiler;
        use std::io::Write;
        use std::process::{Command, Stdio};

        let types_mod = "\
pub type Point = record {
    x: i32,
    y: i32,

    pub fn sum(self: &Self) -> i32 {
        return self.x + self.y;
    }
};

pub fn Pair(comptime T: type) -> type {
    return record {
        first: T,
        second: T,
    };
}
";

        let simd_ext_mod = "\
import root::types::Pair;

// Extension on built-in comptime-parameterized `simd[T; N]`
pub fn first_lane(comptime T: type, comptime N: usize, self: &simd[T; N]) -> T {
    return self[0];
}

// Extension on user-defined comptime-parameterized `Pair(T)`
pub fn dot(comptime T: type, self: &Pair(T), other: &Pair(T)) -> T {
    return self.first * other.first + self.second * other.second;
}

// Parameterized specificity (score = 2) vs concrete specificity (score = 3)
pub fn tag_rank(comptime T: type, self: &Pair(T)) -> i32 {
    return 10;
}
";

        let root_mod = "\
import root::types::{Point, Pair};
import root::simd_ext::{first_lane, dot, tag_rank};

// Localconcrete extension on `Point`
fn scale_x(self: &mut Point, factor: i32) {
    self.x *= factor;
}

// Concrete extension on `Pair(i32)` (specificity 3 > parameterized `tag_rank(comptime T, &Pair(T))` specificity 2)
fn tag_rank(self: &Pair(i32)) -> i32 {
    return 25;
}

// Shadowing test: inherent `Point::sum` must win over extension `sum(self: &Point)`
fn sum(self: &Point) -> i32 {
    return 999;
}

pub fn main() -> i32 {
    let mut pt = Point { x: 3, y: 4 };
    pt.scale_x(2);               // pt.x = 6, pt.y = 4
    let s = pt.sum();            // Inherent method wins: 6 + 4 = 10 (NOT 999)

    let v: simd[i32; 4] = simd[i32; 4]{ 7, 8, 9, 10 };
    let f = v.first_lane();      // Infers T = i32, N = 4 -> 7

    let p1 = Pair(i32){ first: 2, second: 3 };
    let p2 = Pair(i32){ first: 4, second: 5 };
    let d = p1.dot(&p2);         // Infers T = i32 -> 2*4 + 3*5 = 23
    let r = p1.tag_rank();       // Concrete `Pair(i32)` wins over `Pair(T)` -> 25

    // Also callable via normal function syntax with inferred comptime args:
    let f2 = first_lane(&v);     // 7

    // Total: 10 + 7 + 23 + 25 + 7 = 72
    return s + f + d + r + f2;
}
";

        let program = Compiler::compile_package(&[
            ("root::types", types_mod),
            ("root::simd_ext", simd_ext_mod),
            ("root", root_mod),
        ])
        .expect("Failed to compile package with extension methods");

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
            Some(72),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // Verify that ambiguous imported extension methods produce a compile-time error:
        let ext_a = "\
import root::types::Point;
pub fn metric(self: &Point) -> i32 { return self.x; }
";
        let ext_b = "\
import root::types::Point;
pub fn metric(self: &Point) -> i32 { return self.y; }
";
        let ambig_root = "\
import root::types::Point;
import root::ext_a::*;
import root::ext_b::*;

pub fn main() -> i32 {
    let p = Point { x: 1, y: 2 };
    return p.metric();
}
";
        let err = Compiler::compile_package(&[
            ("root::types", types_mod),
            ("root::ext_a", ext_a),
            ("root::ext_b", ext_b),
            ("root", ambig_root),
        ])
        .expect_err("Expected ambiguous extension method call to be rejected");
        assert!(
            err.contains("Ambiguous extension method 'metric'"),
            "Unexpected error: {err}"
        );
    }

    #[test]
    fn test_numeric_metatype_hierarchy_number_integer_signed_unsigned_float() {
        use crate::lower::Compiler;
        use std::io::Write;
        use std::process::{Command, Stdio};

        let num_mod = "\
// 1. `number` matches both `integer` and `float`
pub fn clamp(comptime N: number, self: N, lo: N, hi: N) -> N {
    if self < lo {
        return lo;
    }
    if self > hi {
        return hi;
    }
    return self;
}

// 2. Disjoint overloads on `signed` vs `float` sharing the name `abs`
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

// 3. `integer` matches both `signed` (`i32`) and arbitrary-width `unsigned` (`u24`)
pub fn low_nibble(comptime I: integer, self: I) -> I {
    return self & 15;
}

// 4. Full hierarchy specificity ladder: `unsigned` (4) > `integer` (3) > `number` (2) > `type` (1)
pub fn tier_rank(comptime T: type, self: T) -> i32 {
    return 1;
}

pub fn tier_rank(comptime N: number, self: N) -> i32 {
    return 2;
}

pub fn tier_rank(comptime I: integer, self: I) -> i32 {
    return 3;
}

pub fn tier_rank(comptime U: unsigned, self: U) -> i32 {
    return 4;
}
";

        let root_mod = "\
import root::num::*;

type Dummy = record {
    v: i32,
};

pub fn main() -> i32 {
    let x: i32 = -12;
    let a = x.abs();                     // `signed` overload -> 12
    let clamped_i32 = a.clamp(0, 10);    // `number` on i32 -> 10

    let f: f64 = -4.0;
    let af = f.abs();                    // `float` overload -> 4.0
    let cf = af.clamp(0.0, 3.0);         // `number` on f64 -> 3.0
    let cf_int = cf as i32;              // 3

    let raw_u24: u24 = 31;               // 0x1F -> low_nibble = 15
    let nib = (raw_u24.low_nibble()) as i32;

    // Specificity ladder verification:
    let d = Dummy { v: 0 };
    let r_type = d.tier_rank();          // `type` -> 1
    let r_num = f.tier_rank();           // `float` matches `number` (2) > `type` (1) -> 2
    let r_int = x.tier_rank();           // `signed` matches `integer` (3) > `number` (2) -> 3
    let r_uns = raw_u24.tier_rank();     // `unsigned` matches `unsigned` (4) > `integer` (3) -> 4
    let ladder = r_type * 10 + r_num * 10 + r_int + r_uns; // 10 + 20 + 3 + 4 = 37

    // Total: 10 + 3 + 15 + 37 = 65
    return clamped_i32 + cf_int + nib + ladder;
}
";

        let program = Compiler::compile_package(&[("root::num", num_mod), ("root", root_mod)])
            .expect("Failed to compile numeric meta-type hierarchy package");

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
            Some(65),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // Verify that calling `abs` on `unsigned` (`u32`) is rejected because `abs` is only defined for `signed` and `float`:
        let bad_unsigned_abs = "\
import root::num::*;

pub fn main() -> i32 {
    let u: u32 = 5;
    return (u.abs()) as i32;
}
";
        let err = Compiler::compile_package(&[("root::num", num_mod), ("root", bad_unsigned_abs)])
            .expect_err("Expected `u.abs()` on unsigned u32 to be rejected");
        assert!(
            err.contains("Type 'u32' has no method 'abs'"),
            "Unexpected error: {err}"
        );

        // Verify that passing a non-number (`Dummy`) to `clamp(comptime N: number, ...)` is rejected at the signature boundary:
        let bad_explicit_clamp = "\
import root::num::clamp;

type Dummy = record {
    v: i32,
};

pub fn main() -> i32 {
    let d = Dummy { v: 1 };
    let res = clamp(Dummy, d, d, d);
    return res.v;
}
";
        let err =
            Compiler::compile_package(&[("root::num", num_mod), ("root", bad_explicit_clamp)])
                .expect_err("Expected `clamp(Dummy, ...)` to fail `number` constraint");
        assert!(
            err.contains("Type 'Dummy' does not satisfy comptime constraint 'number'"),
            "Unexpected error: {err}"
        );
    }

    #[test]
    fn test_composite_and_discriminated_metatype_hierarchy() {
        let meta_mod = "\
// 1. Disjoint overloads on open `aggregate` (`record` | `tuple`) vs encapsulated `struct`:
pub fn open_score(comptime A: aggregate, self: &A) -> i32 {
    return 10;
}

pub fn open_score(comptime S: struct, self: &S) -> i32 {
    return 1;
}

// 2. Specificity ranking across `scalar`, `number`, and `aggregate`:
//    - `number` (rank 3) overrides `scalar` (rank 2), while `bool` and `rune` match `scalar` (rank 2)
//    - `record` (rank 3) and `tuple` (rank 3) override `aggregate` (rank 2)
pub fn kind_code(comptime T: type, self: &T) -> i32 {
    return 0;
}

pub fn kind_code(comptime Sc: scalar, self: &Sc) -> i32 {
    return 11;
}

pub fn kind_code(comptime N: number, self: &N) -> i32 {
    return 12;
}

pub fn kind_code(comptime F: fn, self: &F) -> i32 {
    return 13;
}

pub fn kind_code(comptime Cal: callable, self: &Cal) -> i32 {
    return 14;
}

pub fn kind_code(comptime Cl: closure, self: &Cl) -> i32 {
    return 15;
}

pub fn kind_code(comptime A: aggregate, self: &A) -> i32 {
    return 20;
}

pub fn kind_code(comptime R: record, self: &R) -> i32 {
    return 21;
}

pub fn kind_code(comptime Tp: tuple, self: &Tp) -> i32 {
    return 22;
}

pub fn kind_code(comptime V: simd, self: &V) -> i32 {
    return 23;
}

pub fn kind_code(comptime Arr: array, self: &Arr) -> i32 {
    return 24;
}

// 3. `discriminated` (`enum` | `union`) hierarchy & specificity:
pub fn tag_kind(comptime D: discriminated, self: &D) -> i32 {
    return 30;
}

pub fn tag_kind(comptime E: enum, self: &E) -> i32 {
    return 31;
}

pub fn tag_kind(comptime U: union, self: &U) -> i32 {
    return 32;
}

// Function that strictly requires an open `aggregate` (`record` or `tuple`):
pub fn require_open(comptime A: aggregate, val: &A) -> i32 {
    return 5;
}
";

        let root_mod = "\
import root::meta::*;

pub record Point {
    x: i32,
    y: i32,
}

pub struct Vault {
    secret: i32,

    pub fn new(v: i32) -> Self {
        return Self { secret: v };
    }
}

pub enum Color {
    Red = 1,
    Green = 2,
    Blue = 3,
}

pub fn double_it(x: i32) -> i32 {
    return x * 2;
}

pub fn main() -> i32 {
    let p = Point { x: 3, y: 4 };
    let tup: tuple { i32, i32 } = { 7, 8 };
    let v = Vault::new(99);
    let c: Color = Color::Green;
    let opt: ?i32 = 42;

    // `open_score`: Point (`record`) -> 10, tup (`tuple`) -> 10, Vault (`struct`) -> 1 (sum = 21)
    let s1 = p.open_score() + tup.open_score() + v.open_score();

    // `kind_code`: Point (`record` rank 3) -> 21, tup (`tuple` rank 3) -> 22, Vault (`type` rank 1) -> 0 (sum = 43)
    let s2 = p.kind_code() + tup.kind_code() + v.kind_code();

    // `scalar` vs `number` vs `fn` vs `discriminated`:
    //   flag (`bool` -> `scalar` rank 2) -> 11
    //   ch (`rune` -> `scalar` rank 2) -> 11
    //   n (`i32` -> `number` rank 3 > `scalar` rank 2) -> 12
    //   fp (`fn(i32) -> i32` -> `fn` rank 3 > `scalar` rank 2) -> 13, plus calling `fp(3)` -> 6
    //   c (`Color` `enum` is `discriminated`, NOT `scalar` -> `type` rank 1) -> 0
    //   (sum = 11 + 11 + 12 + 13 + 6 + 0 = 53)
    let flag: bool = true;
    let ch: rune = 'A';
    let n: i32 = 42;
    let fp: fn(i32) -> i32 = double_it;
    let s_scalar = flag.kind_code() + ch.kind_code() + n.kind_code() + fp.kind_code() + fp(3) + c.kind_code();

    // `simd` (rank 3 -> 23) and `array` (rank 3 -> 24):
    let vec4 = simd[i32; 4] { 1, 2, 3, 4 };
    let arr2: [i32; 2] = @default([i32; 2]);
    let s_seq = vec4.kind_code() + arr2.kind_code();

    // `tag_kind`: Color (`enum` rank 3) -> 31, ?i32 (`union` rank 3) -> 32 (sum = 63)
    let s3 = c.tag_kind() + opt.tag_kind();

    // `require_open` works on both `record` and `tuple` (5 + 5 = 10)
    let s4 = require_open(Point, &p) + require_open(tuple { i32, i32 }, &tup);

    // Total = 21 + 43 + 53 + 47 + 63 + 10 = 237
    return s1 + s2 + s_scalar + s_seq + s3 + s4;
}
";

        let program = Compiler::compile_package(&[("root::meta", meta_mod), ("root", root_mod)])
            .expect("Failed to compile composite & discriminated meta-type hierarchy package");

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
            Some(237),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // Verify that passing an encapsulated `struct` (`Vault`) to `require_open(comptime A: aggregate, ...)` is rejected!
        let bad_struct_as_aggregate = "\
import root::meta::require_open;

pub struct Vault {
    secret: i32,
    pub fn new(v: i32) -> Self {
        return Self { secret: v };
    }
}

pub fn main() -> i32 {
    let v = Vault::new(10);
    return require_open(Vault, &v);
}
";
        let err = Compiler::compile_package(&[
            ("root::meta", meta_mod),
            ("root", bad_struct_as_aggregate),
        ])
        .expect_err("Expected `require_open(Vault, &v)` to fail `aggregate` constraint");
        assert!(
            err.contains("Type 'Vault' does not satisfy comptime constraint 'aggregate'"),
            "Unexpected error: {err}"
        );
    }

    #[test]
    fn test_never_type_diverging_calls_and_orelse_return() {
        let src = "\
// 1. A diverging helper returning `never` via `@trap()`:
pub fn fatal_abort() -> never {
    @trap();
}

// 2. Non-void function ending in a call to a `-> never` function on one branch
//    without needing a dummy `return` afterward:
pub fn checked_positive(x: i32) -> i32 {
    if x > 0 {
        return x;
    }
    fatal_abort();
}

// 3. `orelse return <expr>` and `orelse fatal_abort()` where `never` coerces to `i32`:
pub fn add_optionals(a: ?i32, b: ?i32) -> i32 {
    let x: i32 = a orelse return 10;
    let y: i32 = b orelse return 20;
    return x + y;
}

pub fn unwrap_or_abort(a: ?i32) -> i32 {
    let v: i32 = a orelse fatal_abort();
    return v * 2;
}

pub fn main() -> i32 {
    let some5: ?i32 = 5;
    let some8: ?i32 = 8;
    let none_val: ?i32 = null;

    // 5 + 8 = 13
    let r1 = add_optionals(some5, some8);
    // `a` is null -> early returns 10 via `orelse return 10`
    let r2 = add_optionals(none_val, some8);
    // `b` is null -> early returns 20 via `orelse return 20`
    let r3 = add_optionals(some5, none_val);
    // `unwrap_or_abort(some5)` -> 10
    let r4 = unwrap_or_abort(some5);
    // `checked_positive(7)` -> 7
    let r5 = checked_positive(7);

    // 13 + 10 + 20 + 10 + 7 = 60
    return r1 + r2 + r3 + r4 + r5;
}
";

        let program = Compiler::compile_source(src).expect("Failed to compile `never` type test");
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
            Some(60),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // Verify that a function declared `-> never` that falls off the end is rejected at compile time:
        let bad_never_fn = "\
pub fn does_not_diverge() -> never {
    let x: i32 = 1;
}
";
        let err = Compiler::compile_source(bad_never_fn)
            .expect_err("Expected `-> never` function that falls through to be rejected");
        assert!(
            err.contains("declared '-> never' reaches end of function without diverging"),
            "Unexpected error: {err}"
        );
    }

    #[test]
    fn test_lambdas_automatic_capture_closures_and_nll_borrows() {
        let src = "\
// 1. Disjoint overloads on `callable` (rank 2) vs `fn` (rank 3) and `closure` (rank 3):
pub fn callable_tag(comptime F: callable, self: &F) -> i32 {
    return 10;
}

pub fn callable_tag(comptime F: fn, self: &F) -> i32 {
    return 11;
}

pub fn invoke_callable(comptime F: callable, f: &mut F, x: i32) -> i32 {
    return f(x);
}

pub fn invoke_fn_only(comptime F: fn, f: F, x: i32) -> i32 {
    return f(x);
}

pub fn invoke_closure_only(comptime C: closure, c: &mut C, x: i32) -> i32 {
    return c(x);
}

// 2. Resource struct with a `drop` hook to verify `move fn` automatic drop elaboration:
pub struct ScopedAdd {
    target: &mut i32,
    delta: i32,

    pub fn new(t: &mut i32, d: i32) -> Self {
        return Self { target: t, delta: d };
    }

    pub fn bonus(self: &Self) -> i32 {
        return self.delta;
    }

    drop(self: &mut Self) {
        *self.target += self.delta;
    }
}

pub fn main() -> i32 {
    // A. Non-capturing lambda (`fn(i32) -> i32`) decays to bare function pointer (`fn` rank 3 > `callable` rank 2):
    let mut pure_lambda = fn(x: i32) -> i32 {
        return x * 3;
    };
    // `pure_lambda.callable_tag()` selects `fn` (rank 3) -> 11
    // `invoke_fn_only(pure_lambda, 4)` -> 12
    // `invoke_callable(&mut pure_lambda, 2)` -> 6
    let r_pure = pure_lambda.callable_tag()
        + invoke_fn_only(pure_lambda, 4)
        + invoke_callable(&mut pure_lambda, 2);

    // B. Automatic shared capture (`&factor`):
    let factor: i32 = 5;
    let mut scale = fn(x: i32) -> i32 {
        return x * factor;
    };
    // While `scale` holds a shared borrow `&factor`, reading `factor` in the outer scope is allowed!
    // `scale.callable_tag()` selects `callable` (rank 2, since `fn` rank 3 does not match `closure`) -> 10
    let r_shared = scale(3) + factor + scale.callable_tag() + invoke_callable(&mut scale, 2);

    // C. Automatic mutable capture (`&mut acc`) + NLL borrow release after last closure call:
    let mut acc: i32 = 10;
    let mut add_to_acc = fn(x: i32) -> i32 {
        acc += x;
        return acc;
    };
    let step1 = add_to_acc(7); // acc = 17
    let step2 = invoke_closure_only(&mut add_to_acc, 3); // acc = 20
    // After the last call to `add_to_acc`, NLL releases `&mut acc` so `acc` can be read & mutated directly:
    acc += 5; // acc = 25
    let r_mut = step1 + step2 + acc; // 17 + 20 + 25 = 62

    // D. `move fn` capturing an owned `ScopedAdd` struct with a `drop` hook:
    let mut drop_log: i32 = 0;
    let mut r_move: i32 = 0;
    if true {
        let guard = ScopedAdd::new(&mut drop_log, 19);
        let moved_closure = move fn(x: i32) -> i32 {
            return x + guard.bonus();
        };
        r_move = moved_closure(1); // 1 + 19 = 20
        // `moved_closure` goes out of scope here, running `ScopedAdd::drop` and adding 19 to `drop_log`!
    }

    // Total:
    //   r_pure   = 11 + 12 + 6 = 29
    //   r_shared = 15 + 5 + 10 + 10 = 40
    //   r_mut    = 17 + 20 + 25 = 62
    //   r_move   = 20
    //   drop_log = 19
    //   Sum = 29 + 40 + 62 + 20 + 19 = 170
    return r_pure + r_shared + r_mut + r_move + drop_log;
}
";

        let program = Compiler::compile_source(src)
            .expect("Failed to compile lambdas & automatic-capture closures test");
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
            Some(170),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // Verify that reading a mutably-captured variable BEFORE the last call to the closure is rejected by Stage 3 NLL borrow checking:
        let bad_conflict_src = "\
pub fn main() -> i32 {
    let mut total: i32 = 10;
    let bump = fn(x: i32) -> i32 {
        total += x;
        return total;
    };
    let illegal_read: i32 = total;
    let after = bump(5);
    return illegal_read + after;
}
";
        let err = Compiler::compile_source(bad_conflict_src).expect_err(
            "Expected reading `total` while mutably captured by live closure `bump` to fail borrow check",
        );
        assert!(
            err.contains("Borrow check error") && err.contains("mutably borrowed"),
            "Unexpected error: {err}"
        );

        // Verify that passing a stateful capturing `closure` to a function constrained by `comptime F: fn` is rejected:
        let bad_closure_as_fn = "\
pub fn require_stateless_fn(comptime F: fn, f: F) -> i32 {
    return f(1);
}

pub fn main() -> i32 {
    let k: i32 = 10;
    let cap = fn(x: i32) -> i32 {
        return x + k;
    };
    return require_stateless_fn(cap);
}
";
        let err2 = Compiler::compile_source(bad_closure_as_fn)
            .expect_err("Expected passing capturing closure to `comptime F: fn` to fail");
        assert!(
            err2.contains("No overload of 'require_stateless_fn'"),
            "Unexpected error: {err2}"
        );
    }

    #[test]
    fn test_slices_range_slicing_sequence_metatype_and_nll_borrows() {
        let src = "\
// 1. Generic function over `sequence` (`array` | `slice`) using `.len` and `s[i]`:
pub fn sum_seq(comptime S: sequence, s: &S) -> i32 {
    let mut i: usize = 0;
    let mut total: i32 = 0;
    while i < s.len {
        total += s[i];
        i += 1;
    }
    return total;
}

// 2. Specificity ranking between `sequence` (rank 2) and `slice` (rank 3):
pub fn seq_tag(comptime S: sequence, self: &S) -> i32 {
    return 20;
}

pub fn seq_tag(comptime S: slice, self: &S) -> i32 {
    return 30;
}

// 3. Function taking a slice `&[T]` directly (inferring `T` from either `&[T]` or `&[T; N]`):
pub fn first_plus_len(comptime T: integer, s: &[T]) -> T {
    return s[0] + (s.len as T);
}

// 4. Function mutating through `&mut [i32]`:
pub fn bump_slice(s: &mut [i32], delta: i32) {
    let mut i: usize = 0;
    while i < s.len {
        s[i] += delta;
        i += 1;
    }
}

pub fn main() -> i32 {
    let mut arr: [i32; 5] = [i32; 5] { 2, 4, 6, 8, 10 };

    // A. `sum_seq` on fixed-length `array` (`[i32; 5]`): 2 + 4 + 6 + 8 + 10 = 30
    let sum_arr = sum_seq(&arr);
    // `arr.seq_tag()` matches `sequence` (rank 2) -> 20
    let tag_arr = arr.seq_tag();

    // B. Coerce `&arr` (`&[i32; 5]`) to `&[i32]` and range-slice `&arr[1..4]` (`{4, 6, 8}`):
    let full_slice: &[i32] = &arr;
    let mid_slice: &[i32] = &arr[1..4];
    // `mid_slice` has elements {4, 6, 8} -> sum_seq = 18, seq_tag (`slice` rank 3 > `sequence` rank 2) = 30
    let sum_mid = sum_seq(&mid_slice);
    let tag_slice = mid_slice.seq_tag();

    // C. Sub-slicing an existing slice (`mid_slice[1..3]` -> `{6, 8}`) and `first_plus_len`:
    let sub_slice: &[i32] = mid_slice[1..3];
    // `sub_slice[0]` = 6, `sub_slice.len` = 2 -> `first_plus_len(sub_slice)` = 8
    // Also pass `&arr` directly to `first_plus_len(&arr)` -> `arr[0]` (2) + 5 = 7
    let sub_val = first_plus_len(sub_slice) + first_plus_len(&arr) + (full_slice.len as i32); // 8 + 7 + 5 = 20

    // D. After the last read of `full_slice`, `mid_slice`, and `sub_slice`, NLL releases the shared borrows on `arr`!
    //    Now take a mutable range slice `&mut arr[1..4]` and mutate through it:
    let mut_mid: &mut [i32] = &mut arr[1..4];
    bump_slice(mut_mid, 3); // arr[1..4] becomes {7, 9, 11}
    mut_mid[0] += 1;        // arr[1] becomes 8

    // After the last use of `mut_mid`, NLL releases the mutable borrow on `arr`, allowing direct access:
    // `arr` is now {2, 8, 9, 11, 10} -> sum_seq(&arr) = 40
    let sum_after = sum_seq(&arr);

    // Total:
    //   sum_arr   = 30
    //   tag_arr   = 20
    //   sum_mid   = 18
    //   tag_slice = 30
    //   sub_val   = 20
    //   sum_after = 40
    //   Sum = 30 + 20 + 18 + 30 + 20 + 40 = 158
    return sum_arr + tag_arr + sum_mid + tag_slice + sub_val + sum_after;
}
";

        let program = Compiler::compile_source(src)
            .expect("Failed to compile slices & sequence meta-type test");
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
            Some(158),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // Verify Stage 3 NLL borrow checker rejects mutating `arr` while a slice `s` (or sub-slice `sub`) is still live:
        let bad_mutate_while_sliced = "\
pub fn main() -> i32 {
    let mut arr: [i32; 4] = [i32; 4] { 1, 2, 3, 4 };
    let s: &[i32] = &arr[1..3];
    let sub: &[i32] = s[0..1];
    arr[2] = 99;
    return sub[0];
}
";
        let err1 = Compiler::compile_source(bad_mutate_while_sliced).expect_err(
            "Expected mutating `arr` while sub-slice `sub` is live to fail NLL borrow check",
        );
        assert!(
            err1.contains("Borrow check error") && err1.contains("currently borrowed"),
            "Unexpected error: {err1}"
        );

        // Verify Stage 3 NLL borrow checker rejects mutating through an immutable `&[i32]` slice:
        let bad_write_immutable_slice = "\
pub fn main() -> i32 {
    let mut arr: [i32; 3] = [i32; 3] { 10, 20, 30 };
    let s: &[i32] = &arr[0..2];
    s[0] = 99;
    return s[0];
}
";
        let err2 = Compiler::compile_source(bad_write_immutable_slice)
            .expect_err("Expected writing through immutable slice `&[i32]` to fail borrow check");
        assert!(
            err2.contains("through an immutable reference"),
            "Unexpected error: {err2}"
        );
    }

    #[test]
    fn test_linear_structs_consuming_methods_shared_drop_and_contagion() {
        let src = "\
// 1. Meta-type constraint hierarchy with `linear` (rank 4) refining `struct` (rank 3) and `aggregate` (rank 2):
pub fn linearity_tag(comptime T: type, self: &T) -> i32 {
    return 1;
}
pub fn linearity_tag(comptime A: aggregate, self: &A) -> i32 {
    return 2;
}
pub fn linearity_tag(comptime S: struct, self: &S) -> i32 {
    return 3;
}
pub fn linearity_tag(comptime L: linear, self: &L) -> i32 {
    return 4;
}

pub struct NormalBox {
    val: i32,
    pub fn new(v: i32) -> Self {
        return Self { val: v };
    }
}

// 2. Must-consume `struct(linear)` with multiple consuming `move self` methods and shared `drop` cleanup:
pub struct(linear) Transaction {
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
    let tag_normal = nb.linearity_tag(); // selects `struct` (rank 3) -> 3

    // A. Consuming `Transaction` via `commit(move self)` and `rollback(move self)`:
    let mut log_a: i32 = 0;
    let mut res_a: i32 = 0;
    let mut tag_tx: i32 = 0;
    if true {
        let tx1 = Transaction::begin(5, &mut log_a);
        tag_tx = tx1.linearity_tag(); // selects `linear` (rank 4 > `struct` rank 3) -> 4
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
        tag_pair = pair.linearity_tag(); // selects `linear` (rank 4 > `aggregate` rank 2) -> 4
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

        let program = Compiler::compile_source(src)
            .expect("Failed to compile linear struct & shared drop test");
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
            Some(98),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // 1. Verify that forgetting to consume a `linear struct` before scope exit is rejected by Stage 3b:
        let bad_unconsumed_src = "\
pub struct(linear) Ticket {
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
            err1.contains("Linear value") && err1.contains("Ticket") && err1.contains("must be explicitly consumed"),
            "Unexpected error: {err1}"
        );

        // 2. Verify that consuming a `linear struct` on only ONE branch of an `if`/`else` is rejected:
        let bad_partial_branch_src = "\
pub struct(linear) Ticket {
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
            err2.contains("Linear value") && err2.contains("Ticket") && err2.contains("must be explicitly consumed"),
            "Unexpected error: {err2}"
        );

        // 3. Verify that forgetting to consume a `tuple` or `?Ticket` containing a `linear struct` is rejected:
        let bad_tuple_src = "\
pub struct(linear) Ticket {
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
            err3.contains("Linear value") && err3.contains("Ticket") && err3.contains("must be explicitly consumed"),
            "Unexpected error: {err3}"
        );

        // 4. Verify that calling a single-use `move fn` linear closure twice is rejected as a use-after-move:
        let bad_closure_twice_src = "\
pub struct(linear) Ticket {
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

        // 5. Verify that defining `clone` on a `linear struct` is rejected at compile time:
        let bad_clone_linear_src = "\
pub struct(linear) Ticket {
    code: i32,
    clone(self: &Self) -> Self {
        return Self { code: self.code };
    }
}
pub fn main() -> i32 { return 0; }
";
        let err5 = Compiler::compile_source(bad_clone_linear_src)
            .expect_err("Expected `clone` hook on `linear struct` to fail compilation");
        assert!(
            err5.contains("Linear struct 'Ticket' cannot implement `clone`"),
            "Unexpected error: {err5}"
        );
    }

    #[test]
    fn test_rel_references_slices_str_and_nll_borrows() {
        let src = "\
pub struct InlinePacket {
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
        let program = Compiler::compile_source(src)
            .expect("Failed to compile relative reference (&rel) test");
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
            Some(197),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // 1. Verify that using `&rel` in a `record` (or outside a `struct` field) is rejected:
        let bad_record_rel_src = "\
pub record BadRec {
    x: i32,
    p: &rel i32,
}
pub fn main() -> i32 { return 0; }
";
        let err1 = Compiler::compile_source(bad_record_rel_src)
            .expect_err("Expected `&rel` inside a `record` to be rejected");
        assert!(
            err1.contains("'&rel' relative references are only permitted in 'struct' field declarations"),
            "Unexpected error: {err1}"
        );

        // 2. Verify that pointing `&rel` at an outer stack variable violates the Co-Residence Rule:
        let bad_outer_rel_src = "\
pub struct BadHolder {
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
            err2.contains("Co-Residence violation") && err2.contains("must reside inside the enclosing struct 'self'"),
            "Unexpected error: {err2}"
        );

        // 3. Verify that pointing `&rel` through an external pointer/slice dereference violates Co-Residence:
        let bad_deref_rel_src = "\
pub struct BadExt {
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
        let err3 = Compiler::compile_source(bad_deref_rel_src)
            .expect_err("Expected `&rel` traversing a slice/pointer dereference to fail Co-Residence check");
        assert!(
            err3.contains("Co-Residence violation") && err3.contains("cannot traverse a pointer or slice dereference"),
            "Unexpected error: {err3}"
        );

        // 4. Verify Option A mutability enforcement: mutating through `*self.focus` inside `self: &Self` is rejected:
        let bad_imm_mut_src = "\
pub struct Holder {
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
pub struct Packet {
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

// 2. `Mutex(T)` (`unsafe sync struct`): encapsulates the OS mutex and protected payload `data: T`.
//    Even if it stores internal raw pointers, `unsafe sync struct` marks it `send` and `sync` iff `T: send`.
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

// 3. Flat Scoped Thread Handle (`linear struct`): retains `anchor: *mut F` so Stage 3 NLL borrow
//    checking keeps all stack borrows captured by `f` active until `.join(move self)` is called!
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
        let program = Compiler::compile_source(src)
            .expect("Failed to compile safe threading, send/sync, scoped threads, and linear Mutex program");
        let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

        let tmp_path = std::env::temp_dir().join("lrrr_safe_threading_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
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
        let err2 = Compiler::compile_source(&bad_guard_send_src)
            .expect_err("Expected capturing `&mut MutexGuard(i32)` in `spawn_scoped` to fail `comptime F: send`");
        assert!(
            err2.contains("does not satisfy comptime constraint 'send'"),
            "Unexpected error: {err2}"
        );

        // Negative Test 3: Mutating `child_out` in parent thread BEFORE `worker.join()` is rejected by Stage 3 NLL borrow checker:
        let bad_race_before_join_src = format!(
            "{src}\n",
        ).replace(
            "let worker_status = worker.join();",
            "child_out = 999;\n    let worker_status = worker.join();"
        );
        let err3 = Compiler::compile_source(&bad_race_before_join_src)
            .expect_err("Expected mutating `child_out` before `worker.join()` to fail Stage 3 NLL borrow check");
        assert!(
            err3.contains("Borrow check error") && err3.contains("borrowed"),
            "Unexpected error: {err3}"
        );

        // Negative Test 4: Forgetting to call `worker.join()` before scope exit is rejected by Stage 3b linear type checker:
        let bad_unjoined_handle_src = format!(
            "{src}\n",
        ).replace(
            "let worker_status = worker.join();",
            "let worker_status: i32 = 7;"
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
    fn test_core_and_std_library_prelude_and_no_std() {
        use crate::lower::Compiler;

        // 1. Hosted mode (`std::prelude::*` injected automatically; zero `import` or `extern fn` needed):
        let hosted_src = r"
pub fn main() -> i32 {
    // `core::math` & `core::cmp` from prelude
    let neg: i32 = -15;
    let raw: i32 = 25;
    let a: i32 = neg.abs();
    let b: i32 = raw.clamp(0, 10);
    let c: i32 = min(a, b);
    let d: i32 = max(a, b);

    // `core::mem` from prelude
    let mut x: i32 = 10;
    let mut y: i32 = 20;
    swap(&mut x, &mut y);
    let old_x = replace(&mut x, 50);

    // `core::slice` & `core::option` from prelude
    let arr: [i32; 3] = {7, 8, 9};
    let s: &[i32] = &arr;
    let first_opt: ?i32 = s.first();
    let last_opt: ?i32 = s.last();
    let first_val = first_opt orelse 0;
    let last_val = last_opt orelse 0;
    let empty_check = !arr.is_empty() && first_opt.is_some() && !last_opt.is_none();

    // `std::mem::Box(T)` from prelude (heap-allocated with automatic `free` on scope exit)
    let mut boxed = Box(i32)::new(30);
    let p: &mut i32 = boxed.get_mut();
    *p = *p + 12;
    let box_val: i32 = *boxed.get();

    // `std::sync::Mutex(T)` and `std::thread::spawn_scoped` from prelude
    let mtx = Mutex(i32)::new(box_val);
    let worker = spawn_scoped(fn() -> i32 {
        return mtx.with_lock(fn(v: &mut i32) -> i32 {
            *v = *v + 8;
            return *v;
        });
    });
    let worker_res = worker.join();
    let final_mtx = mtx.with_lock(fn(v: &mut i32) -> i32 { return *v; });

    if a == 15
        && b == 10
        && c == 10
        && d == 15
        && x == 50
        && y == 10
        && old_x == 20
        && first_val == 7
        && last_val == 9
        && empty_check
        && box_val == 42
        && worker_res == 50
        && final_mtx == 50
    {
        return 42;
    }
    return 1;
}
";
        let program = Compiler::compile_source(hosted_src)
            .expect("Failed to compile zero-import hosted std::prelude program");
        let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

        let tmp_path = std::env::temp_dir().join("lrrr_stdlib_prelude_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
        assert_eq!(
            output.status.code(),
            Some(42),
            "Expected exit code 42 from lli, got {:?}\nstderr: {}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
        );

        // 2. Explicit stdlib module imports (`import core::math;`) & lexical shadowing of prelude items:
        let shadowing_src = r"
import core::math;

// Local definition cleanly shadows `std::prelude::min` without ambiguity
fn min(a: i32, b: i32) -> i32 {
    return a + b;
}

pub fn main() -> i32 {
    let custom = min(10, 20);
    let std_min = core::cmp::min(10, 20);
    let m = math::abs(-12);
    if custom == 30 && std_min == 10 && m == 12 {
        return 0;
    }
    return 1;
}
";
        let shadow_prog = Compiler::compile_source(shadowing_src)
            .expect("Failed to compile lexical prelude shadowing program");
        assert!(
            shadow_prog.externs.is_empty(),
            "Expected zero extern declarations when no OS/libc std functions are referenced, got {:?}",
            shadow_prog.externs
        );

        // 3. Freestanding `no_std` mode (`Compiler::compile_source_no_std`):
        //    `core::prelude::*` is available, while `std::*` (`Box`, `Mutex`, `spawn_scoped`) is absent.
        let no_std_ok_src = r"
pub fn main() -> i32 {
    let n: i32 = -7;
    let r: i32 = 99;
    let mut a: i32 = n.abs();
    let mut b: i32 = r.clamp(0, 5);
    swap(&mut a, &mut b);
    if a == 5 && b == 7 {
        return 0;
    }
    return 1;
}
";
        Compiler::compile_source_no_std(no_std_ok_src)
            .expect("Expected `no_std` program using `core::prelude` to compile cleanly");

        let no_std_err_src = r"
pub fn main() -> i32 {
    let b = Box(i32)::new(1);
    return *b.get();
}
";
        let err = Compiler::compile_source_no_std(no_std_err_src)
            .expect_err("Expected `Box` from `std` to be unavailable in `no_std` mode");
        assert!(
            err.contains("Undefined symbol 'Box'"),
            "Unexpected error in no_std mode: {err}"
        );
    }

    #[test]
    fn test_string_formatting_fstrings_transparent_vs_struct_and_specifiers() {
        use crate::lower::Compiler;

        let src = r#"
pub record Point {
    x: i32,
    y: i32,
}

pub enum Status {
    Ok = 0,
    Pending = 1,
}

pub struct Ipv4Addr {
    octets: [u8; 4],

    format(self: &Self, f: &mut Formatter) {
        f.write(f"{self.octets[0]}.{self.octets[1]}.{self.octets[2]}.{self.octets[3]}");
    }

    pub fn new(a: u8, b: u8, c: u8, d: u8) -> Self {
        return Self {
            octets: { a, b, c, d },
        };
    }
}

pub struct TagId {
    id: u32,

    format(self: &Self, f: &mut Formatter, spec: &str) {
        if str_eq(spec, "x") {
            f.write(f"id(0x{self.id:04x})");
        } else {
            f.write(f"id({self.id})");
        }
    }

    pub fn new(id: u32) -> Self {
        return Self { id: id };
    }
}

pub fn main() -> i32 {
    // 1. Primitives & inline format specifiers (`:x`, `:04X`, `:08b`, `:o`, `:?`, `:.2`, `{{` / `}}`)
    let name: &str = "Alice";
    let ch: rune = 'A';
    let hex_v: u32 = 255;
    let bin_v: u8 = 10;
    let oct_v: u32 = 15;
    let neg_v: i32 = -42;
    let pi: f64 = 3.14159;

    let mut buf1: [u8; 256] = @default([u8; 256]);
    let s1: &str = fmt_buf(
        &mut buf1,
        f"{{name={name:?}, ch={ch:?}, hex={hex_v:04x}/{hex_v:04X}, bin={bin_v:08b}, oct={oct_v:o}, neg={neg_v:4}, pi={pi:.2}}}"
    );
    let ok1 = str_eq(
        s1,
        "{name=\"Alice\", ch='A', hex=00ff/00FF, bin=00001010, oct=17, neg= -42, pi=3.14}"
    );

    // 2. Auto-formatting of transparent types (`record`, `tuple`, `[T; N]`, `&[T]`, `?T`, `enum`)
    let pt = Point { x: 10, y: 20 };
    let tup: tuple { i32, bool } = { 7, true };
    let arr: [i32; 3] = { 1, 2, 3 };
    let sl: &[i32] = &arr[1..3];
    let opt_some: ?i32 = 99;
    let opt_none: ?i32 = null;
    let st: Status = Status::Pending;

    let mut buf2: [u8; 256] = @default([u8; 256]);
    let s2: &str = fmt_buf(
        &mut buf2,
        f"pt={pt} tup={tup} arr={arr} sl={sl} some={opt_some} none={opt_none} st={st}({st:d})"
    );
    let ok2 = str_eq(
        s2,
        "pt=Point { x: 10, y: 20 } tup={ 7, true } arr=[1, 2, 3] sl=[2, 3] some=99 none=null st=Status::Pending(1)"
    );

    // 3. Encapsulated `struct` with lowercase `format` hook (2-param & 3-param `spec`) + nested lazy `f"..."` + heap `String`
    let ip = Ipv4Addr::new(127, 0, 0, 1);
    let tag = TagId::new(255);
    let mut port: u16 = 8080;
    let endpoint = f"{ip}:{port}";
    let full_msg = f"connect({endpoint}) [{tag} / {tag:x}]";
    let owned: String = format(full_msg);
    // Once `format(full_msg)` finishes, NLL borrow of `port` ends so `port` can be mutated!
    port = 9090;

    let mut buf3: [u8; 256] = @default([u8; 256]);
    let s3: &str = fmt_buf(&mut buf3, f"{owned} next_port={port}");
    let ok3 = str_eq(
        s3,
        "connect(127.0.0.1:8080) [id(255) / id(0x00ff)] next_port=9090"
    );

    if ok1 && ok2 && ok3 {
        return 42;
    }
    return 1;
}
"#;
        let program = Compiler::compile_source(src)
            .expect("Failed to compile string formatting program");
        let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");

        let tmp_path = std::env::temp_dir().join("lrrr_string_formatting_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
        assert_eq!(
            output.status.code(),
            Some(42),
            "Expected exit code 42 from lli, got {:?}\nstderr: {}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
        );

        // Negative Test 1: Defining a `format` hook on a transparent `record` is forbidden at compile time
        let bad_record_format_src = r#"
pub record Point {
    x: i32,
    y: i32,
    format(self: &Self, f: &mut Formatter) {
        f.write_str("custom");
    }
}
pub fn main() -> i32 { return 0; }
"#;
        let err1 = Compiler::compile_source(bad_record_format_src)
            .expect_err("Expected defining `format` hook on transparent `record` to be rejected");
        assert!(
            err1.contains("Lifecycle hook 'format' is forbidden on transparent 'record' types"),
            "Unexpected error: {err1}"
        );

        // Negative Test 2: Interpolating an encapsulated `struct` that has no `format` hook is rejected at compile time
        let bad_struct_no_format_src = r#"
pub struct SecretKey {
    raw: u64,
    pub fn new(raw: u64) -> Self { return Self { raw: raw }; }
}
pub fn main() -> i32 {
    let k = SecretKey::new(12345);
    let _msg = f"secret={k}";
    return 0;
}
"#;
        let err2 = Compiler::compile_source(bad_struct_no_format_src)
            .expect_err("Expected formatting a `struct` without a `format` hook to be rejected");
        assert!(
            err2.contains("Struct 'SecretKey' does not define a 'format' hook"),
            "Unexpected error: {err2}"
        );

        // Negative Test 3: Stage 3c NLL borrow checker rejects mutating a variable while a lazy `f"..."` borrowing it is still live
        let bad_nll_mutation_while_borrowed_src = r#"
pub fn main() -> i32 {
    let mut x: i32 = 10;
    let lazy = f"val={x}";
    x = 20;
    let _s = format(lazy);
    return 0;
}
"#;
        let err3 = Compiler::compile_source(bad_nll_mutation_while_borrowed_src)
            .expect_err("Expected mutating `x` while `lazy = f\"val={x}\"` is live to fail Stage 3c NLL borrow check");
        assert!(
            err3.contains("Borrow check error") && err3.contains("borrowed"),
            "Unexpected error: {err3}"
        );
    }

    #[test]
    fn test_soundness_review_fixes() {
        // 1. A transparent `record` holding `&mut T` is NOT Copy (cannot be copied to create two live `&mut T`):
        let record_with_mut_ref_src = r#"
pub record MutHolder {
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
            .expect_err("Expected copying `record { r: &mut i32 }` to fail move analysis");
        assert!(
            err1.contains("Use of moved or uninitialized value"),
            "Unexpected error: {err1}"
        );

        // 2. A plain `struct` with no lifecycle hooks is move-only by default (never implicitly Copy):
        let plain_struct_move_only_src = r#"
pub struct Token {
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
            .expect_err("Expected plain `struct` to be move-only by default");
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
pub struct RawBuf {
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
pub record RefSlot {
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
        let err5 = Compiler::compile_source(param_to_param_flow_src)
            .expect_err("Expected storing `&short_lived` into `slot` via `stash` to fail when `short_lived` dies");
        assert!(
            err5.contains("Borrow check error") && err5.contains("goes out of scope (StorageDead) while still borrowed"),
            "Unexpected error: {err5}"
        );

        // 6. `@drop` on a linear type (including via raw pointer in a generic container) is rejected:
        let drop_linear_in_container_src = r#"
pub struct(linear) MustCommit {
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

        // 7. Bare `struct(sync)` without `unsafe` is rejected at compile time:
        let bare_sync_struct_src = r#"
pub struct(sync) UncheckedSync {
    ptr: *mut u8,
}
pub fn main() -> i32 { return 0; }
"#;
        let err7 = Compiler::compile_source(bare_sync_struct_src)
            .expect_err("Expected bare `struct(sync)` without `unsafe` to be rejected");
        assert!(
            err7.contains("requires 'struct(unsafe sync)'"),
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

        // 9. `struct(copy)` is implicitly copyable (`Copy`), supports `@clone`, satisfies `comptime T: copy`,
        //    and rejects `drop` hooks or non-copy fields:
        let copy_struct_src = r#"
pub struct(copy) UserId {
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
            .expect("Expected `struct(copy)` to be implicitly copyable and satisfy `comptime T: copy`");
        let _ir9 = LlvmLowering::lower(&prog9).expect("Expected LLVM lowering of `struct(copy)` to succeed");

        let bad_copy_struct_drop_src = r#"
pub struct(copy) BadCopy {
    x: i32,
    drop(self: &mut Self) {}
}
pub fn main() -> i32 { return 0; }
"#;
        let err9 = Compiler::compile_source(bad_copy_struct_drop_src)
            .expect_err("Expected `struct(copy)` with `drop` hook to be rejected");
        assert!(
            err9.contains("Copy struct 'BadCopy' ('struct(copy)') cannot implement `drop`"),
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

pub struct(linear) Transaction {
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
    return struct {
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

        pub fn push(self: &mut Self, val: T) {
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

        // 1. `Vec(i32)` is `struct(affine)`: supports `clear()`, `@clone(&v)`, and implicit scope-exit drop (`where T: !linear`):
        if true {
            let mut vi = Vec(i32)::new(4, 4, vec_drops);
            vi.push(10);
            vi.push(20);
            let mut vi_clone = @clone(&vi);
            vi_clone.clear();
        }
        // Both `vi` and `vi_clone` ran `drop where T: !linear`, so `*vec_drops == 2`!

        // 2. `Vec(Transaction)` is automatically upgraded to `struct(linear)` because `drop where T: linear` matched:
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

        let tmp_path = std::env::temp_dir().join("lrrr_conditional_vec_drop_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
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
pub struct(linear) Transaction {
    id: i32,
    pub fn commit(move self) -> i32 { return self.id; }
}
pub fn BadVec(comptime T: type) -> type {
    return struct {
        ptr: ?*mut T = null,
        drop(self: &mut Self) where T: !linear {}
    };
}
pub fn main() -> i32 {
    let v: BadVec(Transaction) = BadVec(Transaction) { ptr: null };
    return 0;
}
"#;
        let err3 = Compiler::compile_source(missing_linear_drop_src).expect_err(
            "Expected `BadVec(Transaction)` missing `drop where T: linear` to be rejected",
        );
        assert!(
            err3.contains("defines 'drop' with 'where T: !linear', but is missing a matching 'drop(self: &mut Self) where T: linear' teardown hook"),
            "Unexpected error: {err3}"
        );
    }

    #[test]
    fn test_surface_pub_fn_borrows_contracts_and_param_flows() {
        // 1. Valid `pub fn` with explicit `borrows(a, b)`, `borrows(second)`, and `borrows(dst: x)`:
        let valid_src = r#"
pub record RefSlot {
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
        let tmp_path = std::env::temp_dir().join("lrrr_surface_borrows_contracts_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
        let _ = std::fs::remove_file(&tmp_path);
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
            err2.contains("return value borrows from parameter '_1', which is not permitted by explicit contract borrows(_2)"),
            "Unexpected error: {err2}"
        );

        // 4. `pub fn stash(dst: &mut RefSlot, x: &i32)` without `borrows(dst: x)` is rejected:
        let missing_param_flow_contract_src = r#"
pub record RefSlot {
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
            err3.contains("parameter '_1' borrows from parameter '_2', which is not permitted by explicit borrows(...) contract"),
            "Unexpected error: {err3}"
        );

        // 5. `pub fn stash(dst: &mut RefSlot, x: &i32) borrows(dst: x)` rejects caller when `x` dies before `dst`:
        let caller_dangling_stash_src = r#"
pub record RefSlot {
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
    fn test_unified_error_adhoc_unions_try_catch_and_match() {
        // 1. Positive end-to-end test:
        //    - Unified `error` declarations (unit leaves, payload leaves, inline record leaves, embedded error types)
        //    - Ad-hoc error unions `IoError || DbError` and `DbError || IoError` (algebraic commutativity/idempotence + conflicting `Timeout` leaves)
        //    - `E!T` result types, `try` automatic widening, `catch` / `catch |err|`, `match` with leaf and subtype group narrowing
        //    - Tagged `union` declarations and `match`
        //    - Automatic formatting of `error`, `union`, and `E!T`
        let valid_src = r#"
pub error IoError {
    Timeout,
    NotFound,
}

pub error DbError {
    Timeout,
    Deadlock(u32),
}

pub error ParseError {
    UnexpectedToken: u32,
    Eof,
}

pub error ConfigError {
    IoError,
    ParseError,
    SyntaxError: record {
        line: u32,
        col: u32,
    },
}

pub union Shape {
    Unit,
    Circle(i32),
    Rect: record {
        w: i32,
        h: i32,
    },
}

fn read_io(mode: i32) -> IoError!i32 {
    if mode == 1 {
        return IoError::Timeout;
    }
    if mode == 2 {
        return IoError::NotFound;
    }
    return 10;
}

fn query_db(mode: i32) -> DbError!i32 {
    if mode == 1 {
        return DbError::Timeout;
    }
    if mode == 2 {
        return DbError::Deadlock(7);
    }
    return 20;
}

// `IoError || DbError` and `DbError || IoError` are the exact same canonical error set:
fn fetch_ab(io_mode: i32, db_mode: i32) -> (IoError || DbError)!i32 {
    let a: i32 = try read_io(io_mode);
    let b: i32 = try query_db(db_mode);
    return a + b;
}

fn fetch_ba(io_mode: i32, db_mode: i32) -> (DbError || IoError)!i32 {
    return try fetch_ab(io_mode, db_mode);
}

fn load_config(mode: i32) -> ConfigError!i32 {
    if mode == 1 {
        return try read_io(1);
    }
    if mode == 2 {
        return ParseError::UnexpectedToken(99);
    }
    if mode == 3 {
        return ConfigError::SyntaxError { line: 4, col: 12 };
    }
    return 50;
}

fn area(s: Shape) -> i32 {
    return match s {
        Shape::Unit => 0,
        Shape::Circle(r) => r * r,
        Shape::Rect(rect) => rect.w * rect.h,
    };
}

pub fn main() -> i32 {
    // 1. Happy path through `try` and `catch`:
    let ok_sum: i32 = fetch_ba(0, 0) catch -1;
    if ok_sum != 30 {
        return 1;
    }

    // 2. Conflicting variant names (`IoError::Timeout` vs `DbError::Timeout`) preserved distinctly:
    let err_io_code: i32 = fetch_ba(1, 0) catch |err| match err {
        IoError::Timeout => 101,
        IoError::NotFound => 102,
        DbError::Timeout => 201,
        DbError::Deadlock(code) => (200 + code) as i32,
    };
    if err_io_code != 101 {
        return 2;
    }

    let err_db_code: i32 = fetch_ab(0, 1) catch |err| match err {
        IoError::Timeout => 101,
        IoError::NotFound => 102,
        DbError::Timeout => 201,
        DbError::Deadlock(code) => (200 + code) as i32,
    };
    if err_db_code != 201 {
        return 3;
    }

    // 3. Subtype group matching (`IoError(io_err) => ...` and `DbError(db_err) => ...`):
    let group_code: i32 = fetch_ab(0, 2) catch |err| match err {
        IoError(io_err) => match io_err {
            IoError::Timeout => 10,
            IoError::NotFound => 20,
        },
        DbError(db_err) => match db_err {
            DbError::Timeout => 30,
            DbError::Deadlock(c) => (40 + c) as i32,
        },
    };
    if group_code != 47 {
        return 4;
    }

    // 4. Hierarchical `ConfigError` with payload and inline record variant:
    let cfg2: i32 = load_config(2) catch |err| match err {
        IoError(_) => 1,
        ParseError::UnexpectedToken(tok) => tok as i32,
        ParseError::Eof => 2,
        ConfigError::SyntaxError(syn) => (syn.line * 10 + syn.col) as i32,
    };
    if cfg2 != 99 {
        return 5;
    }

    let cfg3: i32 = load_config(3) catch |err| match err {
        IoError(_) => 1,
        ParseError(_) => 2,
        ConfigError::SyntaxError(syn) => (syn.line * 10 + syn.col) as i32,
    };
    if cfg3 != 52 {
        return 6;
    }

    // 5. General `union` construction and `match`:
    let s1 = Shape::Circle(3);
    let s2 = Shape::Rect { w: 4, h: 5 };
    if area(s1) + area(s2) != 29 {
        return 7;
    }

    // 6. Automatic string formatting of `error`:
    let e_val: IoError = IoError::Timeout;
    let mut buf: [u8; 64] = @default([u8; 64]);
    let formatted: &str = fmt_buf(&mut buf, f"{e_val}");
    if !str_eq(formatted, "IoError::Timeout") {
        return 8;
    }

    return 42;
}
"#;
        let program = Compiler::compile_source(valid_src)
            .expect("Expected unified error, ad-hoc unions, try/catch, and match to compile");
        let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower to LLVM IR");
        let tmp_path = std::env::temp_dir().join("lrrr_unified_error_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
        let _ = std::fs::remove_file(&tmp_path);
        assert_eq!(
            output.status.code(),
            Some(42),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // 2. Negative test: explicit integer discriminant `= 1` on `error` is rejected:
        let explicit_disc_src = r#"
pub error BadError {
    Timeout = 1,
}
pub fn main() -> i32 { return 0; }
"#;
        let err1 = Compiler::compile_source(explicit_disc_src)
            .expect_err("Expected explicit discriminant on `error` to be rejected");
        assert!(
            err1.contains("Explicit integer discriminants ('= N') are forbidden on 'error'"),
            "Unexpected error: {err1}"
        );

        // 3. Negative test: explicit backing integer type `error(u8)` is rejected:
        let backing_ty_src = r#"
pub error(u8) BadError {
    Timeout,
}
pub fn main() -> i32 { return 0; }
"#;
        let err2 = Compiler::compile_source(backing_ty_src)
            .expect_err("Expected backing type on `error` to be rejected");
        assert!(
            err2.contains("Explicit backing integer types ('error(...)') are forbidden"),
            "Unexpected error: {err2}"
        );

        // 4. Negative test: non-exhaustive `match` on `error` is rejected:
        let non_exhaustive_src = r#"
pub error IoError {
    Timeout,
    NotFound,
}
pub fn main() -> i32 {
    let e: IoError = IoError::Timeout;
    return match e {
        IoError::Timeout => 1,
    };
}
"#;
        let err3 = Compiler::compile_source(non_exhaustive_src)
            .expect_err("Expected non-exhaustive match on `IoError` to be rejected");
        assert!(
            err3.contains("Non-exhaustive `match` on error type") && err3.contains("IoError::NotFound"),
            "Unexpected error: {err3}"
        );

        // 5. Negative test: `try` on incompatible error set is rejected:
        let incompatible_try_src = r#"
pub error IoError { Timeout }
pub error DbError { Deadlock }
fn fail_db() -> DbError!i32 {
    return DbError::Deadlock;
}
fn caller() -> IoError!i32 {
    return try fail_db();
}
pub fn main() -> i32 { return 0; }
"#;
        let err4 = Compiler::compile_source(incompatible_try_src)
            .expect_err("Expected `try` with incompatible error set to be rejected");
        assert!(
            err4.contains("Error type 'DbError' is not a subset of 'IoError': missing variant 'DbError::Deadlock'"),
            "Unexpected error: {err4}"
        );
    }

    #[test]
    fn test_traits_static_bounds_and_dynamic_dispatch_fat_pointers() {
        use crate::llvm::LlvmLowering;
        use crate::lower::Compiler;
        use crate::vm::{Value, Vm};

        // 1. End-to-end positive test:
        //    - `pub trait Name { ... }`, `type Name = trait { ... };`, and `fn From(comptime Src: type) -> trait`
        //    - Static `comptime` bounds: `comptime T: Trait`, `comptime T: A + B`, `comptime T: From(i32)`
        //    - Static monomorphized calls (`a: T`, `a: &T`) and `comptime a: &Trait`
        //    - Dynamic dispatch via `&Trait` and `&mut Trait` fat pointers (without `dyn`), including
        //      coercing `&T` -> `&Trait`, `&mut T` -> `&mut Trait`, `&mut Trait` -> `&Trait`, and reborrowing
        let valid_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
    fn add(self: &mut Self, delta: i32);
}

type Describable = trait {
    fn code(self: &Self) -> i32;
};

pub fn ScaleBy(comptime Factor: type) -> trait {
    return trait {
        fn scale(self: &Self, k: Factor) -> i32;
    };
}

// Non-object-safe trait (takes `self: Self` by value and returns `Self`) — valid for `comptime T: Doubler`
pub trait Doubler {
    fn doubled(self: Self) -> Self;
}

pub record StepCounter {
    val: i32,
    step: i32,

    pub fn get(self: &Self) -> i32 {
        return self.val;
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.val = self.val + delta * self.step;
    }

    pub fn doubled(self: Self) -> Self {
        return Self { val: self.val * 2, step: self.step };
    }
}

// Extension methods in the same module satisfying `Describable` and `ScaleBy(i32)` for `StepCounter`
pub fn code(self: &StepCounter) -> i32 {
    return self.val + 100;
}

pub fn scale(self: &StepCounter, k: i32) -> i32 {
    return self.val * k;
}

pub record SimpleBox {
    n: i32,

    pub fn get(self: &Self) -> i32 {
        return self.n;
    }

    pub fn add(self: &mut Self, delta: i32) {
        self.n = self.n + delta;
    }
}

// Static dispatch with single trait bound (by value and by reference)
fn static_read(comptime T: Counter, c: &T) -> i32 {
    return c.get();
}

fn static_double(comptime T: Doubler, v: T) -> T {
    return v.doubled();
}

// Static dispatch with multi-trait `+` bounds and parameterized trait `ScaleBy(i32)`
fn static_combo(comptime T: Counter + Describable + ScaleBy(i32), c: &T) -> i32 {
    return c.get() + c.code() + c.scale(3);
}

// Compile-time constant trait reference (`comptime a: &Counter`) — no runtime vtable
fn eval_const_counter(comptime c: &Counter) -> i32 {
    return c.get() + 5;
}

// Dynamic dispatch via `&Counter` and `&mut Counter` fat pointers (no `dyn` keyword)
fn dyn_read(c: &Counter) -> i32 {
    return c.get();
}

fn dyn_bump_and_read(c: &mut Counter, delta: i32) -> i32 {
    c.add(delta);
    // Automatic reborrow / coercion of `&mut Counter` -> `&Counter`
    return dyn_read(c);
}

pub fn main() -> i32 {
    let mut sc = StepCounter { val: 10, step: 2 };
    let mut sb = SimpleBox { n: 7 };

    // 1. Static dispatch (inferred `T` and explicit `T`)
    if static_read(&sc) != 10 {
        return 1;
    }
    if static_read(SimpleBox, &sb) != 7 {
        return 2;
    }
    let sc2 = static_double(sc);
    if sc2.val != 20 {
        return 3;
    }

    // 2. Multi-trait `+` bounds + generic trait `ScaleBy(i32)`
    // 10 + (10 + 100) + (10 * 3) = 150
    if static_combo(&sc) != 150 {
        return 4;
    }

    // 3. `comptime c: &Counter`
    let ct_res = eval_const_counter(&StepCounter { val: 37, step: 1 });
    if ct_res != 42 {
        return 5;
    }

    // 4. Dynamic dispatch through `&Counter` and `&mut Counter` over heterogeneous types
    if dyn_bump_and_read(&mut sc, 5) != 20 {
        return 6;
    }
    if dyn_bump_and_read(&mut sb, 5) != 12 {
        return 7;
    }

    let dyn_ref: &Counter = &sc;
    if dyn_ref.get() != 20 {
        return 8;
    }

    return 42;
}
"#;
        let mut program = Compiler::compile_source(valid_src)
            .expect("Expected valid traits program (static + dynamic dispatch) to compile");

        // Verify execution on Stage 3 VM
        let main_fn = program
            .functions
            .iter()
            .find(|f| f.export.as_deref() == Some("main"))
            .unwrap()
            .id;
        let vm_ret = Vm::eval(&mut program, main_fn, Vec::new())
            .expect("VM execution of traits program failed");
        assert_eq!(vm_ret, Value::Int(42));

        // Verify execution on Stage 4 LLVM (`lli`)
        let llvm_ir = LlvmLowering::lower(&program).expect("Failed to lower traits program to LLVM IR");
        let tmp_path = std::env::temp_dir().join("lrrr_traits_test.ll");
        std::fs::write(&tmp_path, &llvm_ir).unwrap();
        let output = std::process::Command::new("lli")
            .arg(&tmp_path)
            .output()
            .expect("Failed to execute lli");
        let _ = std::fs::remove_file(&tmp_path);
        assert_eq!(
            output.status.code(),
            Some(42),
            "lli stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );

        // 2. Negative test: bare `fn bad(a: Counter)` by value is rejected:
        let bare_param_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
}
fn bad(a: Counter) -> i32 {
    return 0;
}
pub fn main() -> i32 { return 0; }
"#;
        let err_bare = Compiler::compile_source(bare_param_src)
            .expect_err("Expected bare trait parameter by value to be rejected");
        assert!(
            err_bare.contains("Trait 'Counter' is an unsized meta-type constraint and cannot be passed by value"),
            "Unexpected error: {err_bare}"
        );

        // 3. Negative test: calling `&mut Self` trait method on shared `&Counter` is rejected:
        let mut_on_shared_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
    fn add(self: &mut Self, delta: i32);
}
fn bad(c: &Counter) {
    c.add(1);
}
pub fn main() -> i32 { return 0; }
"#;
        let err_mut = Compiler::compile_source(mut_on_shared_src)
            .expect_err("Expected calling `&mut Self` method on `&Counter` to be rejected");
        assert!(
            err_mut.contains("Cannot call '&mut Self' method 'Counter.add' on shared trait object '&Counter'"),
            "Unexpected error: {err_mut}"
        );

        // 4. Negative test: coercing immutable `&T` to `&mut Counter` is rejected:
        let immut_to_mut_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
}
pub record Boxed {
    v: i32,
    pub fn get(self: &Self) -> i32 { return self.v; }
}
fn take_mut(c: &mut Counter) -> i32 {
    return c.get();
}
pub fn main() -> i32 {
    let b = Boxed { v: 1 };
    return take_mut(&b);
}
"#;
        let err_immut = Compiler::compile_source(immut_to_mut_src)
            .expect_err("Expected coercing `&Boxed` to `&mut Counter` to be rejected");
        assert!(
            err_immut.contains("Cannot coerce immutable reference '&Boxed' to mutable trait object '&mut Counter'"),
            "Unexpected error: {err_immut}"
        );

        // 5. Negative test: non-object-safe trait (`self: Self` by value or returning `Self`) cannot form `&Trait`:
        let obj_safety_src = r#"
pub trait Cloneable {
    fn duplicate(self: &Self) -> Self;
}
fn bad(c: &Cloneable) -> i32 {
    return 0;
}
pub fn main() -> i32 { return 0; }
"#;
        let err_obj_safety = Compiler::compile_source(obj_safety_src)
            .expect_err("Expected non-object-safe trait to be rejected when forming `&Cloneable`");
        assert!(
            err_obj_safety.contains("Trait 'Cloneable' is not object-safe and cannot form '&Cloneable'"),
            "Unexpected error: {err_obj_safety}"
        );

        // 6. Negative test: built-in structural constraint `&number` cannot be used as a dynamic trait object:
        let builtin_obj_src = r#"
fn bad(x: &number) -> i32 {
    return 0;
}
pub fn main() -> i32 { return 0; }
"#;
        let err_builtin = Compiler::compile_source(builtin_obj_src)
            .expect_err("Expected `&number` to be rejected");
        assert!(
            err_builtin.contains("Built-in meta-type constraint 'number' cannot be used as a dynamic trait object '&number'"),
            "Unexpected error: {err_builtin}"
        );

        // 7. Negative test: Orphan rule coherence violation across modules:
        let trait_mod_src = r#"
pub trait Hasher {
    fn hash_val(self: &Self) -> i32;
}
pub fn compute_hash(comptime T: Hasher, x: &T) -> i32 {
    return x.hash_val();
}
"#;
        let type_mod_src = r#"
pub record ForeignKey {
    id: i32,
}
"#;
        let root_orphan_src = r#"
import root::trait_mod::{Hasher, compute_hash};
import root::type_mod::ForeignKey;

// Orphan extension method in `root` (neither `root::trait_mod` nor `root::type_mod`)
pub fn hash_val(self: &ForeignKey) -> i32 {
    return self.id;
}

pub fn main() -> i32 {
    let k = ForeignKey { id: 7 };
    return compute_hash(&k);
}
"#;
        let err_orphan = Compiler::compile_package(&[
            ("root::trait_mod", trait_mod_src),
            ("root::type_mod", type_mod_src),
            ("root", root_orphan_src),
        ])
        .expect_err("Expected orphan extension method satisfying foreign trait for foreign type to be rejected");
        assert!(
            err_orphan.contains("Orphan rule violation"),
            "Unexpected error: {err_orphan}"
        );

        // 8. Negative test: NLL borrow checker tracks loan through `&Counter` trait object fat pointer:
        let nll_trait_obj_src = r#"
pub trait Counter {
    fn get(self: &Self) -> i32;
}
pub record Val {
    n: i32,
    pub fn get(self: &Self) -> i32 { return self.n; }
}
pub fn main() -> i32 {
    let mut v = Val { n: 10 };
    let obj: &Counter = &v;
    v = Val { n: 20 };
    return obj.get();
}
"#;
        let err_nll = Compiler::compile_source(nll_trait_obj_src)
            .expect_err("Expected NLL borrow checker to reject mutating `v` while `obj: &Counter` is live");
        assert!(
            err_nll.contains("because it is currently borrowed"),
            "Unexpected error: {err_nll}"
        );
    }

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
        let err_opaque_let = Compiler::compile_source(
            "pub fn main() -> i32 { let x: opaque = 0; return 0; }",
        )
        .expect_err("Expected `let x: opaque` to be rejected");
        assert!(
            err_opaque_let.contains("Unsized type 'opaque' cannot be bound by value"),
            "Unexpected error: {err_opaque_let}"
        );

        let err_opaque_param = Compiler::compile_source(
            "pub fn bad(x: opaque) {} pub fn main() -> i32 { return 0; }",
        )
        .expect_err("Expected parameter `x: opaque` by value to be rejected");
        assert!(
            err_opaque_param.contains("Unsized type 'opaque' cannot be passed by value"),
            "Unexpected error: {err_opaque_param}"
        );

        let err_opaque_field = Compiler::compile_source(
            "pub record Bad { f: opaque } pub fn main() -> i32 { return 0; }",
        )
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
            err_opaque_arr.contains("Unsized type 'opaque' has unknown size and cannot be an array element"),
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
        let err_cld = Compiler::compile_source("pub fn main() -> i32 { let x: c_longdouble = 0.0; return 0; }")
            .expect_err("Expected `c_longdouble` to be rejected as reserved");
        assert!(
            err_cld.contains("Type 'c_longdouble' is reserved"),
            "Unexpected error: {err_cld}"
        );

        let err_f128 = Compiler::compile_source("pub fn main() -> i32 { let x: f128 = 0.0; return 0; }")
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
pub type Sqlite3 = opaque {
    pub fn from_addr(addr: usize) -> *mut Self {
        return addr as *mut Self;
    }

    pub fn tag(self: *const Self) -> i32 {
        return (self as usize) as i32;
    }
};

pub opaque CFile {
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

pub record StepCounter {
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
pub opaque Sqlite3;
pub opaque CFile;
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
pub opaque Sqlite3;
pub fn main() -> i32 {
    let mut x: i32 = 10;
    let db: *mut Sqlite3 = &mut x;
    return 0;
}
"#,
        )
        .expect_err("Expected implicit conversion from `&mut i32` to `*mut Sqlite3` to be rejected");
        assert!(
            err_concrete_to_named_opaque.contains("cannot implicitly convert '&mut i32' to '*mut Sqlite3'"),
            "Unexpected error: {err_concrete_to_named_opaque}"
        );

        let err_deref_named_opaque = Compiler::compile_source(
            r#"
pub opaque Sqlite3;
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
pub record StepCounter {
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
            err_exist_concrete_annot.contains("return value to explicit concrete type 'StepCounter' in 'let c'"),
            "Unexpected error: {err_exist_concrete_annot}"
        );

        let err_exist_field = Compiler::compile_source(
            r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub record StepCounter {
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
        .expect_err("Expected direct field access `c.val` on `-> opaque Counter` variable to be rejected");
        assert!(
            err_exist_field.contains("Cannot access concrete field 'val' on existential"),
            "Unexpected error: {err_exist_field}"
        );

        let err_exist_method = Compiler::compile_source(
            r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub record StepCounter {
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
pub record NotACounter { val: i32 }
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
            err_exist_unsatisfied.contains("Return type 'NotACounter' in 'make_counter' does not satisfy 'opaque' return bound"),
            "Unexpected error: {err_exist_unsatisfied}"
        );

        let err_exist_conflict = Compiler::compile_source(
            r#"
pub trait Counter { fn get(self: &Self) -> i32; }
pub record CounterA {
    val: i32,
    pub fn get(self: &Self) -> i32 { return self.val; }
}
pub record CounterB {
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
            err_exist_conflict.contains("Conflicting concrete return types in '-> opaque ...' function 'make_counter'"),
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

export record Point {
    x: c_int,
    y: c_int,
    coords: [i32; 2],
}

export opaque struct Counter {
    pub val: c_int,
}

export fn counter_add(c: *mut Counter, delta: c_int) -> c_int {
    (*c).val = (*c).val + delta;
    return (*c).val;
}

export fn counter_try_get(c: ?*const Counter, fallback: c_int) -> c_int {
    let ptr = c orelse return fallback;
    return (*ptr).val;
}

export fn counter_nonnull_if_positive(c: *mut Counter) -> ?*mut Counter {
    if (*c).val > (0 as c_int) {
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
    let mut cnt = Counter { val: 5 as c_int };
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
        assert!(header.contains("typedef struct Counter Counter;"), "Header:\n{header}");
        assert!(header.contains("typedef enum MathErr {"), "Header:\n{header}");
        assert!(header.contains("MathErr_DivByZero = 0,"), "Header:\n{header}");
        assert!(header.contains("typedef uint64_t HandleId;"), "Header:\n{header}");
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
            header.contains("bool make_point_if_valid(int x, int y, bool ok, /* out */ Point* out_val);"),
            "Header:\n{header}"
        );
        assert!(
            header.contains("bool checked_div(int a, int b, /* out */ MathErr* out_err, /* out */ int* out_val);"),
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
export struct Counter { pub val: i32 }
export fn counter_inc(c: *mut Counter) -> i32 {
    (*c).val = (*c).val + 1;
    return (*c).val;
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
        // 1. Passing `export struct` by value in `export fn`
        let err_struct_val = Compiler::compile_source(
            r#"
export struct Engine { x: i32 }
export fn take_engine(e: Engine) -> i32 { return 0; }
pub fn main() -> i32 { return 0; }
"#,
        )
        .expect_err("Expected passing `export struct` by value in `export fn` to be rejected");
        assert!(
            err_struct_val.contains("'export struct' is an opaque handle type and must be passed behind a raw pointer"),
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
            err_bare_arr.contains("Bare fixed-size array '[i32; 4]' cannot be passed or returned by value"),
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
    }
}



