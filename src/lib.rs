pub mod ast;
pub mod borrowck;
pub mod drop;
pub mod frontend;
pub mod ir;
pub mod lexer;
pub mod llvm;
pub mod lower;
pub mod parser;
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
    let c_int = a.clamp(0, 10);          // `number` on i32 -> 10

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
    return c_int + cf_int + nib + ladder;
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

// 2. Must-consume `linear struct` with multiple consuming `move self` methods and shared `drop` cleanup:
pub linear struct Transaction {
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
pub linear struct Ticket {
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
pub linear struct Ticket {
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
pub linear struct Ticket {
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
pub linear struct Ticket {
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
pub linear struct Ticket {
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
}


