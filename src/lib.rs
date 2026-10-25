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
}


