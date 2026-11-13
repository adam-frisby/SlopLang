use super::*;

#[test]
fn test_compile_package_from_directory() {
    let dir = std::env::temp_dir().join(format!("sloplang_pkg_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("src/net")).unwrap();
    std::fs::write(
        dir.join("src/main.slop"),
        "import root::net::http::get;\npub fn main() -> i32 { return get(); }",
    )
    .unwrap();
    std::fs::write(dir.join("src/net/http.slop"), "pub fn get() -> i32 { return 42; }").unwrap();
    let modules = Compiler::load_package_dir(&dir).expect("load");
    let names: Vec<&str> = modules.iter().map(|(m, _)| m.as_str()).collect();
    assert_eq!(names, vec!["root", "root::net::http"]);
    Compiler::compile_package_dir(&dir).expect("package compiles");
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_design_md_examples_compile() {
    // Every ```rust block in DESIGN.md compiles (with a trivial `main` added when it has none);
    // fragments and pseudo-code are fenced ```rust,ignore.
    let design = include_str!("../../../DESIGN.md");
    let mut lines = design.lines().enumerate();
    let mut checked = 0;
    while let Some((i, line)) = lines.next() {
        if line.trim_start() != "```rust" {
            continue;
        }
        let indent = line.len() - line.trim_start().len();
        let mut block = String::new();
        for (_, l) in lines.by_ref() {
            if l.trim_start() == "```" {
                break;
            }
            block.push_str(l.get(indent..).unwrap_or(l.trim_start()));
            block.push('\n');
        }
        if !block.contains("fn main(") {
            block.push_str("pub fn main() -> i32 { return 0; }\n");
        }
        if let Err(e) = Compiler::compile_source(&block) {
            panic!("DESIGN.md example at line {} does not compile: {e}\n{block}", i + 1);
        }
        checked += 1;
    }
    assert!(checked >= 15, "only {checked} DESIGN.md examples found");
}

#[test]
fn test_design_md_soundness_audit_fixes() {
    // 1. `borrows(*x)` is rejected when reborrowing through a safe `&mut T` (since `x` retains
    //    exclusive access to the same referent unless `x` itself stays borrowed):
    reject(
        "borrows_contents_through_mut_ref_mut",
        "pub fn split_mut(x: &mut &mut i32) -> &mut i32 borrows(*x) { return &mut **x; }\npub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'x'",
    );
    reject(
        "borrows_contents_through_mut_ref_shared",
        "pub fn split_shared(x: &&mut i32) -> &i32 borrows(*x) { return &**x; }\npub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'x'",
    );

    // 2. `borrows(*self)` is rejected when taking a reference behind an `*own` or raw pointer:
    reject(
        "borrows_contents_through_own_ptr",
        "pub opaque OwnBox {
    p: *own i32,
    pub fn get(&self) -> &i32 borrows(*self) { unsafe { return &*self.p; } }
}
pub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'self'",
    );
    reject(
        "borrows_contents_ref_to_own_ref_box",
        "pub opaque OwnRef {
    p: *own &i32,
    pub fn get(&self) -> &&i32 borrows(*self) { unsafe { return &*self.p; } }
}
pub fn main() -> i32 { return 0; }",
        "return value borrows from parameter 'self'",
    );

    // 3. Reborrowing an iterator (`let r2 = &mut *r1`) and calling a `borrows(*self)` method
    //    cannot let the yielded element outlive the sequence borrowed by the iterator:
    reject(
        "reborrow_chain_borrows_contents_dangling",
        "pub opaque Iter {
    p: *ref i32,
    pub fn new(x: &i32) -> Self { return Self { p: x as *ref i32 }; }
    pub fn next(&mut self) -> &i32 borrows(*self) { unsafe { return &*self.p; } }
}
pub fn main() -> i32 {
    let dummy: i32 = 0;
    let mut out: &i32 = &dummy;
    if true {
        let local: i32 = 99;
        let mut it = Iter::new(&local);
        let r1: &mut Iter = &mut it;
        let r2: &mut Iter = &mut *r1;
        out = r2.next();
    }
    return *out;
}",
        "goes out of scope while still borrowed",
    );

    // 4. Interprocedural summary inference tracks flows through local containers, reborrows,
    //    and references into by-value composite parameters:
    reject(
        "infer_flow_via_local_container",
        "struct Slot { r: &i32 }
fn indirect_stash(dst: &mut Slot, x: &i32) {
    let tmp = Slot { r: x };
    *dst = tmp;
}
pub fn main() -> i32 {
    let d: i32 = 0;
    let mut s = Slot { r: &d };
    if true {
        let short: i32 = 10;
        indirect_stash(&mut s, &short);
    }
    return *s.r;
}",
        "goes out of scope while still borrowed",
    );
    reject(
        "infer_flow_via_reborrow",
        "struct Slot { r: &i32 }
fn reborrow_stash(dst: &mut Slot, x: &i32) {
    let r: &mut Slot = &mut *dst;
    r.r = x;
}
pub fn main() -> i32 {
    let d: i32 = 0;
    let mut s = Slot { r: &d };
    if true {
        let short: i32 = 10;
        reborrow_stash(&mut s, &short);
    }
    return *s.r;
}",
        "goes out of scope while still borrowed",
    );
    reject(
        "infer_return_from_by_value_composite_param",
        "struct Wrap { r: &i32 }
fn extract(w: Wrap) -> &i32 {
    let p: &&i32 = &w.r;
    return *p;
}
pub fn main() -> i32 {
    let d: i32 = 0;
    let mut out: &i32 = &d;
    if true {
        let short: i32 = 10;
        let w = Wrap { r: &short };
        out = extract(w);
    }
    return *out;
}",
        "goes out of scope while still borrowed",
    );

    // 5. Escaping a borrow of a local stack variable or by-value parameter through a mutable
    //    reference parameter is rejected:
    reject(
        "escape_local_borrow_through_mut_param",
        "struct Slot { r: &i32 }
fn escape(out: &mut Slot) {
    let local: i32 = 42;
    out.r = &local;
}
pub fn main() -> i32 { return 0; }",
        "goes out of scope while still borrowed",
    );
    reject(
        "escape_by_val_param_borrow_through_mut_param",
        "struct Slot { r: &i32 }
fn escape_param(out: &mut Slot, val: i32) {
    out.r = &val;
}
pub fn main() -> i32 { return 0; }",
        "escapes through parameter",
    );

    // 6. `cell` field soundness:
    //    (a) Taking a safe `&` or `&mut` reference or slice to a `cell` field is rejected:
    reject(
        "safe_ref_to_cell_field",
        "pub opaque CellBox {
    cell v: i32,
    pub fn borrow_it(&self) -> &i32 { return &self.v; }
}
pub fn main() -> i32 { return 0; }",
        "Cannot take a safe reference ('&' or '&mut') to 'cell' field 'CellBox.v'",
    );
    reject(
        "safe_slice_to_cell_field",
        "pub opaque CellArr {
    cell buf: array[i32; 4],
    pub fn slice_it(&self) -> &slice[i32] { return &self.buf[0..2]; }
}
pub fn main() -> i32 { return 0; }",
        "Cannot take a safe slice reference to 'cell' field 'CellArr.buf'",
    );
    //    (b) Casting `&self` to `*mut Self` on an `opaque` that has a `cell` field (but NOT
    //        `unsafe sync`) is rejected so non-`cell` sibling fields cannot be mutated behind `&Self`:
    reject(
        "cast_shared_self_to_mut_ptr_with_only_cell_field",
        "pub opaque Mixed {
    cell count: i32,
    imm: i32,
    pub fn bad(&self) {
        let p = self as *mut Self;
        unsafe { (*p).imm = 99; }
    }
}
pub fn main() -> i32 { return 0; }",
        "Cannot cast shared reference '&Mixed' to '*mut Mixed'",
    );

    // 7. `unsafe impl drop(may_dangle T)` soundness:
    //    (a) A type with `unsafe impl drop(may_dangle T)` that also holds a direct `&i32` field
    //        not covered by `T` cannot let that `&i32` dangle at drop:
    reject(
        "may_dangle_with_uncovered_ref_field",
        "fn BadBox[T]() -> type {
    return opaque {
        val: T,
         spy: &i32,
        pub fn new(val: T, spy: &i32) -> Self { return Self { val: val, spy: spy }; }
        unsafe impl drop(may_dangle T) {
            fn drop(&mut self) {
                let _ = *self.spy;
            }
        }
    };
}
pub fn main() -> i32 {
    let d: i32 = 1;
    let mut b = BadBox[i32]::new(0, &d);
    let short: i32 = 2;
    b = BadBox[i32]::new(0, &short);
    return 0;
}",
        "goes out of scope while still borrowed",
    );
    //    (b) Dropping a `may_dangle` field (`Vec[&i32]`) of an enclosing struct must not erase
    //        active loans held by a sibling field (`Peek`) whose drop reads its borrow:
    reject(
        "dangling_drop_ptr_does_not_erase_sibling_loan",
        "opaque Peek {
    r: &i32,
    pub fn new(r: &i32) -> Self { return Self { r: r }; }
    impl drop {
        fn drop(&mut self) {
            let _ = *self.r;
        }
    }
}
struct Both {
    v: Vec[&i32],
    p: Peek,
}
pub fn main() -> i32 {
    let d: i32 = 1;
    let mut b = Both { v: Vec[&i32]::new(), p: Peek::new(&d) };
    let short: i32 = 2;
    b.p = Peek::new(&short);
    return 0;
}",
        "goes out of scope while still borrowed",
    );

    // 8. `Channel[T]` borrow tracking across `send`, `try_send`, `recv`, and `@select`:
    reject(
        "channel_send_borrow_outlives_referent",
        "pub fn main() -> i32 {
    let ch = Channel[&i32]::new();
    let d: i32 = 0;
    let mut r: &i32 = &d;
    if true {
        let short: i32 = 42;
        _ = ch.send(&short);
        r = (ch.recv() catch |e| unreachable);
    }
    return *r;
}",
        "goes out of scope while still borrowed",
    );
    reject(
        "channel_select_send_recv_borrow_outlives_referent",
        "pub fn main() -> i32 {
    let ch = Channel[&i32]::new();
    let d: i32 = 0;
    let mut r: &i32 = &d;
    if true {
        let short: i32 = 42;
        let _ = @select {
            ch.send(&short) => 1,
        };
        r = @select {
            v = ch.recv() => v,
        };
    }
    return *r;
}",
        "goes out of scope while still borrowed",
    );
}

#[test]
fn test_printing() {
    let run = |name: &str, body: &str| {
        let src = format!("pub struct P {{ x: i32 }}\npub fn main() -> i32 {{ {body} return 0; }}");
        let program = Compiler::compile_source(&src).unwrap_or_else(|e| panic!("[{name}] {e}"));
        let ir = crate::llvm::LlvmLowering::lower_with_trap_exit(&program, 222).unwrap();
        let out = crate::tests::lli(&ir);
        assert_eq!(out.status.code(), Some(0), "[{name}] {}", String::from_utf8_lossy(&out.stderr));
        (String::from_utf8_lossy(&out.stdout).into_owned(), String::from_utf8_lossy(&out.stderr).into_owned())
    };
    for (name, body, stdout, stderr) in [
        ("integer", "let _n = println(5);", "5\n", ""),
        ("no_binding", "println(5);", "5\n", ""),
        ("variable", "let x: i32 = -12; println(x);", "-12\n", ""),
        ("string", "println(\"hi\");", "hi\n", ""),
        ("without_a_newline", "print(1); print(\"a\");", "1a", ""),
        ("print_str", "let _n = std::io::print_str(\"raw\");", "raw", ""),
        ("to_stderr", "eprint(7); eprintln(\"e\");", "", "7e\n"),
        ("owned_string", "let s = String::from(\"owned\"); println(s.as_str());", "owned\n", ""),
    ] {
        let (out, err) = run(name, body);
        assert_eq!((out.as_str(), err.as_str()), (stdout, stderr), "[{name}]");
    }
    // Nothing is cut off, however long it is.
    let long = "let mut s = String::new(); for i in 0..2000 { s.push_byte(120); }";
    for (name, body, fd_is_stdout, bytes) in [
        ("long_println", format!("{long} println(s.as_str());"), true, 2001),
        ("just_over_the_buffer", "let mut s = String::new(); for i in 0..512 { s.push_byte(120); } println(s.as_str());".to_string(), true, 513),
        ("exactly_the_buffer", "let mut s = String::new(); for i in 0..511 { s.push_byte(120); } println(s.as_str());".to_string(), true, 512),
        ("long_interpolation", format!("{long} let t = s.as_str(); print(f\"<{{t}}>\");"), true, 2002),
        ("long_eprintln", format!("{long} eprintln(s.as_str());"), false, 2001),
    ] {
        let (out, err) = run(name, &body);
        assert_eq!(if fd_is_stdout { out.len() } else { err.len() }, bytes, "[{name}]");
    }
    assert_runs(
        "format_is_whole",
        "pub fn main() -> i32 { let mut s = String::new(); for i in 0..2000 { s.push_byte(120); } let t = format(s.as_str()); return (t.len() / 100) as i32; }",
        20,
    );
}

// Each example is a test of its own, so that they run in parallel.
#[test]
fn test_example_kvstore() {
    let (code, out) = example_natively("kvstore", KVSTORE);
    assert_eq!(code, Some(3), "{out}");
    // The clients run together, so they finish in any order.
    let mut lines: Vec<&str> = out.lines().collect();
    lines.sort();
    assert_eq!(lines, ["6 requests, 0 failures", "alpha = one", "beta = two", "gamma = three"]);
    for seed in [None, Some(1), Some(2), Some(3)] {
        let (value, out) = example_checked("kvstore", KVSTORE, seed);
        assert_eq!(value, 3);
        assert!(out.contains("6 requests, 0 failures"), "{out}");
    }
}

#[test]
fn test_example_httpd() {
    // The port it listens on differs each run.
    let without_port = |out: &str| -> String {
        out.lines().filter(|l| !l.starts_with("Port: ")).map(|l| format!("{l}\n")).collect()
    };
    let (code, out) = example_natively("httpd", HTTPD);
    assert_eq!(code, Some(0), "{out}");
    assert_eq!(without_port(&out), "4000 requests handled, 4000 hits, 0 failures\n");
    let small = HTTPD
        .replace("const CLIENTS: i32 = 200;", "const CLIENTS: i32 = 4;")
        .replace("const REQUESTS: i32 = 20;", "const REQUESTS: i32 = 5;");
    for seed in [None, Some(1), Some(2), Some(3)] {
        let (value, out) = example_checked("httpd", &small, seed);
        assert_eq!((value, without_port(&out).as_str()), (0, "20 requests handled, 20 hits, 0 failures\n"));
    }
}

#[test]
fn test_example_serve() {
    // Built natively and run on a port the system picks, it answers real connections until it
    // is stopped.
    let src = SERVE.replace("const PORT: u16 = 8080;", "const PORT: u16 = 0;");
    assert_ne!(src, SERVE, "the example declares PORT");
    let program = Compiler::compile_source(&src).unwrap_or_else(|e| panic!("{e}"));
    let ir = crate::llvm::LlvmLowering::lower(&program).unwrap();
    let bin = crate::tests::link_ir("serve", &ir);
    let mut child = std::process::Command::new(bin.path())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    let mut first = String::new();
    std::io::BufRead::read_line(
        &mut std::io::BufReader::new(child.stdout.as_mut().unwrap()),
        &mut first,
    )
    .unwrap();
    let port: u16 = first
        .trim()
        .strip_prefix("listening on http://localhost:")
        .and_then(|p| p.strip_suffix('/'))
        .and_then(|p| p.parse().ok())
        .unwrap_or_else(|| panic!("{first}"));
    let get = |path: &str| -> String {
        use std::io::{Read, Write};
        let mut conn = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        conn.set_read_timeout(Some(std::time::Duration::from_secs(10))).unwrap();
        write!(conn, "GET {path} HTTP/1.1\r\nHost: localhost\r\n\r\n").unwrap();
        let mut reply = String::new();
        conn.read_to_string(&mut reply).unwrap();
        reply
    };
    let body = |reply: &str| reply.split_once("\r\n\r\n").map(|(_, b)| b.to_string()).unwrap_or_default();
    assert_eq!(body(&get("/hits/home")), "1\n");
    assert_eq!(body(&get("/hits/home")), "2\n");
    assert_eq!(body(&get("/hits/about")), "1\n");
    // More connections at once than it serves at a time.
    let threads: Vec<_> = (0..40).map(|_| std::thread::spawn(move || {
        use std::io::{Read, Write};
        let mut conn = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        conn.set_read_timeout(Some(std::time::Duration::from_secs(10))).unwrap();
        write!(conn, "GET /hits/load HTTP/1.1\r\n\r\n").unwrap();
        let mut reply = String::new();
        conn.read_to_string(&mut reply).unwrap();
    })).collect();
    for t in threads {
        t.join().unwrap();
    }
    assert_eq!(body(&get("/total")), "43\n");
    let missing = get("/nope");
    assert!(missing.starts_with("HTTP/1.1 404 Not Found"), "{missing}");
    assert!(get("/").contains("GET /hits/<name>"));
    child.kill().unwrap();
    let _ = child.wait();
}

#[test]
fn test_example_wordcount() {
    let (code, out) = example_natively("wordcount", WORDCOUNT);
    assert_eq!(code, Some(11), "{out}");
    assert!(out.starts_with(" 120 the\n"), "{out}");
    assert!(out.ends_with("500 words, 11 different\n"), "{out}");
    let (value, out) = example_checked("wordcount", WORDCOUNT, None);
    assert_eq!(value, 11);
    assert!(out.ends_with("500 words, 11 different\n"), "{out}");
}

#[test]
fn test_example_script() {
    let (code, out) = example_natively("script", SCRIPT);
    assert_eq!(code, Some(6), "{out}");
    assert_eq!(out, SCRIPT_OUT);
    let (value, out) = example_checked("script", SCRIPT, None);
    assert_eq!((value, out.as_str()), (6, SCRIPT_OUT));
}

#[test]
fn test_example_reflect() {
    let expected = "{\"name\": \"ada\", \"age\": 36, \"active\": true, \"role\": \"Admin\", \"home\": {\"city\": \"london\", \"zip\": 1815}}
parsed: Member
changed: age
changed: home.city
{\"name\": \"ada\", \"age\": 40, \"active\": false, \"role\": \"Admin\", \"home\": {\"city\": \"london\", \"zip\": 1815}}
total of integer fields: 1851
User: 48 bytes
    0  16  name: &str
   16   4  age: i32
   20   1  active: bool
   21   1  role: Role
   24  24  home: Address
labels: london (1815), User
";
    let (code, out) = example_natively("reflect", REFLECT);
    assert_eq!((code, out.as_str()), (Some(2), expected));
    let (value, out) = example_checked("reflect", REFLECT, None);
    assert_eq!((value, out.as_str()), (2, expected));
}

#[test]
fn test_example_ledger() {
    // A package of modules.
    let (code, out) = native_output(&compile_ledger("const EVENTS: i32 = 3000;"));
    assert_eq!(code, Some(0), "{out}");
    assert_eq!(
        out,
        "account 28: 2039.87\naccount 20: 1967.79\naccount 40: 1964.26\n64 accounts, 14932 changes, 98 refused, 110882.87 held\n"
    );
}

#[test]
fn test_example_ledger_tests() {
    // Its test blocks pass, under the VM and natively.
    let ledger = ledger_modules("const EVENTS: i32 = 3000;");
    let refs: Vec<(&str, &str)> = ledger.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let outcomes = crate::testing::run_tests(&refs).unwrap();
    assert_eq!(outcomes.len(), 7);
    for o in &outcomes {
        assert_eq!(o.result, Ok(()), "[ledger test '{}']", o.name);
        assert_eq!(crate::testing::run_native(&refs, o.index), Ok(()), "[ledger test '{}', natively]", o.name);
    }
}

#[test]
fn test_example_ledger_schedules() {
    // Its numbers do not depend on how its workers interleave.
    let mut small = compile_ledger("const EVENTS: i32 = 150;");
    let (code, small_out) = native_output(&small);
    assert_eq!(code, Some(0), "{small_out}");
    for seed in [None, Some(1), Some(2), Some(3)] {
        let run = crate::tests::run_vm_long(&mut small, seed, 30_000_000)
            .unwrap_or_else(|e| panic!("[ledger, seed {seed:?}] {e}"));
        assert_eq!((run.value, run.leaks, run.output.as_str()), (0, 0, small_out.as_str()), "[ledger, seed {seed:?}]");
    }
}

#[test]
fn test_assert() {
    // `@assert(cond)` and `@assert(cond, "message")` trap unless `cond`, saying so with where
    // they are written: on stderr natively, as the error under the VM and at compile time.
    let src = "pub fn main() -> i32 {\n    let x: i32 = 3;\n    @assert(x == 3);\n    @assert(x == 4, \"x is four\");\n    return x;\n}";
    let err = super::run_vm("assert", src).unwrap_err();
    assert_eq!(err, "assertion failed: x is four (line 4, column 5)");
    let program = Compiler::compile_source(src).unwrap();
    let out = crate::tests::lli(&crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT).unwrap());
    assert_eq!(out.status.code(), Some(TRAP_EXIT));
    assert_eq!(String::from_utf8_lossy(&out.stderr), "assertion failed: x is four (line 4, column 5)\n");
    assert_runs("holds", "pub fn main() -> i32 { let x: i32 = 3; @assert(x == 3, \"three\"); return x; }", 3);
    for (name, src, message) in [
        ("at_compile_time", "fn f() -> i32 { @assert(1 == 2, \"never\"); return 1; }\nconst N: i32 = f();\npub fn main() -> i32 { return N; }", "assertion failed: never (line 1, column 17)"),
        // Without a message, the condition as written, on one line.
        ("unnamed", "fn f() -> i32 { @assert(1 + 1 == 3); return 1; }\nconst N: i32 = f();\npub fn main() -> i32 { return N; }", "assertion failed: 1 + 1 == 3 (line 1, column 17)"),
        ("over_lines", "fn f() -> i32 {\n    @assert(1 + 1\n        == 3);\n    return 1;\n}\nconst N: i32 = f();\npub fn main() -> i32 { return N; }", "assertion failed: 1 + 1 == 3 (line 2, column 5)"),
        ("not_a_bool", "pub fn main() -> i32 { @assert(1); return 0; }", "'@assert' takes a 'bool', found 'i32'"),
        ("message_is_a_literal", "pub fn main() -> i32 { let m = \"x\"; @assert(true, m); return 0; }", "the message is a string literal"),
    ] {
        assert_rejected(name, src, message);
    }
}

#[test]
fn test_test_blocks() {
    // `test "name" { ... }` blocks run one by one under the VM, which fails them on a trap, a
    // leak, or undefined behaviour; an ordinary build leaves them out.
    let root = "import root::util;
pub fn main() -> i32 { return 7; }
test \"passes\" { @assert(util::twice(2) == 4); println(\"hello from a test\"); }
test \"asserts\" { @assert(util::twice(2) == 5, \"twice two is five\"); }
test \"leaks\" { let b = Box[i32]::new(1); unsafe { @forget(b); } }
test \"overflows\" { let mut x: u8 = 255; x = x + 1; }
test \"dangles\" { let p: *mut i32 = unsafe { @raw_alloc(4) as *mut i32 }; unsafe { *p = 1; @dealloc(p); let v = *p; } }
";
    let util = "pub fn twice(n: i32) -> i32 { return n * 2; }
fn secret() -> i32 { return 9; }
test \"sees private items\" { @assert(secret() == 9); }
";
    let sources = [("root", root), ("root::util", util)];
    let outcomes = crate::testing::run_tests(&sources).unwrap();
    let results: Vec<(&str, &str, bool)> =
        outcomes.iter().map(|o| (o.module.as_str(), o.name.as_str(), o.result.is_ok())).collect();
    assert_eq!(
        results,
        [
            ("root", "passes", true),
            ("root", "asserts", false),
            ("root", "leaks", false),
            ("root", "overflows", false),
            ("root", "dangles", false),
            ("root::util", "sees private items", true),
        ]
    );
    assert_eq!(outcomes[0].output, "hello from a test\n");
    let why = |i: usize| outcomes[i].result.clone().unwrap_err();
    assert!(why(1).starts_with("assertion failed: twice two is five (line 4, column 18"), "{}", why(1));
    assert_eq!(why(2), "1 heap block(s) leaked");
    assert!(why(4).contains("Undefined behaviour"), "{}", why(4));
    let report = crate::testing::report(&outcomes);
    assert!(report.starts_with("test passes ... ok\ntest asserts ... FAILED: assertion failed"), "{report}");
    assert!(report.ends_with("test root::util: sees private items ... ok\n2 passed, 4 failed\n"), "{report}");

    // An ordinary build has no tests, and its `main` is the package's own.
    let program = Compiler::compile_package(&sources).unwrap();
    assert!(!program.functions.iter().any(|f| f.debug_name.as_deref().is_some_and(|n| n.contains("__slop_test"))));
    assert_eq!(super::run_vm_scheduled(&mut Compiler::compile_package(&sources).unwrap(), None).map(|r| r.value), Ok(7));
    // Natively, one test at a time: its own `main`, with the package's kept aside.
    let native = |index: usize| {
        let program = Compiler::compile_test_entry(&sources, index).unwrap();
        let out = crate::tests::lli(&crate::llvm::LlvmLowering::lower_with_trap_exit(&program, TRAP_EXIT).unwrap());
        (out.status.code(), String::from_utf8_lossy(&out.stderr).into_owned())
    };
    assert_eq!(native(0).0, Some(0));
    assert_eq!(native(1), (Some(TRAP_EXIT), "assertion failed: twice two is five (line 4, column 18)\n".to_string()));
    assert_eq!(native(3).0, Some(TRAP_EXIT));
    assert_eq!(native(5).0, Some(0));
}

#[test]
fn test_slop_command() {
    // `slop run` and `slop test` on a file and on a package directory.
    let dir = std::env::temp_dir().join(format!("sloplang_cli_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(dir.join("pkg/src")).unwrap();
    std::fs::write(
        dir.join("pkg/src/main.slop"),
        "import root::shapes;\npub fn main() -> i32 { println(\"area\"); return shapes::area(2, 3); }\ntest \"area\" { @assert(shapes::area(2, 3) == 6); }\ntest \"area of nothing\" { @assert(shapes::area(0, 3) == 1, \"zero by three\"); }\n",
    )
    .unwrap();
    std::fs::write(
        dir.join("pkg/src/shapes.slop"),
        "pub fn area(w: i32, h: i32) -> i32 { return w * h; }\ntest \"squares\" { @assert(area(4, 4) == 16); }\n",
    )
    .unwrap();
    std::fs::write(dir.join("leaks.slop"), "pub fn main() -> i32 { let b = Box[i32]::new(1); unsafe { @forget(b); } return 0; }").unwrap();
    let slop = |args: &[&str]| {
        let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let code = crate::cli::main_with(&args, &mut out, &mut err);
        (code, String::from_utf8(out).unwrap(), String::from_utf8(err).unwrap())
    };
    let pkg = dir.join("pkg").to_string_lossy().into_owned();
    // `run`: what `main` wrote, and what it returned as the status.
    // `run` builds it natively; `run --vm` runs it under the VM. Both give its output and status.
    assert_eq!(slop(&["run", &pkg]), (6, "area\n".to_string(), String::new()));
    assert_eq!(slop(&["run", "--vm", &pkg]), (6, "area\n".to_string(), String::new()));
    // The program's stdout and stderr go to their own streams, as they are written.
    std::fs::write(dir.join("streams.slop"), "pub fn main() -> i32 { println(\"out\"); eprintln(\"err\"); return 3; }").unwrap();
    let streams = dir.join("streams.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["run", &streams]), (3, "out\n".to_string(), "err\n".to_string()));
    assert_eq!(slop(&["run", &streams, "--vm"]), (3, "out\n".to_string(), "err\n".to_string()));
    // A failed check traps natively, which `run` reports.
    std::fs::write(dir.join("traps.slop"), "fn at(a: &slice[i32], i: usize) -> i32 { return a[i]; }\npub fn main() -> i32 { let v: array[i32; 2] = [1, 2]; println(\"before\"); return at(&v, 5); }").unwrap();
    let traps = dir.join("traps.slop").to_string_lossy().into_owned();
    let (code, output, error) = slop(&["run", &traps]);
    assert_eq!((code, output.as_str()), (crate::cli::FAILED, "before\n"));
    assert!(error.starts_with("error: the program trapped: a check failed"), "{error}");
    let leaks = dir.join("leaks.slop").to_string_lossy().into_owned();
    // Only the VM sees a leak.
    assert_eq!(slop(&["run", "--vm", &leaks]), (crate::cli::FAILED, String::new(), "error: 1 heap block(s) leaked\n".to_string()));
    assert_eq!(slop(&["run", &leaks]).0, 0);
    // `test`: every test, in module order, on however many threads.
    let report = "test area ... ok\ntest area of nothing ... FAILED: assertion failed: zero by three (line 4, column 26)\ntest root::shapes: squares ... ok\n2 passed, 1 failed\n";
    for jobs in ["1", "3"] {
        assert_eq!(slop(&["test", &pkg, "--jobs", jobs]), (1, report.to_string(), String::new()), "--jobs {jobs}");
    }
    assert_eq!(slop(&["test", &pkg, "--filter", "squares"]), (0, "test root::shapes: squares ... ok\n1 passed, 0 failed\n".to_string(), String::new()));
    assert_eq!(slop(&["test", &pkg, "--filter", "shapes: sq"]).0, 0);
    // Natively too: what passes under the VM must pass as compiled code.
    assert_eq!(slop(&["test", &pkg, "--native", "--jobs", "2"]), (1, report.to_string(), String::new()));
    let pkg_sources = Compiler::load_package_dir(&dir.join("pkg")).unwrap();
    let refs: Vec<(&str, &str)> = pkg_sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    assert_eq!(crate::testing::run_native(&refs, 0), Ok(()));
    assert_eq!(
        crate::testing::run_native(&refs, 1),
        Err("natively, trapped: assertion failed: zero by three (line 4, column 26)".to_string())
    );
    // `build`: an executable (with `clang`), or the LLVM IR.
    let exe = dir.join("shapes").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &pkg, "-o", &exe, "-O1"]), (0, format!("built {exe}\n"), String::new()));
    let ran = std::process::Command::new(&exe).output().unwrap();
    assert_eq!((ran.status.code(), String::from_utf8_lossy(&ran.stdout).into_owned()), (Some(6), "area\n".to_string()));
    let ll = dir.join("shapes.ll").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &pkg, "--emit", "ll", "-o", &ll]).0, 0);
    assert!(std::fs::read_to_string(&ll).unwrap().contains("define"), "LLVM IR");
    assert!(slop(&["build", &pkg, "--emit", "wasm"]).2.contains("expected 'exe', 'll', or 'h'"));
    // `--emit h`: the C declarations of what a package exports.
    std::fs::write(
        dir.join("exports.slop"),
        "export error ParseError { Empty }\nexport fn half(n: usize) -> ParseError!usize { if n == 0 { return .Empty; } return n / 2; }\n",
    )
    .unwrap();
    let exports = dir.join("exports.slop").to_string_lossy().into_owned();
    let h = dir.join("exports.h").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &exports, "--emit", "h", "-o", &h]), (0, format!("wrote {h}\n"), String::new()));
    let header = std::fs::read_to_string(&h).unwrap();
    assert!(header.contains("ParseError half(size_t n, /* out */ size_t* out_val);"), "{header}");
    assert!(header.contains("#ifndef SLOPLANG_EXPORT_H"), "{header}");
    let onto_a_directory = dir.join("pkg").to_string_lossy().into_owned();
    assert!(slop(&["build", &pkg, "-o", &onto_a_directory]).2.contains("is a directory; name the executable with '-o'"));
    // `new`: a package that runs, tests, and builds as it is.
    let fresh = dir.join("fresh").to_string_lossy().into_owned();
    assert_eq!(slop(&["new", &fresh]), (0, format!("created package 'fresh' in {fresh}\n"), String::new()));
    assert_eq!(slop(&["run", &fresh]), (0, "hello\n".to_string(), String::new()));
    assert_eq!(slop(&["test", &fresh]), (0, "test greets ... ok\n1 passed, 0 failed\n".to_string(), String::new()));
    assert!(slop(&["new", &fresh]).2.contains("exists already"));
    // `check`: everything `test` and `build` compile, tests included, running nothing; a library
    // needs no `main`. Warnings are printed, by every command.
    assert_eq!(slop(&["check", &pkg]), (0, "checked pkg (3 tests)\n".to_string(), String::new()));
    std::fs::write(dir.join("library.slop"), "pub fn area(w: i32, h: i32) -> i32 { return w * h; }\n").unwrap();
    let library = dir.join("library.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["check", &library]), (0, "checked library (0 tests)\n".to_string(), String::new()));
    assert_eq!(slop(&["run", &library]).2, "error: the package has no 'main'\n");
    std::fs::write(dir.join("bad_test.slop"), "pub fn main() -> i32 { return 0; }\ntest \"t\" { let x: bool = 5; }\n").unwrap();
    let bad_test = dir.join("bad_test.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["run", &bad_test]).0, 0, "run leaves tests out");
    let (code, _, err) = slop(&["check", &bad_test]);
    assert_eq!((code, err.as_str()), (crate::cli::FAILED, "error: Type mismatch: cannot implicitly convert 'i32' to 'bool' (line 2, column 12)\n"));
    std::fs::write(
        dir.join("warned.slop"),
        "opaque(owns T) Holder[T] { p: *own T }\npub fn main() -> i32 { let h: ?Holder[i32] = null; return 0; }\n",
    )
    .unwrap();
    let warned = dir.join("warned.slop").to_string_lossy().into_owned();
    let warning = "warning: 'owns T' on opaque 'Holder' is redundant: a field already holds 'T' behind '*own' or in 'uninit' storage\n";
    assert_eq!(slop(&["check", &warned]), (0, "checked warned (0 tests)\n".to_string(), warning.to_string()));
    assert_eq!(slop(&["run", &warned]), (0, String::new(), warning.to_string()));
    assert_eq!(slop(&["test", &warned]).2, warning);
    // A generic is linted where it is declared, used or not.
    std::fs::write(dir.join("unused.slop"), "opaque(owns T) Holder[T] { p: *own T }\npub fn main() -> i32 { return 0; }\n").unwrap();
    let unused = dir.join("unused.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["check", &unused]), (0, "checked unused (0 tests)\n".to_string(), warning.to_string()));
    // `check --all-targets`: for each C ABI the backend knows. Fibers switch stacks on x86-64
    // only, which a check on this machine alone would not show.
    assert_eq!(
        slop(&["check", &library, "--all-targets"]),
        (0, "checked library (0 tests) for x86_64-linux, aarch64-linux, aarch64-macos, riscv64-linux\n".to_string(), String::new())
    );
    std::fs::write(dir.join("fibers.slop"), "fn one() -> i32 { return 1; }\npub fn main() -> i32 { let t = async(Fibers { }) one(); return t.await(); }\n").unwrap();
    let fibers = dir.join("fibers.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["check", &fibers]).0, 0);
    assert_eq!(
        slop(&["check", "--all-targets", &fibers]),
        (
            crate::cli::FAILED,
            "checked fibers (0 tests) for x86_64-linux\n".to_string(),
            "error: for aarch64-linux: Fibers switch stacks only on x86-64\nerror: for aarch64-macos: Fibers switch stacks only on x86-64\nerror: for riscv64-linux: Fibers switch stacks only on x86-64\n".to_string()
        )
    );
    // A target its manifest refuses is not built for, and not an error.
    std::fs::create_dir_all(dir.join("linux_only/src")).unwrap();
    std::fs::write(dir.join("linux_only/src/main.slop"), "pub fn main() -> i32 { return 0; }\n").unwrap();
    std::fs::write(
        dir.join("linux_only/package.slop"),
        "import std::build::{Package, Target, Dependency};
pub fn package[target: Target]() -> Package {
    if target.os != Target::Os::Linux { @compile_error(\"Linux only\"); }
    return Package { name: \"linux_only\", version: .{ 1, 0, 0 }, root: \"src/main.slop\", no_std: false, deps: &[], system_libs: &[] };
}",
    )
    .unwrap();
    let linux_only = dir.join("linux_only").to_string_lossy().into_owned();
    assert_eq!(
        slop(&["check", &linux_only, "--all-targets"]),
        (0, "checked linux_only (0 tests) for x86_64-linux, aarch64-linux, riscv64-linux\nnot built for aarch64-macos\n".to_string(), String::new())
    );
    // `fmt`: what changes is rewritten; `--check` lists it and fails, changing nothing.
    std::fs::write(dir.join("messy.slop"), "pub fn main() -> i32 {\nlet x = 1;\n\t\treturn x;   \n}\n\n\n").unwrap();
    let messy = dir.join("messy.slop").to_string_lossy().into_owned();
    assert_eq!(slop(&["fmt", &messy, "--check"]), (1, format!("would format {messy}\n"), String::new()));
    assert_eq!(slop(&["fmt", &messy]), (0, format!("formatted {messy}\n"), String::new()));
    assert_eq!(std::fs::read_to_string(dir.join("messy.slop")).unwrap(), "pub fn main() -> i32 {\n    let x = 1;\n    return x;\n}\n");
    assert_eq!(slop(&["fmt", &messy, "--check"]), (0, String::new(), String::new()));
    assert_eq!(slop(&["fmt", &pkg, "--check"]).0, 0, "a package's files");
    // Wrong use says how to use it.
    let (code, _, err) = slop(&["build"]);
    assert_eq!(code, crate::cli::FAILED);
    assert!(err.starts_with("error: usage: slop new <dir>"), "{err}");
    assert!(slop(&["test", &pkg, "--jobs", "many"]).2.contains("'--jobs many' is not a count"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_slop_reads_package_manifests() {
    // A package's `package.slop`, evaluated for the host: its name names the executable, its
    // system libraries are linked, `no_std` compiles it freestanding, and what slop cannot do
    // yet (fetch dependencies) is an error.
    let dir = std::env::temp_dir().join(format!("sloplang_manifest_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let manifest = |name: &str, extra: &str| {
        format!("import std::build::{{Package, Target, Dependency}};
pub fn package[target: Target]() -> Package {{
    return Package {{ name: \"{name}\", version: .{{ 0, 1, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[], system_libs: &[] {extra} }};
}}")
    };
    let make = |pkg: &str, manifest_src: String, main: &str| {
        std::fs::create_dir_all(dir.join(pkg).join("src")).unwrap();
        std::fs::write(dir.join(pkg).join("package.slop"), manifest_src).unwrap();
        std::fs::write(dir.join(pkg).join("src/main.slop"), main).unwrap();
        dir.join(pkg).to_string_lossy().into_owned()
    };
    let slop = |args: &[&str]| {
        let args: Vec<String> = args.iter().map(|a| a.to_string()).collect();
        let (mut out, mut err) = (Vec::new(), Vec::new());
        let code = crate::cli::main_with(&args, &mut out, &mut err);
        (code, String::from_utf8(out).unwrap(), String::from_utf8(err).unwrap())
    };
    let main = "pub fn main() -> i32 { return 5; }\ntest \"five\" { @assert(main() == 5); }";
    let plain = make("plain", manifest("geometry", ""), main);
    // What is built is named after the package, not the directory.
    let package = crate::cli::load(&plain, "Debug").unwrap();
    assert_eq!((package.name.as_str(), package.no_std, package.system_libs.len()), ("geometry", false, 0));
    let exe = dir.join("geometry").to_string_lossy().into_owned();
    assert_eq!(slop(&["build", &plain, "-o", &exe]), (0, format!("built {exe}\n"), String::new()));
    assert_eq!(std::process::Command::new(&exe).status().unwrap().code(), Some(5));
    assert_eq!(slop(&["test", &plain]).0, 0);
    // Its system libraries reach the link: one that does not exist fails it.
    let libs = make("libs", manifest("linked", ", system_libs: &[\"slop_no_such_lib\"]").replace("system_libs: &[] ,", ""), main);
    assert_eq!(crate::cli::load(&libs, "Debug").unwrap().system_libs, ["slop_no_such_lib"]);
    let linked = dir.join("linked").to_string_lossy().into_owned();
    let (code, _, err) = slop(&["build", &libs, "-o", &linked]);
    assert_eq!(code, crate::cli::FAILED);
    assert!(err.contains("slop_no_such_lib"), "{err}");
    // `no_std`: freestanding, with `core` only.
    let free = make("free", manifest("free", "").replace("no_std: false", "no_std: true"), "pub fn main() -> i32 { return 3; }");
    assert_eq!(slop(&["run", &free]).0, 3);
    let needs_std = make("needs_std", manifest("needs_std", "").replace("no_std: false", "no_std: true"), "pub fn main() -> i32 { println(\"x\"); return 0; }");
    assert_eq!(slop(&["run", &needs_std]).0, crate::cli::FAILED);
    // A dependency that is not where its manifest says.
    let deps = make("deps", manifest("deps", "").replace("deps: &[]", "deps: &[Dependency { name: \"tls\", url: \"missing.tar\", sha256: 1_u256 }]"), main);
    assert!(slop(&["run", &deps]).2.contains("missing.tar"), "{:?}", slop(&["run", &deps]));
    let rooted = make("rooted", manifest("rooted", "").replace("src/main.slop", "lib/app.slop"), main);
    assert!(slop(&["run", &rooted]).2.contains("has root 'lib/app.slop'"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_tour() {
    // Each `slop` block in TOUR.md runs, under the VM and natively, and its `main` returns 0;
    // each `slop rejected` block is refused with what its first line, `// error: ...`, says.
    let tour = include_str!("../../../TOUR.md");
    let mut blocks = 0;
    let mut lines = tour.lines().enumerate();
    while let Some((at, line)) = lines.next() {
        let Some(info) = line.strip_prefix("```slop") else { continue };
        let body: Vec<&str> = lines.by_ref().map(|(_, l)| l).take_while(|l| *l != "```").collect();
        let src = body.join("\n");
        let name = format!("TOUR.md line {}", at + 1);
        match info.trim() {
            "" => assert_runs(&name, &src, 0),
            "rejected" => {
                let what = body[0].strip_prefix("// error: ").unwrap_or_else(|| panic!("[{name}] starts with '// error: '"));
                assert_rejected(&name, &src, what);
            }
            other => panic!("[{name}] unknown block kind '{other}'"),
        }
        blocks += 1;
    }
    assert!(blocks >= 10, "{blocks} blocks");
}

#[test]
fn test_readme() {
    // Every `slop` block in README.md compiles and runs (or, for the C FFI library block without
    // `main`, compiles and emits the documented C header declarations).
    let readme = include_str!("../../../README.md");
    let mut blocks = 0;
    let mut lines = readme.lines().enumerate();
    while let Some((at, line)) = lines.next() {
        let Some(info) = line.strip_prefix("```slop") else { continue };
        let body: Vec<&str> = lines.by_ref().map(|(_, l)| l).take_while(|l| *l != "```").collect();
        let src = body.join("\n");
        let name = format!("README.md line {}", at + 1);
        assert_eq!(info.trim(), "", "[{name}] unexpected block kind '{info}'");
        if src.contains("pub fn main()") {
            assert_runs(&name, &src, 0);
        } else {
            let (prog, header) = crate::lower::Compiler::compile_source_with_c_header(&src)
                .unwrap_or_else(|e| panic!("[{name}] failed to compile: {e}"));
            crate::llvm::LlvmLowering::lower(&prog)
                .unwrap_or_else(|e| panic!("[{name}] failed to lower to LLVM IR: {e}"));
            assert!(header.contains("bool digit_value(uint8_t c, /* out */ uint8_t* out_val);"), "{header}");
            assert!(header.contains("ParseError parse_u32(const uint8_t* s, size_t len, /* out */ uint32_t* out_val);"), "{header}");
        }
        blocks += 1;
    }
    assert!(blocks >= 10, "{blocks} blocks");
}

#[test]
fn test_package_dependencies() {
    // A manifest's dependencies are fetched, checked against their SHA-256, unpacked into a
    // cache, and mounted under their names, with their own `root` meaning themselves.
    let dir = std::env::temp_dir().join(format!("sloplang_deps_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    let write = |path: &str, text: &str| {
        let p = dir.join(path);
        std::fs::create_dir_all(p.parent().unwrap()).unwrap();
        std::fs::write(p, text).unwrap();
    };
    let manifest = |name: &str, deps: &str, libs: &str| {
        format!("import std::build::{{Package, Target, Dependency}};
pub fn package[target: Target]() -> Package {{
    return Package {{ name: \"{name}\", version: .{{ 1, 0, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[{deps}], system_libs: &[{libs}] }};
}}")
    };
    // The dependency, as its author wrote it: the root of its own build.
    write("shapes/package.slop", &manifest("shapes", "", "\"m\""));
    write("shapes/src/main.slop", "import root::util;\npub fn area(w: i32, h: i32) -> i32 { return util::mul(w, h); }\npub fn twice(x: i32) -> i32 { return root::util::mul(x, 2); }\ntest \"its own\" { @assert(area(2, 2) == 4); }\n");
    write("shapes/src/util.slop", "pub fn mul(a: i32, b: i32) -> i32 { return a * b; }\n");
    let tar = std::process::Command::new("tar").current_dir(&dir).args(["-cf", "shapes.tar", "shapes"]).status().unwrap();
    assert!(tar.success());
    let archive = std::fs::read(dir.join("shapes.tar")).unwrap();
    let hash = crate::sha256::hex(&crate::sha256::digest(&archive));
    let dep = |hash: &str| format!("Dependency {{ name: \"shapes\", url: \"../shapes.tar\", sha256: 0x{hash}_u256 }}");
    write("app/package.slop", &manifest("app", &dep(&hash), ""));
    write("app/src/main.slop", "import shapes;\npub fn main() -> i32 { return shapes::area(2, 3) + shapes::twice(1); }\n");
    let build = crate::packages::BuildFor {
        os: "Linux".to_string(),
        arch: "X86_64".to_string(),
        optimize: "Debug".to_string(),
        cache: dir.join("cache"),
    };
    let load = || crate::packages::load_package(&dir.join("app"), &build);
    let run = |pkg: &crate::packages::LoadedPackage| {
        let refs: Vec<(&str, &str)> = pkg.sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
        let mut program = Compiler::compile_package(&refs).unwrap_or_else(|e| panic!("{e}"));
        super::run_vm_scheduled(&mut program, None).map(|r| r.value)
    };
    let pkg = load().unwrap();
    let mut modules: Vec<&str> = pkg.sources.iter().map(|(m, _)| m.as_str()).collect();
    modules.sort();
    assert_eq!(modules, ["root", "shapes", "shapes::util"]);
    assert_eq!(pkg.system_libs, ["m"], "a dependency's libraries are linked too");
    assert_eq!(run(&pkg), Ok(8));
    // The dependency's tests stay its own: a build of the app runs none of them.
    let refs: Vec<(&str, &str)> = pkg.sources.iter().map(|(m, s)| (m.as_str(), s.as_str())).collect();
    let outcomes = crate::testing::run_tests(&refs).unwrap();
    assert!(outcomes.is_empty(), "{outcomes:?}");
    // Fetched once: from the cache when the archive is gone.
    std::fs::remove_file(dir.join("shapes.tar")).unwrap();
    assert_eq!(run(&load().unwrap()), Ok(8));
    // Fetching writes the lock, and a build holds to it.
    let fetch = |targets: &[crate::packages::BuildFor]| crate::packages::fetch_package(&dir.join("app"), targets);
    let lock = fetch(std::slice::from_ref(&build)).unwrap().lock;
    let text = std::fs::read_to_string(&lock).unwrap();
    assert!(text.contains(&format!("\nshapes {hash} ../shapes.tar\n")), "{text}");
    assert_eq!(run(&load().unwrap()), Ok(8));
    let zeros = "0".repeat(64);
    std::fs::write(&lock, text.replace(&hash, &zeros)).unwrap();
    let err = load().unwrap_err();
    assert!(err.contains(&format!("has SHA-256 {hash}, but package.lock says {zeros}; run 'slop fetch'")), "{err}");
    std::fs::write(&lock, "# nothing\n").unwrap();
    assert!(load().unwrap_err().contains("dependency 'shapes' is not in package.lock"));
    std::fs::write(&lock, "shapes\n").unwrap();
    assert!(load().unwrap_err().contains("is not 'name sha256 url'"));
    // A fetch writes what the targets need and nothing else.
    std::fs::write(&lock, format!("other {} x.tar\n", "a".repeat(64))).unwrap();
    fetch(std::slice::from_ref(&build)).unwrap();
    let text = std::fs::read_to_string(&lock).unwrap();
    assert!(text.contains(&format!("shapes {hash} ")) && !text.contains("other "), "{text}");
    // A dependency only one target has is locked by a fetch for every target, and a target
    // the manifest refuses is skipped.
    let per_target = format!("import std::build::{{Package, Target, Dependency}};
pub fn package[target: Target]() -> Package {{
    if target.arch == Target::Arch::Wasm32 {{ @compile_error(\"no wasm\"); }}
    if target.os == Target::Os::Windows {{
        return Package {{ name: \"app\", version: .{{ 1, 0, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[{}], system_libs: &[] }};
    }}
    return Package {{ name: \"app\", version: .{{ 1, 0, 0 }}, root: \"src/main.slop\", no_std: false, deps: &[], system_libs: &[] }};
}}", dep(&hash));
    write("app/package.slop", &per_target);
    let linux_only = fetch(std::slice::from_ref(&build)).unwrap();
    assert!(linux_only.deps.is_empty(), "{linux_only:?}");
    let every = fetch(&crate::packages::all_targets(&build.cache)).unwrap();
    assert_eq!(every.deps.iter().map(|d| d.name.as_str()).collect::<Vec<_>>(), ["shapes"]);
    assert_eq!(every.refused, 20, "every OS and mode on Wasm32");
    std::fs::remove_file(&lock).unwrap();
    write("app/package.slop", &manifest("app", &dep(&hash), ""));
    // A hash that does not match what is downloaded is refused.
    std::fs::write(dir.join("shapes.tar"), &archive).unwrap();
    // The archive's hash differs from run to run (tar records times), so the last digit is
    // changed to one it is not.
    let last = if hash.ends_with('0') { '1' } else { '0' };
    let wrong = format!("{}{last}", &hash[..63]);
    write("app/package.slop", &manifest("app", &dep(&wrong), ""));
    let err = load().unwrap_err();
    assert!(err.contains(&format!("has SHA-256 {hash}, but the manifest says {wrong}")), "{err}");
    write("app/package.slop", &manifest("app", "Dependency { name: \"std\", url: \"x.tar\", sha256: 1_u256 }", ""));
    assert!(load().unwrap_err().contains("a dependency cannot be named 'std'"));
    let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn test_what_the_ledger_example_found() {
    // Each was found writing `examples/ledger`.
    for (name, src, value) in [
        // A type parameter inside a type call inside another (`T` in `Box[N[T]]`) is inferred.
        ("infer_nested", "struct N[T] { v: T }\nfn f[T: copy](a: &Box[N[T]]) -> T { return a.get().v; }\npub fn main() -> i32 { let b = Box[N[i32]]::new(N[i32] { v: 4 }); return f(&b); }", 4),
        ("infer_nested_optional", "struct N[T] { v: T }\nfn f[T: copy](a: &?Box[N[T]], x: T) -> T { if let ?ref b = *a { return b.get().v; } return x; }\npub fn main() -> i32 { let b: ?Box[N[i32]] = null; return f(&b, 5); }", 5),
        // A `&mut self` call's arguments are read before its borrow starts, places as well as
        // calls: `s.r(s.n)`, through a reference too.
        ("arg_reads_receiver", "struct S { n: u64, pub fn r(&mut self, b: u64) -> u64 { self.n = b + 1; return self.n; } }\npub fn main() -> i32 { let mut s = S { n: 1 }; let a = s.r(s.n); let m = &mut s; return (a + m.r(m.n)) as i32; }", 5),
        // Storing into a container does not store into what the container already borrows.
        ("store_reaches_the_container", "fn eat(v: Vec[tuple { &Vec[i64], &i32 }]) -> i32 { return v.len() as i32; }\npub fn main() -> i32 { let a = Vec[i64]::new(); let mut b: i32 = 1; let mut keep = Vec[tuple { &Vec[i64], &i32 }]::new(); keep.push(.{ &a, &b }); keep.push(.{ &a, &b }); let n = eat(keep); b = 2; return n + b + a.len() as i32; }", 4),
        ("tasks_borrowing_an_array", "fn f(m: &array[Vec[i64]; 2], w: u64) -> i32 { return 1; }\npub fn main() -> i32 { let m: array[Vec[i64]; 2] = [Vec[i64]::new(), Vec[i64]::new()]; let pool = WorkerPool::new(2); let mut tasks = Vec[Task[i32]]::new(); tasks.push(async(&pool) f(&m, 1)); tasks.push(async(&pool) f(&m, 2)); let mut n = 0; while let ?t = tasks.pop() { n = n + t.await(); } return n; }", 2),
        // A field of what a trait method returns evaluates the call once.
        ("field_of_await", "struct P { a: i32 }\nfn g() -> P { return P { a: 3 }; }\npub fn main() -> i32 { let t = async g(); return t.await().a; }", 3),
        ("packed_field_of_a_call", "packed struct F { lo: u4, hi: u4 }\nfn mk() -> F { return F { lo: 2, hi: 5 }; }\npub fn main() -> i32 { return mk().hi as i32 + mk().bits as i32; }", 13),
        // `Vec::insert` and `Vec::remove` shift what follows, and drop what they should.
        ("vec_insert_remove", "pub fn main() -> i32 { let mut v = Vec[Box[i32]]::new(); v.push(Box[i32]::new(1)); v.insert(0, Box[i32]::new(2)); v.insert(2, Box[i32]::new(3)); v.insert(1, Box[i32]::new(4)); let r = v.remove(0) orelse unreachable; if v.remove(9) != null { return 99; } return r.into_inner() * 100 + *(v.get(0) orelse unreachable).get() * 10 + *(v.get(2) orelse unreachable).get(); }", 243),
    ] {
        assert_runs(name, src, value);
    }
    for (name, src, message) in [
        ("arg_still_borrowing_receiver", "struct S { n: u64, pub fn k(&mut self, r: &u64) -> u64 { return *r; } }\npub fn main() -> i32 { let mut s = S { n: 1 }; return s.k(&s.n) as i32; }", "already borrowed"),
        ("store_still_tracked", "pub fn main() -> i32 { let mut keep = Vec[&i32]::new(); if true { let x: i32 = 1; keep.push(&x); } return keep.len() as i32; }", "goes out of scope while still borrowed"),
    ] {
        assert_rejected(name, src, message);
    }
}

