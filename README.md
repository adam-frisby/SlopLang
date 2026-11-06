# SlopLang

As the name implies, this is 100% AI generated compiler. 

SlopLang is a systems language that combines Rust's memory safety (ownership, moves,
destructors, borrow checking, and `linear` types that must be consumed) with Zig's `comptime`:
types are values, generics are functions that take them, and compile-time code replaces
macros. It compiles through LLVM, and runs under a checking VM that stops on a leak, a use after
free, an aliasing violation, or a data race.

## Why?

1. Experimentation - Testing the abilities of LLMs
2. Exploration - Exploring ideas without committing to long development cycles

## Is it sound?

Maybe.

## Should I use it?

Probably not.

## Example

```slop
error ParseError { Empty, NotADigit(u8) }

fn parse(s: &str) -> ParseError!u32 {
    if s.len == 0 {
        return .Empty;
    }
    let mut n: u32 = 0;
    for i in 0..s.len {
        let c = s[i];            // a `&str` is its UTF-8 bytes
        if c < 48 || c > 57 {
            return .NotADigit(c);
        }
        n = n * 10 + (c - 48) as u32;
    }
    return n;
}

pub fn main() -> i32 {
    let n = parse("42") catch |e| {
        println(f"not a number: {e}");
        return 1;
    };
    println(f"parsed {n}");
    return 0;
}
```

`E!T` is a value of type `T` or an error from `E`. The caller handles the error with `catch`,
or passes it on with `try`.

Generics are functions run at compile time, and the same code can read a type's shape:

```slop
/// A type function: run at compile time, it returns a new type.
fn Pair[T] -> type {
    return struct { first: T, second: T };
}

struct Point { x: i32, y: i32, label: &str }

/// Prints the fields of any struct: one function, unrolled for each type.
fn describe[T: struct](t: &T) {
    println(f"{@type_name(T)}:");
    comptime for f in @fields(T) {
        let value = @field(*t, f.name);
        println(f"  {f.name} = {value}");
    }
}

pub fn main() -> i32 {
    let p = Pair[i64] { first: 2, second: 3 };
    let q = Point { x: 1, y: 2, label: "origin" };
    describe(&p);
    describe(&q);
    return 0;
}
```

This prints:

```text
Pair:
  first = 2
  second = 3
Point:
  x = 1
  y = 2
  label = origin
```

`comptime for` unrolls over the fields `@fields` lists, and `@field` reads one by name. `[T: unchecked]` lets `describe` use whatever each type turns out to have, checked where it is called.

A `struct` is plain data, while an `opaque` keeps its fields to itself:

```slop
/// Plain data: every field is public.
struct Point { x: i32, y: i32 }

/// An invariant: the fields are private to this block, so only its methods can
/// make or change a `Celsius`, and none is ever below absolute zero.
opaque Celsius {
    degrees: f64,

    pub fn new(degrees: f64) -> ?Self {
        if degrees < -273.15 {
            return null;
        }
        return Self { degrees: degrees };
    }

    pub fn degrees(self: &Self) -> f64 {
        return self.degrees;
    }
}

pub fn main() -> i32 {
    let p = Point { x: 1, y: 2 };
    let t = Celsius::new(21.5) orelse return 1;
    @assert(Celsius::new(-300.0) == null);
    println(f"{p.x + p.y} {t.degrees()}");
    return 0;
}
```

Outside its block, `t.degrees` and `Celsius { degrees: -500.0 }` are compile errors. That leaves the methods as the only way in, so they can keep the invariant. An `opaque` can also define what happens when it is cloned or dropped, and `opaque(linear)` makes a value that must be used up explicitly rather than dropped.

A `linear` value must be used up exactly once, on every path. That makes "forgot to commit" a compile error rather than a bug:

```slop
/// A transaction that must end: committed or rolled back, never just dropped.
opaque(linear) Transaction {
    id: i32,

    pub fn begin(id: i32) -> Self {
        return Self { id: id };
    }

    pub fn commit(move self) -> i32 {
        println(f"commit {self.id}");
        return self.id;
    }

    pub fn rollback(move self) {
        println(f"roll back {self.id}");
    }
}

fn transfer(amount: i32) -> i32 {
    let tx = Transaction::begin(amount);
    if amount < 0 {
        tx.rollback();
        return 0;
    }
    return tx.commit();
}

pub fn main() -> i32 {
    @assert(transfer(5) == 5 && transfer(-1) == 0);
    return 0;
}
```

Take out the `tx.rollback()` and `transfer` no longer compiles:

```text
error: Linear value 'tx' of type 'Transaction' must be explicitly consumed before going out of scope in root::transfer (fn3) (line 22, column 9)
```

Generics accept linear types only when they say so, with `[T: ?linear]`. The standard containers (`Vec`, `Box`, `Mutex`, `Channel`) do.

## Building

You need a recent stable Rust toolchain (edition 2024). `slop build` and `slop test --native`
also need `clang` on the `PATH`.

```sh
cargo build --release      # builds target/release/slop
cargo test --lib           # runs the test suite
```

## Using `slop`

```sh
slop new hello                  # a package: package.slop and src/main.slop
slop run hello                  # runs main under the checking VM
slop test hello [--native]      # runs the test blocks, natively too with --native
slop check hello                # compiles everything, tests included, and runs nothing
slop check hello --all-targets  # the same for each target the backend supports
slop fmt hello [--check]        # lays out the source files
slop build hello [-O3]          # an executable, through LLVM and clang
```

A path can be a single `.slop` file instead of a package directory.

## Learning more

- [TOUR.md](TOUR.md) introduces the language to someone who knows Rust, Zig, or C. The test
  suite runs every example in it.
- [DESIGN.md](DESIGN.md) has the full design, with the reasons for it.
- [examples/](examples) has whole programs: an HTTP server and a key-value store on fibers,
  an interpreter, a word counter, a reflection showcase, and `ledger`, a multi-module package.
- [lib/](lib) is the standard library, written in SlopLang.
