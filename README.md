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

## Are their bugs?

For sure.

## Examples

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

A type parameter's bound can be a kind of type rather than a trait. Every type sits on exactly one branch of this tree:

```
                                                     type
        ┌───────────────────┬─────────────────────────┼─────────────────────────┬──────────────────┬─────────┬─────────┐
     scalar              callable                  sequence                 aggregate        discriminated opaque    simd
   ┌────┼────┬────┐      ╱      ╲                  ╱      ╲                 ╱       ╲        ┌─────┼─────┐
number bool rune *T    fn     closure           array    slice           struct   tuple     enum union error
 ╱   ╲
integer float
 ╱   ╲
signed unsigned
(i1..i512, (u1..u512,
  isize)     usize)
```

A bound names any node, such as `[T: integer]`, `[T: discriminated]` or `[T: sequence]`, and overloads are chosen by the most specific bound that fits. Other bounds cut across the tree: `copy`, `linear`, `send`, `sync`, `default`, `clone` and `format`.

```slop
/// Overloads chosen by kind: the most specific one that fits wins.
fn kind[T: signed](x: T) -> &str { return "signed"; }
fn kind[T: integer](x: T) -> &str { return "integer"; }
fn kind[T: float](x: T) -> &str { return "float"; }
fn kind[T: discriminated](x: T) -> &str { return "has a tag"; }
fn kind[T](x: T) -> &str { return "something else"; }

enum Color { Red, Green }

/// One body for every integer width, from `u1` to `i512`.
fn bits_set[T: integer](x: T) -> u32 {
    let mut n: u32 = 0;
    let mut v = x;
    while v != 0 {
        n += (v & 1) as u32;
        v = v >> 1;
    }
    return n;
}

pub fn main() -> i32 {
    println(f"{kind(-3 as i8)} {kind(7 as u64)} {kind(1.5)} {kind(Color::Red)} {kind(true)}");
    @assert(bits_set(255 as u8) == 8 && bits_set(5 as u24) == 2);
    @assert(@satisfies(u24, unsigned) && !@satisfies(f32, integer));
    return 0;
}
```

This prints `signed integer float has a tag something else`: `i8` is `signed`, which is narrower than `integer`, while `u64` is only an `integer`.

Traits come in three strengths. A nominal trait is met only by an `impl`. A `trait(structural)` is met by any type with matching `pub` methods. An `unchecked` parameter promises nothing, which is duck typing:

```slop
/// Nominal: a type meets it only by saying so, with `impl`.
trait Shape {
    fn area(self: &Self) -> i32;
    fn describe(self: &Self) -> String {
        return format(f"a shape of area {self.area()}");
    }
}

/// Structural: any type with a matching `pub` method meets it, no `impl` needed.
trait(structural) Named {
    fn name(self: &Self) -> &str;
}

struct Square {
    side: i32,

    pub fn name(self: &Self) -> &str {
        return "square";
    }
}

impl Shape for Square {
    fn area(self: &Self) -> i32 {
        return self.side * self.side;
    }
}

/// The body may use only what the bounds promise, checked where it is written.
fn label[T: Shape + Named](t: &T) -> String {
    return format(f"{t.name()}: {t.describe()}");
}

/// `unchecked` promises nothing: the body is checked for each type it is used with.
fn twice_len[T: unchecked](t: &T) -> usize {
    return t.len() * 2;
}

pub fn main() -> i32 {
    let sq = Square { side: 3 };
    println(label(&sq));
    let any: &Shape = &sq;                 // a trait object, through a vtable
    @assert(any.area() == 9);
    let s = String::from("abc");
    let v = Vec[u8]::new();
    @assert(twice_len(&s) == 6 && twice_len(&v) == 0); // anything with `len()`
    return 0;
}
```

A bounded generic is checked once, against its bounds, wherever it is written. If `twice_len` said `[T]` instead of `[T: unchecked]`, it would be refused with "uses its type parameters beyond what their bounds promise: Type 'T' has no method 'len'", even if nothing called it. `unchecked` puts the check off until each use: `twice_len(&Square { side: 1 })` fails with "Type 'Square' has no method 'len'", and the message names that instance. Use it where a bound can't say what the body needs, as the reflection examples above do.

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

A pattern type is an integer limited to some ranges, such as `u8 in 0..=100` or `u8 in 0..=9 | 200..=255`. `rune` is `u32 in 0..=0xD7FF | 0xE000..=0x10FFFF`.

```slop
alias Percent = u8 in 0..=100;

/// Any integer type but zero.
fn NonZero[Int: integer] -> type {
    return Int in 1..=Int::MAX;
}

fn discount(price: u32, off: Percent) -> u32 {
    return price - price * (off as u32) / 100;
}

pub fn main() -> i32 {
    let half: Percent = 50;               // checked when compiled
    @assert(discount(80, half) == 40);

    let typed: u8 = 120;
    let off = (typed as ?Percent) orelse 0; // checked when run: 120 is out of range
    @assert(off == 0);

    // A value outside the range stands for `null`, so these need no tag.
    @assert(@size_of(?NonZero[u32]) == 4 && @size_of(?Percent) == 1);
    return 0;
}
```

- Constants are checked when the program compiles: `let half: Percent = 150;` is an error.
- A run-time value never narrows by itself. `x as ?P` checks it and gives `null` when it is out of range, and `x as P` traps instead.
- Arithmetic works on the base type, so `off + 1` is a plain `u8`.
- Values outside the ranges give `?P` its `null` with no extra tag. Indexing `[T; N]` with `usize in 0..=N-1` needs no bounds check, and LLVM is told the range of each load.

Code that manages memory itself, such as containers and buffers, says what each pointer or slot holds, so the compiler can still reason about ownership:

| Type | Holds | Treated as |
| :--- | :--- | :--- |
| `*own T` | values of `T` the type owns, such as a `Box`'s or a `Vec`'s buffer | the `T`s: a `Box[Tx]` is linear and a `Box[&i32]` carries the borrow |
| `*ref T`, `*ref mut T` | a borrow of `T`, such as an iterator's view of a `Vec` | `&T` / `&mut T` for borrow checking |
| `uninit T` | a `T`'s bytes, holding a `T` or not yet | nothing until read with `unsafe { x.assume_init }`; never dropped by itself |
| `&rel T`, `&rel [T]`, `&rel str` | a reference into the `opaque` it is a field of | an offset, so it survives the value being moved |

The three pointer kinds follow the raw-pointer rules (dereferencing needs `unsafe`) and compile to the same code; they differ in what they tell the checker. `*const T` and `*mut T` claim nothing.

```slop
/// Room for `N` values, none of them made until pushed: `uninit T` is a `T`'s
/// bytes with no `T` in them yet, so nothing is built or dropped by itself.
opaque Stack[T: copy, N: usize] {
    items: [uninit T; N],
    len: usize,

    pub fn new() -> Self {
        return Self { items: uninit, len: 0 };
    }

    pub fn push(self: &mut Self, value: T) {
        @assert(self.len < N, "stack full");
        self.items[self.len] = uninit(value);
        self.len += 1;
    }

    pub fn pop(self: &mut Self) -> ?T {
        if self.len == 0 {
            return null;
        }
        self.len -= 1;
        return unsafe { self.items[self.len].assume_init };
    }
}

/// A buffer and a view into it: `&rel` is an offset from the field to its
/// target, so the view stays right when the value is moved.
opaque Word {
    text: [u8; 8],
    middle: &rel [u8],

    pub fn new() -> Self {
        return Self { text: { b'w', b'o', b'r', b'd', b's', b'!', b' ', b' ' }, middle: &rel self.text[1..4] };
    }

    pub fn middle(self: &Self) -> &[u8] {
        return self.middle;
    }
}

pub fn main() -> i32 {
    let mut s = Stack[i32, 4]::new();
    s.push(1);
    s.push(2);
    @assert((s.pop() orelse 0) == 2 && (s.pop() orelse 0) == 1);
    @assert(s.pop() == null);

    let w = Word::new();
    let moved = w;
    @assert(moved.middle().len == 3 && moved.middle()[0] == b'o');
    return 0;
}
```

Containers don't allocate directly. They ask a `Storage` for memory and keep the `Handle` it returns. Every `Allocator` is a storage whose handle is the memory itself (an `*own u8`). `Slots[T, N]` is a storage inside the container, an `[uninit T; N]`, whose handle only says there is room. Because inline memory moves with its container, the container asks for the address on each use (`resolve`). `Vec[T, A]` takes the storage as `A`, and it defaults to the global heap.

```slop
/// Heap memory from the global allocator, saying each time it grows. The
/// handle is the memory itself, an `*own u8`: the container owns what it holds.
opaque Noisy {
    grows: u32,

    pub fn new() -> Self {
        return Self { grows: 0 };
    }

    unsafe impl Storage {
        const Handle: copy = *own u8;

        fn resolve(self: &Self, h: *own u8) -> *own u8 {
            return h;
        }

        fn grow(self: &mut Self, h: ?*own u8, keep: usize, bytes: usize, align: usize) -> ?*own u8 {
            self.grows += 1;
            println(f"grow {self.grows}: {bytes} bytes");
            let heap = Global { };
            let mut raw: *mut u8;
            if let old = h {
                raw = heap.realloc(old as *mut u8, bytes, align);
            } else {
                raw = heap.alloc(bytes, align);
            }
            if (raw as usize) == 0 {
                return null;
            }
            return unsafe { raw as *own u8 };
        }

        fn release(self: &mut Self, h: *own u8) {
            Global { }.dealloc(h as *mut u8);
        }

        fn limit(self: &Self) -> usize {
            return usize::MAX;
        }

        fn sibling(self: &Self) -> Self {
            return Self::new();
        }
    }
}

pub fn main() -> i32 {
    // On the heap, through the storage above.
    let mut v = Vec[i32, Noisy]::new_in(Noisy::new());
    for i in 0..20 {
        v.push(i);
    }

    // Inline: `Slots` is `[uninit T; N]`, so this vector allocates nothing.
    let mut w = Vec[i32, Slots[i32, 8]]::new();
    for i in 0..8 {
        w.push(i * i);
    }
    @assert(v.len() == 20 && (w.pop() orelse 0) == 49);
    return 0;
}
```

This prints `grow 1: 16 bytes` through `grow 4: 128 bytes` as the first vector doubles. The second vector never touches the heap, and its ninth `push` would trap. `Storage` is an `unsafe trait`: the compiler trusts that `grow` returns enough memory and that nothing else uses it until `release`.

An `export fn` can be called from C. Optionals and errors become what a C programmer would write by hand: a status return plus an out-pointer for the value.

```slop
export error ParseError { Empty, NotADigit }

/// The digit `c` stands for, if it is one.
export fn digit_value(c: u8) -> ?u8 {
    if c < 48 || c > 57 {
        return null;
    }
    return c - 48;
}

/// The number `len` bytes at `s` spell out.
export fn parse_u32(s: *const u8, len: usize) -> ParseError!u32 {
    if len == 0 {
        return .Empty;
    }
    let mut n: u32 = 0;
    for i in 0..len {
        let d = digit_value(unsafe { *(s + i) }) orelse return .NotADigit;
        n = n * 10 + d as u32;
    }
    return n;
}
```

The matching C declarations:

```c
typedef enum ParseError {
    ParseError_Ok = 0,
    ParseError_Empty = 1,
    ParseError_NotADigit = 2,
} ParseError;

bool digit_value(uint8_t c, /* out */ uint8_t* out_val);
ParseError parse_u32(const uint8_t* s, size_t len, /* out */ uint32_t* out_val);
```

- `?T` becomes a `bool`: `true` means the value was written to `*out_val`, and `false` means `null`.
- `E!T` returns the error's enum, `ParseError_Ok` on success, and writes the value to `*out_val`. An error variant with a payload also gets an `E* err_out` parameter for the payload.
- A `?*T` return is just a nullable pointer.

SlopLang callers still see `?u8` and `ParseError!u32`, and use `orelse`, `catch`, and `try` on them; only C sees the lowered form. `slop build lib.slop --emit ll` writes LLVM IR that `clang -c` compiles into an object to link with C. The header comes from `Compiler::compile_source_with_c_header`; `slop` cannot write it yet.

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
- [examples/](examples) has whole programs: [serve](examples/serve.slop), an HTTP server to point a browser or `curl` at
  once built, an HTTP server and a key-value store on fibers that test themselves,
  an interpreter, a word counter, a reflection showcase, and `ledger`, a multi-module package.
- [lib/](lib) is the standard library, written in SlopLang.

## License

SlopLang is licensed under either of

- the Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE)), or
- the MIT license ([LICENSE-MIT](LICENSE-MIT)),

at your option. This covers the compiler, the standard library in `lib/`, and the examples.

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in
SlopLang by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without
any additional terms or conditions.
