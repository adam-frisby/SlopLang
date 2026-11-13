# A tour of SlopLang

This is a quick look at the language for someone who has written Rust, Zig, or C. Every
program here runs: the test suite compiles each `slop` block, runs it, and checks that `main`
returns 0, and checks that each `slop rejected` block is refused with the error its first line
names. [DESIGN.md](DESIGN.md) has the details and the reasons.

## Running a program

```sh
slop new hello        # a package: package.slop and src/main.slop
slop run hello        # builds natively and runs main
slop run hello --vm   # runs main under the checking VM instead
slop test hello       # runs the package's test blocks
slop check hello      # compiles everything, tests included, and runs nothing
slop fmt hello        # lays out the package's files
slop build hello      # an executable, through LLVM and clang
```

`slop run --vm` and `slop test` run code in a VM that checks everything it can: a leak, a use
after free, an aliasing violation, a data race, or a failed `@assert` stops the program and says
where. `slop run` and `slop build` compile the same code natively.

```slop
pub fn main() -> i32 {
    let name = "world";
    println(f"hello, {name}");
    return 0;
}
```

`main` returns the exit status, or nothing (status 0), or an error union: `fn main() -> E!void`
exits with 1 after writing `error: ` and the error to stderr, followed by the trace of functions
it was returned through. `f"..."` is a format string, and `println` writes it.

## Values and control flow

```slop
fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        return a;
    }
    return gcd(b, a % b);
}

pub fn main() -> i32 {
    let x: i32 = 7;          // immutable unless `mut`
    let mut total = 0;
    for i in 0..x {
        total = total + i;
    }
    while total > 10 {
        total = total - 10;
    }
    let big: u64 = 1 << 40;
    let ratio = 2.5 * 4.0;
    @assert(total == 1);
    @assert(gcd(big, 96) == 32);
    @assert(ratio == 10.0);
    return 0;
}
```

Integers do not convert implicitly between types; write `n as i64`. Arithmetic that
overflows traps.

## Structs, unions, and matching

```slop
struct Point {
    x: i32,
    y: i32,
}

union Shape {
    Dot,
    Circle(i32),
    Rect(Point),
}

fn area(s: &Shape) -> i32 {
    match *s {
        .Dot => return 0,
        .Circle(r) => return 3 * r * r,
        .Rect(p) => return p.x * p.y,
    }
}

pub fn main() -> i32 {
    let x = 3;
    let y = 4;
    let shapes = .{ Shape::Dot, Shape::Circle(2), Shape::Rect(Point { x, y }) };
    let weights = [1; 3];
    @assert(area(&shapes.0) + area(&shapes.1) + area(&shapes.2) == 24);
    @assert(weights[0] + weights[1] + weights[2] == 3);
    return 0;
}
```

A struct's fields are public (`Point { x, y }` puns `x: x, y: y`). A `union` is a tagged union, and
`match` must cover every variant. `.{ a, b, c }` is a tuple (`.0` reads its first field), and
an array literal is written in brackets (`[1, 2, 3]` has type `array[i32; 3]`), `[val; N]` repeats an
element `N` times, and `&[3, 9, 4]` is a slice (`&slice[i32]`). The leading `.` of `.{ ... }` means the type comes
from context, as in `.Dot`, and a plain `{ ... }` is always a block.

## Optionals and errors

```slop
error ParseError { Empty, NotADigit(u8) }

fn digit(s: &str) -> ParseError!i32 {
    if s.len == 0 {
        return .Empty;
    }
    let c = s[0];            // a `&str` is its UTF-8 bytes
    if c < 48 || c > 57 {
        return .NotADigit(c);
    }
    return (c - 48) as i32;
}

fn sum_digits(a: &str, b: &str) -> ParseError!i32 {
    let x = try digit(a);    // returns the error to our caller
    let y = try digit(b);
    return x + y;
}

pub fn main() -> i32 {
    let found: ?i32 = 5;
    let missing: ?i32 = null;
    @assert((found orelse 0) + (missing orelse 1) == 6);
    if let ?n = found {
        @assert(n == 5);
    }
    let ?v = found else { return 1; };
    @assert(v == 5);
    @assert((sum_digits("3", "4") catch 0) == 7);
    @assert((sum_digits("3", "x") catch 0) == 0);
    return 0;
}
```

`?T` is a value or `null`; `orelse` gives a fallback, `if let` takes the value out, and
`let ?v = ... else { ... };` unwraps into the current scope or diverges. `E!T` is
a `T` or one of the errors `E` lists; `try` passes an error up, and `catch` handles it. A result
may not be left unused: `_ = f();` discards one on purpose, and an error union cannot be ignored
at all.

## Ownership and borrowing

A value has one owner. Assigning or passing it moves it, unless it is `copy` (as numbers are).
A reference borrows it: any number of `&T`, or one `&mut T`.

```slop
fn longest(words: &Vec[String]) -> usize {
    let mut best: usize = 0;
    for w in words.iter() {
        if w.len() > best {
            best = w.len();
        }
    }
    return best;
}

fn shout(s: &mut String) {
    s.push_str("!");
}

pub fn main() -> i32 {
    let mut words = Vec[String]::new();
    words.push(String::from("borrow"));
    let mut w = String::from("check");
    shout(&mut w);
    words.push(w);           // `w` moves into the vector
    @assert(longest(&words) == 6);
    return 0;
}
```

The compiler refuses a use after a move, and a borrow that outlives what it borrows or
overlaps a `&mut`:

```slop rejected
// error: Use of moved
pub fn main() -> i32 {
    let a = String::from("one owner");
    let b = a;
    let n = a.len();
    return 0;
}
```

```slop rejected
// error: cannot borrow 'v' as mutable because 'v' is already borrowed
pub fn main() -> i32 {
    let mut v = Vec[i32]::new();
    v.push(1);
    let first = v.get(0) orelse return 1;
    v.push(2);               // may move the elements `first` points at
    return *first;
}
```

Values are dropped at the end of their scope, and a type can say what dropping it does.

## Linear types

A `linear` type must be used up exactly once: dropping one is an error. It suits values that
must not be forgotten, such as a transaction that must be committed or rolled back.

```slop
pub opaque(linear) Tx {
    id: i32,
    pub fn begin(id: i32) -> Self { return Self { id: id }; }
    pub fn commit(self) -> i32 { return self.id; }
}

pub fn main() -> i32 {
    let tx = Tx::begin(4);
    @assert(tx.commit() == 4);
    return 0;
}
```

```slop rejected
// error: must be explicitly consumed
pub opaque(linear) Tx {
    id: i32,
    pub fn begin(id: i32) -> Self { return Self { id: id }; }
    pub fn commit(self) -> i32 { return self.id; }
}

pub fn main() -> i32 {
    let tx = Tx::begin(4);
    return 0;                // `tx` is neither committed nor passed on
}
```

An `opaque` type's fields are private to its body, so only its own methods make and take apart
its values.

A generic takes linear types only when it says so, with `?linear`, since a plain `[T]` may drop
what it is given. With it, the compiler holds the body to consuming every `T`:

```slop
pub opaque(linear) Tx {
    id: i32,
    pub fn begin(id: i32) -> Self { return Self { id: id }; }
    pub fn commit(self) -> i32 { return self.id; }
}

fn second[T: ?linear](a: T, b: T) -> tuple { T, T } {
    return .{ b, a };
}

pub fn main() -> i32 {
    let .{ x, y } = second(Tx::begin(1), Tx::begin(2));
    let a = x.commit();      // not inside `&&`, which might skip the second
    let b = y.commit();
    @assert(a == 2 && b == 1);
    return 0;
}
```

`Vec`, `Box`, `Mutex`, `Channel`, and the other standard containers take `?linear`.

`defer` runs a statement when its block is left, however it is left: at the end, or by `return`,
`break`, `continue`, or `try`. It suits a linear value that every path must finish, such as a
lock guard, which must be unlocked on every path, including a `try` that returns early:

```slop
error ParseError { Negative }

fn parse(n: i32) -> ParseError!i32 {
    if n < 0 {
        return .Negative;
    }
    return n;
}

fn add(total: &Mutex[i32], n: i32) -> ParseError!i32 {
    let mut guard = total.lock();
    defer guard.unlock();    // runs on the way out, after the error too
    let v = try parse(n);
    *guard.get_mut() += v;
    return *guard.get();
}

pub fn main() -> i32 {
    let total = Mutex::new(1 as i32);
    @assert((add(&total, 2) catch 0) == 3);
    @assert((add(&total, -5) catch 0) == 0);
    @assert((add(&total, 4) catch 0) == 7);    // the error released the lock
    return 0;
}
```

Deferred statements run in the reverse of the order they were written, among the block's
variables, and see only what was declared before them. One cannot itself leave the block:
`return`, `try`, and `break` or `continue` to a loop outside it are refused.

`errdefer` runs only when the function returns an error: a failed `try`, `return E::X`, or an
`E!T` returned that holds one. With it, a transaction is committed where the work succeeds and
rolled back on every way it can fail. `errdefer |e|` names the error being returned:

```slop
error TransferError { Overdrawn }

pub opaque(linear) Tx {
    pending: i32,
    pub fn begin() -> Self { return Self { pending: 0 }; }
    pub fn withdraw(&mut self, balance: i32, amount: i32) -> TransferError!void {
        if amount > balance {
            return .Overdrawn;
        }
        self.pending = self.pending + amount;
    }
    pub fn commit(self) -> i32 { return self.pending; }
    pub fn rollback(self) { }
}

fn transfer(balance: i32, amount: i32) -> TransferError!i32 {
    let mut tx = Tx::begin();
    errdefer tx.rollback();     // only if this returns an error
    errdefer |e| eprintln(f"transfer of {amount} failed: {e}");
    try tx.withdraw(balance, amount);
    return tx.commit();
}

pub fn main() -> i32 {
    @assert((transfer(100, 30) catch 0) == 30);
    @assert((transfer(10, 30) catch -1) == -1);
    return 0;
}
```

## Generics and bounds

Type parameters go in brackets, with bounds on what the generic needs. The body is checked
against the bounds once, not each time it is used, so a generic that uses more than its bounds
promise is refused where it is written.

```slop
fn largest[T: number](items: &slice[T]) -> T {
    let mut best = items[0];
    for i in 1..items.len {
        if items[i] > best {
            best = items[i];
        }
    }
    return best;
}

fn apply_twice[F: callable(i32) -> i32](f: F, x: i32) -> i32 {
    return f(f(x));
}

pub fn main() -> i32 {
    let nums = &[3, 9, 4];
    @assert(largest(nums) == 9);
    let step: i32 = 5;
    @assert(apply_twice(fn(x) => x + step, 1) == 11);
    return 0;
}
```

`callable(A) -> R` admits functions and closures taking an `A` and returning an `R` (inferring
the closure's parameter and return types when omitted). A closure captures what it uses by
reference, or by value with `move fn`.

## Traits

A trait names methods a type provides. A type opts in with `impl`, and a trait may give a
method a default body, which an implementation can replace.

```slop
trait Shape {
    fn area(&self) -> i32;
    fn describe(&self) -> String {
        return format(f"a shape of area {self.area()}");
    }
}

struct Square { side: i32 }

impl Shape for Square {
    fn area(&self) -> i32 { return self.side * self.side; }
}

fn total[T: Shape](shapes: &Vec[T]) -> i32 {
    let mut sum = 0;
    for s in shapes.iter() {
        sum = sum + s.area();
    }
    return sum;
}

pub fn main() -> i32 {
    let mut v = Vec[Square]::new();
    v.push(Square { side: 2 });
    v.push(Square { side: 3 });
    @assert(total(&v) == 13);
    let d = v.get(0) orelse return 1;
    @assert(d.describe().as_str() == "a shape of area 4");
    return 0;
}
```

## Compile-time code

Code runs at compile time where a value is needed then: a `const`, an array length, or a type
parameter. Types are values there, and a function returning `type` makes one; its arguments
go in brackets, as a generic's do.

```slop
fn fib(n: u64) -> u64 {
    if n < 2 {
        return n;
    }
    return fib(n - 1) + fib(n - 2);
}

const FIB_20: u64 = fib(20);   // computed by the compiler

fn Pair[T]() -> type {
    return struct { first: T, second: T };
}

pub fn main() -> i32 {
    let p = Pair[i64] { first: 2, second: 3 };
    let table: array[u8; 64] = zeroinit;
    @assert(FIB_20 == 6765);
    @assert(p.first + p.second == 5);
    @assert(table[63] == 0 && @size_of(Pair[u8]) == 2);
    return 0;
}
```

`zeroinit` is the all-zero value of a type that has one, written as one store.

## Reflection

Compile-time code can read a type's shape. `comptime for` unrolls over its fields
(`@fields`), enum variants (`@variants`), or nested leaves (`@leaves`), and `@field` reads or
writes a field by name, so one function serves every struct:

```slop
struct Point { x: i32, y: i32 }
struct Line { from: Point, to: Point, weight: i64 }

/// The sum of every integer field, however deeply nested.
fn total[T: struct](t: &T) -> i64 {
    let mut sum: i64 = 0;
    comptime for p in @leaves(T) {
        if @satisfies(FieldAt[T, p], integer) {
            sum = sum + @field(*t, p) as i64;
        }
    }
    return sum;
}

/// How many fields `T` has.
fn count_fields[T: struct]() -> usize {
    return @fields(T).len;
}

pub fn main() -> i32 {
    let l = Line { from: Point { x: 1, y: 2 }, to: Point { x: 3, y: 4 }, weight: 10 };
    @assert(total(&l) == 20);
    @assert(count_fields[Line]() == 3 && @has_field(Point, "y"));
    @assert(@type_name(Line) == "Line");
    return 0;
}
```

`[T: struct]` bounds a generic to structs, and `comptime for` unrolls its body for each concrete
struct it is used with, compiling to what one would have written by hand for that type. The
bound is required: `@fields(T)` and `@leaves(T)` need `T` bounded to a kind with fields
(`struct`, `tuple`, `aggregate`), and `@variants(T)` to one with variants (`enum`, `union`,
`error`), or `[T: unchecked]`, which checks each use instead. The
[reflect example](examples/reflect.slop) serializes structs to JSON, diffs them, and builds a
patch type with `@Struct`.

## Collections and strings

```slop
pub fn main() -> i32 {
    let mut ages = HashMap[&str, i32]::new();
    ages.insert("ada", 36);
    ages.insert("alan", 41);
    let a = ages.get("ada") orelse return 1;
    @assert(*a == 36);

    let mut v = Vec[i32]::new();
    for i in 0..5 {
        v.push(i * i);
    }
    v.sort_by(fn(a: &i32, b: &i32) -> bool { return *a > *b; });
    let top = v.get(0) orelse return 2;
    @assert(*top == 16);

    let mut s = String::from("tour");
    s.push_str(" done");
    @assert(s.as_str().words().len() == 2);
    return 0;
}
```

## Generators

A function declared `-> gen T` gives its values one at a time: each `yield` hands one to the
caller and waits for the next request. `for` loops over it, and `Iterator`'s methods adapt it.
`lines` and `words_iter` are generators over a string, whose pieces borrow it.

```slop
fn squares(n: i32) -> gen i32 {
    for i in 0..n {
        yield (i + 1) * (i + 1);
    }
}

pub fn main() -> i32 {
    let mut sum = 0;
    for s in squares(4) {
        sum += s; // 1 + 4 + 9 + 16
    }
    @assert(sum == 30);

    let even = squares(6).filter(fn(s: &i32) -> bool { return *s % 2 == 0; }).count();
    @assert(even == 3);

    let text = "first line\nand the second\n";
    let mut words = 0;
    for line in text.lines() {
        words += line.words_iter().count();
    }
    @assert(words == 5);
    return 0;
}
```

## Tests

`test` blocks sit beside the code they test. `slop test` runs each in a fresh VM, and a test
fails if an `@assert` fails, if it leaks, or if it does anything undefined. A test returns no
error, so a `try` in one that fails fails the test, naming the error and where it was returned.

```slop
fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo { return lo; }
    if x > hi { return hi; }
    return x;
}

test "clamps both ways" {
    @assert(clamp(-5, 0, 10) == 0);
    @assert(clamp(50, 0, 10) == 10, "too high is the top");
}

pub fn main() -> i32 {
    return clamp(3, 0, 10) - 3;
}
```

## Threads

`spawn` runs a `move fn` on a new thread. Values shared between threads are `send` and `sync`,
which the compiler works out from what a type holds. `Mutex` and `Channel` share data, and a
`Mutex`'s guard is linear, so a lock cannot be left held.

```slop
pub fn main() -> i32 {
    let jobs = Channel[i32]::new();
    let total = Mutex[i32]::new(0);
    _ = jobs.send(3);
    _ = jobs.send(4);
    let worker = spawn(move fn() -> i32 { return 10; });
    let ten = worker.join(); // a `JoinHandle` is linear: joined or detached, never dropped
    for i in 0..2 {
        let n = jobs.recv() catch return 1;
        _ = total.with_lock(fn(t: &mut i32) -> i32 { *t = *t + n; return 0; });
    }
    let mut g = total.lock();
    let sum = *g.get_mut();
    g.unlock();
    @assert(sum + ten == 17);
    return 0;
}
```

## Tasks

Functions do not say whether they wait: `f(x)` returns a `T` whether `f` waits on a channel,
a lock, or nothing, so one library serves threads and fibers alike. Work starts concurrently
only where a caller asks, with `async`, which gives a handle to `await`:

```slop
fn square(n: i32) -> i32 {
    return n * n;
}

fn sum_of_squares(a: i32, b: i32) -> i32 {
    let x = async square(a);   // may run elsewhere, or right here
    let y = async square(b);
    return x.await() + y.await();
}

pub fn main() -> i32 {
    // On fibers: tasks take turns on this thread, each with a stack of its own. What a task
    // starts with `async` runs on its executor too.
    let t = async(Fibers { }) sum_of_squares(3, 4);
    @assert(t.await() == 25);
    return 0;
}
```

There are three ways to start work, for three promises:

| Write | It gives | It promises |
|---|---|---|
| `async f(x)` | a `Task[R]`, to `await` | the work happens, perhaps right there in the call; never that it overlaps the caller |
| `spawn_scoped(fn ...)` | a `ScopedHandle`, linear, to `join` | a thread of its own, running alongside: for work that must overlap, such as a producer and its consumer |
| `spawn(move fn ...)` | a `JoinHandle`, linear, to `join` or `detach` | a thread of its own that may outlive the caller, so it borrows nothing |

**Dropping a task's handle cancels the task and waits for it to end**, so a task never outlives
what it borrows and a result is never silently lost. That wait happens wherever the handle
goes out of scope, which is the one place a drop can suspend.

## Packages

A package is a directory with `src/main.slop` (or `src/lib.slop`) and a `package.slop`
manifest. The manifest is SlopLang, evaluated at compile time for the target, and lists
dependencies by URL and SHA-256:

```
import std::build::{Package, Target, Dependency};

pub fn package[target: Target]() -> Package {
    return Package {
        name: "app",
        version: { 0, 1, 0 },
        root: "src/main.slop",
        no_std: false,
        deps: &[Dependency { name: "shapes", url: "https://example.com/shapes.tar.gz", sha256: 0x9f..._u256 }],
        system_libs: &[],
    };
}
```

`slop fetch app` downloads and checks the dependencies and writes `package.lock`. A dependency
named `shapes` is imported as `import shapes;`, and each module `src/x.slop` is
`import root::x;` in its own package.
