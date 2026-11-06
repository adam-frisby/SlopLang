# SlopLang

As the name implies, this is a 100% AI-generated compiler.

SlopLang is a systems language that combines Rust's memory safety (ownership, moves,
destructors, borrow checking, and `linear` types that must be consumed) with Zig's `comptime`:
types are values, generics are functions that take them, and compile-time code replaces
macros. It compiles through LLVM, and can also run under a checking VM that stops on a leak, a
use after free, an aliasing violation, or a data race.

## Why?

1. Experimentation - Testing the abilities of LLMs
2. Exploration - Exploring ideas without committing to long development cycles

## Is it sound?

Maybe.

## Should I use it?

Probably not.

## Are there bugs?

For sure.

## Examples

### Error handling (`E!T` and `?T`)

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

### Compile-time types and reflection

Generics are functions run at compile time, and the same code can read a type's shape:

```slop
/// A type function: run at compile time, it returns a new type.
/// (`struct Pair[T] { first: T, second: T }` is shorthand for this.)
fn Pair[T] -> type {
    return struct { first: T, second: T };
}

struct Point { x: i32, y: i32, label: &str }

/// Prints the fields of any struct: one function, unrolled for each type.
fn describe[T: unchecked](t: &T) {
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

### Meta-type constraints and overloading

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

### Nominal, structural, and `unchecked` generics

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

### Encapsulation (`struct` vs. `opaque`)

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

### Must-consume linear types (`opaque(linear)`)

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

### Borrow checking and lifetime contracts (`borrows`)

Instead of `'a` lifetime parameters, `pub` functions name the parameters a returned reference (or a mutated parameter) may borrow from with `borrows(...)`. Single-input and `self` borrows are elided, and private functions have their borrow flows inferred across the call graph:

```slop
/// The returned slice may borrow from `a` or `b`, but not `ignored`.
pub fn longer(a: &str, b: &str, ignored: &str) -> &str borrows(a, b) {
    if a.len >= b.len {
        return a;
    }
    return b;
}

pub struct Slot { r: &i32 }

/// Parameter-to-parameter flow: `dst` stores a borrow from `x`.
pub fn stash(dst: &mut Slot, x: &i32) borrows(dst: x) {
    dst.r = x;
}

pub fn main() -> i32 {
    let a = String::from("longer");
    let b = String::from("hi");
    let mut temp = String::from("temporary");
    let pick = longer(a.as_str(), b.as_str(), temp.as_str());
    @drop(temp); // `temp` is dropped here, which is fine: `longer` did not borrow from it
    @assert(pick == "longer");

    let x: i32 = 10;
    let y: i32 = 20;
    let mut s = Slot { r: &x };
    stash(&mut s, &y);
    @assert(*s.r == 20);
    return 0;
}
```

### Range-restricted pattern types

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

### References and pointer kinds (`&T`, `*own T`, `*ref T`, `*const T`)

Every reference and pointer in SlopLang is **non-null by default** (`?&T`, `?*own T`, and `?*mut T` add nullability via the zero-address niche). Beyond safe references (`&T`, `&mut T`), containers and low-level code use **pointer kinds** to declare what a raw address logically holds, replacing Rust's `NonNull<T>`, `PhantomData<T>`, and manual `Send`/`Sync` boilerplate:

| Type | Nullability | Deref | What it holds | Linearity, borrows, and `send` / `sync` |
| :--- | :--- | :--- | :--- | :--- |
| `&T`, `&[T]`, `&str` | Non-null (`?&T` nullable) | Safe | Shared borrow of `T` | `copy`; carries a shared loan; `send` & `sync` iff `T: sync` |
| `&mut T`, `&mut [T]` | Non-null (`?&mut T` nullable) | Safe | Unique mutable borrow of `T` | Move-only (`affine`); carries an exclusive loan; `send` iff `T: send` |
| `*own T` | Non-null (`?*own T` nullable) | `unsafe` | Owned `T` value(s) (e.g., `Box`, `Vec` buffer) | Only in `opaque`; makes the `opaque` linear if `T: linear`, borrow-carrying if `T` borrows, and `send`/`sync` as `T` |
| `*ref T`, `*ref mut T` | Non-null (`?*ref T` nullable) | `unsafe` | Borrowed view of `T` (e.g., `Iter`, `MutexGuard`) | Carries a borrow and `send`/`sync` exactly like `&T` / `&mut T`, with raw pointer arithmetic (`p + i`) |
| `*const T`, `*mut T` | Non-null (`?*const T` nullable) | `unsafe` | Untracked raw address | `copy`; claims no ownership or loan; `!send` and `!sync` unless wrapped in `opaque(unsafe send)` |
| `&rel T`, `&rel [T]`, `&rel str` | Non-null (`?&rel T` nullable) | Safe | Offset into the enclosing `opaque` (`addr(target) - addr(field)`) | Zero loans at rest (freely movable); borrows `self` on access |

`*own T`, `*ref T`, and `*const T` compile to identical machine pointers and share raw-pointer rules (`*p` requires `unsafe`, `p + i` steps by elements), but they tell the compiler what the enclosing `opaque` contains:

```slop
/// Owns one `T` on the heap via `*own T`. Because the field is `*own T`,
/// `MiniBox[Transaction]` is automatically linear, `MiniBox[&i32]` carries
/// the reference's borrow, and `MiniBox[i32]` is automatically `send` and `sync`.
opaque MiniBox[T: ?linear] {
    ptr: *own T,

    pub fn new(val: T) -> Self borrows(val) {
        let p: *own T = unsafe { @alloc(T, 1) as *own T };
        unsafe { *p = move val; }
        return Self { ptr: p };
    }

    pub fn get(self: &Self) -> &T {
        return unsafe { &*self.ptr };
    }

    pub fn into_inner(move self) -> T {
        let v = unsafe { move *self.ptr };
        return v;
    }

    unsafe impl drop(may_dangle T) where T: !linear {
        fn drop(self: &mut Self) {
            unsafe {
                @drop(self.ptr);
                @dealloc(self.ptr);
            }
        }
    }

    unsafe impl drop(may_dangle T) where T: linear {
        fn drop(self: &mut Self) {
            unsafe { @dealloc(self.ptr); }
        }
    }
}

/// Steps through a slice using `*ref T`. Because `cur` is a `*ref T` view rather
/// than a raw `*const T`, the borrow checker knows `Cursor[T]` borrows the slice.
opaque Cursor[T] {
    cur: *ref T,
    rem: usize,

    pub fn over(s: &[T]) -> Self borrows(s) {
        let p: *const T = &raw const s[0];
        return Self { cur: unsafe { p as *ref T }, rem: s.len };
    }

    pub fn next(self: &mut Self) -> ?&T borrows(*self) {
        if self.rem == 0 {
            return null;
        }
        let p = self.cur;
        self.cur = p + 1;
        self.rem -= 1;
        return unsafe { &*p };
    }
}

pub fn main() -> i32 {
    let b = MiniBox::new(42);
    @assert(*b.get() == 42);
    @assert(b.into_inner() == 42);

    let nums: [i32; 3] = { 10, 20, 30 };
    let mut c = Cursor::over(&nums);
    let first = c.next() orelse return 1;
    let second = c.next() orelse return 1;
    // Both items come from `borrows(*self)`, so `first` stays valid across `c.next()`:
    @assert(*first + *second == 30);
    return 0;
}
```

### Self-referential relative references (`&rel`)

Every value move in SlopLang is a bitwise `memcpy`. An ordinary pointer (`&T`) into a struct's own inline buffer would dangle as soon as the struct moved. Inside an `opaque`, fields declared `&rel T`, `&rel [T]`, or `&rel str` store the **signed byte offset from the field itself to the target** (`addr(target) - addr(rel_field)`), so moving the value shifts both addresses by the same amount and leaves the offset valid without pinning:

- **Compile-time co-residence**: `&rel <place>` must point to a fixed inline sub-place of `self` (never through a pointer dereference or into a `union` / `overlay` variant that could change).
- **Zero loans at rest, inherited mutability on access**: Because `&rel` fields store offsets rather than addresses, the enclosing `opaque` holds no active borrow when idle and can be moved or returned freely. Reading a `&rel` field borrows `self` (`&Self` yields `&T` / `&[T]` / `&str`; `&mut Self` also allows mutating through `&rel T` and `&rel [T]`).
- **Optional**: `?&rel T` (and `?&rel [T]`, `?&rel str`) may also be `null`, assigned with `self.state = null;`. It takes no more room than `&rel T`: an offset of 0 is `null`, as no field refers to itself. Reading it gives `?&T`, and `&mut self.state` gives `?&mut T`, so `if let r = &mut self.state { *r += 1; }`.

```slop
/// A packet with an inline buffer and two relative views into it (`header`
/// is always present; `focus` is an optional relative reference `?&rel u8`).
/// Moving `Packet` (by return, assignment, or `Vec::push`) needs no pointer fixup.
opaque Packet {
    buf: [u8; 8],
    header: &rel [u8],
    focus: ?&rel u8,

    pub fn new() -> Self {
        return Self {
            buf: b"GET /ok!",
            header: &rel self.buf[0..3],
            focus: &rel self.buf[5],
        };
    }

    pub fn header(self: &Self) -> &[u8] {
        return self.header;
    }

    pub fn focus(self: &Self) -> ?u8 {
        let r = self.focus orelse return null;
        return *r;
    }

    /// On `&mut Self`, `&mut self.focus` yields `?&mut u8` into `self.buf`:
    pub fn set_focus(self: &mut Self, b: u8) {
        if let r = &mut self.focus {
            *r = b;
        }
        self.focus = &rel self.buf[6]; // retarget to another inline element
    }

    pub fn clear_focus(self: &mut Self) {
        self.focus = null;
    }
}

pub fn main() -> i32 {
    let p = Packet::new();
    let mut moved = p;                 // bitwise move: `header` and `focus` stay valid
    @assert(match moved.header() { b"GET" => true, _ => false });
    @assert((moved.focus() orelse 0) == b'o');

    moved.set_focus(b'O');
    @assert((moved.focus() orelse 0) == b'k');

    moved.clear_focus();
    @assert(moved.focus() == null);
    return 0;
}
```

### Inline uninitialized storage (`uninit T` and `zeroinit`)

Where `?T` adds a tag (or uses a niche) and drops its payload at scope exit, **`uninit T`** has the exact size and alignment of `T`, emits no tag, and **never auto-drops**:

- **`uninit` literal**: Initializes a single `uninit T` or an entire `[uninit T; N]` array in one shot with zero memory writes.
- **`slot = uninit(move val)`**: Writes `val` into `slot` without running a destructor on the prior uninitialized bytes.
- **`unsafe { slot.assume_init }`**: Reads, borrows, moves out of, or drops (`@drop(&mut slot.assume_init)`) the initialized `T`.
- **`zeroinit`**: For types where all-zero bytes are a valid value (numbers, `bool`, `?T`, and arrays/structs of them), `let buf: [u8; 4096] = zeroinit;` safely zeroes the storage in a single `memset`.

```slop
/// Fixed-capacity inline stack for any `T` (including non-`copy` types with destructors).
opaque Stack[T, N: usize] {
    items: [uninit T; N],
    len: usize,

    pub fn new() -> Self {
        return Self { items: uninit, len: 0 };
    }

    pub fn push(self: &mut Self, value: T) borrows(self: value) {
        @assert(self.len < N, "stack full");
        self.items[self.len] = uninit(move value);
        self.len += 1;
    }

    pub fn pop(self: &mut Self) -> ?T {
        if self.len == 0 {
            return null;
        }
        self.len -= 1;
        return unsafe { move self.items[self.len].assume_init };
    }

    unsafe impl drop(may_dangle T) {
        fn drop(self: &mut Self) {
            for i in 0..self.len {
                unsafe {
                    @drop(&mut self.items[i].assume_init);
                }
            }
        }
    }
}

pub fn main() -> i32 {
    let mut s = Stack[String, 4]::new();
    s.push(String::from("first"));
    s.push(String::from("second"));
    let top = s.pop() orelse return 1;
    @assert(top.as_str() == "second");
    // `"first"` is still in `s` and is cleaned up by `Stack::drop` at scope exit.

    let counters: [u64; 16] = zeroinit;
    @assert(counters[0] == 0 && counters[15] == 0);
    return 0;
}
```

### Custom storage and inline vectors (`Storage` and `Slots`)

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

### Concurrency: scoped threads, linear locks, and colour-free fibers

`spawn_scoped` starts a thread that can borrow the caller's stack directly, without a callback wrapper: its `ScopedHandle` is `linear` and carries the closure's borrows, so it must be joined before the borrowed stack frame exits. A `MutexGuard` is `linear` too (explicitly unlocked via `g.unlock()`), and functions that wait on channels or locks run unchanged on OS threads or stack-switching `Fibers`:

```slop
fn work(ch: &Channel[i32], total: &Mutex[i32]) -> i32 {
    let v = ch.recv() catch return 1;
    let mut g = total.lock();
    *g.get_mut() += v;
    g.unlock();                // `MutexGuard` is linear: must be unlocked explicitly
    return 0;
}

pub fn main() -> i32 {
    let ch = Channel[i32]::new();
    let total = Mutex[i32]::new(10);

    // Borrow stack locals across a thread without `thread::scope(|s| ...)`:
    let h = spawn_scoped(fn() -> i32 {
        _ = ch.send(32);
        return 0;
    });

    // Run `work` on stack-switching fibers; the same `work` function runs on threads.
    let task = async(Fibers { }) work(&ch, &total);
    @assert(task.await() == 0);
    _ = h.join();              // `ScopedHandle` is linear: must be joined before `ch` exits scope

    @assert(total.into_inner() == 42);
    return 0;
}
```

### Zero-boilerplate C FFI (`export fn`)

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

SlopLang callers still see `?u8` and `ParseError!u32`, and use `orelse`, `catch`, and `try` on them; only C sees the lowered form. To use it from C:

```sh
slop build lib.slop --emit h      # lib.h, the declarations above
slop build lib.slop --emit ll     # lib.ll, LLVM IR
clang -c lib.ll -o lib.o
clang main.c lib.o -o main        # main.c includes "lib.h"
```

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
slop fetch hello                # fetches dependencies and writes package.lock
slop run hello                  # builds natively and runs main
slop run hello --vm             # runs main under the checking VM instead
slop test hello [--native]      # runs the test blocks, natively too with --native
slop check hello                # compiles everything, tests included, and runs nothing
slop check hello --all-targets  # the same for each target the backend supports
slop fmt hello [--check]        # lays out the source files
slop build hello [-O3]          # an executable, through LLVM and clang
slop build hello --emit h       # a C header for its export items
```

A path can be a single `.slop` file instead of a package directory.

## Learning more

- [TOUR.md](TOUR.md) introduces the language to someone who knows Rust, Zig, or C. The test
  suite runs every example in it.
- [DESIGN.md](DESIGN.md) has the full design, with the reasons for it.
- [examples/](examples) has whole programs: [serve](examples/serve.slop), an HTTP server to point a browser or `curl` at
  (`slop run examples/serve.slop`), an HTTP server and a key-value store on fibers that test themselves,
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
