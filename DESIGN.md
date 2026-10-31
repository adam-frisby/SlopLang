# SlopLang & Stage 3 IR (`SLIR`) Design Document

## 1. Core Philosophy `[Status: Implemented]`
The goal of SlopLang is to combine:
1. **Rust-level memory safety** (ownership, move semantics, RAII destructors, must-consume `linear` types, and Non-Lexical Lifetimes borrow checking).
2. **Zig-level `comptime` metaprogramming** (first-class `type` values, functions that compute types, and compile-time evaluation in place of AST/procedural macros). Generics are ordinary functions whose `comptime` parameters are written in brackets (`fn Vec[T] -> type`, `Vec[i32]`), not angle-bracket generics `<T>`.
3. **Clear, orthogonal type taxonomy** (distinct keywords for distinct memory/lifecycle semantics rather than overloading a single keyword).

---

## 2. Compiler Pipeline Architecture `[Status: Implemented]`

```mermaid
flowchart TD
    S1["Stage 1: Lexing & Parsing (AST)<br/>High-level syntax: tuple, struct, opaque, enum, union, overlay, error, trait, comptime"] --> S2
    S2["Stage 2: Name Resolution, Type Checking & Comptime Specialization<br/>Evaluates comptime functions, value and type functions alike, on the Stage 3 VM<br/>Enforces field visibility (struct vs opaque) & meta-type/trait bounds<br/>Lowers to concrete Stage 3 CFG IR"] --> S3A
    S3A["Stage 3a: Unelaborated CFG IR (SLIR)<br/>Places, StorageLive/StorageDead, Terminator::Drop, Rvalue::Ref"] --> S3B
    S3B["Stage 3b: Move Analysis & Drop Elaboration (src/drop.rs)<br/>Rejects use-after-move, uninitialized reads, and unconsumed linear values<br/>Elaborates static, partial-struct, and dynamic flag-guarded drops"] --> S3C
    S3C["Stage 3c: NLL Borrow Checking (src/borrowck.rs)<br/>Backward local liveness + forward loan propagation<br/>Interprocedural borrow summary inference & explicit borrows(...) contracts"] --> S4
    S4["Stage 4: Backend Codegen (src/llvm.rs)<br/>Lifetimes & loans erased; lowers to LLVM IR"]
```

### Implementation Status Overview
To distinguish what is already implemented and tested in the compiler today from planned surface-language extensions, every section in this document carries a status marker:
- **`[Status: Implemented]`**: Fully implemented across the surface parser ([`src/frontend/`](src/frontend/mod.rs)), Stage 2 lowerer ([`src/lower/`](src/lower/mod.rs)), Stage 3 IR/passes ([`src/ir.rs`](src/ir.rs), [`src/vm.rs`](src/vm.rs), [`src/drop.rs`](src/drop.rs), [`src/borrowck.rs`](src/borrowck.rs)), and Stage 4 LLVM backend ([`src/llvm.rs`](src/llvm.rs)).
- **`[Status: Partial]`**: Core semantics and Stage 3/4 representations are implemented, with specific surface syntax sugars still planned (noted inline).
- **`[Status: Planned]`**: Architectural specification not yet enforced by the compiler; used on whole sections or inline on individual rules inside an otherwise implemented section.

### Why `comptime` Specialization Happens *Before* Borrow Checking (Benefits & Tradeoffs)
In Rust, borrow checking happens before monomorphization on abstract generic types `<T>`, requiring complex type-system machinery (`T: 'a`, `PhantomData<T>`, `#[may_dangle]`, variance annotations, higher-ranked trait bounds).

By evaluating `comptime` parameters and type-constructing functions **first** (via [`Vm::eval`](src/vm.rs)) and running [`elaborate_drops`](src/drop.rs) and [`check_borrows`](src/borrowck.rs) on the resulting concrete Stage 3 functions:
- **Benefits**:
  - **No `PhantomData<T>` is needed**: Concrete field types and destructors (`drop tyX = fnY`) are directly visible.
  - **No `T: 'a` or variance annotations are needed**: Concrete structs and closures containing references are tracked directly by the borrow checker.
  - **`comptime` parameters are already folded** into concrete [`TypeId`](src/ir.rs)s and [`ConstValue`](src/ir.rs)s before borrow checking begins.
- **Tradeoffs (Post-Specialization Checking)**:
  - **Instantiation-Time Borrow & Move Diagnostics**: Because [`elaborate_drops`](src/drop.rs) and [`check_borrows`](src/borrowck.rs) operate on concrete Stage 3 IR after `comptime` specialization, a generic library function (`fn foo[T](x: T)`) is only move-checked and borrow-checked for the concrete types `T` with which it is actually instantiated (similar to Zig `comptime` functions and C++ templates). Diagnostics inside a generic body name the instantiation they come from: errors found while lowering it end with `in instantiation of root::foo[T = &mut i32]` (or `in instantiation of Vec[Tx]::push` for a method of a type-function instance), and borrow and move errors name the instantiated function (`in root::foo[T = &mut i32] (fn3)`). Instantiations are lowered after the call that requests them, so the trace names the instantiation itself rather than the full chain of calls leading to it. A generic function that a package never instantiates is still checked: [`Compiler::check_unused_generics`](src/lower/mod.rs) instantiates it, in a scratch copy of the compiler, with a representative of each `comptime` parameter's constraint (`i32` for `integer` / `number` / `scalar`, `u32` for `unsigned`, `f64` for `float`, `tuple { i32 }` for `copy` / `send` / `sync` / `format` / `clone`, the affine `Box[i32]` for `type`, `1` for a value parameter) and reports a body that fails for it as a warning (`does not compile for every type its constraints allow (T = Box[i32])`). Trait-bounded and other structural constraints are not sampled.
  - **Constraint-Dependent IDE Autocomplete**: Inside a function taking an unconstrained type parameter `[T]`, the compiler and IDE can only check syntax and resolve names that do not depend on `T` prior to instantiation. Full pre-instantiation member checking and IDE autocomplete require constraining `T` with a [`trait`](#42-traits-in-a-comptime-language-status-implemented) (`[T: Hash + Eq]`) or a [meta-type constraint](#33-meta-type-constraint-hierarchy--overload-resolution-status-implemented) (`[S: sequence]`, `[N: number]`).

### Panic, Trap, and Unwind Semantics (`panic = abort`) `[Status: Implemented]`
The language has **no stack unwinding** (`panic = abort` in all build modes):
- **Unrecoverable Violations Trap Immediately**: Checked arithmetic overflow (`+`, `-`, `*`), division or remainder by zero, bit shifts $\ge$ bit width, out-of-bounds array/slice indexing, reaching `unreachable`, `@trap()`, or out-of-memory in infallible `@alloc`/`@realloc` immediately terminates the process via LLVM's `@llvm.trap()` intrinsic (`UD2` on x86_64 / `BRK` on AArch64).
- **Recoverable Failures Use Explicit Return Types**: Operations that can legitimately fail at runtime use [`?T` or `E!T`](#36-language-level-optionals-t-and-results-et-status-partial) (`a +? b`, `v.get(i)`, `s.try_push(val)`), never exceptions or unwinding panics.
- **Soundness Guarantee for Linear Types & Scoped Threads**: Because stack unwinding does not exist, a panic can never unwind past a parent stack frame while a child thread spawned via [`spawn_scoped`](#54-safe-threading-automatic-structural-sendsync-linear-mutext--execution-agnostic-select-status-partial) is still reading parent stack memory, nor can unwinding bypass a [`linear struct`](#must-consume-linear-types-linear-struct--shared-drop-cleanup-status-implemented) consumption obligation.

---

## 3. High-Level Type Taxonomy

### 3.0 Primitive Scalar Types, Arbitrary-Width Integers (`i1`..`i512` / `u1`..`u512`), `simd[T; N]`, `rune`, and Scalar Pattern Types (`Int in ...`) `[Status: Implemented]`
The primitive scalar and vector types are:
- **Unit, Bottom (`never`), & Boolean**:
  - `void` (0 bytes, cardinality 1: function returns normally with no data)
  - **`never`** ([`Type::Never`](src/ir.rs); 0 bytes, cardinality 0: uninhabited bottom type for expressions and functions that never return, such as `return ...`, `@trap()`, `unreachable`, or `fn abort() -> never`; implicitly coerces to any expected type `T` on diverging branches like `let x = opt orelse return -1;`)
  - `bool` (1 byte: `true` / `false`)
- **Arbitrary-Width Signed & Unsigned Integers**: **`i1`..`i512`** and **`u1`..`u512`** (any bit width from 1 to 512 bits, represented uniformly by [`Type::Int`](src/ir.rs) `Type::Int { signed, bits }` in Stage 3 and lowered directly to LLVM `iN`), plus pointer-sized `isize` and `usize`
- **Distinct C-Compatible Integer Types (`c_*`)**: **`c_char`**, **`c_schar`**, **`c_uchar`**, **`c_short`**, **`c_ushort`**, **`c_int`**, **`c_uint`**, **`c_long`**, **`c_ulong`**, **`c_longlong`**, and **`c_ulonglong`** (distinct nominal integer types for C FFI imports and C header export generation)
- **Floating-Point**: `f32`, `f64` (with **`f128`** and **`c_longdouble`** reserved `[Status: Planned / Reserved]`)
- **Unsized / Unknown-Layout Type (`opaque`) & Type-Erased Pointers**: **`*const opaque`**, **`*mut opaque`**, **`&opaque`**, and **`&mut opaque`** (replacing C's `void*` so `void` remains a pure zero-sized unit type)
- **First-Class SIMD Vectors**: **`simd[T; N]`** (hardware vector of `N` scalar lanes of integer or float type `T`, represented by [`Type::Simd`](src/ir.rs) in Stage 3 and lowered directly to LLVM `<N x T>`)
- **Unicode Scalar Value**: **`rune`** (4 bytes; represents a single validated Unicode scalar value in `0x0000..=0xD7FF` or `0xE000..=0x10FFFF`)
- **Scalar Pattern / Range Types**: **`Int in Lo..=Hi | ...`** (an integer type constrained to a compile-time union of inclusive ranges, represented by [`Type::Pattern`](src/ir.rs))
- **Compile-Time Meta-Type**: `type` ([`Type::MetaType`](src/ir.rs); 0 runtime bytes, exists only at `comptime`)

#### Arbitrary-Width Integers (`i1`..`i512`, `u1`..`u512`) & `packed` Bit-Level Layouts
1. **Unified Representation (`Type::Int { signed: bool, bits: u16 }`) `[Status: Implemented]`**:
   - Instead of hardcoding only power-of-two integer widths (`8, 16, 32, 64, 128`), any signed (`i1`..`i512`) or unsigned (`u1`..`u512`) integer width up to 512 bits is a first-class primitive type.
   - Standard standalone memory layout rounds `(bits + 7) / 8` up to the next power-of-two byte size (with alignment capped at 16 bytes), while arithmetic (`+`, `+%`, `+|`), comparisons, and casts operate at the exact `N`-bit precision (`[-2^(N-1), 2^(N-1) - 1]` or `[0, 2^N - 1]`).
   - Wide integers (`u256`, `u512`) support 256-bit/512-bit cryptography, hashes (SHA-256, SHA-512), and wide bitsets (`u256` character-class tables or 512-bit AVX-512 bitmasks).
2. **Eliminating C Bitfield Undefined Behavior (`packed struct` / `packed opaque` & `enum(uN)`) `[Status: Implemented]`**:
   - When placed inside a `packed struct` or `packed opaque` (which lowers to an `iN` backing integer with automatic shift/mask field extraction), arbitrary-width integers (`u1`, `u3`, `u4`, `u12`, `u24`, `u48`) and sub-byte enums (`enum(u3)`) pack bit-tightly with deterministic layout—completely replacing C's implementation-defined `: 3` bitfield syntax:
     ```rust
     pub packed struct Ipv4Header {
         ihl:       u4 = 5, // Bits 0..=3  (LSB of byte 0 on little-endian)
         version:   u4 = 4, // Bits 4..=7  (MSB of byte 0 on little-endian)
         ecn:       u2,     // Bits 8..=9
         dscp:      u6,     // Bits 10..=15
         total_len: u16,    // Bits 16..=31
     } // Guaranteed exact 32-bit (4-byte) backing integer `i32`
     ```
   - **Deterministic Bit & Byte Ordering**:
     - Fields of a `packed struct` or `packed opaque` are packed sequentially starting from **least-significant bit 0 (LSB 0)** of the aggregate `iN` backing integer (`bit_offset(field_k) = sum_{j < k} bits(field_j)`). Reading `hdr.version` lowers to `((hdr_bits >> 4) & 0xF) as u4`.
     - In memory, the backing `iN` integer uses the target architecture's native endianness (little-endian on x86_64/AArch64/RISC-V); byte-swapping intrinsics (`@bswap`) can be applied to the whole packed value or multi-byte fields when converting to/from big-endian network byte order.
   - **No References to Packed Fields**:
     - Because fields of a `packed struct` or `packed opaque` may sit at non-byte-aligned bit offsets or unaligned byte boundaries, taking a reference (`&p.field`, `&mut p.field`, or `&rel self.field`) to any field of a `packed` type is a **compile-time error**. Packed fields are read and written strictly by value.
3. **Computed `comptime` Integer Widths (`@Int`) `[Status: Implemented]`**:
   - `comptime` functions can compute exact-width integer types dynamically (e.g., `@Int(.unsigned, a.bits + b.bits)` for lossless widening multiplication without overflow).

#### First-Class SIMD Vector Types (`simd[T; N]`) `[Status: Implemented]`
While `u256` and `u512` represent single 256-bit or 512-bit scalar integers (with carry propagation across all 256/512 bits), **`simd[T; N]`** represents a parallel SIMD vector of `N` independent lanes of scalar element type `T` (`i8`..`i128`, `u8`..`u128`, `f32`, `f64`):
- **Stage 3 & LLVM Lowering**: `simd[ty0; 16]` ([`Type::Simd`](src/ir.rs)) lowers directly to LLVM's first-class vector type `<16 x i32>` (targeting SSE/AVX2/AVX-512/NEON vector registers).
- **Splat & Lane-Wise Construction**: `aggregate ty_simd(copy _scalar)` splats a single scalar across all `N` lanes, while `aggregate ty_simd(op0, op1, ...)` constructs each lane explicitly.
- **Parallel Lane-Wise Operations**: Arithmetic (`add`, `sub`, `mul`, `add_wrap`, `sub_wrap`, `mul_wrap`, `add_sat`, `sub_sat`, `mul_sat`, `div`, `rem`) and bitwise operations (`bitand`, `bitor`, `bitxor`, `shl`, `shr`, `neg`, `not`) operate in parallel across all `N` lanes, lowering to LLVM vector instructions and vector intrinsics (`@llvm.sadd.sat.v16i8`, `@llvm.sadd.with.overflow.v4i32`).
- **Lane Indexing & `comptime` Construction**: Individual lanes can be indexed via `_vec[_idx]`, and `comptime` type functions can construct SIMD types dynamically via `simd[copy _elem; copy _len]` ([`Rvalue::SimdType`](src/ir.rs)).

#### Why `rune` Instead of `char` `[Status: Implemented]`
- **`char` is historically ambiguous**: In C/C++ `char` is a 1-byte integer (`u8` / `i8`), in Java/C#/UTF-16 it is a 16-bit code unit (`u16`), in Rust it is a 32-bit Unicode scalar value, and in human prose a "character" usually means a user-perceived Unicode Extended Grapheme Cluster (which has variable byte length).
- **`rune` (borrowed from Go/Plan 9) is unambiguous**: A `rune` is always a 32-bit Unicode scalar value, while raw bytes are always `u8`.
- **Distinct Type Identity from `u32`**: Unlike Go (where `rune` is merely a type alias for `int32`), `rune` is a **distinct primitive type** ([`Type::Rune`](src/ir.rs) in Stage 3):
  - **Formatting & Display**: Formatting a `rune` outputs the UTF-8 character (`'🦀'`), whereas formatting a `u32` outputs the decimal number (`129408`).
  - **`comptime` Type Reflection**: Because [`Type::Rune`](src/ir.rs) (`rune`) is distinct from `Type::Int { signed: false, bits: 32 }` (`u32`) in Stage 3, `comptime` functions and overloads can distinguish text code points from 32-bit numbers.
  - **No Nonsense Arithmetic**: Arithmetic and bitwise operators on `rune`s (`'a' * 'b'`, `'a' + 1`) are compile errors (comparisons are allowed); explicit casts (`r as u32`) are always zero-cost, and `u8 as rune` is always safe and lossless because ASCII/Latin-1 (`0x00..=0xFF`) is a valid subset of Unicode scalar values.
  - **Literals**: `'a'`, `'\n'`, `'\u{1F980}'` have type `rune`; `b'a'`, `b'\n'`, `b'\x7F'` have type `u8`.

#### Distinct C-Compatible Integer Types (`c_*`) & Type-Erased `opaque` Pointers (`*const opaque` / `*mut opaque` / `&opaque` / `&mut opaque`) `[Status: Implemented]`
1. **Distinct C ABI Integer Types (`c_char`, `c_schar`, `c_uchar`, `c_short`, `c_ushort`, `c_int`, `c_uint`, `c_long`, `c_ulong`, `c_longlong`, `c_ulonglong`)**:
   - Rather than making `c_int` a transparent alias for `i32` or `c_long` a transparent alias for `i64`, each C integer type has a **distinct `TypeId`** in [`src/lower/`](src/lower/mod.rs) backed by the target ABI's [`Type::Int`](src/ir.rs) (`LP64` on 64-bit Unix: `c_char`/`c_schar` = `i8`, `c_uchar` = `u8`, `c_short` = `i16`, `c_ushort` = `u16`, `c_int` = `i32`, `c_uint` = `u32`, `c_long`/`c_longlong` = `i64`, `c_ulong`/`c_ulonglong` = `u64`):
     - **Accurate C Header (`.h`) Export Generation**: Preserving `CIntKind` in the type system allows future C header generation from exported functions/types to emit `int`, `long`, `unsigned long`, and `char` rather than collapsing them to `int32_t`, `int64_t`, or `int8_t`.
     - **Portability & C++ Overload Safety**: Mixing `c_int` with `i32`, `c_long` with `i64`, or `c_long` with `c_longlong` without an explicit `as` cast (`x as c_int`, `y as i32`) is a compile-time error, catching `LP64` (Unix 64-bit `long`) vs. `LLP64` (Windows 32-bit `long`) portability bugs immediately on any host.
     - **Full Ergonomics**: Integer literals coerce directly when a `c_*` type is expected (`let rc: c_int = 0;`), same-type arithmetic (`a + b` where `a: c_int, b: c_int`) works naturally, and all `c_*` types satisfy the `scalar`, `number`, `integer`, and `signed` / `unsigned` meta-type constraints.
   - **Reserved Extended Floating-Point Types (`f128` & `c_longdouble`) `[Status: Planned / Reserved]`**:
     - `f128` (IEEE 754 binary128 quadruple precision) and `c_longdouble` (platform-dependent C `long double`: 80-bit `x86_fp80` on x86_64 SysV, `f128` on AArch64 Linux, `f64` on Windows/macOS ARM64) are reserved keywords in [`src/frontend/mod.rs`](src/frontend/mod.rs).
2. **`void` (Zero-Sized Unit Type) vs. `opaque` (Encapsulated Product Type, Universal Type-Erased Pointee, `extern opaque` FFI Handles, Opaque Newtypes, & Existential Return Types)**:
   - **`void` is strictly a zero-sized unit type (ZST)** (`size_of(void) == 0, align_of(void) == 1`), never C's incomplete type of unknown layout.
     - **Pointers & References to ZSTs (`void`, `struct {}`, `opaque {}`, `[T; 0]`)**: Like Rust and Zig, SlopLang permits pointers and references to any zero-sized type (`&void`, `&mut void`, `*const void`, `*mut void`, `*own void`, `&[void]`), enabling uniform generic containers (`Box[void]`, `Vec[void]`, `HashMap[K, void]`). Canonical ZST allocations and dangling pointers map to their power-of-two alignment **`@align_of(T) as *mut T`** (`1, 2, 4, 8, 16, ...`) in the OS's unmapped null page (`0x1..0x1000`), preserving the `0` null-pointer niche (`?*mut void`, `?&void`) with zero heap traffic and zero-byte memory reads/writes. At the C FFI boundary (`export` / `extern fn`), `*const void` and `*mut void` are rejected with a diagnostic directing the author to `*const opaque` / `*mut opaque` for C's untyped `void*`.
   - **Sized Encapsulated Product Type (`opaque Name { ... }` / `opaque(copy | affine | linear, unsafe send, unsafe sync, !send, !sync)`) `[Status: Implemented]`**:
     - `opaque Name { ... }` (or `opaque { ... }` inside a `comptime` type function) defines a sized, encapsulated nominal product type whose fields are **strictly private** to the `opaque { ... }` block (`pub` on a field inside `opaque { ... }` is a compile-time error), and which owns custom lifecycle hooks (`default`, `clone`, `drop`, `format`) and self-referential `&rel` fields. Even a zero-field `opaque Token {}` is a sized (0-byte ZST) encapsulated value type.
   - **Universal Type-Erased Pointee (`*const opaque`, `*mut opaque`, `&opaque`, `&mut opaque`) `[Status: Implemented]`**:
     - Bare `opaque` in a pointer/reference type is an **unsized, uninstantiable pointee type** representing memory of unknown layout, alignment, and size:
     - **Forbidden by value, dereference, or pointer offset**: Using bare `opaque` by value (`let x: opaque`, parameter `x: opaque`, struct field `f: opaque`, array `[opaque; N]`), dereferencing `*p` on an `opaque` pointer/reference, or performing element-scaled pointer arithmetic `p + i` on `*const opaque` / `*mut opaque` is a **compile-time error**.
     - **Raw type-erased pointers (`*const opaque` and `*mut opaque`)**: Any `*const T`, `*mut T`, `&T`, or `&mut T` implicitly coerces (or casts via `as`) to `*const opaque`, and any `*mut T` or `&mut T` implicitly coerces (or casts via `as`) to `*mut opaque` (matching C's `void*` / `const void*` at FFI boundaries such as `free(ptr: *mut opaque)` or `pthread_create`). Converting back (`p as *mut T` or `p as *const T`) requires an explicit `as` cast.
     - **Safe NLL borrow-checked type-erased references (`&opaque` and `&mut opaque`)**: Any `&T` or `&mut T` coerces to `&opaque`, and any `&mut T` coerces to `&mut opaque` (with automatic reborrowing of `&mut opaque` -> `&mut opaque` / `&opaque`), while **retaining the underlying NLL borrow loan** in [`src/borrowck.rs`](src/borrowck.rs).
   - **Unsized Foreign C Handles (`pub extern opaque Sqlite3;` / `pub extern opaque Sqlite3 { ... }`) `[Status: Implemented]`**:
     - Declaring `pub extern opaque Name;` or `pub extern opaque Name { ... }` (with methods only, no fields) creates a **distinct nominal unsized foreign opaque type** modeling C forward-declared incomplete structs (`typedef struct sqlite3 sqlite3;`, `typedef struct _IO_FILE FILE;`).
     - Like bare `opaque`, an `extern opaque` type is unsized and cannot declare fields, be instantiated by value, dereferenced, or offset with pointer arithmetic.
     - **Distinct Handle Type Safety**: Unlike universal `*mut opaque`, pointers to distinct `extern opaque` types (`*mut Sqlite3` vs. `*mut CFile`) do **not** implicitly coerce to each other (preventing passing a `FILE*` to `sqlite3_close`), nor do arbitrary concrete pointers (`*mut i32`) implicitly coerce to `*mut Sqlite3`. Both `*mut Sqlite3` and `*mut CFile` still implicitly coerce to the universal `*mut opaque` / `*const opaque` (`void*`).
     - **Inherent & Extension Methods**: An `extern opaque` type can define inherent methods inside `{ ... }` (or module-level extension methods) taking `self: *mut Self`, `self: *const Self`, `self: &Self`, or `self: &mut Self`, as well as associated constructor functions (`Sqlite3::open(...)`).
   - **Distinct Types (`pub type UserId = distinct u64;` / `pub type UserId = distinct u64 { ... }`) `[Status: Implemented]`**:
     - Declaring `type Name = distinct Underlying;` (optionally with inherent methods in `{ ... }`) creates a **sized, zero-cost nominal type** with the exact ABI, size, alignment, and ownership semantics of the underlying type. It separates values that share a representation (`UserId` vs `OrderId` vs a raw `u64`); it does not hide the representation, which `opaque Name { ... }` does.
     - **The same rules in every module**: a distinct type never converts implicitly to or from its underlying type (not even in its defining module) and never mixes with another distinct type; `as` converts both ways anywhere (`raw as UserId`, `id as u64`). Literals initialize it (`let id: UserId = 7;`) and the underlying type's operators apply between values of the same distinct type (`id + 1` is a `UserId`).
     - It wraps any sized type except a tuple or an anonymous struct, directly or through an `alias`: their fields would be reachable only through `as`, so write `struct Name { ... }`, which is just as nominal and keeps the fields usable. The former spellings `opaque Name = T` and `type Name = opaque T` are errors that name the new one.
   - **Existential Return Types (`-> opaque MyTrait` / `-> opaque A + B`) `[Status: Implemented]`**:
     - Writing `-> opaque MyTrait` (or `-> opaque A + B` / `-> opaque callable`) in a function return type returns a concrete value **by value on the stack** with zero vtable or heap overhead, while hiding the concrete return type behind the trait/constraint bound.
     - The compiler infers the single concrete return type from the function body's `return` statements and verifies at compile time that it satisfies the declared bound(s). Callers can invoke trait methods, pass the value to generic `[T: MyTrait]` parameters, or borrow it as `&MyTrait`, but cannot bind it to the hidden concrete type name, access private/concrete fields, or call non-trait inherent methods.
   - **C FFI Exports (`export` Types, `export fn`, Automatic Null Checks, `?T` / `E!T` Lowering, & C Header Generation) `[Status: Implemented]`**:
     - **Valid `export` Types**:
       - **By value across C FFI**: Standard fixed-width primitives (`i8`..`i64`, `u8`..`u64`, `isize`, `usize`, `f32`, `f64`, `bool` mapped to C99/C23 `<stdbool.h>` `bool`, `void`), distinct C integer types (`c_char`..`c_ulonglong` mapped to native C `char`, `int`, `unsigned long`, etc.), `export enum`, unit-only `export error` (integer error codes lowered to a C `typedef enum`; see [`export error`: Unit Error Codes vs. Payload-Carrying Errors](#c-values-of-export-error-status-implemented)), `export type Name = distinct T` distinct types over export-valid types, `export struct` (transparent C `struct` whose fields may also include fixed-size arrays `[T; N]` of export-valid types), `export union` (C's tagged representation, see below), `export overlay` (untagged C `union` of export-valid fields, emitted as `typedef union Name Name;`; reading a field is `unsafe` as for any overlay), and raw pointers (`*const T`, `*mut T`, `?*const T`, `?*mut T`).
       - **Payload-carrying `export error` (`export fn ... -> E!T`)**: An `export error` with payload variants (`export error MyError { Bad: i32 }`) is valid as the error side `E` of an `export fn` returning `E!T`, where C receives the status code enum (`MyError_Tag`) as the return value and the untagged payload union (`union MyError* err_out`) via an out-pointer. Because C's `union MyError` is untagged, passing or embedding a payload-carrying `export error` by value outside `E!T` return position is rejected at compile time.
       - **`export opaque` (Opaque Handle Only)**: All exported multi-field `opaque` types (`export opaque Name { ... }`, whether `copy`, affine `drop`, or `linear`) are enforced as **opaque handle types** across FFI (`typedef struct Name Name;` in the generated `.h` header). Passing, returning, or embedding an `opaque` struct by value in an `export fn` or `export struct` is a compile-time error; C callers interact with `export opaque` types strictly through raw pointers (`*mut Name`, `*const Name`, `?*mut Name`, `?*const Name`).
       - **Forbidden across `export` FFI**: Safe references (`&T`, `&mut T`, `&[T]`, `&mut [T]`, `&str`, `&Trait`, `&rel`), bare `[T; N]` arrays by value in `export fn` signatures (must be wrapped in an `export struct` or passed via pointer), `export error` that embeds other error sets or carries non-`copy` payloads, and `export trait` are rejected at compile time.
     - **C Calling Convention for Aggregates** `[Status: Implemented (x86-64 System V, AArch64)]` ([`src/c_abi.rs`](src/c_abi.rs)): `export fn` definitions (the C-ABI wrapper) and calls to `extern fn` pass structs, overlays, and arrays by value the way C does, rather than as LLVM first-class aggregates. Aggregates up to 16 bytes travel in the registers C uses, reinterpreted per eightbyte (`{ i32, f64 }` as `i64, double`; `{ f32, f32 }` as `<2 x float>`); larger ones, and any that no longer fit in the remaining registers, go through memory (`byval` arguments, `sret` returns). Integers narrower than 32 bits and `bool` carry `signext` / `zeroext`. On AArch64 (AAPCS64) a homogeneous floating-point aggregate (1-4 `f32`s or `f64`s) travels in consecutive FP registers (`[3 x float]`), any other aggregate up to 16 bytes in one or two integer registers (`i64`, `[2 x i64]`), and a larger one as a pointer to a caller-made copy (arguments) or through `sret` (returns); narrow integers are extended only on Apple's variant. `LlvmLowering::lower_for_target` emits for a target other than the host; the AArch64 signatures are tested against clang's. Other targets reject by-value aggregates at the C boundary (pass a pointer). Function pointers that cross the C boundary are typed `extern fn(...) -> R`: a distinct type from the SlopLang `fn(...) -> R` (neither converts to the other), produced by `@c_abi(f)` and by naming an `extern fn`, accepted in `export fn` signatures and `export struct` fields (declared in the header as `R (*name)(...)`), and called with the C convention, so callbacks from C and pointers returned by C pass aggregates correctly.
     - **`export union`: C's Tagged Representation** `[Status: Implemented]`: An exported union is laid out, and declared in the header, as `struct Name { Name_Tag tag; union { ... } payload; }`, the same representation as Rust's `#[repr(C)]` enums. SlopLang's own union layout already places the tag first and the payload at its natural alignment, so nothing changes in memory; inside SlopLang, `match`, `if let`, and `T::Tag` work as for any union.
       - **Tag**: a generated `typedef enum Name_Tag { Name_Variant = 0, ... }` numbered in declaration order (or using explicit `= N` values and optional `export union(Int)` backing integer type).
       - **Payload members** are named after their variants: unit variants have none (an all-unit union has no `payload` member), a type payload is a member of that type, and an inline `Variant: struct { ... }` or tuple payload is an inline `struct` (tuple fields are `_0`, `_1`, ...). Payloads must be FFI-safe, and the union must be `copy`, since C copies it freely.
       - **Validation**: values C hands to SlopLang by value are checked before SlopLang code sees them: the C-ABI wrapper of an `export fn` checks its parameters, and a call to an `extern fn` (or through an `extern fn(...)` pointer) checks its result. A union or unit-only `export error` tag must name a variant, and the active variant's payload is checked in turn; a `bool` stored in memory must be 0 or 1, an enum one of its values, a `rune` a Unicode scalar value, and a non-optional raw pointer non-`NULL`; struct fields and array elements are checked recursively. A violation traps. Overlays are not checked (any bits are valid), and values reached through pointers are trusted: C code must store valid data behind them.
     - <a id="c-values-of-export-error-status-implemented"></a>**`export error`: Unit Error Codes vs. Payload-Carrying Errors** `[Status: Implemented]` ([`Compiler::instantiate_error`](src/lower/types.rs)):
       - Any `error` / `export error` (that does not embed another error set) may specify an optional backing integer type (`error(u8)` / `error(c_int)`, like `enum(u8)`), a custom C success sentinel (`ok Success = 200`; `ok Name` alone means `= 0`), and explicit per-variant tag values (`Variant = 404` or `Variant: i32 = 404`): e.g. `export error DbError { NotFound = 404, Busy = -1, Aborted = 7 }`, `export error(c_int) ExplicitCInt { ok Ok = 1, Zero = 0, Neg = -5 }`, or `export error MyError { Bad: i32 = 1 }`.
       - By default, **`Ok = 0` is automatically reserved for the C success sentinel**, and automatic variant enumeration starts at **`1`** (`1, 2, 3, ...`) in declaration order. If a custom `ok <ident> = <value>` success sentinel is declared, `0` is freed for use as an ordinary error variant (`Zero = 0`). The success sentinel is emitted first in the C enum (`<Name>_<OkIdent> = <OkVal>,`) and is used only at the C FFI boundary; inside SlopLang it is not a failure variant, so `match` over an `error` remains exhaustive over failure variants only, and `E::Tag` / `e.tag` expose the failure variants' tag enum.
       - Once one variant has an explicit `= N` value, every variant must; values must be distinct, must not collide with the reserved success sentinel's name or value, and must fit the backing type (or for a default C `enum`, all within `int` or all non-negative within `unsigned int`, so HRESULT-style `0x80004005` works).
       - **Unit-only `export error`**: When all variants have `void` payloads, the C value **is** the stored tag ([`Program::union_tag_values`](src/ir.rs)), and the C header emits `typedef enum Name { Name_Ok = 0, Name_Var = 1, ... } Name;`. A unit-only `export error` has the C enum's layout everywhere: `E!T` return values, by-value parameters, `*mut E` / `*const E` pointees, and `export struct` fields. The C-ABI wrapper of an `export fn` traps on a by-value `export error` parameter whose value names no failure variant (including the C `ok` success sentinel).
       - **Payload-carrying `export error`**: When at least one variant carries a payload (`export error MyError { Bad: i32 }`), the C header splits the tag and payload into:
         - `typedef enum MyError_Tag { MyError_Ok = 0, MyError_Bad = 1, ... } MyError_Tag;` (status code returned by `export fn`), and
         - `typedef union MyError MyError; union MyError { int32_t Bad; ... };` (untagged payload union written through `MyError* err_out` on failure; unit variants are omitted from `union MyError`).
     - **Automatic Panicking Null Checks on Non-Optional `*mut T` / `*const T` Parameters**:
       - In `export fn`, bare `*mut T` and `*const T` parameters are contractually non-null (`T*` / `const T*`), and the C-ABI wrapper (see the two-symbol model below) checks them on entry (`(ptr as usize) == 0` -> `@llvm.trap()`) before calling the SlopLang body.
       - Explicitly nullable raw pointer parameters (`?*mut T` and `?*const T`) accept C `NULL` without trapping and unwrap inside the function via `orelse` or `if let`.
     - **`?T` and `E!T` Return Lowering in `export fn`**:
       - `export fn foo(...) -> ?*mut U` / `-> ?*const U`: Returns a nullable C pointer `U*` / `const U*` directly (`NULL` on `null`).
       - `export fn foo(...) -> ?T` (for non-pointer value `T`): Lowers to `bool foo[...](/* out */ T* out_val)` — writes `*out_val` (if `out_val != NULL`) and returns `true` on `Some(v)`, or returns `false` on `null`.
       - `export fn foo(...) -> E!T` (where `E` is a unit-only `export error`):
         - For `T != void`: Lowers to `E foo[...](/* out */ T* out_val)` — writes `*out_val` (if `out_val != NULL`) and returns `E`'s success sentinel (`<E>_Ok = 0` by default) on `Ok(v)`, or returns the failure variant's `E` enumerator on `Err(e)`.
         - For `T == void`: Lowers to `E foo(...)` — returns `E`'s success sentinel on `Ok`, or the failure variant's `E` enumerator on `Err(e)`.
       - `export fn foo(...) -> E!T` (where `E` is a payload-carrying `export error`):
         - For `T != void`: Lowers to `E_Tag foo[...](/* out */ T* out_val, /* out */ E* err_out)` — on `Ok(v)`, writes `*out_val` (if `out_val != NULL`) and returns `E`'s success sentinel; on `Err(e)`, writes the active variant's payload to `*err_out` (if `err_out != NULL` and the active variant has a payload) and returns the failure variant's `E_Tag` status code.
         - For `T == void`: Lowers to `E_Tag foo[...](/* out */ E* err_out)` — returns `E`'s success sentinel on `Ok`, or writes `*err_out` (if non-`NULL` and non-unit) and returns the failure variant's `E_Tag` status code on `Err(e)`.
     - **Two-Symbol Model: SlopLang Callers Use Only the SlopLang Signature** `[Status: Implemented]`:
       - Every `export fn foo` is compiled to **two functions**: an internal SlopLang-ABI body (returning `?T` / `E!T` natively, with no entry null checks or out-pointer writes) and a C-ABI wrapper exported under the symbol `foo` that performs the null checks and the `?T` / `E!T` out-pointer lowering before delegating to the internal body.
       - Inside SlopLang, an `export fn` is callable **only** through its SlopLang signature (`try`, `catch`, `orelse`); calling it with the lowered C out-pointer arguments is a compile-time error. Every SlopLang call site binds directly to the internal body.
       - Using `foo` as a function value in SlopLang yields its SlopLang function-pointer type (`fn(...) -> E!T`). Handing the C-ABI wrapper to C code as a callback (`qsort`, `pthread_create`) requires the explicit intrinsic **`@c_abi(foo)`**, which yields a C function pointer with the wrapper's lowered C signature (`@c_abi(maybe)` for `export fn maybe(ok: bool) -> ?i32` has type `extern fn(bool, *mut i32) -> bool`). `@c_abi` of a non-`export` function is a compile-time error.
     - **Automatic `.h` C Header Generation** ([`Compiler::generate_c_header`](src/lower/export.rs), [`Compiler::compile_source_with_c_header`](src/lower/mod.rs)): Emits a complete C99/C11/C23/C++ compatible `.h` header with `#include <stdint.h>`, `#include <stddef.h>`, `#include <stdbool.h>`, forward-declared opaque handle structs, enum/error definitions, `struct` definitions, and C function prototypes.

#### Scalar Pattern / Range Types (`Int in Lo..=Hi | ...`) `[Status: Implemented]`
Rather than embedding an unpredictable SMT solver for arbitrary predicate refinement types (`x % 2 == 0`), the type system directly supports **Scalar Pattern Types**—constraining any integer type `Int` to a union of inclusive compile-time ranges:

```rust
// 1. `rune` has the exact same range constraint as:
//    u32 in 0x0000..=0xD7FF | 0xE000..=0x10FFFF

// 2. Non-zero integers via a 3-line comptime function (replaces NonZeroU8..NonZeroU64)
fn NonZero[Int: integer] -> type {
    return Int in 1..=Int::MAX;
}

// 3. Domain-specific bounded scalars & proven-in-bounds array indices
alias Ascii   = u8  in 0x00..=0x7F;
alias Percent = u8  in 0..=100;
alias PosixFd = i32 in 0..=2147483647; // Valid POSIX file descriptors are >= 0

fn Index[len: NonZero[usize]] -> type {
    return usize in 0..=(len - 1);
}
```

1. **Deterministic Niche Optimization Rule (`?T`)** ([`Program::union_niche`](src/ir.rs)):
   - Any bit pattern outside a scalar or pointer type's valid value set is a **niche**. When `T` has one, `?T` is laid out exactly like `T` (no tag): the chosen `null` bit pattern means `null` and every other value means a present payload. The compiler selects the `null` bit pattern using a deterministic priority order so FFI layouts are completely predictable:
     1. **`0` (All-Zeroes)** if `0` is outside `T`'s valid set:
        - `?&T`, `?&mut T`, `?*const T`, `?*mut T`, and `?fn(...)` use `0` (`null` pointer) and are 8 bytes.
        - `?NonZero[u32]` is 4 bytes and uses `0` for `null`.
     2. **All-Ones (`0xFF..FF`, i.e., `-1` for signed or `MAX` for unsigned)** if `0` is valid in `T` but all-ones is outside `T`'s valid set:
        - **`?PosixFd` (`i32 in 0..=i32::MAX`) is 4 bytes and uses `-1` (`0xFFFFFFFF`) for `null`**, matching POSIX C FFI return conventions (`open()`, `socket()`, `read()`) with zero wrapper conversion.
        - **`?rune` is 4 bytes and uses `0xFFFFFFFF` (`u32::MAX`) for `null`**.
        - **`?Ascii` (`u8 in 0x00..=0x7F`) and `?Percent` (`u8 in 0..=100`) are 1 byte and use `0xFF` for `null`**.
     3. **Lowest Excluded Value (`Hi_0 + 1`)** immediately above the first contiguous valid interval if both `0` and all-ones are valid:
        - **`?Digit` (`u8 in 0..=9 | 200..=255`) is 1 byte and uses `10` for `null`**.
     - Types with no niche (`?i32`, `?bool`, optionals of aggregates) keep a separate tag. Niche selection applies to `?T` only; general `union` types always carry a tag.
2. **Conversion, Widening, Narrowing & Arithmetic Rules**:
   - **Bounds Span the Base Type**: Each bound is a constant of the base type and must fit it (`u8 in 0..=256` is a compile error); a range may cover the base type's whole range (`u8 in 0..=255`, `i8 in -128..=127`).
   - **Compile-Time Verified Literals**: Assigning a constant or literal to a pattern type is verified at `comptime` (`let p: Percent = 50;` succeeds; `let p: Percent = 150;` is a compile error). A runtime value of the base type never narrows implicitly (`let p: Percent = x;` is a compile error); it needs one of the explicit conversions below.
   - **Lossless Subset-to-Superset Widening**: A pattern type `A` can be cast (`x as B`) or widened without a runtime check into its base integer type or any pattern type `B` whose valid intervals are a superset of `A`'s intervals (e.g., `Ascii as u8`, `Ascii as rune`, `NonZero[u32] as u32`).
   - **Arithmetic Operates on the Base Integer Type**: To avoid Ada-style intermediate overflow traps or interval-type explosion across loops, arithmetic (`a + b`), unary operators, and comparisons operate on the base integer type (`u8`, `u32`, etc.): `p + 1` is a `u8`, and the literal `1` need not lie in `p`'s ranges. Storing the result back into a pattern type takes an explicit `as P` or `as ?P`.
   - **Checked vs. Unchecked Runtime Narrowing**: Converting an unconstrained runtime integer `x` into a pattern type `P` requires either:
     - **Checked narrowing (`x as ?P`)** `[Status: Implemented]`: Performs the range check and returns `?P` (`null` if out of range), composing naturally with `orelse` (`let p = (raw as ?Percent) orelse return -1;`).
     - **Direct checked cast (`x as P`)** `[Status: Implemented]`: Verifies at `comptime` for constants, or traps at runtime if `x` is outside `P`'s valid intervals.
3. **Bounds-Check Elimination & LLVM `!range` Metadata `[Status: Implemented]`**:
   - Indexing an array `[T; N]` with a value of type `usize in Lo..=Hi` where `Hi < N` elides the runtime bounds check completely at compile time.
   - When lowering to Stage 4 LLVM IR ([`src/llvm.rs`](src/llvm.rs)), loads of pattern-typed values attach LLVM `!range` metadata, enabling LLVM to eliminate redundant comparisons and dead branches downstream. Intervals are normalized to LLVM's signed, sorted, non-adjacent form, and a pattern covering its whole base type gets no metadata.

#### Mutable Bindings `[Status: Implemented]`
A binding's own memory is read-only unless it is declared `mut` (`let mut x`, `let mut { a, b } = t;`, a `mut x` parameter). Assigning to it or any field or element of it, borrowing it `&mut` / `&raw mut`, calling a `&mut self` method on it, iterating it with `for ref mut`, and assigning it from a closure all require `mut`; the error names the binding (`Cannot assign to 'p': it is not declared 'mut'`). Writes through a reference or pointer are governed by that pointer instead (`p: &mut T` permits `p.x = 1` without `mut p`). Loop variables and `match` / `if let` / `while let` bindings are immutable.

#### Implicit Conversions `[Status: Implemented]`
Implicit conversions are a closed list ([`FuncLowerer::classify_coercion`](src/lower/stmt.rs)); any other mismatch is a compile error (`cannot implicitly convert 'i64' to 'i32'`). Numeric types never convert implicitly: widening, narrowing, `bool` to integer, and integer to float all use `as`. The list:
- **References and pointers**: reborrowing a named `&mut T` / `&mut [T]` / `&mut Trait` as `&mut` or `&`; `&mut T` -> `&T`; `&T` / `&mut T` -> `*const T` / `*mut T`; `*mut T` -> `*const T`; any pointer -> `&opaque` / `*const opaque` (keeping mutability rules); `&T` / `&mut T` -> `&Trait` / `&mut Trait` and `&mut Trait` -> `&Trait`.
- **Slices**: a string literal -> `&str`, `&[T; N]` / `&mut [T; N]` -> `&[T]` / `&mut [T]`, and `&mut [T]` -> `&[T]`.
- **Optionals and results**: `T` -> `?T` (a raw pointer `*T` -> `?*T` maps null to `null`), a pointer coercing to `*T` -> `?*T`, `T` -> `E!T`, `E` -> `E!T`, `E'!T` -> `E!T`, and `E'` -> `E` when `E'`'s variants are a subset of `E`'s.
- **Pattern types**: a verified constant -> a pattern type, and a pattern type -> its base type. (A distinct type and its underlying type convert only with `as`.)
- **`never`** (a diverging expression) fits any type.

**Literal bindings infer their type** ([`src/lower/infer.rs`](src/lower/infer.rs)): an unannotated `let` / `let mut` initialized by an integer or float literal takes its type from its first typed use (a parameter, the other operand of an operator, an index, a return value, or an assignment to a typed place), so `let mut i = 0; while i < n { a[i] ... }` makes `i` a `usize` and `let x = 5; f(x)` works for `f(x: i32)`. Literals already given to the binding are checked against the type it settles on (`let x = 300; f_u8(x)` is an error), and a binding used at two different types is an error. With no typed use it is `i64` (`f64` for floats). A use whose type cannot wait (taking the address, a closure capture, a method receiver, a tuple element) settles it on `i64` / `f64` for the moment; if a later typed use then needs another type (`let mut c = 0; let g = fn() { c += 1; }; take_i32(c)`), the function is lowered again with the binding given that type from the start.

Binary operators take both operands at one type: the right operand converts to the left operand's type through the list above (so `s == "text"` compares a `&str` with a literal), and anything else is an error. Shifts are no exception: `a << b` needs `b` of `a`'s type (`a << (b as u64)`).

#### Integer Overflow, Division, Shift & Cast Semantics `[Status: Implemented]`
Following Zig's philosophy, standard integer arithmetic (`+`, `-`, `*`) **never silently wraps**. Instead, distinct operator families express exact overflow semantics:

| Operator Family | High-Level Syntax | Stage 3 (`SLIR`) [`BinOp`](src/ir.rs) | Overflow / Edge-Case Behavior (`comptime` & Runtime) | Stage 4 LLVM Lowering ([`src/llvm.rs`](src/llvm.rs)) |
| :--- | :--- | :--- | :--- | :--- |
| **Default (Checked)** | `a + b`, `a - b`, `a * b` | `add`, `sub`, `mul` | **Compile error** at `comptime`; **traps** (`@llvm.trap()`) at runtime | `@llvm.[s\|u][add\|sub\|mul].with.overflow` + branch to `@llvm.trap()` |
| **Wrapping (Modular)** | `a +% b`, `a -% b`, `a *% b` | `add_wrap`, `sub_wrap`, `mul_wrap` | Wraps modulo $2^N$ at both `comptime` and runtime | Plain two's-complement `add`, `sub`, `mul` |
| **Saturating (Clamping)** | `a +\| b`, `a -\| b`, `a *\| b` | `add_sat`, `sub_sat`, `mul_sat` | Clamps to `[T::MIN, T::MAX]` | `@llvm.[s\|u][add\|sub].sat` / overflow-clamped `select` |
| **Fallible (`-> ?T`)** `[Status: Implemented]` | `a +? b`, `a -? b`, `a *? b` | `add_checked`, `sub_checked`, `mul_checked` | Returns **`?T`** (`null` on overflow); chains with `orelse` / `try` | `@llvm.[s\|u][add\|sub\|mul].with.overflow` -> `?T` |
| **Unchecked (`nsw`/`nuw`)** | `unsafe @add_unchecked(a, b)` (or proven by Pattern Type) | `add_unchecked`, `sub_unchecked`, `mul_unchecked` | **Compile error** at `comptime`; assumed no-wrap at runtime | `add nsw` / `add nuw`, `sub nsw` / `sub nuw`, `mul nsw` / `mul nuw` |

- **Division (`/`), Remainder (`%`), Negation (`-x`), Shifts (`<<`, `>>`), and Casts (`as`)**:
  - **Division & Remainder (`a / b`, `a % b`)**: Truncates toward zero. Dividing by zero (`b == 0`) or signed overflow (`T::MIN / -1` and `T::MIN % -1`) is a **compile error** at `comptime` and **traps** (`@llvm.trap()`) at runtime before executing LLVM `sdiv`/`udiv`/`srem`/`urem` (never undefined behavior).
  - **Unary Negation (`-x`)**: Checked `0 - x` on signed integers (trapping on `T::MIN`); wrapping negation is written `0 -% x`.
  - **Bit Shifts (`a << b`, `a >> b`)**: `<<` (`shl`) is logical left shift; `>>` (`shr`) is arithmetic right shift on `signed` integers and logical right shift on `unsigned` integers. A shift count `b >= bit_width(a)` (or `b < 0`) is a **compile error** at `comptime` and **traps** (`@llvm.trap()`) at runtime.
  - **Explicit Casts (`x as Dest`)**:
    - **Integer-to-Integer**: Widening (`u8 as u32`, `i8 as i32`) zero-extends unsigned integers (`zext`) and sign-extends signed integers (`sext`). Narrowing (`u32 as u8`, `i32 as i8`) performs **modular bitwise truncation** (`trunc i32 to i8`); range-checked narrowing uses pattern types (`x as ?(u8 in 0..=255)`).
    - **Float-to-Integer (`f as i32`, `f as u32`)**: Uses **saturating conversion** (`@llvm.fptosi.sat` / `@llvm.fptoui.sat`): values above `Dest::MAX` clamp to `Dest::MAX`, values below `Dest::MIN` clamp to `Dest::MIN`, and `NaN` maps to `0` (eliminating LLVM `fptosi` poison/UB on out-of-range floats).
    - **Integer-to-Float & Float-to-Float**: Round-to-nearest-even (`sitofp`, `uitofp`, `fpext`, `fptrunc`).

---

### 3.1 First-Class Slices (`&[T]`, `&mut [T]`) & UTF-8 String Views (`&str`) `[Status: Implemented]`
1. **Stage 3 Fat-Pointer Representation (`{ ptr, len }`)**:
   - A slice `&[T]` or `&mut [T]` lowers in Stage 2 to a 2-field Stage 3 [`Type::Struct`](src/ir.rs) `{ ptr: &[T; 0], len: usize }` (or `{ ptr: &mut [T; 0], len: usize }`, 16 bytes on 64-bit).
   - Indexing `s[i]` verifies `i < s.len` (trapping via `@llvm.trap()` on out-of-bounds) and projects `(*s.0)[i]` (`[Projection::Field(0), Projection::Deref, Projection::Index[i]]`), which lowers directly to `getelementptr inbounds [0 x T], ptr %data, i64 0, i64 %i` in LLVM IR while enforcing reference mutability (`&[T]` vs `&mut [T]`) and NLL loan tracking in [`src/borrowck.rs`](src/borrowck.rs).
   - Indices and slice bounds have type `usize` (or a `usize` pattern type); other integers convert explicitly (`a[i as usize]`).
   - Fixed-length arrays and SIMD vectors are checked the same way against their static length. The check is omitted when the index is statically in range (a constant, or a `usize in Lo..=Hi` pattern type with `Hi < N`); a constant index past a static length is a compile-time error. The one unchecked case is the C flexible-array idiom: indexing a zero-length `[T; 0]` reached through a raw pointer or inside `unsafe`.
2. **UTF-8 String Slices (`&str`)**:
   - **`&str`** is a first-class, immutable UTF-8 string slice represented at Stage 3 as `{ ptr: &[u8; 0], len: usize }` (16 bytes on 64-bit) with distinct surface type identity (`TypeExpr::StrRef`):
     - String literals (`"hello"`) have type `&str` and point to static read-only UTF-8 bytes in a Stage 3 [`Global`](src/ir.rs).
     - `&str` exposes `.len -> usize` (byte length) and byte indexing `s[i] -> u8`, is always `Copy`, `send`, and `sync`, and formats as UTF-8 text in `f"..."` strings (whereas `&[u8]` formats as a numeric byte array `"[104, 101, ...]"`).
     - There is no mutable `&mut str` type because arbitrary single-byte writes could violate the UTF-8 invariant.
3. **Coercions & Range Slicing (`lo..hi`)**:
   - References to fixed-length arrays (`&[T; N]` / `&mut [T; N]`) implicitly coerce to slices (`&[T]` / `&mut [T]`), and mutable slices `&mut [T]` implicitly coerce to shared slices `&[T]`.
   - Range slicing (`&arr[lo..hi]`, `&mut arr[lo..hi]`, `s[lo..hi]`, and open-ended `s[lo..]`, `s[..hi]`, `s[..]`) checks `lo <= hi && hi <= base.len`, computes the offset pointer `&base[lo]` and length `hi - lo`, and propagates the underlying NLL borrow loan in Stage 3.
4. **Uniform `sequence` Operations (`.len` and `s[i]`)**:
   - Both `[T; N]` (`array`) and `&[T]` / `&mut [T]` (`slice`) satisfy `[S: sequence]` and expose `.len -> usize` and element indexing `s[i]`.

---

### 3.2 First-Class Lambdas & Automatic-Capture Closures (`fn(...) { ... }` / `move fn(...) { ... }`) `[Status: Implemented]`
1. **Non-Capturing Lambdas Decay to `fn` Pointers (`fn`)**:
   - An anonymous function `fn(x: i32) -> i32 { return x * 2; }` that references no enclosing local variables has zero environment state and lowers directly to a Stage 3 function pointer ([`Type::FnPtr`](src/ir.rs)), satisfying both `fn` and `callable`.
2. **Automatic Capture & Call-Mode Inference (`closure` — No `Fn`/`FnMut`/`FnOnce` Trait Boilerplate)**:
   - When `fn(x: i32) -> i32 { ... }` references outer local variables, Stage 2 ([`src/lower/`](src/lower/mod.rs)) automatically synthesizes a stack-allocated anonymous closure environment (`TypeConstraint::Closure` under `callable`):
     - Outer variables that are only read inside the closure body are captured by shared reference (`&T`).
     - Outer variables that are mutated (`total += x`) inside the closure body are captured by mutable reference (`&mut T`).
     - When prefixed with `move` (`move fn(x: i32) -> i32 { ... }`), outer variables are captured by value (copied if `Copy`, or moved into the closure environment and automatically dropped by Stage 3 [`elaborate_drops`](src/drop.rs) when the closure goes out of scope).
   - **Automatic Call Convention (`&env` vs `&mut env` vs `move env`)**:
     - Instead of requiring callers to write separate `F: Fn(...)`, `F: FnMut(...)`, or `F: FnOnce(...)` trait bounds, a generic function simply accepts `[F: callable]` (or `[F: closure]`).
     - The compiler automatically selects the closure call convention from its captures:
       - **Shared call (`&env`)**: Used when the closure only reads its captures.
       - **Mutable call (`&mut env`)**: Used when the closure mutates a captured variable or reborrows a captured `&mut T`.
       - **Consuming single-use call (`move env`)**: Used when a `move fn` closure captures a [`linear`](#must-consume-linear-types-linear-struct--shared-drop-cleanup-status-implemented) value (or moves a non-`Copy` capture out of its environment on call). Calling such a closure consumes it in Stage 3b [`elaborate_drops`](src/drop.rs), statically preventing a second call.
3. **Zero-Config NLL Borrow Checking Across Closure Captures**:
   - Because Stage 2 lowers closure environments into concrete Stage 3 structs holding `&T` or `&mut T` fields **before** Stage 3 runs, [`check_borrows`](src/borrowck.rs) automatically tracks every captured loan:
     - Reading or mutating a variable while it is mutably captured by an active closure is rejected.
     - Immediately after the last call to the closure, NLL ends the closure's loan so the outer variable is freely accessible again.

---

### 3.3 Meta-Type Constraint Hierarchy & Overload Resolution `[Status: Implemented]`
Rather than requiring verbose trait bounds (`T: PrimInt + Signed` or `F: FnMut(i32) -> i32`) or leaving `[T: type]` completely unconstrained across 1,024 integer widths and structural types, the language provides a built-in hierarchy of **refined meta-types** for constraining `comptime` type parameters.

Meta-type constraints are organized into two orthogonal axes:
1. **The Disjoint Structural Kind Tree** (every concrete type belongs to at most one branch below `type`):

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

2. **Cross-Cutting Property & Lifecycle Constraints** (orthogonal predicates that cut across structural kinds):
   - **Concurrency Properties**: **`send`** (safe to transfer across threads) and **`sync`** (safe to share via `&T` across threads).
   - **Substructural Ownership Modes**: **`copy`** (unrestricted $0..\infty$ uses), **`affine`** (move-only $0..1$ uses, dropped at scope exit), and **`linear`** (must-consume $1..1$ uses; applies to `opaque(linear)` and any `tuple`, `struct`, `?T`/`union`, `[T; N]`, or `move fn` closure containing a linear value).
   - **Lifecycle Properties**: **`default`**, **`clone`**, and **`format`**.

| Meta-Type Constraint | Axis | Matching Types | Direct Super-Constraint in Subsumption Poset |
| :--- | :--- | :--- | :--- |
| **`type`** | Root | Any type | — (top of poset) |
| **`scalar`** | Structural Kind | Any `number`, `bool`, `rune`, or raw pointer (`*const T`, `*mut T`) — single-register, trivially copyable primitives; strictly disjoint from `callable`, `sequence`, `aggregate`, `discriminated`, `opaque`, and `simd` | `type` |
| **`callable`** | Structural Kind | Any `fn` pointer (`fn(...) -> R`) or capturing `closure` | `type` |
| **`sequence`** | Structural Kind | Any fixed-length `array` (`[T; N]`) or dynamically-sized `slice` (`&[T]`, `&mut [T]`) — contiguous homogeneous memory sequences supporting `.len` and `s[i]` | `type` |
| **`aggregate`** | Structural Kind | Any `struct` or `tuple` (transparent open data; excludes encapsulated `opaque`) | `type` |
| **`discriminated`** | Structural Kind | Any `enum`, `union`, or `error` (types with an active discriminant tag) | `type` |
| **`opaque`** | Structural Kind | Encapsulated nominal types (`opaque`, `opaque(copy)`, `opaque(affine)`, `opaque(linear)`) | `type` |
| **`simd`** | Structural Kind | Hardware SIMD vector types (`simd[T; N]`) | `type` |
| **`number`** | Structural Kind | Any `integer` or `float` | `scalar` |
| **`fn`** | Structural Kind | Non-capturing function pointer types (`fn(T1, ...) -> R` and non-capturing lambdas) | `callable` |
| **`closure`** | Structural Kind | Capturing closure types (`fn(...) -> R { ... }` / `move fn(...) -> R { ... }`) | `callable` |
| **`array`** | Structural Kind | Fixed-length array types (`[T; N]`) | `sequence` |
| **`slice`** | Structural Kind | Fat-pointer slice types (`&[T]`, `&mut [T]`) | `sequence` |
| **`struct`** | Structural Kind | Named or anonymous transparent product types (`struct { ... }`) | `aggregate` |
| **`tuple`** | Structural Kind | Positional product types (`tuple { ... }`) | `aggregate` |
| **`enum`** | Structural Kind | Scalar tag-only enumerations (`enum { ... }`) | `discriminated` |
| **`union`** | Structural Kind | Payload-carrying tagged unions (`union { ... }`, optionals `?T`, and results `E!T`) | `discriminated` |
| **`error`** | Structural Kind | Composable error sum types (`error { ... }`, `export error`, and ad-hoc `E1 \|\| E2` error unions) | `discriminated` |
| **`integer`** | Structural Kind | Any `signed` or `unsigned` (`i1`..`i512`, `u1`..`u512`, `isize`, `usize`, integer `pattern`s) | `number` |
| **`float`** | Structural Kind | `f32`, `f64` | `number` |
| **`signed`** | Structural Kind | `i1`..`i512`, `isize` (and signed `pattern`s) | `integer` |
| **`unsigned`** | Structural Kind | `u1`..`u512`, `usize` (and unsigned `pattern`s) | `integer` |
| **`send`** | Cross-Cutting | Any type safe to transfer across threads (primitives, `&T` where `T: sync`, `&mut T` where `T: send`, `opaque(unsafe send)`, and containers/closures whose fields/captures are `send`) | `type` |
| **`sync`** | Cross-Cutting | Any type safe to share by immutable reference (`&T`) across threads (`&T: send` $\iff$ `T: sync`) | `type` |
| **`copy`** | Cross-Cutting | Unrestricted copyable types (primitives, `&T`/`&[T]`/`&str`, `opaque(copy)`, and transparent containers whose elements are all `copy`) | `type` |
| **`affine`** | Cross-Cutting | Move-only non-linear types (`opaque` / `opaque(affine)`, `&mut T`, and containers holding an `affine` value without `linear` fields) | `type` |
| **`linear`** | Cross-Cutting | Must-consume linear types (`opaque(linear)` and any `tuple`, `struct`, `?T`/`union`, `[T; N]`, or `move fn` closure containing a linear value) | `type` |
| **`default` / `clone` / `format`** | Cross-Cutting | Any type supporting `@default(T)` / `@clone(v)` / `@format(f, v)` | `type` |
| **Concrete Type** | Leaf | Specific type (`i32`, `f64`, `Point`, `Pair[i32]`) | All constraints satisfied by that type |

#### Subsumption Partial Order for Overload Resolution
Because cross-cutting constraints (`send`, `sync`, `linear`, `format`) can overlap with structural kind constraints (`number`, `sequence`, `opaque`), overload resolution uses **constraint subsumption ($C_1 \subset C_2$)** rather than a flat numeric rank:
- A constraint $C_1$ is **strictly more specific** than $C_2$ ($C_1 \prec C_2$) if and only if every type satisfying $C_1$ strictly satisfies $C_2$ (i.e., $C_1$ is a descendant of $C_2$ in the structural kind tree, such as `signed` $\prec$ `integer` $\prec$ `number` $\prec$ `scalar` $\prec$ `type`, or a concrete type `i32` $\prec$ `signed`).
- If two candidate overloads match a call with incomparable constraints—for example, `fn foo[T: send](x: T)` and `fn foo[T: number](x: T)` called with `42: i32` (since neither `send` $\subset$ `number` nor `number` $\subset$ `send` holds)—the compiler rejects the call as an **ambiguous overload error** rather than guessing by depth.
- **Negative bounds and `where` clauses** `[Status: Implemented]`: `[T: !sync]` admits any type that does not satisfy the constraint; it is shorthand for `[T]` with `where T: !sync`. A function's `where` clauses (negated or not) are checked during overload selection like its parameter bounds, so `fn kind[T: sync](x: &T)` and `fn kind[T: !sync](x: &T)` are disjoint overloads, and a call no overload's clauses admit is rejected with the clause it fails.

```rust
// Constrained generic extension on any numeric type (`integer` or `float`):
pub fn clamp[N: number](self: N, lo: N, hi: N) -> N {
    if self < lo { return lo; }
    if self > hi { return hi; }
    return self;
}

// Disjoint overloads by meta-type constraint (`signed` vs `float`):
pub fn abs[S: signed](self: S) -> S {
    if self < 0 { return -self; }
    return self;
}
pub fn abs[F: float](self: F) -> F {
    if self < 0.0 { return -self; }
    return self;
}

// Structural & composite constraints (`aggregate` = `struct` | `tuple`, excluding `opaque`):
pub fn is_open_data[A: aggregate](x: &A) -> bool { return true; }
pub fn is_open_data[S: opaque](x: &S) -> bool { return false; }
```

---

### 3.4 Product Types: `tuple` vs `struct` vs `opaque` `[Status: Implemented]`
All three product types (`tuple`, `struct`, and `opaque`) are inline value types (no implicit heap allocation or OOP inheritance) and all three lower to [`Type::Struct`](src/ir.rs) (`{ ty0, ty1, ... }`) in Stage 3, but they form a clear progression of high-level contracts:

| Feature | `tuple` (Anonymous Positional Data) | `struct` (Named Transparent C-Aligned Data) | `opaque` (Encapsulated Invariant / Resource) |
| :--- | :--- | :--- | :--- |
| **Type & Literal Syntax** | `tuple { i32, f64 }` / `{ 10, 3.14 }` | `struct Name { x: i32, y: f64 }` / `struct { x: i32, y: f64 }` | `opaque Name { ... }` / `opaque { ... }` (`opaque(copy \| affine \| linear, unsafe sync)`) |
| **Intent** | Multi-value returns, ad-hoc pairs/triples, positional variant payloads | Plain transparent bundle of named fields (`Point`, `Config`, C FFI `export struct`) | Encapsulated state with private invariants or lifecycle (`Ipv4Addr`, `Vec`, `File`, `MutexGuard`) |
| **Type Identity** | **Structural** (any two `tuple { i32, f64 }` are the exact same type) | **Named means nominal, anonymous means structural.** A named struct is a distinct type per declaration: `struct Name { ... }` and a `struct { ... }` literal returned by a `comptime` type function (named after the function and memoized by `(module, fn_name, comptime_args)`). An anonymous `struct { ... }` is structural by ordered `(field_name, TypeId)` pairs however it is written (`@Struct` / `@PackedStruct` with the same fields, and `@entries` records, give the same type, named `struct { x: i32, ... }` in diagnostics); anonymous `overlay { ... }` types are structural too | **Nominal** (distinct type per declaration; memoized by `(module, fn_name, comptime_args)` for `comptime` type functions) |
| **Field Access & Visibility** | Public positional (`t.0`, `t.1`); empty `tuple {}` is forbidden (use `void`) | All fields are **public** (`r.x`, `r.y`); a named struct may give fields default values (`x: T = expr`), an anonymous one may not | All fields are **strictly private** (visible strictly inside the `opaque { ... }` block; `pub` on fields is rejected) |
| **`comptime` Fields (`[C: T = val]`)** | **Forbidden** | **Forbidden** (every `struct` field is strictly an instance data field) | **Allowed** (serves as associated constants and associated `type`s; 0 runtime bytes) |
| **`static` Fields (`static S: T = val`)** | **Forbidden** | **Forbidden** (no hidden global state on transparent data) | **Allowed** `[Status: Implemented]` (encapsulated type-scoped global state; lowers to Stage 3 [`Global`](src/ir.rs)) |
| **Inherent Methods** | **Forbidden** | Named structs only (stateless convenience helpers); an anonymous struct is pure data, so methods or field defaults on it are a compile error that asks for a name | Allowed (invariant-preserving API) |
| **Custom Lifecycle (`default`, `clone`, `drop`, `format`)** | **Forbidden** (always auto-synthesized structurally from elements) | **Forbidden** (always auto-synthesized structurally from fields) | **Allowed** (`impl default { fn default() -> Self { ... } }`, `impl clone { fn clone(self: &Self) -> Self { ... } }`, `impl drop { fn drop(self: &mut Self) { ... } }`, `impl format { fn format(self: &Self, f: &mut Formatter) { ... } }`) |
| **Substructural Ownership (`copy` vs `affine` vs `linear`)** | **`copy`** $\iff$ all elements are `copy` (otherwise `affine`, or `linear` if any element is `linear`) | **`copy`** $\iff$ all fields are `copy` (otherwise `affine`, or `linear` if any field is `linear`) | **Adaptive on bare `opaque`, strict on `opaque(...)`**:<br/>• `opaque`: `affine` ($0..1$ uses) by default, upgrading to `linear` if any field/`*own T`/`owns T` is `linear` (or `copy` on a plain `packed opaque`)<br/>• `opaque(copy)`: strictly unrestricted ($0..\infty$ uses)<br/>• `opaque(affine)`: strictly move-only ($0..1$ uses; rejects `linear` fields)<br/>• `opaque(linear)`: strictly must-consume ($1..1$ uses) |
| **Partial Moves (`move t.0` / `move r.x`)** | **Always allowed** (remaining elements stay valid and are dropped individually) | **Always allowed** (remaining fields stay valid and are dropped individually) | **Only inside the `opaque`'s own methods** (fields are private), and **forbidden when the type has a `drop` hook**, because the hook would later run on the partially moved value |
| **Stage 3 Drop Behavior** | Decomposed into leaf elements in [`src/drop.rs`](src/drop.rs) | Decomposed into leaf fields in [`src/drop.rs`](src/drop.rs) | Treated as an atomic drop unit if registered in [`Program::destructors`](src/ir.rs) or `opaque(linear)` |

- **Record literals take the expected type** `[Status: Implemented]`: `{ x: 1, y: 2 }` is a literal of the struct (or `opaque`, inside its block, or overlay) type the context expects: a return type, a `let` annotation, an argument, a field, a constant, `?T`, the ok side of `E!T`, or a variant payload (`.Move({ dx: 1, dy: 2 })`). With no expected type it is the structural anonymous struct of its fields, so `let p = { x: 1, y: 2 };` needs no type written, and `struct { x: i32 } { x: 1 }` is never necessary. `Name { ... }` remains for naming the type explicitly. Either form rejects a field the type lacks or one given twice. At compile time a record literal is a record value (`@Struct(&[{ name: "v", ty: i32 }])`).
- **One declaration form per kind; `alias` names** `[Status: Implemented]`: each kind of type is declared with its own keyword, in one spelling: `struct Name { ... }`, `packed struct Name { ... }`, `opaque Name { ... }`, `extern opaque Name;`, `enum Name { ... }`, `union Name { ... }`, `error Name { ... }`, `overlay Name { ... }`, `trait Name { ... }`, and `type Name = distinct T;` for a distinct type (the only use of `type`). Writing `type Name = struct { ... }` (or any other kind after `type =`), `trait Name = trait { ... }`, or `pub export` is an error naming the right form. Every other type (tuples, primitives, pattern types such as `u8 in 0..=100`, pointers, arrays, slices, other named types, error unions `E1 || E2`, type-function calls, and `@Tuple` / `@Struct` results) is structural or already has an identity, so naming it takes `alias Name = ...;`, which declares no new type: `alias Pair = tuple { i32, i32 };` is `tuple { i32, i32 }`. `alias Name = struct { ... }` names the structural anonymous struct; `alias` with an `enum`, `union`, `error`, or `opaque` literal is an error, since those always declare a new type. An alias cannot be `export`ed (export the declaration it names). A trait alias names an existing trait expression (`trait AB = A + B;`, `trait FromI32 = From[i32];`).
- **Why `tuple { T1, T2 }` and `{ v1, v2 }` instead of `(T1, T2)`**:
  - Avoids overloading parentheses `(...)` for both expression grouping and tuples (eliminating the `(x,)` 1-tuple trailing-comma wart—`tuple { i32 }` and `{ 42 }` are completely unambiguous).
  - Matches `struct { ... }`, `opaque { ... }`, and Stage 3 (`SLIR`) `{ ty0, ty1 }` syntax directly.
  - Supports clean destructuring (`let { q, r } = div_rem(17, 5);`) and multi-element `union` / `error` variant payloads (`V4: tuple { u8, u8, u8, u8 }`).
  - **Deferred initialization** `[Status: Implemented]`: `let mut r: T;` declares a variable with no value yet (the `mut` and the type are required). It starts in the state of a value whose every field was moved out: assigning it, or each field of it, initializes it, and move checking and drop elaboration track each field. Reading, borrowing, or capturing anything not definitely initialized is a compile-time error, a scope exit drops exactly what was initialized, and a linear field assigned and not consumed is an error. This builds an aggregate from a `comptime for`, unlike `uninit`, without `unsafe`. A type with a `drop` hook is a single unit to these checks, so it cannot be assembled field by field.
  - **Destructuring `let`** `[Status: Implemented]`: `let { q, r } = e;` binds a tuple's elements and `let Point { x, y: py, .. } = e;` a struct's fields (renaming with `field: name`, skipping with `_`). Every element or field must be named unless the pattern ends in `..`; fields left to `..` are dropped with the value at scope exit (so an unconsumed linear field is still a compile error). Fields are copied or moved out, as for partial moves; an `opaque`'s private fields cannot be destructured.

---

### 3.5 Sum, Error & Overlay Types: `enum`, `union`, `error`, and `overlay` `[Status: Implemented]`
Rather than overloading `enum` or `union`, four distinct one-word keywords represent four distinct memory and safety models:

| Keyword | Concept | Stage 3 Representation | Safety, Status & Semantics |
| :--- | :--- | :--- | :--- |
| **`enum` / `enum(Int)`** | Scalar integer enumeration (`enum(u8) { Red = 0, ... }`) | Integer type (`u8`, `u16`, `i32`, etc.) | `[Status: Implemented]` Safe scalar integer constants; optional explicit `= N` wire values and backing integer type via `enum(u8)`. |
| **`union` / `union(Int)`** | Safe tagged union / sum type (Rust `enum` with payloads) | [`Type::Union`](src/ir.rs) | `[Status: Implemented]` Safe; always has a discriminant tag in all build modes, optional backing integer type `union(u16)` and explicit `= N` variant values, tracks active variant `v0`, `v1`, ... via [`Rvalue::Discriminant`](src/ir.rs), borrow-checks variant references, supports exhaustive `match`, and auto-drops the active variant payload. |
| **`error` / `error(Int)`** | First-class composable error sum type (`error { ... }`, `export error`, and `E1 \|\| E2`) | [`Type::Union`](src/ir.rs) (integer tag + optional payload) | `[Status: Implemented]` Only `error` types (and `E1 \|\| E2` compositions) may appear on the left of `E!T`; supports unit and payload variants, optional `error(Int)` backing type, `ok Ident = Val` C success sentinel, and explicit `= N` tag values, `export error` (unit enum or `MyError_Tag` + `union MyError` in C), hierarchical embedding of child `error`s, automatic `try`/`catch` widening, leaf & subtype `match`, and auto-synthesized `format`. |
| **`overlay`** | Unsafe C-style untagged memory overlay | [`Type::Overlay`](src/ir.rs) | `[Status: Implemented]` Unsafe field reads (`.field`, `.0`, `.1`); **never** injects a hidden debug tag (layout is identical in Debug and Release), and never auto-drops. |

#### `.Variant`: Variants of the Expected Type `[Status: Implemented]`
Where the type is known from context, a variant is written `.Name` (or `.Name(payload)`), without the type name:
- **Patterns**: `match c { .Red => ..., .Circle(r) => ..., .Denied(n) => ... }` names a variant of the scrutinee's type (for an `error`, the one leaf of that name; an ambiguous one asks for `ErrorType::Name`). A bare name in a pattern **always binds** the value, so writing a variant without the dot (`Red =>`, `Circle(r) =>`) is a compile error that asks for `.Red` rather than a catch-all that silently swallows every case; a misspelled `.Redd` is a "no variant" error. Qualified patterns (`Color::Red`, `IoError::Timeout(t)`) and embedded error types (`IoError(e)`) keep their meaning.
- **Values**: `let c: Color = .Blue;`, `f(.Red)`, `let s: Shape = .Circle(5);`, `return .Denied(7);` construct a variant of the expected type, looking through `?T` and through both sides of `E!T`. Without an expected type (`let x = .Red;`) it is an error asking for `Color::Red`.

#### Explicit `enum(Int)` / `union(Int)` / `error(Int)` Backing Types, Derived `T::Tag` & Safe `match` Reading
1. **Specifying `enum` Backing Width (`enum(u8)`) `[Status: Implemented]`**:
   - By default, the compiler picks the smallest integer (`u8`, `u16`, `u32`, `u64`, or the signed equivalent when a value is negative) that fits all variants of an `enum`. An `export enum` without an explicit backing type keeps at least 32 bits, matching the size of a C `enum` in the generated header.
   - Writing `enum(u16)` or `enum(i32)` explicitly fixes the backing integer representation for wire protocols, FFI, or hardware registers:
     ```rust
     pub enum(u16) Opcode {
         Ping       = 0x0001,
         Auth       = 0x0010,
         Disconnect = 0xFFFF,
     }
     ```
2. **Automatic `T::Tag` Synthesis & `.tag` Access on `union` and `error` `[Status: Implemented]`**:
   - Every `union` or `error` type `T` automatically exposes an associated scalar `enum` **`T::Tag`** with the same variant names and discriminant values (`Shape::Tag::Circle`, `MyError::Tag::Bad`), and every instance `v: T` exposes **`v.tag -> T::Tag`**, computed from Stage 3 [`Rvalue::Discriminant`](src/ir.rs). `.tag` reads the value in place (it never moves it); it applies to variables, fields, and dereferences, so bind the result of a call to a local first.
3. **Explicit Backing Types & Variant Values on `union` (`union(u16)`) `[Status: Implemented]`**:
   - Writing `union(u16)` and/or `= N` on variants fixes the union's backing tag integer type and discriminant values directly on the union (without requiring a separate linked `enum` whose variant order might drift), and `Message::Tag` derives those exact values (`0x0001`, `0x0010`, `0xFFFF`), recorded in [`Program::union_tag_values`](src/ir.rs); the Stage 3 discriminant remains the variant index, so `match` and the borrow checker are unaffected:
     ```rust,ignore
     pub union(u16) Message {
         Ping: u64 = 0x0001,
         Auth: AuthCredentials = 0x0010,
         Disconnect = 0xFFFF,
     }
     ```
4. **Safe Pattern Matching (`match`, `if let`, and `while let`) `[Status: Implemented]`**:
   - `match`, `if let`, and `while let` support general, composable patterns across sum types, primitives, strings, and aggregates:
     - **Sum types (`enum`, `union`, `error`, `?T`, `E!T`)**:
       - Named and shorthand `.Variant` patterns (`Message::Ping(seq)`, `.Ping(seq)`, `.Ok(v)`, `.Err(e)`), plus `null` and non-null subpatterns on `?T`.
     - **Primitives, ranges, and `&str`**:
       - `bool` (`true`, `false`), `rune` (`'a'`, `'0'..='9'`), integers and `u8` byte literals (`0`, `-5`, `b'A'`, `1..10`, `10..=20`), floats (`0.0`, `-1.5`, including signed negative zero `-0.0`), and `&str` string literals (`""`, `"GET"`, `"POST"`).
       - Integer range exhaustiveness is checked precisely against both full primitive integer bounds (`u8` `0..=255`, `i8` `-128..=127`, etc.) and `Type::Pattern` range-restricted integer subtypes (`i32 in 0..=10`).
     - **Structs, `packed struct`, and `opaque` (within its defining module)**:
       - Brace field patterns `Point { x: 0, y }`, anonymous `{ x: 0, y }`, field shorthand `{ x, y }`, and partial matching `{ x, .. }`.
       - Encapsulation is enforced: matching on private fields or `opaque` fields from outside the defining module is rejected at compile time.
     - **Tuples, fixed-size arrays `[T; N]`, and slices `&[T]` / `&mut [T]`**:
       - Tuple patterns `(a, b)` or `{ a, b }` (with optional `..` rest pattern `{ head, .. }`).
       - Array and slice patterns `[a, b, c]` and prefix/suffix rest patterns `[head, .., tail]`, `[]`, `[first, ..]`. Fixed-size arrays verify pattern length at compile time; slice patterns check length at runtime and support exhaustive coverage when `[]`, `[_, ..]` (or fixed lengths `0..K` plus `[_, ..]` of length `K`) are covered.
     - **Or-patterns (`p1 | p2`) and deep nesting**:
       - Or-patterns may appear at top level or nested inside variant/struct/tuple/array/slice patterns (`"PUT" | "PATCH"`, `.Move({ x: 0, y } | { x: y, y: 0 })`). All alternatives must bind the same set of variable names with identical types and binding modes (`plain`, `move`, `ref`, `ref mut`).
     - **Ownership-safe binding timing**:
       - Pattern tests (`SwitchInt`, range comparisons, string equality, slice length checks, nested subpattern checks) execute **before** any pattern bindings in an arm are materialized. A failed pattern arm never moves or drops `affine` or `linear` fields from the scrutinee.
     - **Single-pattern conditional unwrapping (`if let` / `while let`)**:
       - For `?T`: `if let val = opt { ... }` and `while let val = iter.next() { ... }`.
       - For any general refutable pattern: `if let Message::Ping(seq) = msg { ... } else { ... }`, `if let { x: 0, y } = pt { ... }`, or `while let [head, ..] = slice { ... }` desugars to a `match` with that pattern arm and a wildcard else arm.
     - **Exhaustive `match` statement/expression (`[Status: Implemented]`)**:
       ```rust,ignore
       match msg {
           Message::Ping(seq)       => handle_ping(seq),
           Message::Auth(move cred) => authenticate(move cred),
           Message::Disconnect      => close(),
       }
       ```
       Simple flat sum-type matches compile directly to a single Stage 3 [`Rvalue::Discriminant`](src/ir.rs) + [`Terminator::SwitchInt`](src/ir.rs) dispatch table, while nested, structural, range, slice, and `&str` patterns lower to a decision sequence of basic blocks that test all conditions before binding variables in the matched arm. Plain bindings (`Message::Ping(seq)`) copy or move the payload, and move bindings (`Message::Auth(move cred)`) move `_msg.v1` and mark `_msg` consumed in [`src/drop.rs`](src/drop.rs). Borrow bindings (`Message::Auth(ref cred)`, `ref mut cred`) bind a reference into the matched place instead; a `match` with any `ref` binding matches on a borrow of the scrutinee (`&msg` / `&mut msg`), so the matched value is not moved and stays usable afterwards.

---

### 3.6 The Value Lifecycle Quartet: `default`, `clone`, `drop`, `format` `[Status: Implemented]`
Creation (`default`), duplication (`clone`), destruction (`drop`), and formatting (`format`) are **language-level lifecycle constructs** (always written in **lowercase**), rather than user-implemented traits:

| Lifecycle Hook | On Transparent Data (`tuple`, `struct`, `[T; N]`, `&[T]`, `?T`, `enum`, `union`) | On an `opaque` (Encapsulated Resource / Invariant) |
| :--- | :--- | :--- |
| **`default`** | **Auto-synthesized** if all elements/fields have `default` (or field default values). **Forbidden** to implement manually. | **No default by default.** Allowed to implement `impl default { fn default() -> Self { ... } }`. |
| **`clone`** | **Auto-synthesized** if all elements/fields have `clone`. **Forbidden** to implement manually. | **Not clonable by default.** Allowed to implement `impl clone { fn clone(self: &Self) -> Self { ... } }`. |
| **`drop`** | **Auto-synthesized** if any element/field has `drop`. **Forbidden** to implement manually. | **No custom drop by default.** Allowed to implement `impl drop { fn drop(self: &mut Self) { ... } }`. |
| **`format`** | **Auto-synthesized** structurally if all elements/fields satisfy `format`. **Forbidden** to implement manually. | **Not formattable by default** (never leaks private fields). Allowed to implement `impl format { fn format(self: &Self, f: &mut Formatter) { ... } }` (or with optional `spec: &str`). |

- **Lowercase Bounds (`[T: format]`, `[T: clone]`, `[T: default]`) & Matching Intrinsics (`@format(f, v)`, `@clone(v)`, `@default(T)`, `@drop(v)`)**:
  - Because `default`, `clone`, `drop`, and `format` are built-in language lifecycle properties (like `type`), they use lowercase keywords when constraining `comptime` type parameters (`[T: format]`). This visually distinguishes language-level lifecycle properties from user-defined `PascalCase` types.
  - Each lifecycle hook is invoked uniformly through its matching intrinsic:
    - **`@default(T) -> T`**: Constructs the default value of type `T`.
    - **`@clone(expr) -> T`**: Accepts either a value `v: T` or a shared reference `&v: &T` (or dereferenced pointer `*ptr` inside `unsafe`) and returns a freshly cloned `T` by invoking `T`'s `impl clone { fn clone(self: &Self) -> Self { ... } }` hook or structural field-by-field clone.
    - **`@drop(target)`**: Runs `T`'s destructor in-place (`Terminator::Drop { place, target }`). Accepts a mutable local/field `v: T`, a mutable reference `&mut T`, or (inside an `unsafe` block) a raw pointer `*mut T` (such as `@drop(p + i)` in `Vec::drop`). **Calling `@drop` on any `linear` type is a compile-time error** (preventing generic containers like `Vec[T]` from silently dropping linear elements).
    - **`@format(f, v)` / `@format(f, v, "spec")`**: Streams `v` into `f: &mut Formatter` via `T`'s `format` hook or structural formatting.
- **Substructural Ownership Modes on `opaque`: bare `opaque` vs `opaque(copy)` vs `opaque(affine)` vs `opaque(linear)`** ([`Compiler::is_copy_type`](src/lower/types.rs)):
  Just as `enum(u8)`, `union(u16)`, and `error(c_int)` parameterize sum declarations, `opaque(...)` accepts an optional substructural ownership discipline (`copy`, `affine`, or `linear`) and an optional concurrency qualifier (`unsafe sync`). Omitting the ownership modifier (`opaque`) selects the adaptive default (`affine` unless upgraded to `linear` by a linear field/element), while writing `opaque(copy)`, `opaque(affine)`, or `opaque(linear)` asserts that exact ownership discipline:

  | Declaration | Usage Count | Field Requirement | Allowed Lifecycle Hooks | Copy / Clone / Drop Semantics |
  | :--- | :--- | :--- | :--- | :--- |
  | **`opaque`** | $0..1$ (Affine by default; $1..1$ Linear if holding a `linear` field/`*own T`/`owns T`; $0..\infty$ Copy on a plain `packed opaque`) | Any fields | `default`, `clone` (when not linear), `drop`, `format` | Move-only and implicitly droppable by default; automatically upgrades to `linear` when instantiated with or holding a `linear` value (`Box[Tx]`, `Vec[Tx]`) |
  | **`opaque(copy)`** | $0..\infty$ (Unrestricted) | All fields must be `copy` (compile error if any field is `affine`, `linear`, `*own T`, or `&mut T`) | `default`, `format` (**forbids** `drop` and custom `clone`) | Implicitly bitwise-copied on assignment/argument pass; automatically satisfies `copy` and `clone` (`@clone(x)` performs a bitwise copy) |
  | **`opaque(affine)`** | $0..1$ (Strictly Affine) | No field, `*own T`, `uninit T`, or `owns T` may be `linear` (compile error if any is `linear`) | `default`, `clone`, `drop`, `format` | Guaranteed move-only and always implicitly droppable at scope exit (never `copy`, even on `packed opaque(affine)`, and never `linear`) |
  | **`opaque(linear)`** | $1..1$ (Strictly Linear) | Any fields | `default`, `drop` (shared cleanup for `move self` methods), `format` (**forbids** `clone`) | Must be consumed exactly once on every control-flow path; `@drop(x)` in caller scopes is a compile error |

- **Exact Rules for Implicit `copy` Across All Types**:
  1. **Primitive scalars, shared views, and raw pointers are `copy`**: `void`, `never`, `bool`, `rune`, all integers (`i1`..`i512`, `u1`..`u512`, `isize`, `usize`), `f32`, `f64`, `enum`, scalar pattern types, `simd[T; N]`, `fn` pointers, raw pointers (`*const T`, `*mut T`), and **shared** references/slices (`&T`, `&[T]`, `&str`) are implicitly `copy`.
  2. **Unique mutable references (`&mut T` and `&mut [T]`) are NEVER `copy`**: Passing or assigning a `&mut T` (or a `struct`/`tuple` containing `&mut T`) moves the mutable reference (or automatically reborrows it when coerced to a shorter-lived `&mut T`/`&T` parameter), statically preventing two live `&mut T` aliases from being created via a `struct { r: &mut i32 }` copy.
  3. **Nominal `opaque` types are `copy` if and only if declared `opaque(copy)` (or plain `packed opaque` without `drop`/`clone`)**: Bare `opaque` and `opaque(affine)` are move-only, while small encapsulated value types with private invariants or custom `format` (such as `pub opaque(copy) Ipv4Addr { octets: [u8; 4], format(...) { ... } }`) opt into implicit bitwise copyability via `opaque(copy)`.
  4. **Transparent containers (`tuple`, `struct`, `[T; N]`, `?T`, `union`) are `copy` if and only if all of their fields/elements/variants are `copy`** (and the type is not `linear`).

#### Must-Consume Linear Types (`opaque(linear)`) & Shared `drop` Cleanup `[Status: Implemented]`
Standard RAII `opaque` types (`opaque` / `opaque(affine)`) are **affine** (used *at most* once, then implicitly dropped at scope exit). When a resource requires explicit disposition (`commit(move self)` vs `rollback(move self)`, `join(move self)` vs `detach(move self)`), declaring **`opaque(linear)`** (`pub opaque(linear) Transaction { ... }`)—or holding a linear value inside a bare `opaque` (`Box[Transaction]`, `Vec[Transaction]`)—gives it a **linear** lifecycle (must be consumed *exactly* once on every control-flow path):

1. **Encapsulated Linearity + Contagious Structural Propagation**:
   - Only `opaque` declarations may be declared `opaque(linear)` (since only `opaque` has strictly private fields and encapsulated methods that can retire the value).
   - Linearity propagates **contagiously** to any open container (`tuple`, `struct`, `?T` / `union`, `[T; N]`, or `move fn` closure) that holds a linear value:
     - Moving the linear field out of a `tuple` or `struct` (`let tx = pair.1; tx.commit();`) marks that leaf as consumed so the outer container can exit scope cleanly.
     - Unwrapping `?Transaction` with `if let tx = maybe_tx { tx.commit(); }` or `let tx = maybe_tx orelse return ...;` consumes `maybe_tx` and requires `tx` to be consumed on the `Some` branch.
     - A `move fn` closure that captures a linear value is automatically a single-use (`FnOnce`) linear closure that must be called once and whose body must consume the captured linear value.
2. **Stage 3b Path-Sensitive Enforcement & Shared `impl drop { fn drop(self: &mut Self) { ... } }` Cleanup**:
   - **In caller scopes**: Reaching scope exit (`Terminator::Drop`) while a linear value (or linear container leaf) is still `maybe_init` on any control-flow branch is a compile-time error in [`elaborate_drops`](src/drop.rs). Furthermore, calling `@drop(x)` on a linear type (including through a raw pointer `@drop(p + i)` inside a generic container) is rejected at compile time.
   - **Inside the `opaque(linear)`'s own consuming `move self` methods**: Any associated method taking `self` by value (`pub fn commit(move self) -> i32`, `pub fn rollback(move self) -> i32`) is privileged to retire `self`. If the `opaque(linear)` defines a `impl drop { fn drop(self: &mut Self) { ... } }` hook, [`elaborate_drops`](src/drop.rs) automatically invokes `impl drop { fn drop(self: &mut Self) { ... } }` at the exit of every consuming `move self` method (unless `self` was delegated by move to another consuming method), providing DRY shared teardown without permitting silent implicit drops in caller scopes.
     - **Retiring `self` Does Not Retire Its Linear Fields**: A linear value held inline in `self` (a field `t: Tx`, or `p.t` inside a field `p: P` of a plain `struct`) must be moved out on every path before `self` is retired (`return self.t;`, `let p = self.p; ... p.t.commit()`, or delegating `self` to another consuming method). [`elaborate_drops`](src/drop.rs) tracks these fields from the method's entry and rejects `fn discard(move self) {}` with `Linear field 'self.0' of type 'Tx' must be moved out before 'self' is retired`. Since a field cannot be moved out of a type with a `drop` hook, an `opaque(linear)` with both a `drop` hook and an inline linear field has no way to consume itself. Values a container keeps behind an `*own` pointer are invisible here: such a container's methods are trusted to hand every element back, as the `unsafe` code that made the owning pointer asserts.
   - Implementing `clone` on an `opaque(linear)` is forbidden at compile time.
3. **Pointer Kinds: Ownership and Borrowing Follow Contents** `[Status: Implemented]`:
   - **One rule**: a type is linear, carries borrows, and is `send` / `sync` according to what it **contains**. For inline fields this is structural (a `struct` holding a `Tx` is linear). Generic containers hold their elements out of line, so pointers come in kinds that say what they contain ([`ast::PtrKind`](src/ast.rs)):

     | Field type | Holds | Linear, borrow-carrying, `send` / `sync` as | Storing a linear value through it |
     |---|---|---|---|
     | `T`, `uninit T`, `[uninit T; N]` | values of `T` | `T` | `uninit`: allowed in a method of a linear type |
     | `*own T` (owning pointer, possibly to a buffer) | values of `T` | `T` | allowed |
     | `*ref T` / `*ref mut T` (view) | a borrow of `T` | `&T` / `&mut T` | refill only |
     | `*const T` / `*mut T` (raw) | nothing | nothing (never `send` / `sync`) | refill only |

     All three pointer kinds share the raw-pointer rules: dereferencing needs `unsafe`, `p + i` keeps the kind, and `?*own T` is nullable. They compile to the same code.
     ```rust
     fn Box[T] -> type {
         return opaque {
             ptr: *own T, // Box[Tx] is linear, Box[&i32] carries the borrow, Box[i32] is `send`
             // ...
         };
     }
     ```
   - **Conversions carry the obligation**: making a pointer that claims ownership or a borrow asserts something only `unsafe` code can know, so `p as *own T` and `p as *ref T` from a raw pointer or an integer require an `unsafe` block, and nothing converts into those kinds implicitly. The one safe conversion is a reference becoming a view of the same type (`&x as *ref T`, `&mut x as *ref mut T`, or implicitly), which carries the reference's borrow. Converting any kind out to a raw pointer is safe. A round trip through `usize` therefore cannot drop a view's borrow without `unsafe`.
   - **Only `opaque` owns**: a `struct` (whose fields anyone can take apart) may not hold an `*own` pointer, and neither may an `opaque(copy)` (a copy would duplicate what it owns). A bare `opaque` holding a linear value (inline, behind `*own`, in `uninit` storage, or via `owns T`) automatically upgrades to linear—regardless of which hooks the type defines—so caller scope-exit drops of `Box[Transaction]` or `Vec[Transaction]` are rejected by [`elaborate_drops`](src/drop.rs). Conversely, an explicit `opaque(affine)` asserts that the type is always droppable without consumption and rejects any linear field, `*own T`, `uninit T`, or `owns T` at compile time.
   - **Borrows through signatures**: a type holding a view, or an owning pointer to borrowing values, counts as a reference for [borrow contracts](#51-the-sweet-spot-lifetime--self-elision-rules-status-implemented): `Vec::iter(self: &Self) -> Iter[T]` borrows `self` by elision, and `Box[&i32]::new(r)` borrows `r`. An owning pointer confers its pointee's borrows only on the `opaque` that holds it; a bare `*own T` read out of a container is just an address. Stage 3 learns which opaques carry borrows from [`Program::loan_types`](src/ir.rs).
   - **Declared contents** (`opaque(owns T)`, `opaque(borrows T)`): for values a type holds through no typed field, such as `JoinHandle[R]`, whose result travels through the `*mut u8` that `pthread_join` fills. `owns T` acts as a hidden `*own T` field and `borrows T` as a hidden `*ref T` field, for linearity, borrows, and `send` / `sync`. Declaring `opaque(copy, owns T)` is a compile-time error.
   - **Lints** (collected by [`Compiler::compile_package_with_warnings`](src/lower/mod.rs)): an `opaque` from a `comptime` type function that has a `drop` hook (the signature of an owning container) and holds a type parameter `T` only behind a raw pointer is warned to use `*own T`; an `owns T` that a visible `*own T` or `uninit T` field already implies is warned as redundant.
   - **Storing a Linear Value Out of Sight Requires an Owner**: inside a method of a type, writing a linear value through a pointer (`*p = move v`), storing it with `uninit(v)`, or `@forget`-ing it (after copying it into the container) is a compile-time error unless that type's instantiation is itself linear ([`FuncLowerer::check_linear_sink`](src/lower/stmt.rs)). A non-linear `Holder[Tx]` would otherwise be dropped at scope exit with the `Tx` inside it, and a leaked `ScopedHandle` would let its thread outlive the stack it borrows. The check runs per instantiation, so `Holder[i32]` is unaffected. Closures inside a method are checked as part of it.
     - **Only Owned Storage, Otherwise Refills**: a linear value may be stored behind a pointer only through an `*own` pointer, or into `uninit` storage inside a method of a linear type. Any other such store (through a raw pointer or a view, anywhere) must refill a slot the function moved a linear value out of on every path to the store, as `core::mem::replace` (`let old = move *p; *p = move src;`) and `core::mem::swap` do ([`check_linear_raw_stores`](src/drop.rs), a must-dataflow over vacated slots, with [`Function::linear_owner`](src/ir.rs) marking methods of linear types). Otherwise a non-owning container could delegate the store to a helper such as `fn write_raw[T](p: *mut T, v: T)`, and nothing obliges its author to declare it [`unsafe fn`](#unsafe-fn-and-safe-extern-fn-status-implemented). Explicit `unsafe { @forget(v) }` remains the deliberate escape hatch.
4. **Conditional `drop` Hooks (`where T: !linear` & `where T: linear`) on Owning Containers (`Vec[T]`, `StackVec[T, cap]`)**:
   - Because `@drop` on a linear type is a compile-time error, a `drop` hook that destroys owned elements (`@drop(p + i)`) cannot compile for a linear instantiation. An owning container that wants to support **both** affine/copy and linear element types provides **two disjoint `drop` hooks** ([`Compiler::instantiate_composite`](src/lower/types.rs)):
     - **`impl drop where T: !linear { fn drop(self: &mut Self) { ... } }`**: Selected when `T` is not linear. Drops remaining elements `0..self.len` via `@drop(p + i)` and frees the backing buffer (`@dealloc(p)`).
     - **`impl drop where T: linear { fn drop(self: &mut Self) { ... } }`**: Selected when `T` is linear (the instantiation is already linear, holding `T` behind `*own T`). It runs only as shared teardown at the exit of consuming `move self` methods (such as `v.drain(fn(tx) { tx.commit(); })` or `b.into_inner()`), and frees storage without touching elements, which those methods have already moved out.
   - If an owning container provides only an unconditional `drop` hook that drops `T`, instantiating it with a linear `T` fails to compile inside that hook. The fix is to add the `where T: linear` alternative plus at least one consuming exit (`into_inner(move self) -> T`, `drain(move self, f)`).
   - Inherent methods that drop elements in-place without consuming them (such as `pub fn clear(self: &mut Self) where T: !linear` or `pub fn truncate(self: &mut Self, new_len: usize) where T: !linear`) are similarly gated by `where T: !linear`.
5. **No Silent Discarding of Linear Values** `[Status: Implemented]`:
   - **No Overwriting a Linear Place**: Assigning to an initialized (or `maybe_init`) place of linear type (`t = Tx::new(2);` while `t` is still live, or `*r = Tx::new(9);` through `r: &mut Tx`) is a compile-time error, because the old value would be discarded unconsumed. A `&mut L` always points to an initialized value, so `*r = ...` on a linear `L` is always rejected. Replacement uses `core::mem::replace(r, new) -> L` (whose returned old value must then be consumed) or `core::mem::swap(a, b)`.
   - **`catch` Cannot Discard a Linear Error**: `error` variants cannot carry linear payloads (rejected at the declaration), so `x catch fallback` can never discard a linear value.
   - **Writes Through Raw Pointers**: Writes into uninitialized storage (`*(p + len) = move value` in `Vec::push`) run no destructor, and are allowed for a linear value only in a method of a linear owner or as a refill (see [Storing a Linear Value Out of Sight](#must-consume-linear-types-opaquelinear--shared-drop-cleanup-status-implemented)).
   - **`match` and Pattern `if let` Settle Their Scrutinee**: A scrutinee moved into a `match` is a hidden variable of the enclosing scope ([`FuncLowerer::lower_match`](src/lower/expr.rs)), so an arm that does not move the payload out (`_ => 0`, `.B(n) => n`, the fall-through of `if let .B(n) = u`) leaves it to the scope-exit drop: an affine payload is dropped and a linear one is rejected (`Linear value 'match scrutinee' of type 'Tx' must be explicitly consumed`). An arm whose variants carry only `copy` payloads retires the scrutinee, since nothing in it needs dropping.
   - **Linear Values Do Not Cross the C Boundary**: A linear type (including any `struct`, `tuple`, `?T`, or array holding one) cannot appear by value in the parameters or return type of an `extern fn`, an `export fn`, or an `extern fn(...)` pointer type ([`Compiler::reject_linear_across_ffi`](src/lower/export.rs)). C cannot be made to consume a value it receives, and a value C returns could be forged (`extern fn forge() -> ScopedHandle[...]` would yield a handle for a thread that never existed). Raw pointers to linear values (`*const Tx`) may cross.
   - **`@forget` Is the Only Escape Hatch**: `unsafe { @forget(v) }` on a linear value compiles; the `unsafe` block asserts that discarding `v` cannot violate any invariant (it is unsound to `@forget` a `ScopedHandle`, whose soundness relies on `.join()` running).

---

### 3.7 Language-Level Optionals (`?T`) and Results (`E!T`) `[Status: Implemented]`
Instead of library-level generic sum types (`Option(T)` and `Result[T, E]`), optionality and fallibility are first-class type modifiers inspired by Zig (`?T` and `E!T`), eliminating verbose `Option(T)::Some(...)` / `Option(T)::None` and `Result::Ok(...)` / `Result::Err(...)` ceremony in a macro-less language.

#### Non-Null by Default for *Both* References and Raw Pointers `[Status: Implemented]`
Both safe references (`&T`, `&mut T`) and raw pointers (`*const T`, `*mut T`) are **non-null by default**. Nullability is orthogonal and expressed uniformly with `?`:

| Type | Nullability | Safety / Borrow Checking | Layout (64-bit) |
| :--- | :--- | :--- | :--- |
| `&T` / `&mut T` | **Non-null** (`0` is invalid) | Safe; tracked by [`src/borrowck.rs`](src/borrowck.rs) | 8 bytes |
| `?&T` / `?&mut T` | **Nullable** (`null` is `0`) | Safe; must unwrap before dereferencing; borrow-tracked | 8 bytes (null niche) |
| `*const T` / `*mut T` | **Non-null** (`0` is invalid; replaces `NonNull<T>`) | Unsafe to dereference (`*ptr`) | 8 bytes |
| `?*const T` / `?*mut T` | **Nullable** (`null` is `0`; C FFI pointer) | Must unwrap (`?*mut T -> *mut T`) before unsafe deref | 8 bytes (null niche) |

#### Implicit Wrapping Coercions & Dedicated Control-Flow Operators `[Status: Implemented]`
- **Implicit Value Wrapping**:
  - **`T -> ?T`**: Any value `v: T` implicitly coerces to `?T` (wrapping `v` in the active `Some` variant `v1`), and `null` coerces to any `?T` (setting discriminant `0`).
  - **`T -> E!T` and `E -> E!T`**: Inside a function returning `E!T` (or any context expecting `E!T`), a success value `v: T` implicitly wraps in the `Ok` payload (`v0`), and an error `err: E` (or any child error subtype embedded in `E`) implicitly widens to `E` and wraps in the `Err` payload (`v1`).
- **Control-Flow Unwrapping Operators**:
  - **`null` literal**: The empty value for any `?T`.
  - **`x orelse fallback`**: Unwraps `?T` to `T`, or evaluates `fallback` (a default value of type `T`, or a diverging `never` expression: `return ...`, `break`, `continue`, `unreachable`, `@trap()`).
  - **`if let val = opt_expr { ... }` / `while let val = iter.next() { ... }`**: Safe conditional unwrapping for `?T`.
  - **`for` loops** `[Status: Implemented]`:
    - `for i in a..b` / `for i in a..=b` count over integers. The counter takes a bound's type, or, when both bounds are literals, is inferred from its uses like a literal `let` (`for i in 0..4 { a[i] }` counts in `usize`). An inclusive range stops at `b` without stepping past it, so `0..=255` over `u8` cannot overflow.
    - `for x in seq` iterates an array, a slice, or a reference to an array by copying elements (non-`copy` elements need `for ref x`); `for ref x` / `for ref mut x` borrow them, and `for (x, i) in seq` also binds the `usize` index.
    - Any other value is an iterator: `for x in it` is `let mut tmp = it; while let x = tmp.next() { ... }`, so a type iterates by defining `next(self: &mut Self) -> ?T`.
    - In the head of `if`, `while`, `for`, and `match`, `name {}` is `name` followed by an empty block, not an empty struct literal (parenthesize one there: `match (Unit {}) { ... }`).
  - **`break` / `continue`**: Leave or restart the innermost `while` / `while let` / `for` loop (`continue` in a `for` steps to the next element). Both are `never`-typed expressions, so they also work as `orelse` / `catch` fallbacks (`let v = next() orelse break;`); the loop body's locals are dropped on the way out (a still-live linear value is a compile error). A loop can be labelled (`outer: for ...`, `outer: while ...`) and left or restarted from nested loops with `break outer` / `continue outer`; a label must not shadow an enclosing loop's.
  - **`try expr`**: Unwraps `E!T` to `T` (or `?T` to `T`), returning the error (or `null`) early from the enclosing function and automatically widening embedded/child error types into the enclosing function's return error type.
  - **`x catch fallback` / `x catch |err| fallback`**: The `E!T` counterpart to `orelse`. Unwraps `E!T` to `T` on success, or evaluates `fallback` (either a fallback value/block of type `T` or a diverging `never` expression such as `return ...` or `unreachable`, optionally binding the error payload `|err|`). Because `error` variants cannot carry linear payloads, `catch` never discards a linear value ([No Silent Discarding of Linear Values](#must-consume-linear-types-opaquelinear--shared-drop-cleanup-status-implemented)).

#### First-Class Unified `error` Types, Hierarchical Embedding & Ad-Hoc Error Unions (`E1 || E2`) `[Status: Implemented]`
To eliminate Rust's `impl Display` / `impl Error` / `impl From<ChildError>` boilerplate (and `thiserror` proc-macros), the language provides a single unified **`error`** sum type construct (`pub error Name { ... }`). The left-hand side `E` of `E!T` must be an **`error`** type or an ad-hoc union `E1 || E2` of `error` types:

```rust
// 1. Symbolic error variants (with optional `= N` tag values and `error(Int)` backing):
pub error IoError {
    PermissionDenied,
    ConnectionReset,
    Timeout,
}

pub error DbError {
    Deadlock,
    Timeout,
}

// 2. Payload-carrying error variants:
pub error ParseError {
    InvalidUtf8,
    UnexpectedToken: usize,
}

// 3. Hierarchical embedding in `error`:
pub error ConfigError {
    IoError,    // Directly embeds IoError without wrapper or `From` boilerplate!
    ParseError, // Directly embeds ParseError!
    MissingHeader,
    SyntaxError: struct {
        line: usize,
        col: usize,
    },
}
```

1. **Unified `error` Representation, Optional `= N` Discriminants & `export error`**:
   - **No `error` / `errorcode` split**: Every `error` declaration is a tagged sum type ([`Type::Union`](src/ir.rs)) whose variants may be unit variants (`PermissionDenied`), payload-carrying variants (`UnexpectedToken: usize`), or embedded child `error` types (`IoError`). When all variants of an `error` have `void` payloads, Stage 4 LLVM codegen ([`src/llvm.rs`](src/llvm.rs)) automatically emits a 0-byte payload (`{ i32, {} }`), so a purely symbolic `error` has the exact same footprint as an integer tag (and as a C `enum`).
   - **Optional `error(Int)` Backing, `ok` Sentinel & `= N` Values**: An `error` that does not embed child error sets may specify an optional backing integer type (`error(c_int)` / `error(u8)`), a custom C success sentinel (`ok Success = 200`; defaults to `ok Ok = 0`), and explicit `= N` integer tag values on unit or payload variants (`NotFound = 404`, `Bad: i32 = 1`), and may be declared `export error`; see [`export error`: Unit Error Codes vs. Payload-Carrying Errors](#c-values-of-export-error-status-implemented). Unioning two `error`s (`E1 || E2`) or embedding an `error` inside `error { ... }` produces a composed `error` sum type and does not flatten their numeric tag values.
2. **Zero-Boilerplate Hierarchy & Automatic `try` Widening**:
   - Embedding `IoError` directly inside `ConfigError` declares `IoError` as a subtype of `ConfigError`.
   - When `try read_file(path)` (`IoError!String`) is used inside a function returning `ConfigError!Config`, `try` automatically widens `IoError` into `ConfigError` without any manual `From` conversion.
3. **Ad-Hoc Error Unions (`E1 || E2`), Qualified Leaf Identity & Subtype Group Matching**:
   - Functions can compose error types inline in their signature without declaring a new named wrapper type:
     ```rust,ignore
     fn query_and_save(path: &str) -> (IoError || DbError)!Data {
         let rows = try query_db();       // DbError widens into (IoError || DbError)
         let data = try write_file(path); // IoError widens into (IoError || DbError)
         return data;
     }
     ```
   - **Algebraic Properties (`||` is Commutative, Associative, and Idempotent)**:
     - Error composition `E1 || E2` flattens all leaf variants into a **canonical set** sorted and deduplicated by fully qualified nominal leaf identity `(module_path, error_type_name, variant_name)`.
     - Consequently, **`A || B` and `B || A` are the exact same type** (`TypeId`), `(A || B) || C == A || (B || C)`, and `A || A == A`.
     - **Diamond Embedding**: If `ErrorA` and `ErrorB` both embed `IoError`, then `ErrorA || ErrorB` deduplicates `IoError`'s variants so `IoError::PermissionDenied` appears once in the composed error set.
     - **Disjoint Same-Named Variants (`IoError::Timeout` vs `DbError::Timeout`)**: Because leaf identity includes the defining error type `(module_path, error_type_name, variant_name)`, `IoError::Timeout` and `DbError::Timeout` remain distinct variants in `IoError || DbError` and never collide.
   - **Leaf & Subtype Group Pattern Matching in `match`**:
     - When matching on a composed error `err: IoError || DbError` (or `ConfigError`), `match` arms can match **individual qualified leaves** (`IoError::Timeout`), **entire embedded error subtypes** (`IoError(io_err)`), or a mix of both:
       ```rust,ignore
       match err {
           IoError::Timeout => retry_io(),       // Matches specifically IoError::Timeout
           DbError::Timeout => retry_query(),    // Matches specifically DbError::Timeout
           IoError(io_err)  => log_io(io_err),   // Narrows all remaining IoError variants to `io_err: IoError`
           DbError(db_err)  => log_db(db_err),   // Narrows all remaining DbError variants to `db_err: DbError`
       }
       ```
     - Exhaustiveness checking tracks coverage at the leaf level: once `IoError::Timeout` is handled by an earlier arm and `IoError(io_err)` handles the remaining `IoError` leaves, all of `IoError` is covered.
4. **Automatic Structural `format` Synthesis**:
   - Just like transparent `enum` and `union` types, every `error` automatically synthesizes the lowercase **`format`** lifecycle hook (`"IoError::PermissionDenied"`, `"ParseError::UnexpectedToken(42)"`, `"ConfigError::SyntaxError(SyntaxError { line: 10, col: 4 })"`), so errors can be interpolated directly into `f"Failed: {err}"` with zero boilerplate.

#### Interaction with the Value Lifecycle Quartet (`default`, `clone`, `drop`, `format`)
| Lifecycle Hook | `?T` (Optional) | `E!T` (Result) |
| :--- | :--- | :--- |
| **`default`** | **Always has `default` (`null`)**, even if `T` does *not* satisfy `default`. | Does **not** satisfy `default`. |
| **`clone`** | Satisfies `clone` if `T: clone` (clones payload if non-null). | Satisfies `clone` if `T: clone` and `E: clone`. |
| **`drop`** | Automatically drops `T` if active (`!= null`) and `T` has a destructor. | Automatically drops active `T` or `E` if it has a destructor. |
| **`format`** | Satisfies `format` if `T: format` (outputs `"null"` or formatted payload). | Satisfies `format` if `T: format` and `E: format`. |
| **Copy vs Move** | Implicitly `Copy` if `T` is `Copy`; move-only if `T` is move-only. | Implicitly `Copy` if both `T` and `E` are `Copy`. |

#### Stage 3 (`SLIR`) Lowering & Borrow Checking
`?T` and `E!T` require no new Stage 3 IR instructions — they lower directly to [`Type::Union`](src/ir.rs) (`union u8 { void, T }` for `?T` and `union u8 { T, E }` for `E!T`):
- [`src/drop.rs`](src/drop.rs) automatically checks the active discriminant ([`Rvalue::Discriminant`](src/ir.rs)) and drops the active variant payload (`_opt.v1`).
- [`src/borrowck.rs`](src/borrowck.rs) propagates loans across variant projections (`.v0`, `.v1`), so functions returning `?&T` or `E!&mut T` work seamlessly with both explicit `borrows(_1)` contracts and automatic interprocedural borrow inference ([`infer_borrow_summaries`](src/borrowck.rs)).

---

### 3.8 Uninitialized Storage: `uninit T` and `uninit` `[Status: Implemented]`
Just as `?T` + `null` provide language-level optional values, **`uninit T`** (type modifier) + **`uninit`** (value literal) provide zero-overhead uninitialized inline storage (replacing Rust's `MaybeUninit<T>` wrapper):

| Concept | Optional (`?T`) | Uninitialized Storage (`uninit T`) |
| :--- | :--- | :--- |
| **Type Syntax** | `?T` | `uninit T` |
| **Empty Value Literal** | `null` | `uninit` |
| **Size & Alignment** | `size_of(T) + tag` (or niche) | **Identical to `T`** (`size_of(T)`, `align_of(T)`) |
| **Automatic `drop`** | Drops `T` if active (`!= null`) | **Never auto-drops** (caller manages lifecycle via `@drop`) |
| **Stage 3 (`SLIR`) Lowering** | `union u8 { void, T }` ([`Type::Union`](src/ir.rs)) | `overlay { void, T }` ([`Type::Overlay`](src/ir.rs)) |

- **Array Initialization**: An array `[uninit T; cap]` can be initialized in one shot with `uninit` (which sets field `.0 = const void` in Stage 3 and emits zero memory writes in LLVM).
- **Overwriting Without Drop**: Assigning `slot = uninit(move val)` writes directly into the slot without running a destructor on the prior uninitialized bytes.
- **Unsafe Access & In-Place Drop**: Reading, borrowing, moving out of, or dropping the inner `T` (`slot.assume_init`, which projects `.1` on `overlay { void, T }` in Stage 3) requires `unsafe`.

---

### 3.9 Zero-Allocation String Formatting (`f"..."`), Lazy Stack Formatter Structs, and Inline Specifiers `[Status: Implemented]`
String interpolation (`f"Hello {name}, x={x:04x}"`) unifies Rust's `Display`/`Debug` traits and `format_args!` macro with Zig's `comptime` formatting into a single zero-allocation, macro-less mechanism:

1. **Transparent Types vs. Encapsulated `opaque` Types (No `#[derive(Debug)]` Boilerplate)**:
   - **Transparent data types** (`signed`, `unsigned`, `float`, `bool`, `rune`, `&str`, `struct`, `tuple`, `[T; N]`, `&[T]`, `?T`, `enum`, `union`) have no private invariants and are **always auto-formatted structurally** by the compiler (provided all inner fields/elements satisfy `format`):
     - `Point { x: 10, y: 20 }` (`struct Point`) $\rightarrow$ `"Point { x: 10, y: 20 }"`
     - `{ 1, "ok" }` (`tuple`) $\rightarrow$ `"{ 1, ok }"`
     - `[10, 20, 30]` / `&[10, 20, 30]` $\rightarrow$ `"[10, 20, 30]"`
     - `?T` $\rightarrow$ `"null"` or the formatted payload
     - `Color::Red` (`enum Color`) $\rightarrow$ `"Color::Red"`
     - Defining a custom `format` hook on a transparent `struct` is **forbidden** at compile time.
   - **Encapsulated `opaque` types** have strictly private fields and **never** auto-format their internal representation (preventing accidental leakage of raw pointers or sensitive invariants). An `opaque` type is formattable (`[T: format]`) if and only if it defines a lowercase **`format` lifecycle hook**:
     ```rust
     pub opaque Ipv4Addr {
         octets: [u8; 4],

         impl format {
             fn format(self: &Self, f: &mut Formatter) {
                 f.write(f"{self.octets[0]}.{self.octets[1]}.{self.octets[2]}.{self.octets[3]}");
             }
         }
     }
     ```
     An `opaque` type that also wishes to inspect inline format specifiers (`{addr:?}`) may declare the 3-parameter form `fn format(self: &Self, f: &mut Formatter, spec: &str)` inside `impl format`.
2. **Lazy, Stack-Allocated Formatter Structs & Stage 3c NLL Borrow Checking**:
   - An expression `f"User {name} at {pt}"` does **not** eagerly allocate a heap `String`. Instead, Stage 2 ([`src/lower/`](src/lower/mod.rs)) lowers it into an anonymous stack-allocated `opaque` holding shared references (`{ &name, &pt }`) with a compiler-synthesized `format[self: &Self](f: &mut Formatter)` hook.
   - Because every `f"..."` expression is itself an `opaque` with a `format` hook:
     - **Nested `f"..."` expressions compose with zero intermediate allocation**: `let inner = f"({x}, {y})"; let outer = f"pos={inner}";` streams directly into the target `Formatter` in a single pass.
     - **NLL Borrow Checking ([`src/borrowck.rs`](src/borrowck.rs))**: Captured `&T` references inside a lazy `f"..."` value are tracked by Stage 3c NLL borrow analysis—preventing mutation of borrowed variables while the `f"..."` value is live and rejecting returning a lazy `f"..."` that borrows a stack local.
3. **Inline Format Specifiers (`{expr:spec}`)**:
   - `{x}` (default): decimal for numbers, UTF-8 text for `&str` and `rune`, `"true"`/`"false"` for `bool`, structural representation for transparent composites, and `format` hook for `opaque`.
   - `{x:x}` / `{x:X}`: lowercase / uppercase hexadecimal integers.
   - `{x:b}` / `{x:o}`: binary / octal integers.
   - `{x:04x}` / `{x:08b}` / `{x:6}`: minimum width with `'0'` or `' '` padding.
   - `{s:?}` / `{r:?}`: debug-quoted string (`"\"hello\""`) and rune (`"'a'"`).
   - `{val:.2}`: fixed decimal places for floating-point values (`f32`, `f64`).
4. **Freestanding `core::fmt` vs. Hosted `std::fmt` & `std::io` (Buffer Truncation Behavior)**:
   - **`core::fmt`** (re-exported in `core::prelude` in [`src/stdlib.rs`](src/stdlib.rs)): `Formatter`, `fmt_slice(buf: &mut [u8], val: T) -> &str`, and `fmt_buf(buf: &mut [u8; N], val: T) -> &str` format any `T: format` into a caller-supplied buffer with zero heap allocation or OS dependencies.
   - **Buffer Exhaustion in `Formatter` (`truncated` flag)**: When writing into a fixed-capacity buffer (`fmt_slice` / `fmt_buf`), if the remaining capacity (`cap - pos`) is smaller than the incoming bytes, `Formatter::write_str` / `Formatter::write_byte` clamps the copy to the remaining space, advances `pos` to `cap` (never writing out of bounds or splitting a multi-byte `rune`), sets `f.truncated = true` (queryable via `f.is_truncated() -> bool`), and returns the valid written prefix `&str` (`buf[0..pos]`).
   - **`std::fmt` & `std::io`** (re-exported in `std::prelude`): `String` (RAII heap-allocated UTF-8 string with `drop` and `format` hooks that dynamically doubles its heap buffer when `f.is_truncated()`), `format(val: T) -> String`, `print(val: T)`, and `println(val: T)`.

---

## 4. `comptime` Metaprogramming & Traits (Macro-less Design)

### 4.1 Type-Generating Functions, Memoization & the `comptime` VM Evaluation Model `[Status: Implemented]`
A function's `comptime` parameters are declared in brackets before its runtime parameters: `fn f[T, N: usize](x: T)`. A bare name is a type parameter (`T` means `T: type`); `N: usize` is a compile-time value; `K: Hash + Eq` or `S: sequence` constrains a type. When there are no runtime parameters the parentheses may be omitted (`fn Vec[T] -> type`). Writing `comptime` in the runtime list is a compile error.

Generic types are ordinary functions that take `comptime` parameters and return `type` ([`Type::MetaType`](src/ir.rs)):
```rust
fn Array[T, len: usize] -> type {
    return struct {
        data: [T; len],
    };
}
```
- **Type values are ordinary values**: a type literal may appear wherever a value of type `type` is expected: an initializer (`let p: type = *mut u8;`, `let k: type = enum { A, B };`), the right of an assignment (`t = tuple { t, u8 };`), an argument, or a `return`.
- **Comptime arguments go in brackets too**: `Vec[i32]`, `Array[u8, 4]`, `Vec[i32]::new()`, `Pair[i32] { first: 1, second: 2 }`, `id[i32](42)`, methods (`x.conv[i64]()`, `Num::make[1]()`), and `impl[T: Hash] Hash for Pair[T]`. A type function without parameters is written `T()`. Because the two lists are separate, a call always has the same runtime arity: `f(x)` omits the comptime arguments and infers them from the value arguments (`fn id[T](v: T) -> T` is called `id(x)`), and `f[A](x)` gives them all explicitly; `f(A, x)` is an arity error. When inference cannot determine them, the error asks for `f[...](...)`.
- **Defaults and `_`**: a comptime parameter may declare a default (`fn HashMap[K, V, S: Hasher = Fnv] -> type`, `fn scaled[T: integer, k: i32 = 2](self: &Self, x: T)`); parameters after a defaulted one need defaults too, and generic `impl[...]` parameters take none. Each comptime argument is resolved in a fixed order: **explicit, then inferred, then default, then error**. An argument list may stop early (`HashMap[str, i32]`), and `_` marks one to infer (`widen[i64, _](x)` infers the source type from `x`). A default may name the parameters before it (`[T, U = ?T]`), and a method's defaults may name its type's parameters. Static methods have no receiver to infer from, so their comptime arguments are given or defaulted. Defaults are filled before memoization, so `Table[i32]` and `Table[i32, 4]` are the same type when `4` is the default.
- **Brackets versus indexing**: `F[T]` and `a[i]` have the same shape. The parser keeps a single bracketed argument as an index unless a struct literal or `::` follows, and lowering treats it as a type-function call when `F` names a function rather than a local or comptime value; a list of types `ts[i]`, a comptime map `M[key]`, a local array of function pointers `fs[i](x)`, and a field holding them (`s.fs[i](x)`, when `fs` is a field and not a method) still index. Several arguments (`Map[K, V]`) are always a type-function call.
- **A type function returns any kind of type**: the result is an ordinary `type` value, so one function may return an array, a struct, an `opaque`, or a union depending on its arguments (`if N == 0 { return [u8; 0]; } return opaque { ... };`). The bracket syntax only changes how arguments are written, not what the body may compute.
- **Optional binding**: `if let v = opt { ... }` / `while let v = opt { ... }` unwrap a `?T` (as in Swift); applied to a value that is not optional it is a compile error, so it never reads as a plain `let`.

In Stage 3 IR, `comptime` functions can dynamically construct and intern all composite types via [`Vm::eval`](src/vm.rs):
- **Opaque / Struct / Tuple types**: `aggregate ty_meta(copy _1, copy _2)` ([`Rvalue::Aggregate`](src/ir.rs))
- **Pointer / Reference types**: `&_1` / `&mut _1` ([`Rvalue::Ref`](src/ir.rs))
- **Array types**: `[copy _1; copy _2]` ([`Rvalue::ArrayType`](src/ir.rs))
- **SIMD Vector types**: `simd[copy _1; copy _2]` ([`Rvalue::SimdType`](src/ir.rs))
- **Union (safe tagged sum) types**: `union(const ty_tag, copy _1, copy _2)` ([`Rvalue::UnionType`](src/ir.rs))
- **Overlay (unsafe untagged memory overlay) types**: `overlay(copy _1, copy _2)` ([`Rvalue::OverlayType`](src/ir.rs))
- **Scalar Pattern / Range types**: `copy _1 in const 0..=copy _2` ([`Rvalue::PatternType`](src/ir.rs))

#### Type Identity & `comptime` Type-Function Memoization
- **Memoization Key**: Every call to a `comptime` function returning `type` is memoized in [`src/lower/`](src/lower/mod.rs) by the canonical key **`(module_path, fn_name, comptime_arg_values)`** where type arguments are compared by interned [`TypeId`](src/ir.rs) and scalar arguments by [`ConstValue`](src/ir.rs).
- **Identity Guarantee**: Two calls `Array[i32, 2 + 2]` and `Array[i32, 4]` anywhere in the program evaluate to the **exact same `TypeId`**—even when the body returns a nominal `opaque { ... }` (such as `Box[i32]` or `Vec[i32]`). Distinct `comptime` arguments (`Vec[i32]` vs `Vec[u32]`) produce distinct nominal `opaque` types.

#### `comptime` VM Safety, Termination & Target Width Rules
1. **One Evaluator**: A call to a compile-time function (in a `const` initializer, an array length, a `comptime` argument, or a type position) is instantiated for its `comptime` arguments, lowered with its callees, and run on the Stage 3 VM ([`Vm::eval`](src/vm.rs)), so it may use the whole language: loops, assignment, recursion, and `unsafe` code. Type functions (`-> type`) run the same way ([`src/lower/typefn.rs`](src/lower/typefn.rs)); `type` values and records of them (`[FieldSpec; N]`) are ordinary VM locals, and each expression that builds a type (`[T; N]`, `opaque { ... }`, `@Struct(&specs)`, a call of another type function) is a call of a *host function*: the VM suspends ([`VmExit::Host`](src/vm.rs)), Stage 2 builds the type from the expression and the current values of the locals it names, and the VM resumes. Types are thus built only on the path the function takes, so `if N == 0 { return void; } return tuple { u8, List(N - 1) };` terminates. A type literal a type function returns is named after the function and memoized under its arguments. Borrow and move checking run afterwards on the whole program, so a compile-time call can execute code that the checkers later reject; compilation still fails in that case.
2. **Sandbox & Deterministic Step Limit (Halting Guarantee)**: The VM refuses calls to `extern` functions, so compile-time code cannot perform I/O; its pointers are symbolic, so an invalid memory access in `unsafe` code is an evaluation error rather than corruption. Evaluation is bounded by a deterministic fuel budget (`1,000,000` VM steps per evaluation, and 256 nested type-function calls; the compiler runs on a 512 MiB stack so that these limits, not the host stack, stop runaway recursion). Exceeding it stops compilation with a `step limit` diagnostic rather than hanging the compiler or IDE language server.
3. **Target Architecture Width**: Inside `comptime`, `usize` and `isize` always use the **target architecture's pointer width** (64-bit on `x86_64`/`aarch64`, represented by [`Type::Int`](src/ir.rs) `{ signed: false/true, bits: 64 }`), ensuring `size_of`, array lengths, and struct layouts computed at `comptime` match runtime layout identically.
4. **Compile-Time Integer Constants (up to 512 bits)**: Integer literals and constants of every width up to `i512` / `u512` are exact at compile time: values that fit in `i128` use [`ConstValue::I64`](src/ir.rs), and wider ones use [`ConstValue::Wide`](src/ir.rs) backed by a fixed 1088-bit two's-complement integer ([`src/wide.rs`](src/wide.rs)), which the Stage 3 VM shares (`Value::Wide`). Constant folding and the VM both use the declared type's runtime semantics ([`wide::apply_binop`](src/wide.rs)): checked `+ - *` overflowing the type, division or remainder by zero, `MIN / -1`, and shift amounts outside `0..bits` are compile errors; wrapping and saturating operators wrap or clamp at the type's width. A literal that does not fit its type (`let x: u8 = 300;`) is a compile error, and a literal beyond `i128` needs an explicit wide type. [`Type::Pattern`](src/ir.rs) interval bounds are `Wide` values too, so range types cover every width and the whole range of their base (`u8 in 0..=255`, `u128 in 1..=u128::MAX`, `NonZero[u256]`), and `Int::MIN` / `Int::MAX` are exact for every width.

---

### 4.2 Traits in a `comptime` Language `[Status: Implemented]`
While built-in [meta-type constraints](#33-meta-type-constraint-hierarchy--overload-resolution-status-implemented) (`number`, `signed`, `sequence`, `callable`, `send`, `sync`, `format`, `clone`, `default`) cover standard numeric, container, closure, concurrency, and lifecycle bounds without traits, user-defined **`trait`** declarations serve both static `comptime` bounds and dynamic vtable dispatch without requiring angle brackets or a separate `dyn` keyword. Types opt into a trait explicitly with **`impl`**:

```rust,ignore
pub trait Eq {
    fn eq(self: &Self, other: &Self) -> bool;
}

pub trait Hash {
    fn hash(self: &Self) -> u64;
}

pub opaque(copy) Point {
    x: i32,
    y: i32,

    impl Eq {
        fn eq(self: &Self, other: &Self) -> bool { return self.x == other.x && self.y == other.y; }
    }
    impl Hash {
        fn hash(self: &Self) -> u64 { return (self.x as u64) *% 31 +% (self.y as u64); }
    }
}

// 1. Static constraint on a `comptime` type parameter:
fn HashMap[K: Hash + Eq, V] -> type { ... }
fn same_hash[T: Hash](a: &T, b: &T) -> bool {
    return a.hash() == b.hash();
}

// 2. Dynamic dispatch via `&Trait` / `&mut Trait` fat pointer (no `dyn` keyword needed):
fn compute_hash(a: &Hash) -> u64 {
    return a.hash();
}
```

#### Traits Are a Distinct Kind, Not Types `[Status: Implemented]`
A trait name plays two roles: in `[T: Hash]` it is a **constraint** on a type, and in `a: &Hash` it names an **existential** ("some implementor, behind a vtable"). To keep these from leaking into each other, `trait` is a compile-time kind of its own, separate from `type`:
- **`[T: type]` rejects traits.** Passing `Hash` where a `type` is expected (`id[Hash](&p)`, `fn pick[T] -> type { return T; }` with `pick[Hash]`) is a compile-time error. A generic `fn f[T](x: &T)` therefore always receives a thin pointer, and its representation never depends on whether the argument happens to be a trait.
- **Trait objects are special forms.** `&Tr`, `&mut Tr`, and `-> opaque Tr` are only valid where `Tr` resolves (at `comptime`) to a trait. They are not `&T` applied to a type `T`.
- **Trait aliases and trait-returning functions use the `trait` kind.** A trait is declared `trait Describable { ... }`, an alias of a trait expression is written `trait Name = <trait expression>;` (not `type Name = ...`), and generic traits are `comptime` functions returning `trait` (`fn From[Src] -> trait`).
- **Meta-type constraints (`number`, `sequence`, `copy`, `send`, …) and lifecycle properties (`format`, `clone`, `default`) are not traits**: they remain compiler-known structural properties that need no `impl`.

#### Static vs. Dynamic Trait Parameter Rules (Why No `dyn` Keyword Is Needed)
In Rust, `<T: Trait>`, `&impl Trait`, and `&Trait` blurred static and dynamic dispatch, forcing Rust 2018 to add `&dyn Trait`. In SlopLang, **static monomorphization is always introduced by `comptime`**, and because [traits are not types](#traits-are-a-distinct-kind-not-types-status-implemented), `&MyTrait` is never ambiguous with static dispatch and directly denotes a 16-byte fat-pointer trait object (`{ data_ptr, vtable_ptr }`)—exact same principle as how `[T]` is unsized by value (`a: [T]` is invalid) while `&[T]` is a 16-byte fat-pointer slice (`{ ptr, len }`):

| Signature | Valid? | Meaning & Representation |
| :--- | :---: | :--- |
| `fn foobar[T: MyTrait]()` | **Yes** | `T` is a compile-time **`type`** constrained by `MyTrait`. |
| `fn foobar[T: MyTrait](a: T)` | **Yes** | **Static dispatch (by value)**: monomorphized per concrete type `T`. |
| `fn foobar[T: MyTrait](a: &T)` | **Yes** | **Static dispatch (by ref)**: monomorphized per concrete type `T` (`a` is a thin 8-byte pointer). |
| `fn foobar[T: MyTrait, a: T]()` | **Yes** | **Compile-time value**: `a` is a `comptime` value of concrete type `T: MyTrait`. |
| `fn foobar(a: MyTrait)` | **No** | **Compile error**: `MyTrait` is an unsized meta-type constraint; use `[T: MyTrait](a: T)` for static dispatch or `(a: &MyTrait)` for dynamic dispatch. |
| `fn foobar(a: &MyTrait)` / `(a: &mut MyTrait)` | **Yes** | **Dynamic dispatch**: `a` is a 16-byte fat pointer `{ data_ptr: &void, vtable_ptr: &VTable }`. |
| `fn foobar[a: &MyTrait]()` | **Yes** | **Compile-time trait object**: `a` is a `{ data_ptr, vtable_ptr }` fat pointer evaluated in the Stage 3 VM (e.g., heterogeneous `comptime` tables `&[&MyTrait]`). |

1. **How a Type Conforms to a `trait`: Explicit `impl` Only** `[Status: Implemented]`:
   - **No duck typing**: A type `T` satisfies a trait `Tr` **if and only if** an `impl Tr` for `T` exists. Inherent or extension methods that happen to have matching names and signatures do **not** make `T` conform.
   - **Three `impl` forms**:
     ```rust,ignore
     // (a) Inside the type's own block (the common case):
     pub opaque Point {
         // ...
         impl Hash { fn hash(self: &Self) -> u64 { ... } }
     }

     // (b) Retroactively, at module level, for an existing type:
     impl Hash for i32 {
         fn hash(self: &Self) -> u64 { return *self as u64; }
     }

     // (c) Generically, over every instantiation of a type function that meets a bound:
     impl[T: Hash] Hash for Pair[T] {
         fn hash(self: &Self) -> u64 { return self.first.hash() *% 31 +% self.second.hash(); }
     }
     ```
     Form (a) is allowed in `struct { ... }` and `opaque { ... }` blocks (and in the method blocks of distinct types and `extern opaque` handles), and its method bodies have the block's private access. Forms (b) and (c) are written outside the block and, like extension functions, have no access to private `opaque` fields. Neither `impl` blocks nor their methods take a visibility modifier: trait methods are as visible as the trait and the type.
   - **Signature Matching**: Every method of `Tr` must be implemented with exactly the declared signature. An `impl` method's [borrow contract](#51-the-sweet-spot-lifetime--self-elision-rules-status-implemented) is the trait method's: it either omits `borrows(...)` (inheriting the trait's) or restates it identically. An `impl` may not add methods that `Tr` does not declare.
   - **Coherence (Orphan Rule & No Overlap)**: To guarantee that constructing a trait object `&Tr` / `&mut Tr` produces the exact same vtable regardless of which module performs the coercion, an `impl Tr for T` must be written in **either the module defining `T` or the module defining `Tr`**, and the whole program may contain **at most one** `impl Tr` applying to any concrete type. Overlapping `impl`s (for example an inline `impl Tr` plus a module-level `impl Tr for T`, or two generic `impl(...)` blocks matching the same instantiation) are rejected as conflicting as soon as both apply to a type that is checked against `Tr`; there is no specialization. Adapting a third-party type to a third-party trait requires a distinct type `type Name = distinct Underlying` in the adapting module.
   - **Method Namespacing & Trait Scope**: Trait methods belong to their `impl`, not to the type's inherent namespace, and `x.method()` only considers traits **in scope** in the calling module (declared there, or imported by name, glob, or prelude), so a new `impl` elsewhere in the program cannot change what an existing call means; calling a method of an out-of-scope trait reports which import to add. Generic bodies are unaffected (their `[T: Tr]` bound names `Tr`), and the qualified form `Tr::method(&x)` works wherever `Tr` can be named. In method-call syntax, an inherent method of the same name takes priority, then the methods of in-scope traits the type implements, then `self`-receiver extension functions ([§6.4](#64-inherent-methods-extension-functions-self-receivers--coherence-status-implemented)). If two implemented traits declare the same method name, `x.hash()` is an ambiguity error and the call must be qualified (`Hash::hash(&x)`), which dispatches statically to the receiver type's `impl`.
   - **Static Constraints (`[K: Hash + Eq]`)**: Verified at the call site by looking up `impl`s; because the trait lists explicit method signatures (`k.hash()`, `k.eq(&other)`), the compiler and IDE provide full pre-instantiation type checking and autocomplete for all trait methods inside `HashMap`.
   - **Generic Traits**: Simply `comptime` functions returning a `trait` (implemented per argument: `impl From[i32] for BigInt { ... }`):
     ```rust
     fn From[Src] -> trait {
         return trait {
             fn from(src: Src) -> Self;
         };
     }
     ```
2. **Dynamic Dispatch (`&Trait` / `&mut Trait`) & Object Safety**:
   - **VTable Eligibility (Object Safety)**: A trait `Tr` can be used as a trait object reference (`&Tr` / `&mut Tr`) if and only if every method in `Tr`:
     1. Takes a pointer receiver `self: &Self` or `self: &mut Self` (calling a `&mut Self` method requires `&mut Tr`; `&Tr` only permits `&Self` methods).
     2. Does not mention `Self` in any non-receiver parameter or return type (traits like `Eq` with `other: &Self` or `From` returning `Self` are valid for static `[T: Eq]` bounds, and report a compile error if used as `&Eq`).
     3. Has no method-level `comptime` parameters.
   - **Borrow Contracts in Trait Signatures**: Because a `&Tr` call has no callee body available to the caller, every trait method signature carries a [borrow contract](#51-the-sweet-spot-lifetime--self-elision-rules-status-implemented) (explicit or elided), and the vtable call site enforces exactly that contract.
   - **Built-in Meta-Types**: Structural/marker meta-type constraints (`number`, `signed`, `sequence`, `send`, `sync`, `copy`, `linear`) are compile-time type predicates only and cannot form `&number` trait objects.
   - **Stage 3 (`SLIR`) Lowering**: Lowers directly to a Stage 3 2-field fat pointer struct `{ data_ptr: &void, vtable_ptr: &VTable }` where `VTable` is a compiler-synthesized read-only [`Global`](src/ir.rs) struct of function pointers ([`Type::FnPtr`](src/ir.rs)).
   - [`src/borrowck.rs`](src/borrowck.rs) automatically propagates the borrow loan of `data_ptr` into the fat pointer struct via [`Rvalue::Cast`](src/ir.rs) and [`Rvalue::Aggregate`](src/ir.rs).

---
- **Static trait methods** `[Status: Implemented]`: a trait method without a `self` parameter is called on a type, as `T::sides()` in a function bounded by `T: Shape`, or `Square::make(3)`, and may return `Self`. An inherent method of the same name wins, and two traits declaring the name make the call ambiguous. A trait with such a method is not object-safe, since a trait object has no type to call it on.

### 4.3 `comptime` Associative Maps (`map[K, V]`) `[Status: Implemented]`
A `map[K, V]` is an immutable, compile-time-constructed associative lookup table mapping a set of unique keys of type `K` to values of type `V`. Because `type` is a first-class `comptime` value, `K` and `V` can be runtime types *or* `type` itself:

```rust
// 1. Type-to-Type mapping (replaces associated-type helper traits)
comptime UNSIGNED_OF: map[type, type] = {
    i8  => u8,
    i16 => u16,
    i32 => u32,
    i64 => u64,
};

// 2. Enum / Scalar metadata table (with compile-time bidirectional inversion)
enum Method { Get, Post, Delete }
comptime HTTP_METHODS: map[Method, &str] = {
    Method::Get    => "GET",
    Method::Post   => "POST",
    Method::Delete => "DELETE",
};
comptime PARSE_METHOD: map[&str, Method] = @invert(HTTP_METHODS);
```

- **Compile-Time Uniqueness & Exhaustiveness**:
  - Duplicate keys in a `map` literal (or duplicate values when calling `@invert(MAP)`) are rejected at compile time.
  - `MAP.get(k) -> ?V` performs a safe lookup for any runtime or `comptime` key.
  - `MAP[k] -> V` is allowed when `k` is a `comptime` key (compile error if absent) *or* when `K` is an `enum` and `MAP` exhaustively covers all variants of `K`.
- **Automatic Zero-Cost Stage 3 (`SLIR`) Lowering**:
  - **`comptime` key (`MAP[comptime_k]`)**: Constant-folded at Stage 2 to a [`ConstValue`](src/ir.rs) or [`TypeId`](src/ir.rs) (0 runtime instructions).
  - **Dense integer / `enum` keys**: Lowers to a read-only Stage 3 [`Global`](src/ir.rs) array `[V; N]` with direct `O(1)` indexing.
  - **Sparse integer / `enum` keys**: Lowers to a Stage 3 [`Terminator::SwitchInt`](src/ir.rs) jump table.
  - **String (`&str`) or composite keys**: Lowers to a compiler-synthesized Perfect Hash Table (PHF) in a read-only Stage 3 `Global` (eliminating the need for Rust's `phf_map!` proc-macro or startup heap allocation).

---

### 4.4 `comptime` Structural Reflection, Unrolled Iteration (`comptime for`), and Programmatic Type Synthesis `[Status: Implemented]`
Instead of procedural macros or runtime RTTI, SlopLang provides compile-time reflection and type synthesis (`core::meta`, re-exported in `core::prelude` and `std::prelude`) governed by a strict encapsulation boundary:
- **Transparent types (`struct`, `packed struct`, `tuple`, `enum`, `union`, `error`, `overlay`, `map[K, V]`)**: Full structural reflection (`@fields`, `@variants`, `@entries`, `@has_field`, `@backing_type`) and programmatic reconstruction are always permitted.
- **Encapsulated `opaque` types**: Calling `@fields(T)`, `@has_field(T, ...)`, or `@backing_type(T)` on an `opaque` type from **outside** `T`'s defining `opaque { ... }` block (`self_ty != Some(T)`) is a **compile-time error**, preserving representation encapsulation. Inside `T`'s own `opaque { ... }` block, `@fields(Self)`, `@has_field(Self, ...)`, and `@field(self, f.name)` are permitted so an `opaque` can write DRY internal helpers over its own fields; external callers can reflect only over `T`'s public API via `@declarations(T)` and `@satisfies(T, Bound)`.

#### 1. Type & Value Reflection Intrinsics (`core::meta`)
| Intrinsic | Accepted Target(s) | Return Type / Descriptor (`core::meta`) | Notes |
| :--- | :--- | :--- | :--- |
| **`@type_name(T)`** | Any `T: type` | `&str` | Canonical display name of `T` (`"Point"`, `"i32"`). |
| **`@satisfies(T, Bound)`** | `T: type` (or `module`), `Bound` (constraint, lifecycle hook, or `trait`) | `bool` | Evaluates to `true` if `T` satisfies `Bound` (`copy`, `send`, `sync`, `linear`, `format`, `integer`, or a user `trait`). |
| **`@has_field(T, name_or_idx)`** | `struct`, `tuple`, `overlay`, or `Self` inside `opaque` | `bool` | Checks whether field `name: &str` (or `idx: usize` on `tuple`) exists on `T` (or `&T`/`&mut T`). |
| **`@fields(T)`** | `struct` / `packed struct` / `Self` in `opaque`<br/>`tuple`<br/>`overlay` | `&[StructField]` (`{ name: &str, ty: type, offset: usize, has_default: bool }`)<br/>`&[TupleField]` (`{ name: &str, index: usize, ty: type, offset: usize }`, where `name` is the index in decimal)<br/>`&[OverlayField]` (`{ name: &str, ty: type }`) | `offset` is byte offset for standard `struct`/`tuple` and bit offset for `packed struct`. |
| **`@backing_type(T)`** | `enum`, `union`, `error`, `distinct`, `pattern`, `packed struct`, or `Self` in `packed opaque` | `type` | Backing integer type of an `enum`/`error`/`pattern`/`packed` composite, underlying type of a `distinct` type, or `T::Tag` of a `union`. |
| **`@variants(T)`** | `enum`<br/>`union`<br/>`error` | `&[EnumVariant[T]]` (`{ name: &str, val: T, value: @backing_type(T) }`)<br/>`&[UnionVariant[T]]` (`{ name: &str, tag: T::Tag, payload: type }`)<br/>`&[ErrorVariant]` (`{ error_name: &str, name: &str, payload: type }`) | For `enum`, `@variants(T)` is also usable as a zero-allocation runtime slice `&[EnumVariant[T]]`. |
| **`@entries(M)`**, **`M.keys`**, **`M.values`** | `M: map[K, V]` | `&[MapEntry(K, V)]` (`{ key: K, val: V }`), `&[K]`, `&[V]` | Usable in `comptime for`, and materialized as static slices `&[...]` when `K`/`V` are runtime types. |
| **`@declarations(X)`** | `X: module` or `X: type` (`struct`, `opaque`, `trait`, distinct type) | `&[&str]` | Public declaration names exported by module `X` or associated `pub` constants/statics/methods on type `X`. |
| **`@leaves(T)`** | Any `T: type` | `&[&[&str]]` | The path (see `@field`) of every field of `T` that is not itself a `struct` or `tuple`, depth-first. `opaque` types are leaves, so this never reveals private fields. Usable in `comptime for` and `comptime let`. |
| **`@compile_error(parts...)`** | Compile-time strings, integers, types, and other values | Does not return | Fails compilation with the parts joined (strings verbatim, types by name). In a type function it fires when the function reaches it, so only on the path taken. In any other function it fires if lowering reaches it, so it belongs in a branch pruned at compile time (a `comptime` type predicate). |
| **`@fn_info(f)`** | `f: callable` (function item, `fn(...) -> R` type, or closure) | `FnInfo` (`{ params: &[type], ret: type }`) | Inspects parameter and return types at `comptime`. |

#### 2. Unrolled `comptime for` & First-Class Place/Value Intrinsics (`@field`, `@variant`, `@make_union`)
Because fields of a `struct`/`tuple`, variants of a `union`/`error`, and entries of a `map[&str, type]` have **heterogeneous types** across iterations, **`comptime for`** unrolls at Stage 2 across any `comptime` slice or reflection list (`comptime for item in ...` or `comptime for (item, idx) in ...`), type-checking and borrow/move-checking each unrolled iteration with its concrete per-field or per-variant type (and pruning untaken `if` branches whose condition is a `comptime` type predicate):
- **`@field(base, comptime name_or_index_or_path)`**: First-class **place expression** (supports reading `@field(s, f.name)`, mutation `@field(s, f.name) = v`, borrowing `&@field(s, f.name)` / `&mut @field(s, f.name)`, and `move @field(s, f.name)`), lowering directly to `Projection::Field(idx)` in Stage 3 IR.
- **Paths**: a path is ordinary comptime data, a list of field names and tuple indices such as `&["inner", "b", "1"]`, so it can be bound with `comptime let`, sliced, or passed as a parameter (`fn get[T, P: &[&str]](t: &T)`). `@field(t, p)` expands to the nested projections, so loans see the exact place: `&mut @field(o, &["i", "a"])` and `&mut @field(o, &["i", "b"])` may coexist, and an overlapping pair is a borrow error, in generic code when it is instantiated. `FieldAt[T, P]` (`core::meta`) is the type at a path. With `@leaves(T)`, one loop visits every leaf of a nested aggregate, each with its concrete type, and linear leaves are checked individually.
- **`@variant(base, comptime variant_name)`**: First-class **place expression** on a `union` value/reference (`@variant(u, v.name)`), emitting a runtime discriminant check against `v` that traps if inactive and projecting `Projection::Variant(v_idx)`.
- **`@make_union(comptime U, comptime variant_name[, payload]) -> U`**: Constructs variant `variant_name` of `union` or `error` type `U` (`Rvalue::Union`).

#### 3. Programmatic Type & Map Synthesis (`@Struct`, `@PackedStruct`, `@Tuple`, `@Enum`, `@Union`, `@Error`, `@Map`)
`comptime` functions returning `type` (or `map[K, V]`) can programmatically construct new types from slices of descriptor structs (`FieldSpec`, `EnumSpec`, `UnionSpec`, `ErrorSpec` in `core::meta`), memoized structurally so identical descriptor slices yield the exact same `TypeId`:
- **`@Struct(fields: &[FieldSpec]) -> type`** and **`@PackedStruct(fields: &[FieldSpec]) -> type`** (`FieldSpec { name: &str, ty: type }`)
- **`@Tuple(types: &[type]) -> type`**: `core::meta` builds on it with `TupleConcat[A, B]`, `TupleTake[T, N]`, and `TupleSkip[T, N]`, and with the value functions `tuple_concat(a, b)` and `tuple_split[N, T](t)`, which move every element and so work on linear elements. `tuple_split` needs `0 < N < len`, since an empty tuple does not exist; anything else is a compile error naming `N` and the tuple.
- **`@Enum(comptime Backing: integer, variants: &[EnumSpec]) -> type`** (`EnumSpec { name: &str, value: i128 }`)
- **`@Union(tag_enum: ?type, variants: &[UnionSpec]) -> type`** (`UnionSpec { name: &str, payload: type = void }`)
- **`@Error(variants: &[ErrorSpec]) -> type`** (`ErrorSpec { name: &str, payload: type = void }`)
- **`@Map(comptime K: type, comptime V: type, entries: &[(K, V)]) -> map[K, V]`**

```rust
fn Partial[T] -> type {
    comptime let src = @fields(T);
    comptime let mut out: [FieldSpec; src.len] = uninit;
    comptime for (f, i) in src {
        out[i] = FieldSpec { name: f.name, ty: ?f.ty };
    }
    return @Struct(&out);
}
```

---

## 5. Ownership, Lifetimes, and Borrow Checking

### 5.1 The "Sweet Spot" Lifetime & `self` Elision Rules `[Status: Implemented]`
Instead of abstract tick-lifetime parameters (`<'a, 'b>`), borrow relationships on function signatures are expressed directly in terms of **parameter names** via **`borrows(...)`**:
- **Return borrows (`borrows(a, b)`)**: Declares which parameter(s) the return value may borrow from (`BorrowContractItem::Return` in [`src/ast.rs`](src/ast.rs)).
- **Parameter-to-parameter borrow flows (`borrows(dst: src)`)**: Declares that a mutable destination parameter `dst` may store a reference derived from parameter `src` (`BorrowContractItem::ParamFlow` in [`src/ast.rs`](src/ast.rs)).
- **Borrows held by a parameter (`borrows(*p)`)** `[Status: Implemented]`: Declares that the return value carries only the borrows held by what `p` refers to, not a borrow of `p` itself. `Iter::next(self: &mut Self) -> ?&T borrows(*self)` yields items that borrow the sequence the iterator borrows, so two items may be held at once and an item may outlive the iterator; `fn unnest(x: &&i32) -> &i32 borrows(*x)` returns an inner reference that outlives the outer one. At a call site, the result takes the loans held by the local the argument's own loan points at ([`check_borrows`](src/borrowck.rs)). Inside the body, inference distinguishes the two origins ([`LocalId::contents`](src/ir.rs)): reading a borrow-carrying value through a dereference of a borrow-carrying root (`self.p` for a view field, `*x`) or referencing through a second shared reference (`&T`) or view (`*ref T` / `*ref mut T`) dereference (`&*self.p`) yields `*self`, while referencing `self`'s own fields (`&self.n`), memory behind an owning or raw pointer (`&*self.ptr`), or reborrowing through a safe `&mut T` held inside `self` (`&*self.m`, since `self.m` retains exclusive access unless `self` itself stays borrowed) yields `self`, which `borrows(*self)` does not cover. A contract item `p` covers `*p`. Function-pointer types write it positionally (`borrows(*_1)`).

```rust
// Explicit multi-parameter return borrow contract (no `'a` syntax needed):
pub fn pick_longer(a: &str, b: &str) -> &str borrows(a, b) {
    if a.len >= b.len { return a; }
    return b;
}

// Returning a reference strictly from `second` while ignoring `first`:
pub fn second_ref(first: &i32, second: &i32) -> &i32 borrows(second) {
    return second;
}

// Explicit parameter-to-parameter borrow flow contract (`dst` absorbs a borrow from `x`):
pub struct RefSlot { r: &i32 }
pub fn stash(dst: &mut RefSlot, x: &i32) borrows(dst: x) {
    dst.r = x;
}
```

1. **Every `pub` Function Defines Its Borrow Contract (Signature-Only)** `[Status: Implemented]`:
   - **Scope**: The rule applies to **every** `pub` callable (a `pub(mod)` method, called only within its module, has its contract inferred like a private function): free functions, inherent methods (inside `struct { ... }` / `opaque { ... }` blocks, including `opaque` blocks returned from `comptime` type functions), extension functions, `impl` methods, and generic functions. A `pub` function's borrow behaviour is fixed entirely by its signature; callers never depend on inference over its body, so editing the body can never silently change what callers keep borrowed.
   - **A contract is "defined" either explicitly or by elision**. The elision rules below are part of the signature (they are decided from parameter and return types alone, never from the body), so they count as a defined contract:
     - **`self` Elision Rule**: If a method takes `self: &Self` or `self: &mut Self` (`_1` in Stage 3), returned references borrow from `self` (`borrows(self)` $\rightarrow$ `borrows(_1)`) unless an explicit `borrows(...)` clause says otherwise. This covers methods like `get(self: &Self, index: usize) -> ?&T` and `get_mut(self: &mut Self, index: usize) -> ?&mut T`.
     - **Single-Input Elision Rule**: A function with exactly one reference-containing parameter has its return borrow from that parameter (`borrows(param)`).
     - **No-Reference Elision**: A function whose return type contains no reference and that has at most one reference-containing parameter needs no clause.
   - **Explicit Clause Required Otherwise**: Stage 2 ([`Compiler::apply_func_borrow_contracts`](src/lower/types.rs)) reports a compile-time error requiring an explicit clause when:
     - **Return**: the return type contains a reference and the borrow source is not fixed by elision (several reference-containing non-`self` parameters). `borrows()` (empty) declares that the return borrows from no parameter (only from `static` data).
     - **Parameter-to-Parameter**: the function stores a reference derived from parameter `src` into storage reachable from another parameter `dst`, including `self` (`pub fn push(self: &mut Self, value: T) borrows(self: value)`). Elision never infers a parameter-to-parameter flow; a missing `borrows(dst: src)` is rejected by [`check_borrows`](src/borrowck.rs) as a contract violation.
   - **Contracts on Generic Parameters**: A contract may name any parameter whose type *may* contain a reference after specialization. For instantiations where it contains none (`Vec[i32]::push`), the clause has no effect. The body is verified against the declared contract once per instantiation; callers use only the declared contract.
   - **`unsafe` Bodies**: Where a body stores or derives references through raw pointers in ways [`check_borrows`](src/borrowck.rs) cannot follow (`*(p + len) = move value` in `Vec::push`), the declared contract is a **trusted assertion** of the `unsafe` code, exactly as lifetime signatures are on unsafe Rust APIs. The checker still verifies everything it can see.
   - **What Needs a Clause**: Only flows that can carry a checked borrow count. A flow from a parameter whose type holds no pointer (a by-value `i32`), or from or into a raw-pointer parameter (`*mut T`, unchecked by design), needs no `borrows(...)`.
   - **Contracts Are Part of Function Types**: Function-pointer types carry a contract written with positional parameter names (`fn(&i32, &i32) -> &i32 borrows(_2)`, `fn(&mut Slot, &i32) borrows(_1: _2)`); their return contract may be elided when at most one parameter carries a reference. Calls through a pointer enforce its contract exactly like a direct call, and types that differ only in their contract are distinct (a pointer value may be converted only to a type whose contract is at least as wide).
     - **Function Values**: Naming a function as a value (`let f = helper;`) or writing a non-capturing lambda gives it a default pointer type whose return may borrow from every reference-carrying parameter and which permits no parameter-to-parameter flows. Wherever a function value is stored into a function-pointer type (assignments, struct fields, call arguments, vtables), [`check_borrows`](src/borrowck.rs) verifies the function's actual contract (declared, or inferred for private functions) fits inside that type's, e.g. `stash` must be stored as `fn(&mut Slot, &i32) borrows(_1: _2)`.
     - [Trait method signatures](#42-traits-in-a-comptime-language-status-implemented) carry contracts in the same way: vtable slots use the trait method's contract, and `impl` methods inherit or restate it.
   - **Closures Passed to `pub` Functions**: A closure is an ordinary value whose environment contains its captured references, so storing one (`spawn`-style APIs) is covered by the same `borrows(dst: f)` parameter-to-parameter clause.
   - Lowers to explicit Stage 3 contracts on [`Function::ret_borrows`](src/ir.rs) and [`Function::param_borrows`](src/ir.rs) (and, for function-pointer types, [`Program::fn_ptr_contracts`](src/ir.rs)), verified locally inside the function and enforced at call sites by [`check_borrows`](src/borrowck.rs).
2. **Internal (Private) Functions & Interprocedural Borrow Summary Inference**:
   - On private (non-`pub`) functions, `borrows(...)` annotations are optional and **inferred automatically** across the call graph by [`infer_borrow_summaries`](src/borrowck.rs):
     - **Direct & Field/Container Return Origins (`return_origins`)**: Tracks which parameter locals `_1..=arg_count` flow into `_0` at `return;`. Only a return type that can carry a borrow records origins: a reference, a type holding a view or an owning pointer to borrowing values ([Pointer Kinds](#must-consume-linear-types-opaquelinear--shared-drop-cleanup-status-implemented)), or declared contents. A function returning a raw or owning pointer (`Vec::grow`, whose result is derived from `self.ptr`), or a type holding only raw pointers, borrows nothing; a parameter of such a type likewise needs no `borrows(...)` clause.
     - **Dereferenced Pointer & Raw-Pointer Field Origins**: When a function reads a reference through a dereference (`fn unnest(x: &&i32) -> &i32 { return *x; }`) or constructs a reference by dereferencing a raw pointer stored inside a parameter (`fn get_private(self: &Self) -> &i32 { unsafe { return &*self.ptr; } }`), [`infer_borrow_summaries`](src/borrowck.rs) attributes the origin to the root parameter (`x` or `self`) so callers keep the underlying argument borrowed for the lifetime of the returned reference.
     - **Parameter-to-Parameter Mutation Flows (`param_flows`) & Local Escape Prevention**: When a function stores a reference from parameter `src` into a mutable parameter `dst` (`fn stash(dst: &mut RefSlot, x: &i32) { dst.r = x; }`), [`infer_borrow_summaries`](src/borrowck.rs) records the flow `(src -> dst)`. At every call site `stash(&mut slot, &short_lived)`, [`check_borrows`](src/borrowck.rs) propagates `short_lived`'s loan into `slot`, rejecting the program if `short_lived` goes out of scope while `slot` is still live. Storing a borrow of a local stack variable into a reference parameter (`*out = &local`, or through a callee that flows into `out`) is likewise rejected at `return`, preventing dangling stack references from escaping through output parameters.
3. **How Structs Holding References Track Loans**:
   - In [`src/borrowck.rs`](src/borrowck.rs), the `PointsTo` dataflow lattice maps each local variable `LocalId` whose type contains any pointer/reference ([`place_type_contains_ptr`](src/borrowck.rs)) to the set of `LoanId`s stored anywhere inside that local (whether via `Rvalue::Aggregate`, field assignment `_s.0 = _ref`, or call-site propagation).
   - While local-level loan tracking is conservatively unioned across all reference-bearing fields of a single local `s`, Stage 3b move analysis ([`src/drop.rs`](src/drop.rs)) tracks field-level `MovePath`s (`_s.0`, `_s.1`) independently, and NLL backward liveness (`compute_liveness`) immediately expires all loans held by `s` after the last statement that reads `s`.
   - **Reading through a pointer**: a value read through a dereference (`let v = *rr`, moving a `&i32` out of `*p`) carries the loans held by what the pointer points at, not the pointer's own loan on it. Copying a reference out of a container therefore does not keep the container borrowed, but still depends on what the copied reference refers to.
4. **Precise Drop Check (`unsafe impl drop(may_dangle T)`)** `[Status: Implemented]`:
   - Locals are destroyed in reverse declaration order, so a container declared before the data its elements borrow is dropped after that data dies. Dropping a value whose type has a `drop` hook counts as a use of the borrows it holds, unless the drop provably never reads them ([`Compiler::drop_ignores_borrows`](src/lower/types.rs)):
     - a value holding no borrow, a pointer, or a type without a `drop` hook whose parts all qualify (a `tuple { &i32, i32 }`);
     - a type whose hook is declared **`unsafe impl drop(may_dangle T)`**, when every borrow-carrying field (and any declared `owns` / `borrows` content) recursively holds borrows *only* inside `T` values (inline, behind `*own T`, in `uninit T`, or in nested composites whose parts all qualify) and dropping the concrete `T` itself qualifies. The declaration is the hook author's assertion that it only drops, moves, or frees `T` values and never otherwise reads them; writing `may_dangle` without `unsafe`, or `unsafe` without `may_dangle`, is rejected.
   - `Vec`, `Box`, `HashMap`, `Mutex`, and `Channel` declare it, so `let mut v = Vec[&i32]::new(); let x = 7; v.push(&x);` compiles: dropping an `&i32` reads nothing. `Vec[Peek]` still requires its borrows live when `Peek`'s own hook reads its reference, as does a `may_dangle` type that also holds a reference directly (its hook may read that one), and any use of the container after the referent dies is still rejected.
   - Stage 2 lists the qualifying hooked types in [`Program::dangle_types`](src/ir.rs); Stage 3c recognizes elaborated destructor calls on them and does not count the `&mut v` they take as a use of `v` for liveness ([`check_borrows`](src/borrowck.rs)), so the borrows `v` holds may end before it is dropped.

---

- **Receiver borrows start after the arguments** `[Status: Implemented]`: a method call auto-borrows a `&mut self` receiver after evaluating its arguments, so they can read the receiver: `v.push(v.len())`, `self.add(self.get())`, `m.insert(m.len() as i32, x)`. The IR shows the true order, so the borrow checker needs no special case: an argument that still holds a borrow of the receiver when the call starts (`self.add_ref(&self.n)`) conflicts as usual, and one that moves the receiver makes the borrow a use after move. Trait-object calls work the same way. An explicit `&mut v` argument is evaluated in order, as written.

### 5.2 Lifetime Erasure Timeline `[Status: Implemented]`
- **Surface `borrows(...)` clauses**: Lowered to Stage 3 parameter indices on [`Function::ret_borrows`](src/ir.rs) and [`Function::param_borrows`](src/ir.rs).
- **Loans & mutability (`&T` vs `&mut T`)**: Verified by [`check_borrows`](src/borrowck.rs) in Stage 3, then erased when lowering to Stage 4 LLVM IR ([`src/llvm.rs`](src/llvm.rs)), where all pointers become `ptr`.

---

### 5.3 Self-Referential Relative References (`&rel T`, `&rel [T]`, `&rel str`) `[Status: Implemented]`
Because every value move in the language is a bitwise `memcpy` without C++-style move constructors or Rust-style `Pin<T>`, an absolute pointer (`&T`) into an `opaque` type's own inline fields would dangle the moment the value is moved. To support safe, movable self-referential `opaque` types (inline parsers, zero-copy network packets, ring buffers, small-buffer-optimized views), `opaque` field declarations may use **relative references**:

| `opaque` Field Type | Meaning | Stage 3 Representation | On-the-Fly Resolution (`self: &Self` vs `self: &mut Self`) |
| :--- | :--- | :--- | :--- |
| **`&rel T`** | Single-element relative reference into `self` | `isize` (`i64`, 8 bytes): `addr(target) - addr(rel_field)` | Resolves to `&T` on `&Self`, or `&T` / `&mut T` on `&mut Self` |
| **`&rel [T]`** | Relative slice into `self` | `{ offset: isize, len: usize }` (16 bytes): `addr(elem_0) - addr(rel_field)` | Resolves to `&[T]` on `&Self`, or `&[T]` / `&mut [T]` on `&mut Self` |
| **`&rel str`** | Relative UTF-8 string slice into `self` | `{ offset: isize, len: usize }` (16 bytes): `addr(byte_0) - addr(rel_field)` | Resolves to `&str` (always immutable) |

1. **Self-Field-Anchored Offset Invariant (Move-Transparent & Composable)**:
   - Each `&rel` field stores the signed byte offset from **its own field address** (`&self.<rel_field>`) to the target byte inside `self`:
     $$\text{offset} = \text{addr}(\text{target}) - \text{addr}(\text{rel\_field})$$
   - When the enclosing `opaque` is moved by bitwise `memcpy` (or embedded inside an outer `opaque`, `struct`, `tuple`, or `[S; N]` array that is relocated in memory), both `addr(target)` and `addr(rel_field)` shift by the exact same $\Delta$, so their difference $\text{offset}$ remains **100% invariant** with zero fixup code.
2. **Scope & Encapsulation (`opaque` Fields Only)**:
   - `&rel T`, `&rel [T]`, and `&rel str` are permitted **strictly in `opaque` field declarations** (rejected in `struct`, `tuple`, function parameters/returns, local variables, and the meta-type constraint hierarchy). Because `opaque` fields are strictly private and `opaque` forbids partial moves (`move s.field`), only the `opaque`'s own methods can initialize or retarget its `&rel` fields, and sibling fields can never be moved out from under a relative reference.
   - Inside `Self { ... }` literals, non-`&rel` fields are initialized in memory first and `self` is bound to the instance so `&rel` field initializers can write `focus: &rel self.nums[0]` or `window: &rel self.buf[2..6]` directly.
3. **Co-Residence Rule (Compile-Time Safety Invariant)** ([`FuncLowerer::verify_rel_coresidence`](src/lower/stmt.rs)):
   - A `&rel` field on `base_place` (`self`) may only be initialized or assigned via `&rel <target_expr>` where `<target_expr>` resolves to a place `rhs_place` that is a **fixed inline sub-place** of `base_place`:
     1. `rhs_place` must share `base_place`'s root local and projection prefix.
     2. `rhs_place` must traverse **zero `Projection::Deref`** indirections after `base_place` (pointing `&rel` at an external stack variable or heap buffer is rejected).
     3. `rhs_place` must traverse **zero `Projection::Variant` (`union` / `?T`)** and **zero `Type::Overlay` (`overlay` / `uninit T`)** projections after `base_place` (preventing a subsequent active-variant switch from invalidating the payload at that offset).
4. **UTF-8 Invariant for `&rel str`**:
   - Initializing or assigning a `&rel str` field from a `str`-typed inline source or validated slice (`&rel self.buf[lo..hi]`) inside an `opaque` method is encapsulated within that `opaque`. While any resolved `&str` borrowed from `self.<rel_str_field>` is live, [`check_borrows`](src/borrowck.rs) holds an active shared loan on `self`, statically preventing any `&mut self` mutation of `self.buf`. If a `&mut self` method mutates a raw `[u8; N]` buffer that backs a `&rel str` field, maintaining valid UTF-8 in `self.buf` (or updating the `&rel str` slice) is part of the `opaque`'s encapsulated invariant.
5. **Inherited Mutability & Zero-Loan-At-Rest NLL Borrow Checking**:
   - There is no `&rel mut` type modifier; mutability is inherited from `self` at the point of access (`self: &Self` yields shared `&T` / `&[T]` / `&str`; `self: &mut Self` additionally permits `*self.focus = v`, `self.window[i] = v`, or taking `&mut T` / `&mut [T]`).
   - Because `&rel` fields lower to pure integer offsets (`isize` / `{ isize, usize }`) containing no `Type::Ptr`, an `opaque` with `&rel` fields holds **zero active loans at rest** and can be freely moved or returned by value.
   - The moment a `&rel` field is read or dereferenced on `base_place`, [`src/lower/`](src/lower/mod.rs) takes an NLL borrow `Rvalue::Ref { mutable: want_mut, place: base_place }` of the enclosing `opaque` and derives the resolved pointer via pointer-offset GEP (`BinOp::AddWrap`), so [`check_borrows`](src/borrowck.rs) keeps the enclosing `opaque` borrowed for the exact lifetime of the resolved `&T` / `&[T]` / `&str`.

---

### 5.4 Safe Threading, Automatic Structural `send`/`sync`, Linear `Mutex[T]` & Execution-Agnostic `@select` `[Status: Implemented]`
Concurrency safety is built directly on the existing `opaque(linear)`, NLL borrow checker, and `comptime` meta-type constraint systems (`send`, `sync`, `ScopedHandle`, `JoinHandle`, `spawn`, `Mutex`, `Channel`, `Waiter`, `WaitNode`, `Timer`, and `@select` are **`[Status: Implemented]`**):

1. **Automatic Structural `send` & `sync` (and Declared Exceptions)**:
   - **`send`** (safe to transfer or capture into another thread) and **`sync`** (safe to share via `&T` across threads) are automatic structural properties and first-class meta-type constraints (`[T: send]`, `[T: sync]`):
     - **Primitives** (`integer`, `float`, `bool`, `rune`, `void`, `never`, `enum`, `simd`, `fn` pointers) are both `send` and `sync`.
     - **Raw pointers** (`*const T`, `*mut T`) are **`!send` and `!sync`** by default. An owning pointer `*own T` is `send` / `sync` as `T` is, and a view `*ref T` / `*ref mut T` as `&T` / `&mut T` is ([Pointer Kinds](#must-consume-linear-types-opaquelinear--shared-drop-cleanup-status-implemented)).
     - **Safe references & slices**: `&T` / `&[T]` / `&str` are `send` and `sync` $\iff$ `T: sync`. Unique mutable borrows `&mut T` / `&mut [T]` are `send` $\iff$ `T: send` (and `sync` $\iff$ `T: sync`).
     - **Open containers & closures** (`tuple`, `struct`, `[T; N]`, `?T`, `union`, `closure`, standard `opaque` / `opaque(copy)` / `opaque(linear)`) are `send` $\iff$ all fields/captures are `send`, and `sync` $\iff$ all fields/captures are `sync`.
     - **`cell` fields (interior mutability)**: an `opaque` assumes its state does not change while shared by `&T`, which is what makes deriving `sync` sound. State that does change behind a shared reference is declared **`cell name: T`** (only in `opaque`, whose fields are private; forbidden in transparent `struct`). A `cell` field makes its type **`!sync`** unless the type declares `unsafe sync`. Taking a safe reference or slice (`&self.n`, `&mut self.n`, `&self.arr[..]`) to a `cell` field is a compile-time error—`cell` fields are read and written by value (`self.n = v`) or addressed with raw pointers (`&raw const self.n`, `&raw mut self.n`), preventing live `&T` references from coexisting with interior writes. Writing through a shared reference must target a `cell` field (`&raw mut self.n` through `self: &Self`, lowered as a shared borrow and cast to `*mut`), whereas casting a shared reference of the whole enclosing composite to a `*mut` pointer (`self as *mut Self` or `&raw mut *self`) is allowed only for an `opaque` that declares `unsafe sync` ([`FuncLowerer::shared_derefs_reach_cells`](src/lower/stmt.rs), [`Compiler::permits_interior_mutation`](src/lower/types.rs)). Without this, `opaque Counter { n: u64 }` mutating `n` through `&self` would be inferred `sync` and race when shared between threads. Laundering the pointer through `*const T` or `usize` remains the `unsafe` author's responsibility.
     - **Atomics** `[Status: Implemented]`: `@atomic_load(p)`, `@atomic_store(p, v)`, `@atomic_swap(p, v)`, `@atomic_cas(p, expected, new)`, and `@atomic_add` / `@atomic_sub` / `@atomic_and` / `@atomic_or` / `@atomic_xor(p, v)` operate on an 8-, 16-, 32-, or 64-bit integer behind a raw pointer, sequentially consistently. They require `unsafe` (they dereference `p`), and all but `store` yield the previous value (`cas` stores only if the value equals `expected`). With `cell` fields and `unsafe sync` they implement lock-free types (`opaque(unsafe sync) Counter { cell n: u64 }` with `@atomic_add(&raw mut self.n, 1)`). Each lowers to a call of a reserved builtin `slir.atomic.<op>.<type>` ([`ir::ATOMIC_PREFIX`](src/ir.rs)), which the LLVM backend emits as the atomic instruction (`atomicrmw`, `cmpxchg`, `load atomic`, `store atomic`) and the compile-time VM evaluates as a plain read-modify-write that synchronizes its location (see [section 9](#9-soundness-testing-status-implemented)).
     - **Declared exceptions** ([`ast::ThreadDecl`](src/ast.rs)): what the compiler cannot verify is asserted, one trait at a time, with **`opaque(unsafe send)`** and **`opaque(unsafe sync)`**. An assertion is unconditional; conditions on type parameters are written as bounds on the type function (`Mutex[T: send]` is `opaque(unsafe send, unsafe sync)`). A `File` owning a C `FILE*` is `opaque(unsafe send)`: movable to another thread, not shareable. Withholding a trait is always sound, so **`opaque(!send)`** and **`opaque(!sync)`** need no `unsafe` (a handle bound to its creating thread). Bare `opaque(send)` / `opaque(sync)` and asserting and withholding the same trait are rejected in [`src/frontend/mod.rs`](src/frontend/mod.rs). A guard type like `opaque(linear) MutexGuard[T]` holds a raw pointer to the lock and declares nothing, so it is **automatically `!send` and `!sync`**, statically preventing a lock guard from being sent or shared across threads.
     - **Per-value assertions**: `std::sync::UnsafeSend[T]` / `UnsafeSync[T]` wrap a single value (`unsafe { UnsafeSend[*mut i32]::new(p) }`) to hand one raw pointer to a worker thread without declaring a type. They are ordinary library types over `opaque(unsafe send)` / `opaque(unsafe sync)` with an `unsafe fn new`.
2. **Flat Scoped & Unscoped Threads (`ScopedHandle` & `JoinHandle`)**:
   - **`spawn_scoped[F: send](f: F) -> ScopedHandle[F]`**: Accepts a borrowing closure `fn() -> R` (where `R` is the return type of `F`, currently `i32` in `std::thread::spawn_scoped`, and `F: send`) and returns an **`opaque(linear) ScopedHandle[F]`** that retains `f`'s NLL borrow loans (it owns the closure through `anchor: *own F`) and exposes **only** `.join(move self)` (no `.detach()`).
     - Because `ScopedHandle[F]` is `opaque(linear)` and [panics abort without unwinding](#panic-trap-and-unwind-semantics-panic--abort-status-implemented), [`elaborate_drops`](src/drop.rs) guarantees `.join()` executes before the parent stack frame exits.
     - Because `ScopedHandle[F]` carries `f`'s NLL loans, [`check_borrows`](src/borrowck.rs) prevents the parent thread from mutating or dropping any stack variable borrowed by the child thread until `.join(move self)` consumes the handle—achieving safe, zero-allocation stack borrowing across threads with a flat API (no nested `thread::scope(|s| ...)` callback required).
   - **`spawn[F: send](f: F) -> JoinHandle[R]`** `[Status: Implemented]`: Requires a non-borrowing `move fn() -> R` (or `fn` pointer) and returns an **`opaque(linear, unsafe sync) JoinHandle[R]`** supporting both `.join(move self) -> R` and `.detach(move self)`.
     - **Linear Results** `[Status: Implemented]`: `JoinHandle[R]` owns its result through declared contents (`opaque(linear, owns R, unsafe sync)`, since `R` arrives through `pthread_join`), so `.detach(move self)` is gated by `where R: !linear`: detaching would discard an unconsumed linear result. A thread returning a linear `R` must be `.join()`ed.
3. **Linear `Mutex[T]` (`MutexGuard[T]` + `with_lock` Helper)**:
   - **`mtx.lock(self: &Self) -> MutexGuard[T]`**: Returns a must-consume **`opaque(linear) MutexGuard[T]`** borrowing `mtx` (`&Mutex[T]`). Every control-flow path must explicitly release the lock via **`g.unlock(move self)`**, preventing accidental long-lived locks across subsequent blocking operations, while NLL borrow checking ensures no `&T` / `&mut T` obtained from `g.get_mut()` can outlive `g.unlock()`.
   - **`mtx.with_lock[F: callable](f: F)`**: Convenience helper that acquires `self.lock()`, invokes `f(g.get_mut())` (forwarding `f`'s return value), and calls `g.unlock()` automatically.
   - **Mutexes and Channels Holding Linear Values** `[Status: Implemented]`: `Mutex[T]` holds its value inline and `Channel[T]` holds its buffer behind `*own [uninit T; 64]`, so `Mutex[Transaction]` and `Channel[Transaction]` are linear instantiations. Threads share them by `&` reference while a single owner holds the value; once every borrower has finished (enforced by NLL and [`ScopedHandle`](#54-safe-threading-automatic-structural-sendsync-linear-mutext--execution-agnostic-select-status-implemented)), the owner consumes it:
     - `Mutex[T]::into_inner(move self) -> T` returns the protected value.
     - `Channel[T]::close_and_drain[F: callable](move self, f: F)` closes the channel and passes every still-buffered value to `f` by move.
     - Their `where T: !linear` drop hooks keep implicit scope-exit drops for affine and `copy` element types (dropping the protected value and any still-buffered values).
     - `Channel[T]::send(self: &Self, val: T) borrows(self: val)` and `Channel[T]::try_send(self: &Self, val: T) -> ?T borrows(val, self: val)` record element borrows in the channel (`try_send` also hands `val` back when the channel is full instead of discarding it), while `Channel[T]::recv(self: &Self) -> T borrows(*self)` and `Channel[T]::try_recv(self: &Self) -> ?T borrows(*self)` (as well as `@select` send and receive arms) propagate those element borrows to receivers so a borrowed value sent through a channel cannot outlive its referent.
4. **Execution-Agnostic `@select` Multi-Wait Architecture `[Status: Implemented]`**:
   - Multi-way waiting over channels (`Channel[T]`) and timers (`Timer::after_ms(...)`) uses a stack-allocated `Waiter` (`WAITING -> CLAIMED(branch_idx)` atomic CAS) and `WaitNode` slots: in blocking OS threads `Waiter::park()` waits on an OS condition variable / timer, while in a future `async` context the identical CFG structure (`FastPoll -> Register -> Park -> Unregister -> SwitchInt(winner)`) suspends as a coroutine `await` point.
   - **Losing Send Arms Settle Their Value** `[Status: Implemented]`: Each `.send(val)` arm evaluates `val` into a caller-owned slot whose address is handed to the channel through `select_fast_send` / `select_register_send`. Only the winning arm's value is transferred (the channel copies it out and the caller forgets its slot). In whichever arm wins (including `default`), every *losing* send arm's value is still owned by the caller and is settled first: it is passed to that arm's optional `else |unsent| handler` clause, or otherwise dropped. Dropping a linear value is a compile-time error, so a linear send needs the clause:
     ```rust,ignore
     let r: i32 = @select {
         txs.send(tx) else |unsent| { unsent.rollback(); } => 1,
         n = acks.recv() => n,
     };
     ```

---

## 6. Module, Visibility & Package System

### 6.1 Files *Are* Modules (No `mod foo;` Declarations) `[Status: Implemented]`
Unlike Rust (where creating `math.rs` requires a separate `mod math;` declaration in `lib.rs` or `main.rs`), the directory hierarchy inside `src/` defines the module tree automatically:
- `src/main.slop` or `src/lib.slop` -> `root` module of the package
- `src/math.slop` -> `root::math`
- `src/net/http.slop` -> `root::net::http`

No `mod foo;` statements exist in the language. [`Compiler::compile_package_dir`](src/lower/mod.rs) loads every `.slop` file under a package's `src/` directory by this mapping ([`Compiler::load_package_dir`](src/lower/mod.rs)); [`Compiler::compile_package`](src/lower/mod.rs) accepts the same `(module_path, source)` pairs directly. Items inside modules are analyzed on demand, as `import`s and uses reach them.

### 6.2 Import Syntax (`import`) & First-Class `comptime` Modules `[Status: Implemented]`
Imports use path syntax rooted at a package name (`core`, `std`, `root`, or an external dependency) or `super`:

```rust
// 1. Bind a module namespace in scope (`http::Request`, `http::get(...)`)
import std::io;
import root::net::http;

// 2. Import specific items directly into scope (with optional aliasing)
import std::mem::{Box, swap};
import root::graphics::Color as GfxColor;

// 3. Re-export items from a module (`pub import`)
pub import root::net::http::{Client, Server};
```

- **Order-Independent Top-Level Declarations**: Functions, types, constants, and `comptime` items within a module can reference one another in any order without forward declarations.
- **First-Class `module` Values at `comptime`** `[Status: Implemented]`: Importing a module (`import std::io;`) binds `io` as a `comptime` module value that can be passed to `comptime` functions (e.g., to swap backends or reflect over exported declarations via `@declarations(mod_val)`).

### 6.3 Strict Visibility Rules: `private`, `pub(mod)`, and `pub` `[Status: Implemented]`
Because [`struct`](#34-product-types-tuple-vs-struct-vs-opaque-status-implemented) (transparent public data) and [`opaque`](#34-product-types-tuple-vs-struct-vs-opaque-status-implemented) (encapsulated invariant/resource) are distinct type kinds, visibility has three clean levels:

| Visibility | Syntax | Scope & Access Rule |
| :--- | :--- | :--- |
| **Private (Default)** | `fn helper()`, `field: i32` | - **Top-level module items** (`fn`, `opaque`, `struct`, `const`): visible only within the **same file/module**.<br/>- **`opaque` fields & private methods** (of any type: `struct`, `opaque`, distinct type): visible **strictly inside that type's block itself**! Even other functions in the same file cannot bypass an `opaque`'s methods to mutate or read its private fields (`pub` on a field inside `opaque { ... }` is rejected). |
| **Module-Internal** | `pub(mod) fn ...` (methods only) | A method callable anywhere in its **defining module**, including other types' blocks, and nowhere else. Cooperating types in one module (a `Mutex` and its guard, a `Channel` and its wait nodes) use it to share an internal API without exposing it: fields stay private to their block, and the module talks to them through `pub(mod)` methods. It is rejected on top-level items (already module-private), on fields, and on trait methods. |
| **Public** | `pub fn ...`, `pub opaque ...`, `pub struct ...` | Visible everywhere (including external packages). Note: fields of a `struct` are always `pub` by default. |

There is no package-level visibility: the compiler builds one package at a time (a `package.slop` manifest's dependencies are evaluated but not yet fetched or linked), so a former `pub(pkg)` would have meant `pub`; it is a compile error until packages exist.

### 6.4 Inherent Methods, Extension Functions (`self` Receivers) & Coherence `[Status: Implemented]`
1. **Inherent Methods & Lifecycle Hook Coherence**:
   - Inherent methods may be declared inside either a `struct { ... }` or `opaque { ... }` block.
   - A lifecycle hook is a built-in trait implemented in the type's own block, named like the constraint it satisfies: `impl drop { fn drop(self: &mut Self) { ... } }`, `impl clone { fn clone(self: &Self) -> Self { ... } }`, `impl default { fn default() -> Self { ... } }`, and `impl format { fn format(self: &Self, f: &mut Formatter) { ... } }` (so `T: clone` means exactly "has `impl clone`"). A conditional hook puts its `where` clause on the `impl` (`impl drop where T: !linear { ... }`). `drop`, `clone`, and `default` are no longer keywords, so they are usable as ordinary names (a local `clone`, a function `drop_all`'s parameter `drop`); the former `drop(self: &mut Self) { ... }` form is an error naming the `impl` form.
   - Lifecycle hooks (`default`, `clone`, `drop`, `format`) can **only** be declared inside an **`opaque { ... }` block** (declaring any lifecycle hook inside `struct { ... }` is a compile-time error) so that value copyability, structural formatting, and Stage 3 destructor elaboration ([`elaborate_drops`](src/drop.rs)) are global, import-independent properties of the type.
2. **Extension Methods via `self`-Receiver Functions**:
   - Any top-level function whose **first runtime parameter** is named `self` (`self: T`, `self: &T`, or `self: &mut T`) can be called both as a normal function (`norm(&p)`) and with method-call dot syntax (`p.norm()`) in any module where the function is in scope (defined locally or brought into scope via `import`).
   - **`comptime`-Parameterized Receivers**: Any `comptime` parameters that precede `self` and appear in `self`'s type annotation are inferred automatically from the receiver at the method call site. This works uniformly for built-in parameterized types (`simd[T; N]`, `[T; N]`, `?T`) and user-defined `comptime` type functions (`Pair[T]`):
     ```rust
     // Extension method on built-in `simd[T; N]`:
     pub fn first[T, N: usize](self: &simd[T; N]) -> T {
         return self[0];
     }

     // Extension method on user-defined `Pair[T]`:
     pub fn dot[T](self: &Pair[T], other: &Pair[T]) -> T {
         return self.first * other.first + self.second * other.second;
     }
     ```
   - **Zero Private Privilege**: Because an extension function is outside the `opaque { ... }` block, it has no access to private `opaque` fields or private `opaque` methods (even when defined in the same file).
   - **Resolution Precedence & Disambiguation**:
     1. Inherent methods defined inside the `struct { ... }` or `opaque { ... }` block always take priority.
     2. In-scope `self`-receiver extension functions, ordered by receiver & meta-type constraint subsumption:
        - Concrete receiver (`self: &Point`, `self: &Pair[i32]`, `self: i32`)
        - Parameterized structural or type-constructor receiver (`self: &simd[T; N]`, `self: &Pair[T]`), sub-ordered by `T`'s meta-type constraint (`signed`/`unsigned` $\prec$ `integer`/`float` $\prec$ `number` $\prec$ `scalar` $\prec$ `type`)
        - Constrained generic receiver (`self: T` where `T: signed` $\prec$ `T: integer` $\prec$ `T: number` $\prec$ `T: scalar` $\prec$ `T: type`)
     3. Disjoint meta-type constraints (`signed`, `unsigned`, `float`) may share a function name in the same scope without ambiguity. If two imported extension functions have incomparable or equal constraints for `recv.method(...)`, the compiler reports an ambiguity error that can be disambiguated via qualified call (`mod_a::method(&recv, ...)`) or import aliasing (`import mod_a::{method as method_a};`).
3. **Stage 3 (`SLIR`) Lowering**:
   - Stage 2 flattens all reachable module items, inherent methods, extension functions, and `comptime` specializations into a single whole-program Stage 3 [`Program`](src/ir.rs), marking only explicit FFI exports (`export "sym"`) and `main` on [`Function::export`](src/ir.rs).

### 6.5 Pure `comptime` Package Manifests (`package.slop`) `[Status: Implemented]`
Instead of splitting package configuration across a static declarative format and an unsandboxed host build script (`Cargo.toml` + `build.rs`), a package's manifest (`package.slop` at the repository root) is a pure `comptime` module exporting a `pub fn package(target: Target) -> Package` function evaluated inside the deterministic, sandboxed Stage 3 VM ([`Vm::eval`](src/vm.rs)):

```rust
import std::build::{Package, Target, OptimizeMode, Dependency};

pub fn package[target: Target]() -> Package {
    return Package {
        name: "http_server",
        version: { 0, 2, 0 },
        root: "src/main.slop",
        no_std: target.os == Target::Os::Freestanding,
        deps: &[
            Dependency {
                name: "tls",
                url: "https://pkg.sloplang.dev/tls-1.4.0.tar.zst",
                sha256: 0x9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08_u256,
            },
        ],
        system_libs: if target.os == Target::Os::Linux {
            &["pthread", "c"]
        } else {
            &["System"]
        },
    };
}
```

- **Sandboxed Heretic Reproducibility (No Arbitrary Host I/O or Network Execution)**:
  - Because `package[target]()` runs inside [`Vm::eval`](src/vm.rs) (which forbids `extern` FFI calls, filesystem writes, and network sockets) with a bounded step limit, evaluating a dependency's manifest can never execute arbitrary shell commands on the developer's machine.
- **Target-Conditional Configuration Without a Separate Macro Sub-Language**:
  - Platform-specific dependencies, `no_std` selection, and C library link flags are written using ordinary `if` / `match` expressions over `[target: Target]` rather than stringly-typed `[target.'cfg(...)'.dependencies]` tables.
- **Content-Addressed `u256` Integrity Hashes**:
  - External dependencies specify a first-class `u256` SHA-256 digest directly in the manifest, verified by the package manager before unpacking.

### 6.6 `core` & `std` Standard Library Architecture & Automatic Prelude `[Status: Implemented]`
The compiler bundles a two-tier standard library hierarchy ([`src/stdlib.rs`](src/stdlib.rs)) with lazy on-demand instantiation and lexical prelude shadowing:
1. **`core` (Freestanding Tier — Zero OS / Libc Dependencies)**:
   - `core::mem`: `swap`, `replace`
   - `core::cmp`: `min`, `max`, `clamp` (both function and `self`-receiver extension method on `number`)
   - `core::math`: disjoint `abs` overloads on `signed` and `float`
   - `core::slice`: `is_empty` (on `sequence`), `first`, `last` (on `&[T]`)
   - `core::option`: `is_some`, `is_none` (on `?T`)
   - `core::fmt`: `Formatter` (with `write_str`, `write_byte`, `is_truncated`), `fmt_slice`, `fmt_buf`
   - `core::meta`: reflection and programmatic type synthesis descriptors (`StructField`, `TupleField`, `OverlayField`, `EnumVariant`, `UnionVariant`, `ErrorVariant`, `MapEntry`, `FnInfo`, `FieldSpec`, `EnumSpec`, `UnionSpec`, `ErrorSpec`)
   - `core::prelude`: re-exports the core extension methods, formatting utilities, and reflection descriptors (`swap`, `replace`, `min`, `max`, `clamp`, `abs`, `is_empty`, `first`, `last`, `is_some`, `is_none`, `Formatter`, `fmt_slice`, `fmt_buf`, `core::meta::*`).
2. **`std` (Hosted Tier — OS / Libc / POSIX Threads, Re-exporting `core`)**:
   - `std::mem`: `malloc`, `free`, `try_alloc[T](len: usize) -> ?*mut T`, `Box[T]` (RAII heap-allocated smart pointer over `*own T` with `new`, `get`, `get_mut`, `into_inner`, and paired `drop` hooks), plus `pub import core::mem::*;`
   - `std::sync`: `Mutex[T: send]` (`opaque(unsafe send, unsafe sync)` with `new`, `lock`, `with_lock`, `into_inner`, `drop`), `MutexGuard[T: send]` (`opaque(linear)` holding a `*ref mut T` view of the data, with `get_mut`, `unlock`), `Channel[T: send]` (`opaque(unsafe send, unsafe sync)` bounded MPMC channel over `*own [uninit T; 64]` with `close_and_drain`, with direct handoff and `@select` hooks), `Waiter`, `WaitNode`, `Timer`, and the per-value assertions `UnsafeSend[T]` / `UnsafeSync[T]`
   - `std::thread`: `ScopedHandle[F: send]` (`opaque(linear)` with `join(move self)`), `spawn_scoped[F: send](f: F)`, `JoinHandle[R: send]` (`opaque(linear, unsafe sync)` with `join(move self) -> R` and `detach(move self)`), and `spawn[F: send](f: F) -> JoinHandle[R]`
   - `std::fmt`: `String` (RAII heap-allocated UTF-8 string with `as_str`, `len`, `format`, `drop`) and `format(val: T) -> String`
   - `std::io`: `puts`, `write`, `read`, `print_str`, `print(val: T)`, `println(val: T)`
   - `std::build`: `Target` (with `Target::Os` and `Target::Arch`), `OptimizeMode`, `Dependency`, `Package`
   - `std::prelude`: re-exports `core::prelude::*`, `Box`, `Mutex`, `MutexGuard`, `Channel`, `Waiter`, `WaitNode`, `Timer`, `ScopedHandle`, `spawn_scoped`, `JoinHandle`, `spawn`, `String`, `format`, `print`, and `println`.
3. **Automatic Prelude & Lexical Shadowing**:
   - User modules automatically receive an implicit prelude import (`std::prelude::*` in hosted mode, or `core::prelude::*` in freestanding `no_std` mode).
   - **Lexical Precedence**: Any local declaration or explicit `import` in a user module shadows prelude items of the same name without triggering ambiguity errors.
   - **Zero Unused Codegen Cost**: `core` and `std` externs, types, and functions are instantiated lazily on demand, emitting zero IR or LLVM declarations for unreferenced standard library items.

---

## 7. Low-Level Memory & Lifecycle Intrinsics (`Vec` & `StackVec` Reference Patterns) `[Status: Implemented]`

Memory management and value lifecycle operations are exposed as compiler intrinsics:
- **`@alloc(comptime T: type, len: usize) -> *mut T`** `[Status: Implemented]`: Allocates uninitialized heap memory for `len` elements of `T` (`len * size_of(T)` bytes aligned to `align_of(T)`). When `@size_of(T) == 0` (a ZST such as `void`, `struct {}`, or `[U; 0]`), `@alloc` returns the aligned null-page address **`(@align_of(T) as usize) as *mut T`** (`1, 2, 4, 8, 16, ...`) with **zero heap calls**. For `@size_of(T) > 0`, returns a non-null `*mut T`; if `len * size_of(T)` overflows `usize` or the OS allocator returns `NULL` (out-of-memory), `@alloc` **immediately traps (`@llvm.trap()`)**. (Fallible allocation uses `std::mem::try_alloc[T](len) -> ?*mut T`, which likewise returns `(@align_of(T) as usize) as *mut T` for ZSTs.)
- **`@realloc(comptime T: type, ptr: *mut T, len: usize) -> *mut T`** `[Status: Implemented]`: Resizes an existing allocation to `len` elements of `T` (returning `(@align_of(T) as usize) as *mut T` with zero heap traffic when `@size_of(T) == 0`), trapping via `@llvm.trap()` on size overflow or out-of-memory.
- **`@dealloc(ptr: *mut T)`** `[Status: Implemented]`: Unsafe; releases heap memory previously allocated by `@alloc` / `@realloc` (a compile-time no-op when `@size_of(T) == 0`, never passing a null-page ZST pointer to `free`).
- **`@memcpy(dest: *mut T, src: *const T, len: usize)`** `[Status: Implemented]`: Unsafe; copies `len` elements of `T` (`len * size_of(T)` bytes) from `src` to `dest`, requiring the memory regions to be **non-overlapping**; lowers to `llvm.memcpy`.
- **`@memmove(dest: *mut T, src: *const T, len: usize)`** `[Status: Implemented]`: Unsafe; copies `len` elements of `T` from `src` to `dest`, allowing **overlapping** memory regions; lowers to `llvm.memmove`.
- **`@transmute(comptime Dest: type, src: Src) -> Dest`** `[Status: Implemented]`: Unsafe bitwise reinterpretation of `src` as `Dest`; enforces `size_of(Src) == size_of(Dest)` at compile time, consumes a non-`copy` `src` by move without running `Src`'s destructor (a `copy` `src` stays usable), and does **not** require equal alignment because `src` is copied/moved by value into a `Dest`-aligned location. The Stage 3 VM reproduces the compiled layout bit for bit (scalars, niche-optimized optionals, tagged unions, structs, arrays, and overlays up to 128 bytes); pointers cannot be reinterpreted during compile-time evaluation.
- **`@size_of(T)` / `@align_of(T)`** `[Status: Implemented]`: `usize` compile-time constants with `T`'s target size and alignment (niche-optimized optionals included); usable in array lengths and `const` initializers.
- **`@default(comptime T: type) -> T`** `[Status: Implemented]`: Invokes `T`'s `default` hook or synthesizes structural default for `tuple`s/`struct`s/primitives.
- **`@clone(v) -> T`** `[Status: Implemented]`: Accepts `v: T` or `&v: &T` and invokes `T`'s `clone` hook or synthesizes structural field-by-field clone for `tuple`s/`struct`s/primitives. `@clone(&e)` clones `e` whatever its type (a `&T` element of a `Vec[&T]` is cloned as a reference), while `@clone(r)` of a reference `r` clones what it refers to.
- **`@drop(target)`** `[Status: Implemented]`: Lowers directly to `Terminator::Drop { place, target }` in Stage 3 — works for early in-place drop of a stack variable `v`, a mutable reference `&mut v`, or (inside `unsafe`) a raw pointer slot `p + i`. Rejects any `linear` type at compile time.
- **`@forget(v)`** `[Status: Implemented]`: Unsafe; consumes `v` by move and suppresses its destructor — marks `v` uninitialized in [`src/drop.rs`](src/drop.rs) without emitting a drop call, compiling to zero runtime instructions. Making `@forget` `unsafe` allows scoped RAII guards such as DMA/io_uring buffers to rely on `drop` running for soundness.

### `unsafe fn` and `safe extern fn` `[Status: Implemented]`
An `unsafe` block asserts that the operations inside it are sound. A function whose soundness depends on what its caller passes (a pointer that must be valid, a slot that must be uninitialized) is declared **`unsafe fn`**, which hands that obligation to each caller:
- **Calls**: Calling an `unsafe fn` (free function, inherent or `impl` method, static method, or generic instantiation) requires an `unsafe { ... }` block ([`FuncLowerer::check_unsafe_call`](src/lower/call.rs)). The body of an `unsafe fn` is *not* itself an `unsafe` block: its own unsafe operations still need blocks, so the lines that carry an obligation stay visible. A closure or lambda written inside an `unsafe` block is inside it: its body may perform unsafe operations too.
- **Function pointers**: Naming an `unsafe fn` as a value gives an `unsafe fn(...) -> R` pointer type, and naming an `extern fn` gives an `extern fn(...)` C pointer that is `unsafe extern fn(...)` unless the declaration is `safe extern fn`; these are distinct from the safe types; calls through it require `unsafe`. A safe function converts to an `unsafe fn` pointer type, never the reverse.
- **Traits**: A trait method declared `unsafe fn` must be implemented as `unsafe fn` and vice versa; its vtable slot has the `unsafe fn` pointer type, so dynamic calls through `&Tr` require `unsafe` too.
- **`extern fn` is unsafe to call**: Every C function may have preconditions the compiler cannot see (`free` of a valid pointer, `pthread_join` of a live thread), so calling an `extern fn` requires `unsafe`. A declaration may opt out with **`safe extern fn`** (`safe extern fn abs(x: i32) -> i32;`), asserting the function is sound for every argument. Safety belongs to each declaration: std declares `safe extern fn malloc` and `safe extern fn usleep`, while a user module that declares `extern fn malloc` itself must still call it in `unsafe`.
- **Within std**, public functions that trust a raw pointer their caller passes are `unsafe fn`: `String::from_raw` (takes ownership of a `malloc` buffer), `Formatter::new` (writes into a buffer of the given capacity), and the `select_*` hooks of `Channel` and `Timer` that `@select` calls with pointers to its own slots. Internal helpers of the same kind (`ScopedHandle::create`, `Channel::try_push_locked`) are `pub(mod)` or private.

### Raw Pointer Address-Of (`&raw const`, `&raw mut`), Arithmetic Units (`p + i`), and `static` / `static mut` Soundness Rules `[Status: Implemented]`
1. **Direct Raw Pointer Creation (`&raw const place -> *const T`, `&raw mut place -> *mut T`)**:
   - Taking a raw pointer with `&raw const <place>` or `&raw mut <place>` produces `*const T` or `*mut T` directly without creating an intermediate safe reference (`&T` / `&mut T`), and is safe outside `unsafe { ... }` blocks (unless evaluating an index expression inside `<place>` itself performs an unsafe operation).
   - **Dereferencing a raw pointer (`*ptr`, `ptr.field`, `ptr[i]`) requires an `unsafe { ... }` block** (`self.unsafe_depth > 0` in [`src/lower/`](src/lower/mod.rs)).
2. **Top-Level and `opaque`-Scoped `const` / `comptime`, `static`, and `static mut` Declarations**:
   - Module scope and `opaque { ... }` blocks support compile-time constants (`[vis] const NAME[: T] = expr;` / `[vis] comptime NAME[: T] = expr;`) and global variables (`[vis] static [mut] NAME: T = expr;`), accessed as `NAME` or `Type::NAME` / `Self::NAME` (respecting `opaque` block privacy when private). Transparent `struct { ... }` blocks forbid associated `static` / `const` items.
   - **Immutable `static NAME: T = expr;` (`T: sync` Required)**:
     - Because an immutable `static` can be read or borrowed via `&NAME` from any thread without `unsafe`, [`Compiler::validate_static_variable_type`](src/lower/comptime.rs) enforces **`T: sync`** at compile time (and rejects `linear` or unsized `opaque`/`trait` types).
     - Reading `NAME` (when `T: copy`) or borrowing `&NAME` / `&raw const NAME` is safe outside `unsafe`. Mutating `NAME` or taking `&mut NAME` / `&raw mut NAME` is rejected at compile time.
   - **Mutable `static mut NAME: T = expr;` (`unsafe` Required, Safe References `&`/`&mut` Strictly Forbidden)**:
     - **Reading or mutating `NAME`** (`NAME`, `NAME.field`, `NAME[i]`, `NAME = ...`, `NAME += ...`) **requires an `unsafe { ... }` block** (`self.unsafe_depth > 0`).
     - **Taking a safe reference (`&NAME` or `&mut NAME`, including `&NAME.field`, `&NAME[0..1]`, or auto-borrowing `&self`/`&mut self` in a method call) to a `static mut` is strictly forbidden even inside `unsafe { ... }`** because Stage 3c [`check_borrows`](src/borrowck.rs) tracks loans on function-local `LocalId`s rather than global `GlobalId`s. Address-of on a `static mut` must use **`&raw const NAME`** (`*const T`) or **`&raw mut NAME`** (`*mut T`).
3. **Element-Scaled Pointer Arithmetic (`p + i`)**:
   - Adding an integer offset `i: usize` (or `isize`) to a typed raw pointer `p: *mut T` or `p: *const T` scales `i` by **`size_of(T)` elements** (lowering to `getelementptr T, ptr %p, i64 %i` in LLVM IR, just like C and Rust's `.add(i)`). Byte-granularity pointer offsets cast to `*mut u8` / `*const u8` first.
4. **No Auto-Drop on Raw Pointer Overwrite**: Writing `*(self.ptr + self.len) = move value` through `*mut T` stores directly into uninitialized heap memory without running a destructor on the old uninitialized bytes.
5. **Moving Out of Raw Pointers**: While `move (*_ref)` on a safe reference `&T` / `&mut T` is rejected by [`check_borrows`](src/borrowck.rs), moving out of a raw pointer `move *(self.ptr + i)` inside `unsafe` (e.g. in `Vec::pop` and `Vec::remove`) is permitted.
6. **In-Place Destructor Elaboration**: Dropping `p + i` via `@drop(p + i)` (`Terminator::Drop`) in `Vec::drop` elaborates to a destructor call if `T` has a destructor, a compile-time error if `T` is `linear`, or a zero-cost `goto` no-op if `T` is trivially droppable ([`src/drop.rs`](src/drop.rs)).

### 7.1 Heap-Allocated Vector: `Vec[T]` `[Status: Implemented]`
`Vec` is `std::collections::Vec`, re-exported by the prelude ([`src/stdlib.rs`](src/stdlib.rs)). Elements are iterated through `iter()` / `iter_mut()` (`for x in v.iter()`), which return `Iter[T]` / `IterMut[T]` views over `*ref T` / `*ref mut T` that borrow the vector, or through `as_slice()` / `as_mut_slice()`. Each item an iterator yields borrows the vector, not the iterator (`next(self: &mut Self) -> ?&T borrows(*self)`), so items may be held across further calls and may outlive the iterator, while the vector stays borrowed for as long as any item lives. An empty vector has no allocation: `ptr` is `null`, and its slices use a dangling, aligned pointer that a zero length never dereferences.
```rust
pub fn Vec[T] -> type {
    return opaque {
        ptr: ?*own T,
        len: usize,
        cap: usize,

        pub fn new() -> Self {
            return Self { ptr: null, len: 0, cap: 0 };
        }

        pub fn with_capacity(cap: usize) -> Self {
            if cap == 0 {
                return Self::new();
            }
            let p: *own T = unsafe { @alloc(T, cap) as *own T };
            return Self { ptr: p, len: 0, cap: cap };
        }

        pub fn len(self: &Self) -> usize {
            return self.len;
        }

        pub fn capacity(self: &Self) -> usize {
            return self.cap;
        }

        pub fn is_empty(self: &Self) -> bool {
            return self.len == 0;
        }

        fn grow(self: &mut Self) -> *own T {
            let mut new_cap: usize = 4;
            if self.cap > 0 {
                new_cap = self.cap * 2;
            }
            self.cap = new_cap;
            if let old_ptr = self.ptr {
                let p: *own T = unsafe { @realloc(T, old_ptr, new_cap) as *own T };
                self.ptr = p;
                return p;
            }
            let p: *own T = unsafe { @alloc(T, new_cap) as *own T };
            self.ptr = p;
            return p;
        }

        pub fn push(self: &mut Self, value: T) borrows(self: value) {
            let p: *own T = if self.len == self.cap {
                self.grow()
            } else {
                self.ptr orelse unreachable
            };
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

        pub fn get(self: &Self, index: usize) -> ?&T {
            if index >= self.len {
                return null;
            }
            let p = self.ptr orelse unreachable;
            unsafe {
                return &*(p + index);
            }
        }

        pub fn get_mut(self: &mut Self, index: usize) -> ?&mut T {
            if index >= self.len {
                return null;
            }
            let p = self.ptr orelse unreachable;
            unsafe {
                return &mut *(p + index);
            }
        }

        /// The elements as a slice (`for x in v.as_slice()`).
        pub fn as_slice(self: &Self) -> &[T] {
            // An empty vector has no allocation: its slice uses a dangling, aligned pointer that
            // a zero length never dereferences.
            let p: *mut T = self.data_ptr();
            unsafe {
                return &(*(p as *const [T; 0]))[0..self.len];
            }
        }

        pub fn as_mut_slice(self: &mut Self) -> &mut [T] {
            let p: *mut T = self.data_ptr();
            unsafe {
                return &mut (*(p as *mut [T; 0]))[0..self.len];
            }
        }

        /// The elements' address: the allocation, or for an empty vector (which has none) a
        /// dangling, aligned pointer that a zero length never dereferences.
        fn data_ptr(self: &Self) -> *mut T {
            if let p = self.ptr {
                return p;
            }
            return (@align_of(T) as usize) as *mut T;
        }

        /// Iterates over the elements by reference (`for x in v.iter()`).
        pub fn iter(self: &Self) -> Iter[T] {
            unsafe {
                return Iter[T]::from_raw(self.data_ptr() as *ref T, self.len);
            }
        }

        /// Drops the elements past `new_len`.
        pub fn truncate(self: &mut Self, new_len: usize) where T: !linear {
            if new_len >= self.len {
                return;
            }
            let p = self.ptr orelse unreachable;
            let mut i: usize = new_len;
            while i < self.len {
                unsafe {
                    @drop(p + i);
                }
                i += 1;
            }
            self.len = new_len;
        }

        pub fn clear(self: &mut Self) where T: !linear {
            self.truncate(0);
        }

        /// Consumes the vector, passing each element to `f` in order.
        pub fn drain[F: callable](move mut self, f: F) {
            let p = self.ptr orelse return;
            let n = self.len;
            self.len = 0;
            let mut i: usize = 0;
            while i < n {
                unsafe {
                    f(move *(p + i));
                }
                i += 1;
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
                let new_ptr: *own T = unsafe { @alloc(T, self.len) as *own T };
                let mut i: usize = 0;
                while i < self.len {
                    unsafe {
                        *(new_ptr + i) = @clone(&*(src_ptr + i));
                    }
                    i += 1;
                }
                return Self { ptr: new_ptr, len: self.len, cap: self.len };
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

        impl drop where T: linear {
            fn drop(self: &mut Self) {
                if let p = self.ptr {
                    unsafe {
                        @dealloc(p);
                    }
                }
            }
        }
    };
}
```

### 7.2 Stack-Allocated Fixed-Capacity Vector: `StackVec[T, cap: usize]`
Using `[uninit T; cap]` (`overlay { void, T }` in Stage 3), `StackVec` holds inline stack storage without requiring `T: default` or auto-dropping uninitialized slots:

```rust
pub error CapacityError {
    Full,
}

fn StackVec[T, cap: usize] -> type {
    return opaque {
        data: [uninit T; cap],
        len: usize,

        pub fn new() -> Self {
            return Self {
                data: uninit, // Zero-cost: leaves stack buffer untouched
                len: 0,
            };
        }

        pub fn try_push(self: &mut Self, value: T) -> CapacityError!void borrows(self: value) where T: !linear {
            if self.len == cap {
                return CapacityError::Full; // `value` is automatically dropped on error return
            }
            self.data[self.len] = uninit(move value);
            self.len += 1;
        }

        pub fn push(self: &mut Self, value: T) borrows(self: value) {
            if self.len == cap {
                unreachable;
            }
            self.data[self.len] = uninit(move value);
            self.len += 1;
        }

        pub fn pop(self: &mut Self) -> ?T {
            if self.len == 0 {
                return null;
            }
            self.len -= 1;
            unsafe {
                return move self.data[self.len].assume_init;
            }
        }

        pub fn get(self: &Self, index: usize) -> ?&T {
            if index >= self.len {
                return null;
            }
            unsafe {
                return &self.data[index].assume_init;
            }
        }

        pub fn get_mut(self: &mut Self, index: usize) -> ?&mut T {
            if index >= self.len {
                return null;
            }
            unsafe {
                return &mut self.data[index].assume_init;
            }
        }

        pub fn drain[F: callable](move mut self, f: F) {
            let n = self.len;
            self.len = 0;
            let mut i: usize = 0;
            while i < n {
                unsafe {
                    f(move self.data[i].assume_init);
                }
                i += 1;
            }
        }

        impl default {
            fn default() -> Self {
                return Self::new();
            }
        }

        impl clone where T: clone {
            fn clone(self: &Self) -> Self {
                let mut out = Self::new();
                let mut i: usize = 0;
                while i < self.len {
                    unsafe {
                        let elem_ref: &T = &self.data[i].assume_init;
                        out.data[i] = uninit(@clone(elem_ref));
                    }
                    out.len += 1;
                    i += 1;
                }
                return out;
            }
        }

        impl drop where T: !linear {
            fn drop(self: &mut Self) {
                let mut i: usize = 0;
                while i < self.len {
                    unsafe {
                        @drop(&mut self.data[i].assume_init);
                    }
                    i += 1;
                }
            }
        }

        impl drop where T: linear { fn drop(self: &mut Self) {} }
    };
}
```

---

### 7.3 Hash Map: `HashMap[K: copy, V]` `[Status: Implemented]`
`std::collections::HashMap` (in the prelude) maps `copy` keys to values with open addressing (linear probing, removed-slot markers, growth at 3/4 occupancy). Keys are hashed by the overloaded `hash_key`: integers with Fibonacci hashing, and byte sequences such as `&str` with FNV-1a (the `integer` overload is more specific, so it wins for integer keys); keys compare with `==`. Like `Vec`, it owns its keys and values (behind `?*own K` and `?*own V`): with a linear `V` the map is linear and is consumed with `drain`. A map keyed by `&str` borrows its keys (`insert` is `borrows(self: key, self: value)`).
- `new`, `len`, `is_empty`, `insert(key, value) -> ?V` (the replaced value), `get(key) -> ?&V`, `get_mut(key) -> ?&mut V`, `contains_key(key)`, `remove(key) -> ?V`, `keys() -> Vec[K]`, and `drain(f)` (consuming; `f[key](value)` for each entry).

### 7.4 Strings & I/O `[Status: Implemented]`
- **`String`** (`std::fmt`, in the prelude) is a growable UTF-8 buffer: `new`, `with_capacity`, `from(&str)`, `push_str`, `push_byte`, `push(rune)` (UTF-8 encoded), `reserve`, `clear`, `len`, `capacity`, `is_empty`, `as_str() -> &str`, `clone`, and `format`. `format[T](value)` renders any `format` value into a new `String`.
- **I/O** (`std::io`, in the prelude): `print` / `println` and `eprint` / `eprintln` (standard error) format a value; `read_line() -> ?String` reads one line of standard input without its newline (`null` at end of input); `read_file(path) -> ?String` and `write_file(path, contents) -> bool` read and replace whole files.

## 8. Stage 3 IR (`SLIR`) Quick Reference `[Status: Implemented]`

| Construct | Syntax Example | Implementation |
| :--- | :--- | :--- |
| **Primitives & Patterns** | `void`, `never`, `bool`, `rune`, `i1`..`i512`, `u1`..`u512`, `f32`, `f64`, `type`, `ty0 in 0..=100 \| 200..=255` | [`Type`](src/ir.rs) |
| **References / Pointers** | `&ty0`, `&mut ty0`, `fn(ty0) -> ty1` | [`Type::Ptr`](src/ir.rs), [`Type::FnPtr`](src/ir.rs) |
| **Composites & SIMD** | `[ty0; 4]`, `simd[ty0; 4]`, `{ ty0, ty1 }`, `overlay { ty0, ty1 }`, `union ty0 { ty1, ty2 }` | [`Type::Array`](src/ir.rs), [`Type::Simd`](src/ir.rs), [`Type::Struct`](src/ir.rs), [`Type::Overlay`](src/ir.rs), [`Type::Union`](src/ir.rs) |
| **Constants & Operands** | `const void`, `const true`, `const 42`, `const 'a'`, `const 3.14f64`, `const ty0`, `const fn1`, `const gl0`, `copy _1`, `move _1` | [`ConstValue`](src/ir.rs), [`Operand`](src/ir.rs) |
| **Destructor & Linear Registration** | `drop ty2 = fn1;` | [`Program::destructors`](src/ir.rs), [`Program::linear_types`](src/ir.rs) |
| **Globals & Externs** | `global [mut] gl0: ty0 = const 0;`<br/>`extern fn0(ty1) -> ty0 = "puts";` | [`Global`](src/ir.rs), [`ExternFunc`](src/ir.rs) |
| **Functions** | `fn0(2) borrows(_1) = "sym" { ... }` | [`Function`](src/ir.rs) |
| **Projections** | `(*_1)`, `_1.0`, `_1.v0`, `_1[_2]` | [`Projection`](src/ir.rs) |
| **Statements** | `StorageLive(_1);`<br/>`StorageDead(_1);`<br/>`_1 = <rvalue>;`<br/>`discriminant(_1) = 1;`<br/>`// line 12` (source position, no effect) | [`Statement`](src/ir.rs) |
| **Rvalues** | `copy _1` / `move _1` / `const 0` (`Use`)<br/>`&_1` / `&mut _1` (`Ref`)<br/>`discriminant(_1)` (`Discriminant`)<br/>`cast copy _1 as ty2` (`Cast`)<br/>`aggregate ty0(copy _1, move _2)` (`Aggregate`)<br/>`union ty0 variant 1(move _2)` (`Union`)<br/>`[copy _1; copy _2]` (`ArrayType`)<br/>`simd[copy _1; copy _2]` (`SimdType`)<br/>`overlay(copy _1, copy _2)` (`OverlayType`)<br/>`union(copy _tag, copy _1, copy _2)` (`UnionType`)<br/>`copy _1 in copy _lo..=copy _hi` (`PatternType`) | [`Rvalue`](src/ir.rs) |
| **Unary Ops** | `neg`, `not` | [`UnOp`](src/ir.rs) |
| **Arithmetic & Overflow Ops** | `add`, `sub`, `mul` (checked trap)<br/>`add_wrap`, `sub_wrap`, `mul_wrap` (`+%`, `-%`, `*%`)<br/>`add_sat`, `sub_sat`, `mul_sat` (`+\|`, `-\|`, `*\|`)<br/>`add_unchecked`, `sub_unchecked`, `mul_unchecked` (`nsw`/`nuw`)<br/>`div`, `rem` (trap on `/ 0` and `MIN / -1`) | [`BinOp`](src/ir.rs) |
| **Bitwise & Comparison Ops** | `bitand`, `bitor`, `bitxor`, `shl`, `shr`<br/>`eq`, `ne`, `lt`, `le`, `gt`, `ge` | [`BinOp`](src/ir.rs) |
| **Terminators** | `goto -> bb1;`<br/>`switchInt(copy _1) -> [0: bb1, otherwise: bb2];`<br/>`_0 = call const fn1(move _1) -> bb1;`<br/>`drop(_1) -> bb1;`<br/>`return;` / `unreachable;` | [`Terminator`](src/ir.rs) |

## 9. Soundness Testing `[Status: Implemented]`

The borrow, move, and drop checkers promise that safe code has no undefined behaviour. Two pieces test that promise directly: the compile-time VM ([`src/vm.rs`](src/vm.rs)) run as a checking interpreter, and a program generator ([`src/tests/fuzz.rs`](src/tests/fuzz.rs)) that asks it about programs the compiler accepted.

### 9.1 What the VM Reports
Errors for undefined behaviour start with [`vm::UB_PREFIX`](src/vm.rs), as opposed to operations the VM does not support.

| Check | Reports | How |
| :--- | :--- | :--- |
| **Storage** | Access to a local that went out of scope, or of a returned function | Each local has an epoch, renewed at `StorageLive` / `StorageDead`, recorded in the pointers to it |
| **Heap** | Use after free, double and interior frees, out-of-bounds access, and leaks at exit | `malloc` blocks are emulated as typed slots |
| **Uninitialized reads** | A read of memory never written or moved out of | Slots keep an `Uninit` value |
| **Data races** | Two accesses to one location by different threads, at least one a write, not ordered by happens-before | Vector clocks, ordered by thread creation, `pthread_join`, a mutex unlock followed by a lock, and atomic operations on the same location. A plain access unordered with an atomic one on the same location also races. |
| **Aliasing** (whole-program runs) | Use of a reference after a conflicting access | Each `&T` and `&mut T` records the place it borrows and the reference it was reborrowed from. An access ends every overlapping reference it was not derived from: a write ends all of them, a read only the `&mut` ones. |
| **Deadlock** | Every thread blocked on a lock, a join, or a condition | One stack per emulated thread; see below |

- **Threads**: the VM emulates pthreads, one thread running at a time. Locks, joins, and condition waits block. Threads switch only at synchronization points, which is enough for race-free programs, and the race check covers what happens between them. Without a seed a created thread runs first and threads switch only when they must. A seed picks the next thread at each synchronization point and replays that interleaving exactly, so running a program under several seeds reaches races and deadlocks that depend on lock order.
- **Addresses**: a pointer cast to an integer gets its allocation's base plus its real byte offset, from the type layout, so differences between addresses within an allocation are real, as `&rel` fields need. Adding to a pointer, or casting back, walks the layout to the field or element of the type asked for.
- **Raw pointers are not tracked for aliasing**. A write through a `&T` is interior mutation, and a write through a reference derived from a raw pointer does not end shared references, so `Mutex`, `cell` fields, and containers need no annotations.

### 9.2 What the Fuzzer Checks
Every generated program the compiler accepts must run under the VM without undefined behaviour or leaks, consume each linear `Tx` exactly once (`main` returns -1 otherwise), and compute what the native build computes under `lli`. Threaded programs run under the default order and several seeded schedules. A failure prints its seed and a program shrunk by deleting statements.

The generator covers scopes, references and containers of them, linear values in every shape, conditional moves of droppable values, pattern matching, `drop` hooks that read their borrows, iterators, closures, threads, mutexes, blocking channels, deferred initialization, field paths, `@leaves`, tuple concat and split, `borrows(...)` contracts, an owning `may_dangle` container, a `*ref` view, trait objects over values holding references, closures with captured borrows, slices, and `&rel` fields moved by value, through a function, and through a `Box`. It also writes unsound code on purpose: dropped linear values, partly filled tuples, use after move, and functions whose body breaks their contract. Those must be rejected, and if one is accepted the VM should report what it does.

```sh
cargo test --lib fuzz_borrow -- --nocapture                # 50 cases
SLOPLANG_FUZZ_CASES=2500 SLOPLANG_FUZZ_SEED=1 SLOPLANG_FUZZ_WORKERS=6 \
    cargo test --lib fuzz_borrow -- --nocapture            # a campaign
SLOPLANG_FUZZ_SEED=<seed> SLOPLANG_FUZZ_CASES=1 \
    cargo test --lib fuzz_borrow -- --nocapture            # reproduce a failure
cargo test --lib fuzz_check_coverage -- --ignored --nocapture   # which checks and constructs are reached
```

### 9.3 Testing std's Containers
The checkers cannot vouch for unsafe code, and std holds most of it. [`src/tests/model.rs`](src/tests/model.rs) generates random operation sequences on `Vec`, `HashMap`, `String`, and `Channel`, with plain and owning (`Box[i32]`) elements, runs them against a Rust model, and asserts every result in the generated program. It must return 0 on the VM, with nothing leaked, and natively. Owning elements make lost and doubled drops visible; few keys force `HashMap` collisions and slot reuse; bounded capacities force channel wrap-around. `SLOPLANG_MODEL_CASES` and `SLOPLANG_MODEL_SEED` control the run.

### 9.4 Testing the Tests
A clean campaign says nothing if the generator cannot reach a bug. A construct or check is covered only once a **mutation test** shows it: disable the check in the compiler, run a campaign, and confirm that programs which should have been rejected fail under the VM. Acceptance that does not change means the generator never depended on the check. Acceptance that rises with no failures means it reaches the check, but never uses what the check protects, usually because the dangling value is not read afterwards. The coverage report is the first thing to look at in either case.

### 9.5 Known Limits
- Borrow and move errors carry a source line, from `Statement::Line` markers the lowerer emits before each statement (a no-op for the VM and backend), not a column or a span. A statement over several lines reports its first, an error at a scope's end reports the block's closing brace, and an error about a whole function, such as a broken contract, reports where its body starts. Errors in generic code report the line in the generic's own source, with the instantiation named in the message.
- Aliasing inside unsafe code that stays behind raw pointers is not reported, and pointers made by arithmetic or inside the VM are untracked, so slices are checked less precisely than single values.
- Schedules are a sample of the possible interleavings, not an exhaustive search.
- A race-free program behaves the same under every schedule the VM can produce, but a racy program does not run every interleaving; it relies on the race being reported.
- Checker bugs usually appear under the default order too, because the race check does not depend on which order threads ran in. Replaying schedules pays off for logic that depends on lock order.
- Threads still running when `main` returns stop there, as in a process, and anything they own counts as a leak. The fuzzer joins every thread.
- The generator writes only sound unsafe code, since a wrong `may_dangle` or a missing `borrows T` is the author's error rather than the checker's.
- Borrow checking is still worse than linear in the size of a function, which limits generated programs to a few hundred statements, and so how far a container grows in one program.

## 10. Contexts and Colour-Free Concurrency `[Status: Planned]`

The goal is one kind of function. A library written once runs under threads or an async scheduler, with any allocator, without `async` markers on its signatures. Nothing here is implemented, and the syntax is a sketch. The multi-way waiting described in section 5.4 (`Waiter`, `WaitNode`) is the existing starting point for `@select`.

### 10.1 A Context Is Policy Plus State
| Layer | Contains | Decided | Mechanism |
| :--- | :--- | :--- | :--- |
| **Policy** | The allocator (`Allocator`), the execution model (`Async`), and whether cancellation exists at all | Compile time | A hidden `comptime` parameter, monomorphized like any other |
| **State** | The current cancel scope, the instance of a stateful allocator | Run time | Held by the running task: a task field, or a `thread_local static mut` under threads |

`thread_local static mut N: i32 = 5;` `[Status: Implemented]` declares a static of which each thread has its own copy, starting at its initial value, so a shared `static mut` that would race can be per thread instead. Access needs `unsafe`, as for any mutable static, and a pointer to one keeps naming the copy of the thread that took it.

Policy selects an instantiation, so a function compiled for two contexts exists twice, and code under the default context compiles as it does today. State is read only where it is needed, such as at a cancellable wait, rather than passed on every call. It therefore also reaches code behind function pointers, trait objects, and C callbacks, which policy cannot.

### 10.2 Allocator Policy `[Status: Partial]`
The allocator policy changes `@alloc`, `@realloc`, and `@dealloc`, so custom allocators work with any function. `with context(alloc=A) { ... }` lowers the block, and whatever it instantiates, in a context whose allocator is `A`, and yields its last expression:

```rust,ignore
pub struct Counted { x: i32 }
impl Allocator for Counted {
    fn alloc(bytes: usize, align: usize) -> *mut u8 { ... }
    fn realloc(ptr: *mut u8, bytes: usize, align: usize) -> *mut u8 { ... }
    fn dealloc(ptr: *mut u8) { ... }
}
let v = with context(alloc=Counted) {
    Vec[i32]::new()
};
v.push(10);   // grown and freed through `Counted`, wherever this runs
```

The context is part of what identifies an instance of a function or type, so `Vec[i32]` from this context is a different type from the default one (an error names it as `Vec (allocator Counted)`) and its methods and `drop` hook use its allocator wherever they are called. `@raw_alloc(bytes)` is the fallible form behind `try_alloc`, yielding null.

Implemented so far: stateless allocators, through the `Allocator` trait (`std::mem`, in the prelude), whose methods take no receiver. Planned: stateful allocators.

**Stateful allocators** `[Status: Partial]` have runtime instances: `with context(alloc=pool) { ... }` for a local `pool` implementing `StatefulAllocator`. A value must carry its instance, because `Vec::new()` does not allocate, and its first `push` may run long after the context ended.

- **Which types carry it.** A type gets a hidden allocator field only if it owns heap memory directly: an `opaque` with an `*own` or raw pointer field, or whose own block uses the allocation intrinsics or constructs context-dependent values. A `struct { v: Vec[i32] }` needs nothing, since `v` carries it. The decision comes from the type's definition alone, because layout is needed before method bodies are lowered.
- **Impls never change layout.** If an outside `impl` could add the field, importing a package would change `@size_of` and the ABI.
- **A foreign impl method is like a free function.** It uses the current context, not the value's allocator. This is safe because only an `opaque` owns memory and outside code cannot reach its private fields, so it cannot free or grow the type's blocks with the wrong allocator.
- **How it works.** The hidden field defaults to the task's current instance (`CONTEXT_INSTANCE`, a `thread_local`), so `Self { ... }` in a container needs no change. A method of such a type sets the task's instance from its field on entry and restores it on exit, so its helpers find it too, and allocation always reads the task's instance.
- **Lifetimes.** Such a type carries a loan on its instance, taken when the block yields it, so the borrow checker rejects a value outliving its arena, and `may_dangle` does not excuse its drop, which uses the allocator.
- **Mistakes are not silent.** An allocation with no instance traps rather than using the wrong allocator, such as a closure from the block called after it.
- **Leaving a block.** `return`, `break`, and `continue` all restore the instance of the enclosing context.
- **Limits.** A spawned thread does not inherit the instance. Each value from a stateful block holds a loan, so a function with thousands of them compiles several times slower than without. A type whose own methods construct context-dependent values without holding a pointer is not yet detected, and traps on allocating. A non-generic type such as `String` has one instance, so it stays on the default allocator, as do the direct `malloc` / `free` pairs inside std, such as the closure box of `spawn`.

- **A value keeps its allocator.** The context chooses the allocator when a value is created; from then on the value carries it. If `@dealloc` used the current context, memory allocated under `A` and dropped under `B` would be freed by the wrong allocator.
- A stateless allocator is a zero-sized part of the type. A stateful one is a handle stored in the value, whose lifetime `borrows` ties to the allocator.

### 10.3 Execution Policy
The execution policy changes `@select` and synchronization primitives such as `Mutex`. Under an async policy they become suspension points, and a function that can reach one is lowered to a state machine in that instantiation. Under threads they block, as they do now.

- **Frames**: locals live across a suspension point become fields of the task's frame. Recursion through a suspension point has no static frame size, so it needs the allocator policy.
- **Moving tasks**: if a scheduler can move tasks between threads, what lives across a suspension point must be `send`. A lock guard held across one is a likely deadlock.
- **References into a frame** break if it moves, so frames are either pinned or use offsets, as `&rel` fields do.
- **Erased calls** cannot be instantiated per context: either the context is part of `fn` types there, or an async erased call returns a boxed future through the allocator policy. `export fn` stays synchronous.
- **The clock** belongs to the `Async` trait (`now()`, `sleep_until()`), so the compile-time VM can run a virtual clock and fire timeouts deterministically under a seeded schedule.

### 10.4 Cancellation `[Status: Partial]`
Implemented so far: `CancelScope` with `new`, `cancel`, `is_cancelled`, and `run`, explicit cancellation from any thread, nesting, `check_cancelled()` returning `CancelError!void`, and `spawn_scoped` inheriting the scope while a detached `spawn` starts a new root. `Channel::recv` returns `CancelError!T`, and `Channel::send` returns `?T`, which is the value back if the task was cancelled before it went, since an error cannot carry a linear value. Inside a scope a blocked wait rechecks cancellation every millisecond; outside one it is a plain condition wait. Planned: deadlines, the other cancellable waits (`sleep`, `join`, `@select`, I/O), shielding, and waking waiters directly instead of rechecking.

A frame is never dropped to cancel a task, because that would discard linear values. Cancellation is a **structured scope**, held as context state, with a handle to trigger it and an optional deadline.

```rust,ignore
let scope = CancelScope::with_timeout(ms(500));
let r = scope.run(fn() -> CancelError!i32 { return ch.recv(); });
// With a reference to the scope, from elsewhere: scope.cancel();
```

- **Scopes form a tree.** Cancelling a scope cancels its children, and the effective deadline is the earliest on the path. Deadlines are absolute and monotonic, so nesting only takes the earlier one.
- **Delivery is an error.** A cancellable wait returns `Cancelled!T`, reporting `.Cancelled` or `.TimedOut`, and the normal error path consumes what is live. Long computation can poll `scope.check()`.
- **Only waits that can last indefinitely are cancellable**: `recv`, `send`, `sleep`, `join`, `@select`, and I/O. Taking a `Mutex` may suspend but never reports cancellation, so cancellation appears only where the error type shows it, and functions stay colour-free.
- **Shielding**: `uncancelled { ... }` lets cleanup that must wait, such as committing a linear transaction, run to completion inside a cancelled scope.
- **Spawning**: `spawn_scoped` inherits the scope. A detached `spawn` starts a new root, since a borrowed parent scope may not outlive it.
- **Completion wins a race**: if an operation finished as cancellation arrived, it reports its result, or a value would be lost.
- **Waking**: a blocked wait registers with its scope, and `cancel()` is safe from any thread.
- **Cost**: under an execution policy without cancellation, all of this compiles away.
- A closure runs under the scope of its caller, not its creator, and a thread blocked in `extern` code cannot be cancelled.

**`@select`** has two cases. Over operations such as channels and timers, a loser is only an unregistered wait node, as `Waiter` works now. Over child tasks, a loser's scope is cancelled and `select` waits for it to finish, returning its result as a linear handle if it also completed.

**Decisions**:
1. `Mutex` is not cancellable.
2. `@select` waits for losing tasks, which keeps it structured, at the cost that a slow loser delays the winner.
3. A timeout is a distinct error from an explicit cancel.

### 10.5 Order of Work
1. **The context mechanism and allocator policy.** It is useful alone, needs no state machines, and proves the hidden parameter.
2. **Execution policy over threads**, with the `Async` trait and cancellation. The VM's seeded scheduler can implement it, so interleavings and races are checked from the start.
3. **State-machine lowering**, once the rules above have been tried.

Static task trees (nested tuples of inline task state, reached by field paths and `@leaves`) are then what `join` and `select` compile to. Each stage is tested by the existing fuzzer, aliasing checks, and race detector.

