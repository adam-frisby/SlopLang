use std::fmt;

use crate::wide::Wide;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LocalId(pub u32);

impl LocalId {
    const CONTENTS: u32 = 1 << 31;

    /// In a borrow contract or origin set: the borrows *held by* what parameter `self` refers to
    /// (`borrows(*p)`), rather than a borrow of the parameter itself. Printed `*_1`.
    pub fn contents(self) -> Self {
        LocalId(self.0 | Self::CONTENTS)
    }

    pub fn is_contents(self) -> bool {
        self.0 & Self::CONTENTS != 0
    }

    /// The parameter a contents marker refers to (or `self` unchanged).
    pub fn base(self) -> Self {
        LocalId(self.0 & !Self::CONTENTS)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BlockId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncId(pub u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct GlobalId(pub u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Type {
    Void,
    Never,
    Bool,
    Rune,
    Int {
        signed: bool,
        bits: u16,
    },
    F32,
    F64,
    MetaType,
    Pattern {
        base: TypeId,
        /// Inclusive bounds, as mathematical values of the base type (so `u128` and wider
        /// types can name their full range).
        ranges: Vec<(Wide, Wide)>,
    },
    Ptr {
        mutable: bool,
        pointee: TypeId,
    },
    Array {
        elem: TypeId,
        len: u64,
    },
    Simd {
        elem: TypeId,
        len: u64,
    },
    Struct(Vec<TypeId>),
    Overlay(Vec<TypeId>),
    Union {
        tag: TypeId,
        variants: Vec<TypeId>,
    },
    FnPtr {
        args: Vec<TypeId>,
        ret: TypeId,
    },
}

impl Type {
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Type::Rune | Type::Int { signed: false, .. })
    }

    pub fn is_float(&self) -> bool {
        matches!(self, Type::F32 | Type::F64)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Projection {
    Deref,
    Field(u32),
    Variant(u32),
    Index(LocalId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Place {
    pub local: LocalId,
    pub projections: Vec<Projection>,
}

impl Place {
    pub fn new(local: LocalId) -> Self {
        Self {
            local,
            projections: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstValue {
    Void,
    Bool(bool),
    I64(i128),
    /// An integer constant that does not fit in `i128` (only used for such values, so equal
    /// integers always share one representation).
    Wide(Box<crate::wide::Wide>),
    F64(u64), // IEEE 754 bits for Eq/Hash
    Type(TypeId),
    Func(FuncId),
    Global(GlobalId),
    Str(String),
    Aggregate(Vec<ConstValue>),
    /// All bytes zero, of the type it is assigned to (`zeroinitializer`): a large zero value,
    /// such as `@default([u8; 4096])`, in one store.
    Zeroed,
}

impl ConstValue {
    pub fn f64_from_val(v: f64) -> Self {
        Self::F64(v.to_bits())
    }

    pub fn as_f64(&self) -> Option<f64> {
        if let Self::F64(bits) = self {
            Some(f64::from_bits(*bits))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Const(ConstValue),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
    Bswap,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    AddWrap,
    SubWrap,
    MulWrap,
    AddSat,
    SubSat,
    MulSat,
    AddChecked,
    SubChecked,
    MulChecked,
    AddUnchecked,
    SubUnchecked,
    MulUnchecked,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rvalue {
    Use(Operand),
    UnaryOp(UnOp, Operand),
    BinaryOp(BinOp, Operand, Operand),
    Cast(Operand, TypeId),
    Transmute(Operand, TypeId),
    Ref {
        mutable: bool,
        place: Place,
    },
    Aggregate(TypeId, Vec<Operand>),
    Union {
        ty: TypeId,
        variant: u32,
        payload: Operand,
    },
    Discriminant(Place),
    /// Comptime array type constructor: `[<elem>; <len>]`
    ArrayType {
        elem: Operand,
        len: Operand,
    },
    /// Comptime SIMD vector type constructor: `simd[<elem>; <len>]`
    SimdType {
        elem: Operand,
        len: Operand,
    },
    /// Comptime untagged overlay type constructor: `overlay(<op0>, <op1>, ...)`
    OverlayType(Vec<Operand>),
    /// Comptime tagged union type constructor: `union(<tag>, <v0>, <v1>, ...)`
    UnionType {
        tag: Operand,
        variants: Vec<Operand>,
    },
    /// Comptime scalar pattern type constructor: `<base> in <lo>..=<hi> | ...`
    PatternType {
        base: Operand,
        ranges: Vec<(Operand, Operand)>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    Assign(Place, Rvalue),
    SetDiscriminant(Place, u32),
    StorageLive(LocalId),
    StorageDead(LocalId),
    /// The statements that follow come from this source position. Has no effect.
    Line(Pos),
}

/// Where a statement starts in its source file.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Pos {
    pub line: u32,
    pub col: u32,
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}, column {}", self.line, self.col)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Terminator {
    Goto {
        target: BlockId,
    },
    SwitchInt {
        discr: Operand,
        targets: Vec<(i128, BlockId)>,
        otherwise: BlockId,
    },
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: BlockId,
    },
    Drop {
        place: Place,
        target: BlockId,
    },
    Return,
    Unreachable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    pub statements: Vec<Statement>,
    pub terminator: Terminator,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternFunc {
    pub id: FuncId,
    pub args: Vec<TypeId>,
    pub ret: TypeId,
    pub symbol: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Function {
    pub id: FuncId,
    pub export: Option<String>,
    pub arg_count: usize,
    /// Optional explicit borrow contract for the return value `_0`:
    /// - `None`: infer which parameter locals (`_1..=arg_count`) `_0` borrows from.
    /// - `Some(params)`: enforce that `_0` only borrows from the listed parameter locals.
    pub ret_borrows: Option<Vec<LocalId>>,
    /// Optional explicit parameter-to-parameter borrow contract `(dst_param, src_param)`.
    pub param_borrows: Option<Vec<(LocalId, LocalId)>>,
    /// When `Some(linear_ty)`, this function is an associated consuming `move self` method of
    /// `linear_ty`, so `LocalId(1)` (`self`) is permitted to be retired at scope exit (and
    /// invokes `linear_ty`'s shared `drop(self: &mut Self)` cleanup hook if defined).
    pub linear_self: Option<TypeId>,
    /// Whether this function is a method (or a closure inside one) of a type whose instantiation
    /// is linear. Only such a function may store a linear value in raw or `uninit` storage
    /// without first moving one out of the same slot; see `drop::check_linear_raw_stores`.
    pub linear_owner: bool,
    /// Human-readable source name (`Vec::push`, `root::main`) used in diagnostics; `None` for
    /// functions parsed directly from Stage 3 text.
    pub debug_name: Option<String>,
    /// Source names of the runtime parameters `_1..=arg_count` (empty when unknown), for diagnostics.
    pub param_names: Vec<String>,
    /// Source names of named locals (variables and parameters), for diagnostics.
    pub local_names: Vec<(LocalId, String)>,
    pub locals: Vec<TypeId>, // Indexed by LocalId: _0 is return, _1..=arg_count are args
    pub blocks: Vec<BasicBlock>, // Indexed by BlockId: bb0, bb1, ...
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Global {
    pub id: GlobalId,
    pub mutable: bool,
    pub ty: TypeId,
    pub init: ConstValue,
}

/// A borrow contract in terms of 1-based parameter locals: which parameters the return value may
/// borrow from (`ret`) and which `(dst, src)` parameter-to-parameter flows are permitted (`flows`).
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct FnContract {
    pub ret: Vec<LocalId>,
    pub flows: Vec<(LocalId, LocalId)>,
}

/// Symbol prefix of the builtin externs that implement `@atomic_<op>` (`slir.atomic.add.<type>`).
/// They are never declared: the LLVM backend emits the atomic instruction in place of the call,
/// and the VM evaluates it directly.
pub const ATOMIC_PREFIX: &str = "slir.atomic.";

/// Symbol prefix of the builtin externs that implement `@memcpy` / `@memmove`
/// (`slir.memcopy.copy.<type>(dest, src, count)`): the LLVM backend emits `llvm.memcpy` /
/// `llvm.memmove` of `count * size_of(type)` bytes, and the VM copies `count` typed slots.
pub const MEMCOPY_PREFIX: &str = "slir.memcopy.";

/// How an optional is stored without a tag (see [`Program::union_niche`]): as `payload`, with
/// `null` in the `scalar` at byte `offset` of it meaning there is none.
#[derive(Debug, Clone, Copy)]
pub struct Niche {
    pub payload: TypeId,
    pub null: i128,
    pub offset: u64,
    pub scalar: TypeId,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Program {
    pub types: Vec<Type>,
    pub destructors: Vec<(TypeId, FuncId)>,
    pub linear_types: Vec<(TypeId, String)>,
    /// Pointer types that are raw (`*const T` / `*mut T`) rather than safe references. Raw pointers
    /// carry no checked borrow contract, so parameter flows through them need no `borrows(...)`.
    pub raw_ptr_types: Vec<TypeId>,
    /// The `raw_ptr_types` that are owning pointers (`*own T`): a value of type `T` stored through
    /// one belongs to the containing type, so a linear one may be stored without a refill.
    pub own_ptr_types: Vec<TypeId>,
    /// The `raw_ptr_types` that are views (`*ref T` / `*ref mut T`): they carry the borrow they were
    /// made from, like `&T` / `&mut T`, although dereferencing one is unchecked.
    pub view_ptr_types: Vec<TypeId>,
    /// `opaque` types that carry borrows through declared contents (`opaque(borrows T)`, or
    /// `opaque(owns T)` with a borrowing `T`) rather than through a visible field.
    pub loan_types: Vec<TypeId>,
    /// Types with a `drop` hook whose drop leaves the borrows they hold unread (a hook declared
    /// `unsafe impl drop(may_dangle T)` over `T` values whose own drop does too), so those borrows
    /// may have ended when the value is dropped.
    pub dangle_types: Vec<TypeId>,
    /// The globals each thread has its own copy of (`thread_local static mut`).
    pub thread_local_globals: Vec<GlobalId>,
    /// Function pointer types that use the C calling convention (`extern fn(...) -> R`).
    pub c_fn_ptr_types: Vec<TypeId>,
    /// Borrow contracts carried by function-pointer types (`fn(&i32) -> &i32 borrows(_1)`). Calls
    /// through a pointer of such a type are checked against its contract, and every function value
    /// stored into it must satisfy the contract.
    pub fn_ptr_contracts: Vec<(TypeId, FnContract)>,
    /// User-declared `union` and `error` types: always laid out with an explicit tag (never
    /// niche-optimized like `?T`).
    pub tagged_unions: Vec<TypeId>,
    /// Stored tag value of each variant for unions linked to an explicit enum (`union(Opcode)`).
    /// The discriminant (`Rvalue::Discriminant`) is still the variant index; only the in-memory
    /// encoding of the tag uses these values. Unions not listed store the variant index.
    pub union_tag_values: Vec<(TypeId, Vec<i128>)>,
    /// Source names of nominal types (`Point`, `Vec[i32]`), for diagnostics.
    pub type_names: Vec<(TypeId, String)>,
    /// Field names of named and anonymous struct / `opaque` types, for diagnostics.
    pub field_names: Vec<(TypeId, Vec<String>)>,
    pub globals: Vec<Global>,
    pub externs: Vec<ExternFunc>,
    pub functions: Vec<Function>,
}

/// Whether `v` lies in one of the inclusive pattern `ranges`.
pub fn pattern_contains(ranges: &[(Wide, Wide)], v: &Wide) -> bool {
    ranges.iter().any(|(lo, hi)| lo <= v && v <= hi)
}

impl Program {
    pub fn intern_type(&mut self, ty: Type) -> TypeId {
        if let Some(idx) = self.types.iter().position(|t| *t == ty) {
            TypeId(idx as u32)
        } else {
            let id = TypeId(self.types.len() as u32);
            self.types.push(ty);
            id
        }
    }

    /// Niche layout for an optional (`union { void, T }`): when the payload `T` has a bit pattern
    /// outside its valid set, returns `(T, null_value)` and the optional is laid out exactly like
    /// `T`, with `null_value` meaning `null` and any other value meaning a present payload.
    /// The null value is chosen deterministically: `0` if it is invalid for `T` (references, raw
    /// pointers, function pointers, `NonZero`), otherwise all-ones (`-1` / `MAX`) if invalid
    /// (`?rune`, `?PosixFd`), otherwise the value just above `T`'s first valid interval.
    ///
    /// A struct has the niche of the first `*own` pointer it holds by value (`?Box[T]`): those
    /// are never null, while a raw pointer in a field may be, and `uninit` storage holds anything.
    pub fn union_niche(&self, id: TypeId) -> Option<Niche> {
        if self.tagged_unions.contains(&id) {
            return None;
        }
        let Some(Type::Union { variants, .. }) = self.types.get(id.0 as usize) else {
            return None;
        };
        let [none, payload] = variants.as_slice() else {
            return None;
        };
        if !matches!(self.types.get(none.0 as usize), Some(Type::Void)) {
            return None;
        }
        let whole = |null| Niche { payload: *payload, null, offset: 0, scalar: *payload };
        let niche = match self.types.get(payload.0 as usize)? {
            Type::Struct(_) => {
                let (offset, scalar) = self.owning_pointer_in(*payload)?;
                return Some(Niche { payload: *payload, null: 0, offset, scalar });
            }
            Type::Ptr { .. } | Type::FnPtr { .. } => 0,
            // Valid scalar values are `0..=0xD7FF | 0xE000..=0x10FFFF`; all-ones is invalid.
            Type::Rune => 0xFFFF_FFFF,
            Type::Pattern { base, ranges } => {
                let Some(&Type::Int { signed, bits }) = self.types.get(base.0 as usize) else {
                    return None;
                };
                if ranges.is_empty() {
                    return None;
                }
                let valid = |v: &Wide| pattern_contains(ranges, v);
                let all_ones = if signed {
                    Wide::from_i128(-1)
                } else {
                    Wide::max_value(bits, false)
                };
                if !valid(&Wide::ZERO) {
                    0
                } else if !valid(&all_ones) {
                    // `-1` has the same bit pattern as an unsigned all-ones too wide for `i128`.
                    all_ones.to_i128().unwrap_or(-1)
                } else {
                    let above = ranges.iter().min()?.1.add(&Wide::from_i128(1));
                    if above > Wide::max_value(bits, signed) || valid(&above) {
                        return None;
                    }
                    above.to_i128()?
                }
            }
            _ => return None,
        };
        Some(whole(niche))
    }

    /// The byte offset and type of the first `*own` pointer `ty` holds by value.
    fn owning_pointer_in(&self, ty: TypeId) -> Option<(u64, TypeId)> {
        match self.types.get(ty.0 as usize)? {
            Type::Ptr { .. } => self.own_ptr_types.contains(&ty).then_some((0, ty)),
            Type::Struct(fields) => {
                let mut offset = 0u64;
                for &field in fields {
                    let (size, align) = self.type_size_align(field).ok()?;
                    offset = offset.next_multiple_of(align);
                    if let Some((inner, pointer)) = self.owning_pointer_in(field) {
                        return Some((offset + inner, pointer));
                    }
                    offset += size;
                }
                None
            }
            _ => None,
        }
    }

    /// Diagnostic name of `ty`: its source name when known, otherwise its structure with nested
    /// types named the same way (`u8 in 0..=3`, `&mut [Point; 4]`), never `tyN`.
    pub fn type_label(&self, ty: TypeId) -> String {
        if let Some((_, n)) = self.type_names.iter().find(|(t, _)| *t == ty) {
            return n.clone();
        }
        let list = |tys: &[TypeId]| -> String {
            tys.iter().map(|t| self.type_label(*t)).collect::<Vec<_>>().join(", ")
        };
        match self.types.get(ty.0 as usize) {
            None => ty.to_string(),
            Some(Type::Pattern { base, ranges }) => {
                let ranges: Vec<String> =
                    ranges.iter().map(|(lo, hi)| format!("{lo}..={hi}")).collect();
                format!("{} in {}", self.type_label(*base), ranges.join(" | "))
            }
            Some(Type::Ptr { mutable, pointee }) => {
                let m = if *mutable { "mut " } else { "" };
                format!("&{m}{}", self.type_label(*pointee))
            }
            Some(Type::Array { elem, len }) => format!("[{}; {len}]", self.type_label(*elem)),
            Some(Type::Simd { elem, len }) => format!("simd[{}; {len}]", self.type_label(*elem)),
            Some(Type::Struct(fields)) => format!("tuple {{ {} }}", list(fields)),
            Some(Type::Overlay(fields)) => format!("overlay {{ {} }}", list(fields)),
            Some(Type::Union { variants, .. }) => format!("union {{ {} }}", list(variants)),
            Some(Type::FnPtr { args, ret }) => {
                format!("fn({}) -> {}", list(args), self.type_label(*ret))
            }
            Some(other) => other.to_string(),
        }
    }

    /// Stored tag values of a union linked to an explicit enum (`union(Opcode)`), if any.
    pub fn union_tag_values(&self, id: TypeId) -> Option<&[i128]> {
        self.union_tag_values
            .iter()
            .find(|(t, _)| *t == id)
            .map(|(_, v)| v.as_slice())
    }

    pub fn type_size_align(&self, id: TypeId) -> Result<(u64, u64), String> {
        if let Some(niche) = self.union_niche(id) {
            return self.type_size_align(niche.payload);
        }
        let ty = self
            .types
            .get(id.0 as usize)
            .ok_or_else(|| format!("Undefined {id}"))?;
        match ty {
            Type::Void | Type::Never => Ok((0, 1)),
            Type::Bool => Ok((1, 1)),
            Type::Int { bits, .. } => {
                let size = u64::from(*bits).div_ceil(8).next_power_of_two();
                let align = size.min(16);
                Ok((size, align))
            }
            Type::Rune | Type::F32 => Ok((4, 4)),
            Type::F64 | Type::Ptr { .. } | Type::FnPtr { .. } => Ok((8, 8)),
            Type::MetaType => {
                Err("Cannot compute runtime size of comptime 'type' (MetaType)".to_string())
            }
            Type::Pattern { base, .. } => self.type_size_align(*base),
            Type::Array { elem, len } => {
                let (es, ea) = self.type_size_align(*elem)?;
                Ok((es * len, ea))
            }
            Type::Simd { elem, len } => {
                let (es, ea) = self.type_size_align(*elem)?;
                let size = es * len;
                Ok((size, size.next_power_of_two().min(64).max(ea)))
            }
            Type::Struct(fields) => {
                let mut offset = 0u64;
                let mut max_align = 1u64;
                for &f in fields {
                    let (fs, fa) = self.type_size_align(f)?;
                    max_align = max_align.max(fa);
                    offset = (offset + fa - 1) & !(fa - 1);
                    offset += fs;
                }
                let size = (offset + max_align - 1) & !(max_align - 1);
                Ok((size, max_align))
            }
            Type::Overlay(variants) => {
                let mut max_size = 0u64;
                let mut max_align = 1u64;
                for &v in variants {
                    let (vs, va) = self.type_size_align(v)?;
                    max_size = max_size.max(vs);
                    max_align = max_align.max(va);
                }
                let size = (max_size + max_align - 1) & !(max_align - 1);
                Ok((size, max_align))
            }
            Type::Union { tag, variants } => {
                let (ts, ta) = self.type_size_align(*tag)?;
                let mut max_vsize = 0u64;
                let mut max_valign = 1u64;
                for &v in variants {
                    let (vs, va) = self.type_size_align(v)?;
                    max_vsize = max_vsize.max(vs);
                    max_valign = max_valign.max(va);
                }
                let union_size = (max_vsize + max_valign - 1) & !(max_valign - 1);
                let max_align = ta.max(max_valign);
                let mut offset = ts;
                offset = (offset + max_valign - 1) & !(max_valign - 1);
                offset += union_size;
                let size = (offset + max_align - 1) & !(max_align - 1);
                Ok((size, max_align))
            }
        }
    }
}

impl fmt::Display for TypeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ty{}", self.0)
    }
}

impl fmt::Display for LocalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_contents() {
            write!(f, "*_{}", self.base().0)
        } else {
            write!(f, "_{}", self.0)
        }
    }
}

impl fmt::Display for BlockId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

impl fmt::Display for FuncId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn{}", self.0)
    }
}

impl fmt::Display for GlobalId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "gl{}", self.0)
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Void => write!(f, "void"),
            Type::Never => write!(f, "never"),
            Type::Bool => write!(f, "bool"),
            Type::Rune => write!(f, "rune"),
            Type::Int { signed: true, bits } => write!(f, "i{bits}"),
            Type::Int {
                signed: false,
                bits,
            } => write!(f, "u{bits}"),
            Type::F32 => write!(f, "f32"),
            Type::F64 => write!(f, "f64"),
            Type::MetaType => write!(f, "type"),
            Type::Pattern { base, ranges } => {
                write!(f, "{base} in ")?;
                for (i, (lo, hi)) in ranges.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{lo}..={hi}")?;
                }
                Ok(())
            }
            Type::Ptr {
                mutable: false,
                pointee,
            } => write!(f, "&{pointee}"),
            Type::Ptr {
                mutable: true,
                pointee,
            } => write!(f, "&mut {pointee}"),
            Type::Array { elem, len } => write!(f, "[{elem}; {len}]"),
            Type::Simd { elem, len } => write!(f, "simd[{elem}; {len}]"),
            Type::Struct(fields) => {
                write!(f, "{{ ")?;
                for (i, ty) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, " }}")
            }
            Type::Overlay(fields) => {
                write!(f, "overlay {{ ")?;
                for (i, ty) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, " }}")
            }
            Type::Union { tag, variants } => {
                write!(f, "union {tag} {{ ")?;
                for (i, ty) in variants.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, " }}")
            }
            Type::FnPtr { args, ret } => {
                write!(f, "fn(")?;
                for (i, ty) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{ty}")?;
                }
                write!(f, ") -> {ret}")
            }
        }
    }
}

impl fmt::Display for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{}", self.local);
        for proj in &self.projections {
            match proj {
                Projection::Deref => s = format!("(*{s})"),
                Projection::Field(idx) => s = format!("{s}.{idx}"),
                Projection::Variant(idx) => s = format!("{s}.v{idx}"),
                Projection::Index(idx) => s = format!("{s}[{idx}]"),
            }
        }
        write!(f, "{s}")
    }
}

impl fmt::Display for ConstValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstValue::Void => write!(f, "void"),
            ConstValue::Zeroed => write!(f, "zeroed"),
            ConstValue::Bool(b) => write!(f, "{b}"),
            ConstValue::I64(n) => write!(f, "{n}"),
            ConstValue::Wide(w) => write!(f, "{w}"),
            ConstValue::F64(bits) => {
                let val = f64::from_bits(*bits);
                if val.fract() == 0.0 {
                    write!(f, "{val:.1}")
                } else {
                    write!(f, "{val}")
                }
            }
            ConstValue::Type(id) => write!(f, "{id}"),
            ConstValue::Func(id) => write!(f, "{id}"),
            ConstValue::Global(id) => write!(f, "{id}"),
            ConstValue::Str(s) => write!(f, "{s:?}"),
            ConstValue::Aggregate(items) => {
                write!(f, "{{ ")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{item}")?;
                }
                write!(f, " }}")
            }
        }
    }
}

impl fmt::Display for Operand {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operand::Copy(p) => write!(f, "copy {p}"),
            Operand::Move(p) => write!(f, "move {p}"),
            Operand::Const(c) => write!(f, "const {c}"),
        }
    }
}

impl fmt::Display for UnOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            UnOp::Neg => "neg",
            UnOp::Not => "not",
            UnOp::Bswap => "bswap",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            BinOp::Add => "add",
            BinOp::Sub => "sub",
            BinOp::Mul => "mul",
            BinOp::AddWrap => "add_wrap",
            BinOp::SubWrap => "sub_wrap",
            BinOp::MulWrap => "mul_wrap",
            BinOp::AddSat => "add_sat",
            BinOp::SubSat => "sub_sat",
            BinOp::MulSat => "mul_sat",
            BinOp::AddChecked => "add_checked",
            BinOp::SubChecked => "sub_checked",
            BinOp::MulChecked => "mul_checked",
            BinOp::AddUnchecked => "add_unchecked",
            BinOp::SubUnchecked => "sub_unchecked",
            BinOp::MulUnchecked => "mul_unchecked",
            BinOp::Div => "div",
            BinOp::Rem => "rem",
            BinOp::BitAnd => "bitand",
            BinOp::BitOr => "bitor",
            BinOp::BitXor => "bitxor",
            BinOp::Shl => "shl",
            BinOp::Shr => "shr",
            BinOp::Eq => "eq",
            BinOp::Ne => "ne",
            BinOp::Lt => "lt",
            BinOp::Le => "le",
            BinOp::Gt => "gt",
            BinOp::Ge => "ge",
        };
        write!(f, "{name}")
    }
}

impl fmt::Display for Rvalue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rvalue::Use(op) => write!(f, "{op}"),
            Rvalue::UnaryOp(op, val) => write!(f, "{op}({val})"),
            Rvalue::BinaryOp(op, lhs, rhs) => write!(f, "{op}({lhs}, {rhs})"),
            Rvalue::Cast(op, ty) => write!(f, "cast({op}, {ty})"),
            Rvalue::Transmute(op, ty) => write!(f, "transmute({op}, {ty})"),
            Rvalue::Ref {
                mutable: false,
                place,
            } => write!(f, "&{place}"),
            Rvalue::Ref {
                mutable: true,
                place,
            } => write!(f, "&mut {place}"),
            Rvalue::Aggregate(ty, ops) => {
                write!(f, "aggregate {ty}(")?;
                for (i, op) in ops.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{op}")?;
                }
                write!(f, ")")
            }
            Rvalue::Union {
                ty,
                variant,
                payload,
            } => {
                write!(f, "union {ty}(v{variant}, {payload})")
            }
            Rvalue::Discriminant(place) => write!(f, "discriminant({place})"),
            Rvalue::ArrayType { elem, len } => write!(f, "[{elem}; {len}]"),
            Rvalue::SimdType { elem, len } => write!(f, "simd[{elem}; {len}]"),
            Rvalue::OverlayType(ops) => {
                write!(f, "overlay(")?;
                for (i, op) in ops.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{op}")?;
                }
                write!(f, ")")
            }
            Rvalue::UnionType { tag, variants } => {
                write!(f, "union({tag}")?;
                for op in variants {
                    write!(f, ", {op}")?;
                }
                write!(f, ")")
            }
            Rvalue::PatternType { base, ranges } => {
                write!(f, "{base} in ")?;
                for (i, (lo, hi)) in ranges.iter().enumerate() {
                    if i > 0 {
                        write!(f, " | ")?;
                    }
                    write!(f, "{lo}..={hi}")?;
                }
                Ok(())
            }
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Assign(place, rval) => write!(f, "{place} = {rval};"),
            Statement::SetDiscriminant(place, variant) => {
                write!(f, "discriminant({place}) = v{variant};")
            }
            Statement::StorageLive(local) => write!(f, "StorageLive({local});"),
            Statement::StorageDead(local) => write!(f, "StorageDead({local});"),
            Statement::Line(pos) => write!(f, "// {pos}"),
        }
    }
}

impl fmt::Display for Terminator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Terminator::Goto { target } => write!(f, "goto -> {target};"),
            Terminator::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                write!(f, "switchInt({discr}) -> [")?;
                for (val, blk) in targets {
                    write!(f, "{val}: {blk}, ")?;
                }
                write!(f, "otherwise: {otherwise}];")
            }
            Terminator::Call {
                func,
                args,
                destination,
                target,
            } => {
                write!(f, "{destination} = call {func}(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") -> {target};")
            }
            Terminator::Drop { place, target } => write!(f, "drop({place}) -> {target};"),
            Terminator::Return => write!(f, "return;"),
            Terminator::Unreachable => write!(f, "unreachable;"),
        }
    }
}

impl fmt::Display for Global {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.mutable {
            write!(
                f,
                "global mut {}: {} = const {};",
                self.id, self.ty, self.init
            )
        } else {
            write!(f, "global {}: {} = const {};", self.id, self.ty, self.init)
        }
    }
}

impl fmt::Display for ExternFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "extern {}(", self.id)?;
        for (i, arg) in self.args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{arg}")?;
        }
        write!(f, ") -> {} = {:?};", self.ret, self.symbol)
    }
}

impl Function {
    /// Diagnostic name of parameter local `p`: its source name when known, otherwise `_N`.
    pub fn param_name(&self, p: LocalId) -> String {
        if p.is_contents() {
            return format!("*{}", self.param_name(p.base()));
        }
        p.0.checked_sub(1)
            .and_then(|i| self.param_names.get(i as usize))
            .cloned()
            .unwrap_or_else(|| p.to_string())
    }

    /// Diagnostic label for `place` in source terms: `self.t` rather than `(*_1).0`. Field names
    /// come from `program`; a dereference followed by a field reads as a field access.
    pub fn place_label(&self, program: &Program, place: &Place) -> String {
        let root = match self.local_names.iter().find(|(l, _)| *l == place.local) {
            Some((_, n)) if n.starts_with("__destructure") => "<destructured value>".to_string(),
            Some((_, n)) if n.starts_with("__for_it") => "<for-loop iterator>".to_string(),
            Some((_, n)) => n.clone(),
            None => return place.to_string(),
        };
        let mut s = root;
        let mut ty = self.locals.get(place.local.0 as usize).copied();
        let mut deref_pending = false;
        for proj in &place.projections {
            let cur = ty.and_then(|t| program.types.get(t.0 as usize));
            if deref_pending && !matches!(proj, Projection::Field(_)) {
                s = format!("(*{s})");
            }
            deref_pending = false;
            match proj {
                Projection::Deref => {
                    deref_pending = true;
                    ty = match cur {
                        Some(Type::Ptr { pointee, .. }) => Some(*pointee),
                        _ => None,
                    };
                }
                Projection::Field(i) => {
                    let name = ty
                        .and_then(|t| program.field_names.iter().find(|(f, _)| *f == t))
                        .and_then(|(_, names)| names.get(*i as usize))
                        .cloned()
                        .unwrap_or_else(|| i.to_string());
                    s = format!("{s}.{name}");
                    ty = match cur {
                        Some(Type::Struct(fields) | Type::Overlay(fields)) => {
                            fields.get(*i as usize).copied()
                        }
                        _ => None,
                    };
                }
                Projection::Variant(i) => {
                    s = format!("{s}.v{i}");
                    ty = match cur {
                        Some(Type::Union { variants, .. }) => variants.get(*i as usize).copied(),
                        _ => None,
                    };
                }
                Projection::Index(i) => {
                    s = format!("{s}[{i}]");
                    ty = match cur {
                        Some(Type::Array { elem, .. } | Type::Simd { elem, .. }) => Some(*elem),
                        _ => None,
                    };
                }
            }
        }
        if deref_pending {
            s = format!("*{s}");
        }
        s
    }

    /// Diagnostic label: `Vec::push (fn12)` when a source name is known, otherwise `fn12`.
    pub fn label(&self) -> String {
        match &self.debug_name {
            Some(name) => format!("{name} ({})", self.id),
            None => self.id.to_string(),
        }
    }
}

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        if self.arg_count > 0 {
            write!(f, "({})", self.arg_count)?;
        }
        if let Some(params) = &self.ret_borrows {
            write!(f, " borrows(")?;
            for (i, p) in params.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{p}")?;
            }
            write!(f, ")")?;
        }
        if let Some(sym) = &self.export {
            write!(f, " = {sym:?}")?;
        }
        writeln!(f, " {{")?;
        for (i, ty) in self.locals.iter().enumerate() {
            writeln!(f, "    let _{i}: {ty};")?;
        }
        for (i, blk) in self.blocks.iter().enumerate() {
            writeln!(f, "    bb{i}: {{")?;
            for stmt in &blk.statements {
                writeln!(f, "        {stmt}")?;
            }
            writeln!(f, "        {}", blk.terminator)?;
            writeln!(f, "    }}")?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, ty) in self.types.iter().enumerate() {
            writeln!(f, "ty{i} = {ty};")?;
        }
        if !self.types.is_empty()
            && (!self.destructors.is_empty()
                || !self.globals.is_empty()
                || !self.externs.is_empty()
                || !self.functions.is_empty())
        {
            writeln!(f)?;
        }
        for (ty_id, fn_id) in &self.destructors {
            writeln!(f, "drop {ty_id} = {fn_id};")?;
        }
        if !self.destructors.is_empty()
            && (!self.globals.is_empty() || !self.externs.is_empty() || !self.functions.is_empty())
        {
            writeln!(f)?;
        }
        for gl in &self.globals {
            writeln!(f, "{gl}")?;
        }
        if !self.globals.is_empty() && (!self.externs.is_empty() || !self.functions.is_empty()) {
            writeln!(f)?;
        }
        for ext in &self.externs {
            writeln!(f, "{ext}")?;
        }
        if !self.externs.is_empty() && !self.functions.is_empty() {
            writeln!(f)?;
        }
        for (i, func) in self.functions.iter().enumerate() {
            if i > 0 {
                writeln!(f)?;
            }
            writeln!(f, "{func}")?;
        }
        Ok(())
    }
}
