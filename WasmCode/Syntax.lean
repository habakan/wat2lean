import WasmShape.Binary

/-!
# Function bodies, decoded

The part of WebAssembly 1.0's instruction set that the functions proven here use: structured control,
calls, locals and globals, i32 and i64 constants, loads, stores, memory.fill, comparisons and arithmetic. A body with
any other instruction does not decode, so a function proven here is exactly the code in the module
(`codeBody`). i64 comparisons and `eqz` share the i32 constructors: on values as naturals they agree.
-/

namespace WasmCode
open WasmShape

inductive BinOp where
  | add | sub | shl | eq | ne | ltU | gtU | leU | geU | and | or | mul | ltS | geS | add64 | sub64 | shrU | xor
  deriving DecidableEq, Repr

inductive Instr where
  /-- `results` is 0 or 1: the block type is empty or one value. -/
  | block (results : Nat) (body : List Instr)
  | loop (results : Nat) (body : List Instr)
  | if_ (results : Nat) (thn els : List Instr)
  | br (l : Nat)
  | brIf (l : Nat)
  | ret
  | drop
  | localGet (i : Nat)
  | localSet (i : Nat)
  | localTee (i : Nat)
  | const (v : UInt32)
  /-- a byte, zero-extended -/
  | load8u (offset : Nat)
  /-- four bytes, little-endian -/
  | load32 (offset : Nat)
  | eqz
  | bin (op : BinOp)
  | unreachable
  | brTable (ls : List Nat) (d : Nat)
  | call (i : Nat)
  | callIndirect (t : Nat)
  | select
  | globalGet (i : Nat)
  | globalSet (i : Nat)
  | const64 (v : Nat)
  | load64 (offset : Nat)
  | store8 (offset : Nat)
  /-- the low four bytes, also i64.store32 -/
  | store32 (offset : Nat)
  | store64 (offset : Nat)
  /-- i32.wrap_i64 -/
  | wrap
  /-- memory.fill -/
  | fill
  /-- a byte, sign-extended to 32 bits -/
  | load8s (offset : Nat)
  /-- two bytes, little-endian -/
  | load16u (offset : Nat)
  | store16 (offset : Nat)
  /-- memory.copy -/
  | copy
  /-- i32.div_u, which traps on a zero divisor -/
  | divU
  deriving Repr

mutual
def Instr.beq : Instr → Instr → Bool
  | .block r b, .block r' b' => r == r' && Instr.beqs b b'
  | .loop r b, .loop r' b' => r == r' && Instr.beqs b b'
  | .if_ r t e, .if_ r' t' e' => r == r' && Instr.beqs t t' && Instr.beqs e e'
  | .br l, .br l' => l == l'
  | .brIf l, .brIf l' => l == l'
  | .ret, .ret => true
  | .drop, .drop => true
  | .localGet i, .localGet i' => i == i'
  | .localSet i, .localSet i' => i == i'
  | .localTee i, .localTee i' => i == i'
  | .const v, .const v' => v == v'
  | .load8u o, .load8u o' => o == o'
  | .load32 o, .load32 o' => o == o'
  | .eqz, .eqz => true
  | .bin o, .bin o' => o == o'
  | .unreachable, .unreachable => true
  | .brTable l d, .brTable l' d' => l == l' && d == d'
  | .call i, .call i' => i == i'
  | .callIndirect t, .callIndirect t' => t == t'
  | .select, .select => true
  | .globalGet i, .globalGet i' => i == i'
  | .globalSet i, .globalSet i' => i == i'
  | .const64 v, .const64 v' => v == v'
  | .load64 o, .load64 o' => o == o'
  | .store8 o, .store8 o' => o == o'
  | .store32 o, .store32 o' => o == o'
  | .store64 o, .store64 o' => o == o'
  | .wrap, .wrap => true
  | .fill, .fill => true
  | .load8s o, .load8s o' => o == o'
  | .load16u o, .load16u o' => o == o'
  | .store16 o, .store16 o' => o == o'
  | .copy, .copy => true
  | .divU, .divU => true
  | _, _ => false

def Instr.beqs : List Instr → List Instr → Bool
  | [], [] => true
  | a :: as, b :: bs => Instr.beq a b && Instr.beqs as bs
  | _, _ => false
end

mutual
theorem Instr.eq_of_beq : ∀ {a b : Instr}, Instr.beq a b = true → a = b
  | a, b, h => by
    cases a <;> cases b <;> simp only [Instr.beq, Bool.and_eq_true, beq_iff_eq, Bool.false_eq_true] at h
    all_goals first
      | rfl
      | (rw [h])
      | (rw [h.1, h.2])
      | (rw [h.1, Instr.eq_of_beqs h.2])
      | (rw [h.1.1, Instr.eq_of_beqs h.1.2, Instr.eq_of_beqs h.2])

theorem Instr.eq_of_beqs : ∀ {a b : List Instr}, Instr.beqs a b = true → a = b
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [Instr.beqs, Bool.and_eq_true] at h; rw [Instr.eq_of_beq h.1, Instr.eq_of_beqs h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Instr.beqs] at h
end

/-- signed LEB128 of at most 64 bits, as the u64 with those bits -/
def sleb64 : Nat → Nat → Nat → R Nat
  | 0, _, _ => fun _ => none
  | f + 1, acc, sh => fun b => match byte b with
    | none => none
    | some (x, b) =>
      let acc := acc + (x % 128) * 2 ^ sh
      if x < 128 then
        some ((if x &&& 0x40 = 0 then acc else acc + (2 ^ 70 - 2 ^ (sh + 7))) % 2 ^ 64, b)
      else sleb64 f acc (sh + 7) b

/-- signed LEB128 of at most 32 bits, as the u32 with those bits -/
def slebAux : Nat → Nat → Nat → R UInt32
  | 0, _, _ => fun _ => none
  | f + 1, acc, sh => fun b => match byte b with
    | none => none
    | some (x, b) =>
      let acc := acc + (x % 128) * 2 ^ sh
      if x < 128 then
        let v := if x &&& 0x40 = 0 then acc else acc + (2 ^ 64 - 2 ^ (sh + 7))
        some (UInt32.ofNat v, b)
      else slebAux f acc (sh + 7) b

def blockType : R Nat := fun b => match byte b with
  | some (0x40, b) => some (0, b)
  | some (0x7f, b) => some (1, b)
  | _ => none

def binOp? : Nat → Option BinOp
  | 0x6a => some .add | 0x6b => some .sub | 0x74 => some .shl | 0x46 => some .eq | 0x47 => some .ne
  | 0x49 => some .ltU | 0x4b => some .gtU | 0x4d => some .leU | 0x4f => some .geU | 0x71 => some .and
  | 0x72 => some .or | 0x6c => some .mul | 0x48 => some .ltS | 0x4e => some .geS | 0x7c => some .add64
  | 0x7d => some .sub64 | 0x54 => some .ltU | 0x56 => some .gtU | 0x76 => some .shrU | 0x73 => some .xor | _ => none

/-- How a sequence of instructions ended: `end`, or `else` inside an `if`. -/
inductive Stop where
  | end_ | else_
  deriving DecidableEq

def memarg : R Nat := fun b => match uleb 32 b with
  | some (_, b) => uleb 32 b
  | none => none

/-- Instructions up to the `end` or `else` that closes them. -/
def instrs : Nat → R (List Instr × Stop)
  | 0 => fun _ => none
  | f + 1 => fun b => match byte b with
    | none => none
    | some (0x0b, b) => some (([], .end_), b)
    | some (0x05, b) => some (([], .else_), b)
    | some (op, b) =>
      let rest (i : Instr) (b : Bytes) : Option ((List Instr × Stop) × Bytes) :=
        (instrs f b).map fun ((is, s), b) => ((i :: is, s), b)
      match op with
      | 0x02 => match blockType b with
        | some (r, b) => match instrs f b with
          | some ((body, .end_), b) => rest (.block r body) b
          | _ => none
        | none => none
      | 0x03 => match blockType b with
        | some (r, b) => match instrs f b with
          | some ((body, .end_), b) => rest (.loop r body) b
          | _ => none
        | none => none
      | 0x04 => match blockType b with
        | some (r, b) => match instrs f b with
          | some ((thn, .end_), b) => rest (.if_ r thn []) b
          | some ((thn, .else_), b) => match instrs f b with
            | some ((els, .end_), b) => rest (.if_ r thn els) b
            | _ => none
          | none => none
        | none => none
      | 0x0c => (uleb 32 b).bind fun (l, b) => rest (.br l) b
      | 0x0d => (uleb 32 b).bind fun (l, b) => rest (.brIf l) b
      | 0x0f => rest .ret b
      | 0x1a => rest .drop b
      | 0x20 => (uleb 32 b).bind fun (i, b) => rest (.localGet i) b
      | 0x21 => (uleb 32 b).bind fun (i, b) => rest (.localSet i) b
      | 0x22 => (uleb 32 b).bind fun (i, b) => rest (.localTee i) b
      | 0x41 => (slebAux 5 0 0 b).bind fun (v, b) => rest (.const v) b
      | 0x28 => (memarg b).bind fun (o, b) => rest (.load32 o) b
      | 0x2d => (memarg b).bind fun (o, b) => rest (.load8u o) b
      | 0x45 | 0x50 => rest .eqz b
      | 0x00 => rest .unreachable b
      | 0x0e => (uleb 32 b).bind fun (n, b) => (items (uleb 32) n b).bind fun (ls, b) =>
          (uleb 32 b).bind fun (d, b) => rest (.brTable ls d) b
      | 0x10 => (uleb 32 b).bind fun (i, b) => rest (.call i) b
      | 0x11 => (uleb 32 b).bind fun (t, b) => match byte b with
        | some (0, b) => rest (.callIndirect t) b
        | _ => none
      | 0x1b => rest .select b
      | 0x23 => (uleb 32 b).bind fun (i, b) => rest (.globalGet i) b
      | 0x24 => (uleb 32 b).bind fun (i, b) => rest (.globalSet i) b
      | 0x42 => (sleb64 10 0 0 b).bind fun (v, b) => rest (.const64 v) b
      | 0x29 => (memarg b).bind fun (o, b) => rest (.load64 o) b
      | 0x2c => (memarg b).bind fun (o, b) => rest (.load8s o) b
      | 0x2f => (memarg b).bind fun (o, b) => rest (.load16u o) b
      | 0x3b => (memarg b).bind fun (o, b) => rest (.store16 o) b
      | 0x3a => (memarg b).bind fun (o, b) => rest (.store8 o) b
      | 0x36 | 0x3e => (memarg b).bind fun (o, b) => rest (.store32 o) b
      | 0x37 => (memarg b).bind fun (o, b) => rest (.store64 o) b
      | 0xa7 => rest .wrap b
      | 0xfc => (uleb 32 b).bind fun (k, b) => if k = 11 then match byte b with
          | some (0, b) => rest .fill b
          | _ => none
        else if k = 10 then match byte b with
          | some (0, b) => match byte b with
            | some (0, b) => rest .copy b
            | _ => none
          | _ => none
        else none
      | 0x6e => rest .divU b
      | op => match binOp? op with
        | some o => rest (.bin o) b
        | none => none

structure Func where
  /-- locals besides the parameters -/
  locals : Nat
  body : List Instr
  deriving Repr

def Func.beq (f g : Func) : Bool := f.locals == g.locals && Instr.beqs f.body g.body

theorem Func.eq_of_beq {f g : Func} (h : f.beq g = true) : f = g := by
  obtain ⟨n, b⟩ := f; obtain ⟨n', b'⟩ := g
  simp only [Func.beq, Bool.and_eq_true, beq_iff_eq] at h
  rw [h.1, Instr.eq_of_beqs h.2]

/-- The decoded function is `f`: a Bool the kernel evaluates, and the equality it gives. -/
def isFunc (o : Option Func) (f : Func) : Bool := match o with
  | some g => g.beq f
  | none => false

theorem eq_of_isFunc {o : Option Func} {f : Func} (h : isFunc o f = true) : o = some f := by
  cases o with
  | none => simp [isFunc] at h
  | some g => simp only [isFunc] at h; rw [Func.eq_of_beq h]

/-- local declarations, i32 or i64 -/
def localDecls : R Nat := fun b => match uleb 32 b with
  | none => none
  | some (k, b) => (items (fun b => match uleb 32 b with
      | some (c, b) => match byte b with
        | some (0x7f, b) | some (0x7e, b) => some (c, b)
        | _ => none
      | none => none) k b).map fun (cs, b) => (cs.foldl (· + ·) 0, b)

def func (b : Bytes) : Option Func := match localDecls b with
  | some (n, b) => match instrs (b.len + 1) b with
    | some ((body, .end_), r) => if r.len = 0 then some ⟨n, body⟩ else none
    | _ => none
  | none => none

/-- The `i`th body in a code section's contents. -/
def nthBody : Nat → Nat → Bytes → Option Bytes
  | 0, _, _ => none
  | _ + 1, _, ⟨_, 0⟩ => none
  | f + 1, i, b => match uleb 32 b with
    | none => none
    | some (sz, b) => match split sz b with
      | none => none
      | some (body, b) => if i = 0 then some body else nthBody f (i - 1) b

/-- The contents of section `k`. -/
def sectionOf (k : Nat) : Nat → Bytes → Option Bytes
  | 0, _ => none
  | f + 1, b => if b.len = 0 then none else match byte b with
    | none => none
    | some (id, b) => match uleb 32 b with
      | none => none
      | some (sz, b) => match split sz b with
        | none => none
        | some (s, b) => if id = k then some s else sectionOf k f b

def moduleSection (k : Nat) (b : Bytes) : Option Bytes := (skip 8 b).bind fun b => sectionOf k (b.len + 1) b

/-- Function `i` of a module with no imported functions, decoded. -/
def codeBody (b : Bytes) (i : Nat) : Option Func :=
  (moduleSection 10 b).bind fun s =>
    match uleb 32 s with
    | some (_, s) => (nthBody (s.len + 1) i s).bind func
    | none => none

def valType : R Unit := fun b => match byte b with
  | some (0x7f, b) | some (0x7e, b) => some ((), b)
  | _ => none

/-- A function type's parameter and result counts. -/
def funcType : R (Nat × Nat) := fun b => match byte b with
  | some (0x60, b) => match vec valType b with
    | some (ps, b) => (vec valType b).map fun (rs, b) => ((ps.length, rs.length), b)
    | none => none
  | _ => none

/-- The parameter and result counts of function `i`, from the function and type sections. -/
def typeOf (b : Bytes) (i : Nat) : Option (Nat × Nat) :=
  (moduleSection 3 b).bind fun fsec => (whole (vec (uleb 32)) fsec).bind fun tys => tys[i]?.bind fun t =>
    (moduleSection 1 b).bind fun tsec => (whole (vec funcType) tsec).bind fun ts => ts[t]?

end WasmCode
