/-!
# Reading WebAssembly module bytes

A partial reader for WebAssembly 1.0 module sections. It provides byte, LEB128, section and module
readers used by the function-body decoder and the module-shape predicates below.

Bytes are stored as one little-endian natural number, so skipping a section is a shift.
-/

namespace WasmShape

structure Bytes where
  n : Nat
  len : Nat

abbrev R (α : Type) := Bytes → Option (α × Bytes)

def byte : R Nat := fun b => if b.len = 0 then none else some (b.n % 256, ⟨b.n >>> 8, b.len - 1⟩)

def skip (k : Nat) (b : Bytes) : Option Bytes := if k ≤ b.len then some ⟨b.n >>> (8 * k), b.len - k⟩ else none

/-- The first `k` bytes on their own, and what follows. -/
def split (k : Nat) (b : Bytes) : Option (Bytes × Bytes) :=
  if k ≤ b.len then some (⟨b.n % 2 ^ (8 * k), k⟩, ⟨b.n >>> (8 * k), b.len - k⟩) else none

def lebAux : Nat → Nat → Nat → R Nat
  | 0, _, _ => fun _ => none
  | f + 1, acc, sh => fun b => match byte b with
    | none => none
    | some (x, b) => if x < 128 then some (acc + x * 2 ^ sh, b) else lebAux f (acc + (x - 128) * 2 ^ sh) (sh + 7) b

/-- unsigned LEB128 of at most `bits` bits -/
def uleb (bits : Nat) : R Nat := fun b => match lebAux ((bits + 6) / 7) 0 0 b with
  | some (v, b) => if v < 2 ^ bits then some (v, b) else none
  | none => none

/-- a signed LEB128 constant, skipped -/
def sleb (bits : Nat) : R Unit := fun b => (lebAux ((bits + 6) / 7) 0 0 b).map fun (_, b) => ((), b)

def bytesN : Nat → R (List Nat)
  | 0 => fun b => some ([], b)
  | k + 1 => fun b => match byte b with
    | none => none
    | some (x, b) => (bytesN k b).map fun (xs, b) => (x :: xs, b)

def name : R (List Nat) := fun b => match uleb 32 b with
  | none => none
  | some (k, b) => if k ≤ b.len then bytesN k b else none

def expect (x : Nat) : R Unit := fun b => match byte b with
  | some (y, b) => if x = y then some ((), b) else none
  | none => none

/-- `n` items, each read by `p` -/
def items {α} (p : R α) : Nat → R (List α)
  | 0 => fun b => some ([], b)
  | k + 1 => fun b => match p b with
    | none => none
    | some (x, b) => (items p k b).map fun (xs, b) => (x :: xs, b)

def vec {α} (p : R α) : R (List α) := fun b => match uleb 32 b with
  | none => none
  | some (k, b) => if k ≤ b.len then items p k b else none

structure Limits where
  min : Nat
  max : Option Nat
  deriving DecidableEq, Repr

def limits : R Limits := fun b => match byte b with
  | some (0, b) => (uleb 32 b).map fun (m, b) => (⟨m, none⟩, b)
  | some (1, b) => match uleb 32 b with
    | some (m, b) => (uleb 32 b).map fun (x, b) => (⟨m, some x⟩, b)
    | none => none
  | _ => none

/-- An import's kind: 0 function, 1 table, 2 memory, 3 global. -/
def importDesc : R Nat := fun b => match byte b with
  | some (0, b) => (uleb 32 b).map fun (_, b) => (0, b)
  | some (1, b) => match byte b with
    | some (_, b) => (limits b).map fun (_, b) => (1, b)
    | none => none
  | some (2, b) => (limits b).map fun (_, b) => (2, b)
  | some (3, b) => match bytesN 2 b with
    | some (_, b) => some (3, b)
    | none => none
  | _ => none

def import_ : R Nat := fun b => match name b with
  | some (_, b) => match name b with
    | some (_, b) => importDesc b
    | none => none
  | none => none

/-- A constant initializer: one constant instruction, then `end`. -/
def constExpr : R Unit := fun b => match byte b with
  | some (0x41, b) => (sleb 32 b).bind fun (_, b) => expect 0x0b b
  | some (0x42, b) => (sleb 64 b).bind fun (_, b) => expect 0x0b b
  | some (0x43, b) => (skip 4 b).bind (expect 0x0b)
  | some (0x44, b) => (skip 8 b).bind (expect 0x0b)
  | some (0x23, b) => (uleb 32 b).bind fun (_, b) => expect 0x0b b
  | _ => none

/-- A global's mutability, after its value type. -/
def global : R Bool := fun b => match bytesN 2 b with
  | some ([_, m], b) => if m ≤ 1 then (constExpr b).map fun (_, b) => (m = 1, b) else none
  | _ => none

structure Export where
  name : List Nat
  kind : Nat
  idx : Nat
  deriving DecidableEq, Repr

def export_ : R Export := fun b => match name b with
  | some (nm, b) => match byte b with
    | some (k, b) => (uleb 32 b).map fun (i, b) => (⟨nm, k, i⟩, b)
    | none => none
  | none => none

structure Module where
  customs : List (List Nat) := []
  imports : List Nat := []
  memories : List Limits := []
  globals : List Bool := []
  exports : List Export := []
  starts : List Nat := []
  deriving Repr

/-- A section read whole: what it holds, with nothing left over. -/
def whole {α} (p : R α) (b : Bytes) : Option α := match p b with
  | some (x, r) => if r.len = 0 then some x else none
  | none => none

/-- Each section by id; the ones these properties do not look at are skipped. A section that appears
twice adds to what was read, so it cannot hide what the first one holds. -/
def addSection (m : Module) (id : Nat) (s : Bytes) : Option Module :=
  match id with
  | 0 => (name s).map fun (nm, _) => { m with customs := m.customs ++ [nm] }
  | 2 => (whole (vec import_) s).map fun xs => { m with imports := m.imports ++ xs }
  | 5 => (whole (vec limits) s).map fun xs => { m with memories := m.memories ++ xs }
  | 6 => (whole (vec global) s).map fun xs => { m with globals := m.globals ++ xs }
  | 7 => (whole (vec export_) s).map fun xs => { m with exports := m.exports ++ xs }
  | 8 => (whole (uleb 32) s).map fun i => { m with starts := m.starts ++ [i] }
  | i => if i ≤ 12 then some m else none

def sections : Nat → Module → Bytes → Option Module
  | 0, _, _ => none
  | f + 1, m, b => if b.len = 0 then some m else match byte b with
    | none => none
    | some (id, b) => match uleb 32 b with
      | none => none
      | some (sz, b) => match split sz b with
        | none => none
        | some (s, b) => (addSection m id s).bind fun m => sections f m b

/-- magic `\0asm`, version 1, then sections to the end -/
def parse (b : Bytes) : Option Module := match bytesN 8 b with
  | some ([0, 0x61, 0x73, 0x6d, 1, 0, 0, 0], b) => sections (b.len + 1) {} b
  | _ => none

/-! ## The properties -/

def allowedCustom : List (List Nat) := ["target_features".toList.map Char.toNat, "producers".toList.map Char.toNat]

/-- It cannot call the host, its memory cannot grow without bound, nothing internal can be rewritten or
swapped from outside, loading it runs nothing, and nothing unfamiliar came along. -/
def Module.Safe (m : Module) : Prop :=
  m.imports = [] ∧
  (∀ l ∈ m.memories, l.max.isSome) ∧
  (∀ e ∈ m.exports, e.kind ≠ 1 ∧ (e.kind = 3 → m.globals[e.idx]? = some false)) ∧
  m.starts = [] ∧
  ∀ c ∈ m.customs, c ∈ allowedCustom

instance (m : Module) : Decidable m.Safe := by unfold Module.Safe; infer_instance

def SafeBytes (b : Bytes) : Prop := match parse b with
  | some m => m.Safe
  | none => False

instance (b : Bytes) : Decidable (SafeBytes b) := by
  unfold SafeBytes; split <;> infer_instance

end WasmShape
