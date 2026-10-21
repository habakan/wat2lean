import Wat2Lean.Syntax

/-!
# WebAssembly instruction semantics

An executable big-step model for the supported instruction subset over read-only linear memory. Values
are represented as naturals with WebAssembly integer-width operations applied explicitly. `fuel`
bounds execution; running out is represented as a trap. `Machine.lean` adds writes, globals and calls.
-/

namespace WasmCode

structure Mem where
  get : Nat → UInt8
  size : Nat

/-- How a sequence of instructions ended, with the value stack (top first) and the locals. -/
inductive Res where
  | normal (st ls : List Nat)
  | br (l : Nat) (st ls : List Nat)
  | ret (st ls : List Nat)
  | trap

def w32 (n : Nat) : Nat := n % 2 ^ 32

/-- Subtraction as u32s, behind an opaque constant with its equation as a theorem: otherwise the kernel,
checking a proof, can try to compute `a + 2^32` for a symbolic `a` one step at a time. -/
structure SubW where
  f : Nat → Nat → Nat
  spec : ∀ a b, f a b = w32 (a + 2 ^ 32 - b)

instance : Inhabited SubW := ⟨⟨fun a b => w32 (a + 2 ^ 32 - b), fun _ _ => rfl⟩⟩

opaque subW : SubW

/-- Addition as u32s, opaque for the same reason. -/
structure AddW where
  f : Nat → Nat → Nat
  spec : ∀ a b, f a b = w32 (a + b)

instance : Inhabited AddW := ⟨⟨fun a b => w32 (a + b), fun _ _ => rfl⟩⟩

opaque addW : AddW

/-- A u32 moved so that signed order is unsigned order, opaque for the same reason. -/
structure SgnW where
  f : Nat → Nat
  spec : ∀ a, f a = (a + 2 ^ 31) % 2 ^ 32

instance : Inhabited SgnW := ⟨⟨fun a => (a + 2 ^ 31) % 2 ^ 32, fun _ => rfl⟩⟩

opaque sgnW : SgnW

def BinOp.eval : BinOp → Nat → Nat → Nat
  | .add, a, b => addW.f a b
  | .sub, a, b => subW.f a b
  | .shl, a, b => w32 (a * 2 ^ (b % 32))
  | .eq, a, b => if a = b then 1 else 0
  | .ne, a, b => if a = b then 0 else 1
  | .ltU, a, b => if a < b then 1 else 0
  | .gtU, a, b => if a > b then 1 else 0
  | .leU, a, b => if a ≤ b then 1 else 0
  | .geU, a, b => if a ≥ b then 1 else 0
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .mul, a, b => w32 (a * b)
  | .ltS, a, b => if sgnW.f a < sgnW.f b then 1 else 0
  | .geS, a, b => if sgnW.f a ≥ sgnW.f b then 1 else 0
  | .add64, a, b => (a + b) % 2 ^ 64
  | .sub64, a, b => (a + 2 ^ 64 - b) % 2 ^ 64
  | .shrU, a, b => w32 a / 2 ^ (b % 32)
  | .xor, a, b => a ^^^ b

def load (m : Mem) (a k : Nat) : Option Nat :=
  if a + k ≤ m.size then some ((List.range k).foldr (fun j v => v * 256 + (m.get (a + j)).toNat) 0) else none

/-- What a block, loop or `if` body's ending means outside it, for a label of `r` results. -/
def leave (r : Nat) (st : List Nat) : Res → Res
  | .normal st' ls => .normal (st' ++ st) ls
  | .br 0 st' ls => .normal (st'.take r ++ st) ls
  | .br (l + 1) st' ls => .br l st' ls
  | .ret st' ls => .ret st' ls
  | .trap => .trap

mutual
def execs (m : Mem) : Nat → List Instr → List Nat → List Nat → Res
  | 0, _, _, _ => .trap
  | _ + 1, [], st, ls => .normal st ls
  | f + 1, i :: is, st, ls => match exec m f i st ls with
    | .normal st ls => execs m f is st ls
    | r => r

def exec (m : Mem) : Nat → Instr → List Nat → List Nat → Res
  | 0, _, _, _ => .trap
  | f + 1, .block r body, st, ls => leave r st (execs m f body [] ls)
  | f + 1, .loop r body, st, ls => match execs m f body [] ls with
    | .br 0 _ ls => exec m f (.loop r body) st ls
    | res => leave r st res
  | f + 1, .if_ r t e, c :: st, ls => leave r st (execs m f (if c ≠ 0 then t else e) [] ls)
  | _ + 1, .br l, st, ls => .br l st ls
  | _ + 1, .brIf l, c :: st, ls => if c ≠ 0 then .br l st ls else .normal st ls
  | _ + 1, .ret, st, ls => .ret st ls
  | _ + 1, .drop, _ :: st, ls => .normal st ls
  | _ + 1, .localGet i, st, ls => match ls[i]? with
    | some v => .normal (v :: st) ls
    | none => .trap
  | _ + 1, .localSet i, v :: st, ls => if i < ls.length then .normal st (ls.set i v) else .trap
  | _ + 1, .localTee i, v :: st, ls => if i < ls.length then .normal (v :: st) (ls.set i v) else .trap
  | _ + 1, .const v, st, ls => .normal (v.toNat :: st) ls
  | _ + 1, .load8u o, a :: st, ls => match load m (a + o) 1 with
    | some v => .normal (v :: st) ls
    | none => .trap
  | _ + 1, .load32 o, a :: st, ls => match load m (a + o) 4 with
    | some v => .normal (v :: st) ls
    | none => .trap
  | _ + 1, .eqz, a :: st, ls => .normal ((if a = 0 then 1 else 0) :: st) ls
  | _ + 1, .bin op, b :: a :: st, ls => .normal (op.eval a b :: st) ls
  | _ + 1, _, _, _ => .trap
end

/-- A call with i32 arguments, returning its one i32 result, or none for a trap. -/
def call (m : Mem) (fuel : Nat) (fn : Func) (args : List Nat) : Option Nat :=
  match execs m fuel fn.body [] (args ++ List.replicate fn.locals 0) with
  | .normal (v :: _) _ | .ret (v :: _) _ => some v
  | _ => none

end WasmCode
