import Wat2Lean.Semantics

/-!
# Running a function that stores and calls

`Semantics.lean` with the store threaded through: a memory that stores write to, the globals, and calls
into the module's other functions. A value is a natural below 2^32 or 2^64 by its type. `call_indirect`
is not modeled and traps, so a theorem that a run returns a value also says it took no such call.
On code with no store, global or call, a run is `Semantics.lean`'s (`execs_pure`).
-/

namespace WasmCode

structure Store where
  mem : Nat → UInt8
  size : Nat
  globals : List Nat

def Store.m (s : Store) : Mem := ⟨s.mem, s.size⟩

/-- A function of the module: its parameter and result counts, and its code. -/
structure Fn where
  params : Nat
  results : Nat
  code : Func

/-- Function `i` of a module with no imported functions. -/
def fnOf (b : WasmShape.Bytes) (i : Nat) : Option Fn :=
  (typeOf b i).bind fun (p, r) => (codeBody b i).map fun c => ⟨p, r, c⟩

inductive Out where
  | normal (st ls : List Nat) (s : Store)
  | br (l : Nat) (st ls : List Nat) (s : Store)
  | ret (st ls : List Nat) (s : Store)
  | trap

def bytesLE (v k : Nat) : List UInt8 := (List.range k).map fun j => UInt8.ofNat (v / 256 ^ j)

def Store.write (s : Store) (a : Nat) (bs : List UInt8) : Option Store :=
  if a + bs.length ≤ s.size then
    some { s with mem := fun x => if a ≤ x ∧ x < a + bs.length then bs.getD (x - a) 0 else s.mem x }
  else none

def Out.leave (r : Nat) (st : List Nat) : Out → Out
  | .normal st' ls s => .normal (st' ++ st) ls s
  | .br 0 st' ls s => .normal (st'.take r ++ st) ls s
  | .br (l + 1) st' ls s => .br l st' ls s
  | .ret st' ls s => .ret st' ls s
  | .trap => .trap

def Out.ofLoad (st ls : List Nat) (s : Store) : Option Nat → Out
  | some v => .normal (v :: st) ls s
  | none => .trap

def Out.ofWrite (st ls : List Nat) : Option Store → Out
  | some s => .normal st ls s
  | none => .trap

mutual
def execInstrs (fs : Nat → Option Fn) : Nat → List Instr → List Nat → List Nat → Store → Out
  | 0, _, _, _, _ => .trap
  | _ + 1, [], st, ls, s => .normal st ls s
  | f + 1, i :: is, st, ls, s => match execInstr fs f i st ls s with
    | .normal st ls s => execInstrs fs f is st ls s
    | r => r

def execInstr (fs : Nat → Option Fn) : Nat → Instr → List Nat → List Nat → Store → Out
  | 0, _, _, _, _ => .trap
  | f + 1, .block r body, st, ls, s => (execInstrs fs f body [] ls s).leave r st
  | f + 1, .loop r body, st, ls, s => match execInstrs fs f body [] ls s with
    | .br 0 _ ls s => execInstr fs f (.loop r body) st ls s
    | res => res.leave r st
  | f + 1, .if_ r t e, c :: st, ls, s => (execInstrs fs f (if c ≠ 0 then t else e) [] ls s).leave r st
  | _ + 1, .br l, st, ls, s => .br l st ls s
  | _ + 1, .brIf l, c :: st, ls, s => if c ≠ 0 then .br l st ls s else .normal st ls s
  | _ + 1, .brTable l d, c :: st, ls, s => .br (l[c]?.getD d) st ls s
  | _ + 1, .ret, st, ls, s => .ret st ls s
  | _ + 1, .drop, _ :: st, ls, s => .normal st ls s
  | _ + 1, .select, c :: b :: a :: st, ls, s => .normal ((if c ≠ 0 then a else b) :: st) ls s
  | _ + 1, .localGet i, st, ls, s => match ls[i]? with
    | some v => .normal (v :: st) ls s
    | none => .trap
  | _ + 1, .localSet i, v :: st, ls, s => if i < ls.length then .normal st (ls.set i v) s else .trap
  | _ + 1, .localTee i, v :: st, ls, s => if i < ls.length then .normal (v :: st) (ls.set i v) s else .trap
  | _ + 1, .globalGet i, st, ls, s => match s.globals[i]? with
    | some v => .normal (v :: st) ls s
    | none => .trap
  | _ + 1, .globalSet i, v :: st, ls, s =>
    if i < s.globals.length then .normal st ls { s with globals := s.globals.set i v } else .trap
  | _ + 1, .const v, st, ls, s => .normal (v.toNat :: st) ls s
  | _ + 1, .const64 v, st, ls, s => .normal (v :: st) ls s
  | _ + 1, .load8u o, a :: st, ls, s => Out.ofLoad st ls s (load s.m (a + o) 1)
  | _ + 1, .load32 o, a :: st, ls, s => Out.ofLoad st ls s (load s.m (a + o) 4)
  | _ + 1, .load64 o, a :: st, ls, s => Out.ofLoad st ls s (load s.m (a + o) 8)
  | _ + 1, .store8 o, v :: a :: st, ls, s => Out.ofWrite st ls (s.write (a + o) (bytesLE v 1))
  | _ + 1, .store32 o, v :: a :: st, ls, s => Out.ofWrite st ls (s.write (a + o) (bytesLE v 4))
  | _ + 1, .store64 o, v :: a :: st, ls, s => Out.ofWrite st ls (s.write (a + o) (bytesLE v 8))
  | _ + 1, .eqz, a :: st, ls, s => .normal ((if a = 0 then 1 else 0) :: st) ls s
  | _ + 1, .wrap, a :: st, ls, s => .normal (w32 a :: st) ls s
  | _ + 1, .bin op, b :: a :: st, ls, s => .normal (op.eval a b :: st) ls s
  | f + 1, .call i, st, ls, s => match fs i with
    | some fn =>
      if fn.params ≤ st.length then
        match execInstrs fs f fn.code.body [] ((st.take fn.params).reverse ++ List.replicate fn.code.locals 0) s with
        | .normal r _ s | .ret r _ s | .br 0 r _ s =>
          if fn.results ≤ r.length then .normal (r.take fn.results ++ st.drop fn.params) ls s else .trap
        | _ => .trap
      else .trap
    | none => .trap
  | _ + 1, .fill, n :: v :: d :: st, ls, s => Out.ofWrite st ls (s.write d (List.replicate n (UInt8.ofNat v)))
  | _ + 1, .load8s o, a :: st, ls, s =>
    Out.ofLoad st ls s ((load s.m (a + o) 1).map fun v => if v < 128 then v else v + 2 ^ 32 - 256)
  | _ + 1, .load16u o, a :: st, ls, s => Out.ofLoad st ls s (load s.m (a + o) 2)
  | _ + 1, .store16 o, v :: a :: st, ls, s => Out.ofWrite st ls (s.write (a + o) (bytesLE v 2))
  | _ + 1, .copy, n :: src :: d :: st, ls, s =>
    if src + n ≤ s.size then Out.ofWrite st ls (s.write d ((List.range n).map fun k => s.mem (src + k))) else .trap
  | _ + 1, .divU, b :: a :: st, ls, s => if w32 b = 0 then .trap else .normal (w32 a / w32 b :: st) ls s
  | _ + 1, _, _, _, _ => .trap
end

/-! ## Code that only reads -/

mutual
def Instr.pure : Instr → Bool
  | .block _ b | .loop _ b => Instr.pures b
  | .if_ _ t e => Instr.pures t && Instr.pures e
  | .br _ | .brIf _ | .ret | .drop | .localGet _ | .localSet _ | .localTee _ | .const _ | .load8u _ | .load32 _
  | .eqz | .bin _ => true
  | _ => false

def Instr.pures : List Instr → Bool
  | [] => true
  | i :: is => Instr.pure i && Instr.pures is
end

def Res.lift (s : Store) : Res → Out
  | .normal st ls => .normal st ls s
  | .br l st ls => .br l st ls s
  | .ret st ls => .ret st ls s
  | .trap => .trap

theorem leave_lift (s : Store) (r : Nat) (st : List Nat) (x : Res) : (x.lift s).leave r st = (leave r st x).lift s := by
  cases x with
  | br l => cases l <;> rfl
  | _ => rfl

theorem pure_sim (fs : Nat → Option Fn) (s : Store) : ∀ f,
    (∀ i st ls, i.pure → execInstr fs f i st ls s = (exec s.m f i st ls).lift s) ∧
    (∀ is st ls, Instr.pures is → execInstrs fs f is st ls s = (execs s.m f is st ls).lift s)
  | 0 => ⟨fun _ _ _ _ => by simp [execInstr, exec, Res.lift], fun _ _ _ _ => by simp [execInstrs, execs, Res.lift]⟩
  | f + 1 => by
    have ih := pure_sim fs s f
    refine ⟨fun i st ls h => ?_, fun is st ls h => ?_⟩
    · cases i with
      | block r b =>
        simp only [Instr.pure] at h
        simp only [execInstr, exec, ih.2 _ _ _ h, leave_lift]
      | loop r b =>
        simp only [Instr.pure] at h
        simp only [execInstr, exec, ih.2 _ _ _ h]
        cases e : execs s.m f b [] ls with
        | br l st' ls' =>
          cases l with
          | zero => simp only [Res.lift]; exact ih.1 _ _ _ (by simp [Instr.pure, h])
          | succ l => rfl
        | _ => rfl
      | if_ r t e =>
        simp only [Instr.pure, Bool.and_eq_true] at h
        cases st with
        | nil => rfl
        | cons c st =>
          simp only [execInstr, exec]
          rw [ih.2 _ _ _ (by split <;> simp [h]), leave_lift]
      | _ =>
        simp only [Instr.pure, Bool.false_eq_true] at h
        all_goals first
          | (cases st with
              | nil => simp only [execInstr, exec]; (repeat' split) <;> simp_all [Res.lift]
              | cons a st => cases st <;> simp only [execInstr, exec, Out.ofLoad] <;> (repeat' split) <;> simp_all [Res.lift])
    · cases is with
      | nil => rfl
      | cons i is =>
        simp only [Instr.pures, Bool.and_eq_true] at h
        simp only [execInstrs, execs, ih.1 _ _ _ h.1]
        cases exec s.m f i st ls with
        | normal st' ls' => exact ih.2 _ _ _ h.2
        | _ => rfl

/-- A call to a function whose code only reads returns what `Semantics.lean`'s `call` gives. -/
theorem mcall_pure {fs : Nat → Option Fn} {i : Nat} {fn : Fn} (hf : fs i = some fn)
    (hp : Instr.pures fn.code.body = true) (hres : fn.results = 1) {args st ls : List Nat} {s : Store} {f v : Nat}
    (hpar : fn.params = args.length) (h : call s.m f fn.code args = some v) :
    execInstr fs (f + 1) (.call i) (args.reverse ++ st) ls s = .normal (v :: st) ls s := by
  have ht : (args.reverse ++ st).take fn.params = args.reverse := by simp [hpar]
  have hd : (args.reverse ++ st).drop fn.params = st := by simp [hpar]
  simp only [execInstr, hf, ht, hd, List.reverse_reverse, show fn.params ≤ (args.reverse ++ st).length by simp [hpar],
    ↓reduceIte, (pure_sim fs s f).2 _ _ _ hp, hres]
  unfold call at h
  split at h <;> simp_all [Res.lift]

/-- `simp` over straight-line steps: every equation of `execInstr` but the loop's and the call's. -/
syntax "msimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| msimp) => `(tactic| simp [execInstrs, execInstr.eq_1, execInstr.eq_2, execInstr.eq_4, execInstr.eq_5, execInstr.eq_6, execInstr.eq_7, execInstr.eq_8, execInstr.eq_9, execInstr.eq_10, execInstr.eq_11, execInstr.eq_12, execInstr.eq_13, execInstr.eq_14, execInstr.eq_15, execInstr.eq_16, execInstr.eq_17, execInstr.eq_18, execInstr.eq_19, execInstr.eq_20, execInstr.eq_21, execInstr.eq_22, execInstr.eq_23, execInstr.eq_24, execInstr.eq_25, execInstr.eq_26, execInstr.eq_28, execInstr.eq_29, execInstr.eq_30, execInstr.eq_31, execInstr.eq_32, execInstr.eq_33, execInstr.eq_34, Out.leave, Out.ofLoad, Out.ofWrite, BinOp.eval, addW.spec])
  | `(tactic| msimp [$ls,*]) => `(tactic| simp [execInstrs, execInstr.eq_1, execInstr.eq_2, execInstr.eq_4, execInstr.eq_5, execInstr.eq_6, execInstr.eq_7, execInstr.eq_8, execInstr.eq_9, execInstr.eq_10, execInstr.eq_11, execInstr.eq_12, execInstr.eq_13, execInstr.eq_14, execInstr.eq_15, execInstr.eq_16, execInstr.eq_17, execInstr.eq_18, execInstr.eq_19, execInstr.eq_20, execInstr.eq_21, execInstr.eq_22, execInstr.eq_23, execInstr.eq_24, execInstr.eq_25, execInstr.eq_26, execInstr.eq_28, execInstr.eq_29, execInstr.eq_30, execInstr.eq_31, execInstr.eq_32, execInstr.eq_33, execInstr.eq_34, Out.leave, Out.ofLoad, Out.ofWrite, BinOp.eval, addW.spec, $ls,*])

end WasmCode
