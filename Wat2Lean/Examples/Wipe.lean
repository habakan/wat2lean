import Wat2Lean.Machine

/-!
# Example proof: wiping a memory range

The loop zeroes `n` bytes from `a` and preserves every other byte (`wipe_call`).
-/

namespace WasmCode.Examples
open WasmCode WasmCode.Instr

private theorem w32_lt {n : Nat} (h : n < 2 ^ 32) : w32 n = n := Nat.mod_eq_of_lt h

def wipeCode : Func :=
  ⟨0, [.loop 0 [.localGet 1,
    .if_ 0 [.localGet 0, .const 0, .store8 0,
      .localGet 0, .const 1, .bin .add, .localSet 0,
      .localGet 1, .const 1, .bin .sub, .localSet 1, .br 1] []]]⟩

def wipeStore (s : Store) (a n : Nat) : Store :=
  { s with mem := fun x => if a ≤ x ∧ x < a + n then 0 else s.mem x }

def wipeLoop : List Instr :=
  [localGet 1, if_ 0 [localGet 0, const 0, store8 0, localGet 0, const 1, bin .add, localSet 0, localGet 1, const 1,
    bin .sub, localSet 1, br 1] []]

theorem wipeCode_eq : wipeCode = ⟨0, [loop 0 wipeLoop]⟩ := rfl

theorem wloop_run (fs : Nat → Option Fn) :
    ∀ n a F (s : Store), a + n ≤ s.size → s.size < 2 ^ 32 → 30 + n ≤ F →
      execInstr fs F (loop 0 wipeLoop) [] [a, n] s = .normal [] [a + n, 0] (wipeStore s a n)
  | 0, a, F, s, _, _, hF => by
    obtain ⟨g, rfl⟩ : ∃ g, F = g + 30 := ⟨F - 30, by omega⟩
    rw [show g + 30 = (g + 29) + 1 by omega]
    have : ∀ x, ¬(a ≤ x ∧ x < a) := by omega
    rw [execInstr.eq_3]
    msimp [wipeLoop, wipeStore, this]
  | n + 1, a, F, s, ha, hs', hF => by
    obtain ⟨g, rfl⟩ : ∃ g, F = g + n + 31 := ⟨F - 31 - n, by omega⟩
    have hw : s.write a (bytesLE 0 1) = some { s with mem := fun x => if a ≤ x ∧ x < a + 1 then 0 else s.mem x } := by
      simp only [Store.write, bytesLE, List.length_map, List.length_range, show a + 1 ≤ s.size by omega, ↓reduceIte,
        Option.some.injEq, Store.mk.injEq, and_true]
      funext x; split
      · generalize x - a = k; cases k <;> simp
      · rfl
    have ih := wloop_run fs n (a + 1) (g + n + 30) { s with mem := fun x => if a ≤ x ∧ x < a + 1 then 0 else s.mem x }
      (by simp; omega) (by simpa using hs') (by omega)
    have e1 : w32 (a + 1) = a + 1 := w32_lt (n := a + 1) (by omega)
    have e2 : subW.f (n + 1) 1 = n := by rw [subW.spec]; simp only [w32]; omega
    rw [show g + n + 31 = (g + n + 30) + 1 by omega]
    rw [execInstr.eq_3]
    msimp [wipeLoop, hw, e1, e2]
    rw [show a + (n + 1) = a + 1 + n by omega, ← wipeLoop, ih]
    simp only [wipeStore, Out.normal.injEq, true_and]
    congr 1; funext x
    repeat' split
    all_goals first | rfl | omega

theorem wipe_call {fs : Nat → Option Fn} {i : Nat} (hf : fs i = some ⟨2, 0, wipeCode⟩) {a n f : Nat} {st ls : List Nat}
    {s : Store} (ha : a + n ≤ s.size) (hs : s.size < 2 ^ 32) :
    execInstr fs (f + n + 40) (.call i) (n :: a :: st) ls s = .normal st ls (wipeStore s a n) := by
  have h := wloop_run fs n a (f + n + 38) s ha hs (by omega)
  rw [show f + n + 40 = (f + n + 39) + 1 by omega]
  simp only [execInstr.eq_27, hf, wipeCode_eq]
  msimp [h]

end WasmCode.Examples
