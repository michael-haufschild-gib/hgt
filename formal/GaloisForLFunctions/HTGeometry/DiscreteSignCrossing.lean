import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The discrete sign-crossing lemma

If a real sequence has opposite (or vanishing) signs at `a < b`, some
consecutive pair in between already has opposite (or vanishing) signs:
otherwise sign is transported along consecutive pairs and `f(a)·f(b) > 0`.
-/

namespace HTGeometry

/-- **Discrete sign crossing**: `f(a)·f(b) ≤ 0` forces a consecutive
crossing `f(m)·f(m+1) ≤ 0` with `a ≤ m < b`. -/
theorem exists_mul_succ_nonpos (f : ℕ → ℝ) {a b : ℕ} (hab : a < b)
    (h : f a * f b ≤ 0) :
    ∃ m, a ≤ m ∧ m < b ∧ f m * f (m + 1) ≤ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  have hclaim : ∀ j, a ≤ j → j ≤ b → 0 < f a * f j := by
    intro j
    induction j with
    | zero =>
      intro haj _
      have ha0 : a = 0 := by omega
      have hstep := hcon 0 (by omega) (by omega)
      have hf0 : f 0 ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hstep
        exact lt_irrefl 0 hstep
      rw [ha0]
      exact mul_self_pos.2 hf0
    | succ j ih =>
      intro haj hjb
      rcases Nat.lt_or_ge j.succ b with hlt | hge
      · rcases Nat.lt_or_ge a (j + 1) with h1 | h2
        · have haj' : a ≤ j := by omega
          have hA := ih haj' (by omega)
          have hB := hcon j haj' (by omega)
          have hfj : f j ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hB
            exact lt_irrefl 0 hB
          have hfj2 : 0 < f j * f j := mul_self_pos.2 hfj
          nlinarith [mul_pos hA hB, hfj2]
        · have ha' : a = j + 1 := by omega
          have hstep := hcon (j + 1) (by omega) hlt
          have hfa : f (j + 1) ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hstep
            exact lt_irrefl 0 hstep
          rw [ha']
          exact mul_self_pos.2 hfa
      · -- j + 1 = b
        have hb' : j + 1 = b := by omega
        rcases Nat.lt_or_ge a (j + 1) with h1 | h2
        · have haj' : a ≤ j := by omega
          have hA := ih haj' (by omega)
          have hB := hcon j haj' (by omega)
          have hfj : f j ≠ 0 := by
            intro h0
            rw [h0, zero_mul] at hB
            exact lt_irrefl 0 hB
          have hfj2 : 0 < f j * f j := mul_self_pos.2 hfj
          nlinarith [mul_pos hA hB, hfj2]
        · omega
  have := hclaim b (le_of_lt hab) le_rfl
  linarith

end HTGeometry
