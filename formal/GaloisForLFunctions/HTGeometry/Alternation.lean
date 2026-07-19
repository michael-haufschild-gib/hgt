import GaloisForLFunctions.HTGeometry.SignConstancy

/-!
# Alternation of `Qₙ` across consecutive nodes

At consecutive roots of `Q_{n+1}` the values of `Qₙ` have opposite signs.  The argument runs
entirely
inside one gap: pick an interior point `x`, note that the cofactors at the two endpoints keep their
signs up to `x` (sign constancy on a zero-free interval), and that `Q_{n+1}(x)` factors through both
of them with linear factors of opposite sign.  The confluent identity then transfers the resulting
sign flip from the cofactors to `Qₙ`.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Alternation.**  `Qₙ` takes opposite signs at consecutive nodes. -/
theorem monicOrtho_eval_alternates (h : PositiveMomentForm s) (n : ℕ) (i : Fin n) :
    (monicOrtho s n).eval (gaussNode h n i.castSucc) *
      (monicOrtho s n).eval (gaussNode h n i.succ) < 0 := by
  set a := gaussNode h n i.castSucc with hadef
  set b := gaussNode h n i.succ with hbdef
  have hab : a < b := gaussNode_lt_succ h n i
  obtain ⟨Ga, hGa, hGa0⟩ := exists_cofactor h n (gaussNode_root h n i.castSucc)
  obtain ⟨Gb, hGb, hGb0⟩ := exists_cofactor h n (gaussNode_root h n i.succ)
  set x := (a + b) / 2 with hxdef
  have hax : a < x := by rw [hxdef]; linarith
  have hxb : x < b := by rw [hxdef]; linarith
  -- the cofactors keep their signs up to the interior point
  have h4 : 0 < Ga.eval a * Ga.eval x := by
    refine mul_pos_of_ne_zero_on_Icc hax.le (continuousOn_eval Ga _) fun y hy => ?_
    rcases eq_or_lt_of_le hy.1 with heq | hlt
    · rw [← heq]; exact hGa0
    · exact cofactor_eval_ne_zero hGa
        (monicOrtho_ne_zero_of_mem_gap h n i hlt (lt_of_le_of_lt hy.2 hxb))
  have h5 : 0 < Gb.eval x * Gb.eval b := by
    refine mul_pos_of_ne_zero_on_Icc hxb.le (continuousOn_eval Gb _) fun y hy => ?_
    rcases eq_or_lt_of_le hy.2 with heq | hlt
    · rw [heq]; exact hGb0
    · exact cofactor_eval_ne_zero hGb
        (monicOrtho_ne_zero_of_mem_gap h n i (lt_of_lt_of_le hax hy.1) hlt)
  -- the two factorisations of `Q_{n+1}(x)` have linear factors of opposite sign
  have hfa : (monicOrtho s (n + 1)).eval x = (x - a) * Ga.eval x := by
    rw [hGa]; simp [← hadef]
  have hfb : (monicOrtho s (n + 1)).eval x = (x - b) * Gb.eval x := by
    rw [hGb]; simp [← hbdef]
  have hxne : (monicOrtho s (n + 1)).eval x ≠ 0 :=
    monicOrtho_ne_zero_of_mem_gap h n i hax hxb
  have h6 : Ga.eval x * Gb.eval x < 0 := by
    have hGax : Ga.eval x ≠ 0 := cofactor_eval_ne_zero hGa hxne
    have hGbx : Gb.eval x ≠ 0 := cofactor_eval_ne_zero hGb hxne
    have hlin : (x - a) * Ga.eval x = (x - b) * Gb.eval x := by rw [← hfa, ← hfb]
    have hxa : 0 < x - a := by linarith
    have hxb' : x - b < 0 := by linarith
    rcases lt_trichotomy (Ga.eval x) 0 with hn1 | hz1 | hp1
    · have : 0 < Gb.eval x := by nlinarith
      nlinarith
    · exact absurd hz1 hGax
    · have : Gb.eval x < 0 := by nlinarith
      nlinarith
  -- chain the three sign facts
  have hcof : Ga.eval a * Gb.eval b < 0 := by
    have hprod := mul_pos h4 h5
    nlinarith [hprod, h6]
  have hA := cofactor_mul_monicOrtho_pos h n hGa
  have hB := cofactor_mul_monicOrtho_pos h n hGb
  nlinarith [mul_pos hA hB, hcof]

end HTGeometry
