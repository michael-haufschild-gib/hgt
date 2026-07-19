import GaloisForLFunctions.HTGeometry.OrthoNoCommonRoot

/-!
# Sign alternation at the roots

At a root of `Q_{n+1}` the three-term recurrence collapses to `Q_{n+2} = −bₙ Qₙ`, and
`bₙ = h_{n+1}/hₙ` is positive.  Since `Qₙ` cannot also vanish there, the neighbours `Qₙ` and
`Q_{n+2}` take strictly opposite signs at every root of `Q_{n+1}`.

This is the Sturm-sequence property, the mechanism behind interlacing of the zeros.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

theorem recurOff_pos (h : PositiveMomentForm s) (n : ℕ) : 0 < recurOff s n :=
  div_pos (monicOrtho_inner_self_pos h (n + 1)) (monicOrtho_inner_self_pos h n)

/-- At a root of `Q_{n+1}` the recurrence collapses. -/
theorem monicOrtho_eval_succ_succ_of_root (h : PositiveMomentForm s) (n : ℕ) {x : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0) :
    (monicOrtho s (n + 2)).eval x = -recurOff s n * (monicOrtho s n).eval x := by
  rw [monicOrtho_succ_succ_eval h n x, hx, mul_zero, zero_sub]
  ring

/-- **Sturm alternation.**  At every root of `Q_{n+1}` the neighbours `Qₙ` and `Q_{n+2}` have
strictly opposite signs. -/
theorem monicOrtho_eval_mul_neg_of_root (h : PositiveMomentForm s) (n : ℕ) {x : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0) :
    (monicOrtho s (n + 2)).eval x * (monicOrtho s n).eval x < 0 := by
  have hne : (monicOrtho s n).eval x ≠ 0 := fun h0 =>
    monicOrtho_succ_no_common_root h n h0 hx
  have hsq : 0 < (monicOrtho s n).eval x ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne))
  rw [monicOrtho_eval_succ_succ_of_root h n hx]
  nlinarith [mul_pos (recurOff_pos h n) hsq]

/-- Neither neighbour vanishes at a root of `Q_{n+1}`. -/
theorem monicOrtho_eval_succ_succ_ne_zero (h : PositiveMomentForm s) (n : ℕ) {x : ℝ}
    (hx : (monicOrtho s (n + 1)).eval x = 0) :
    (monicOrtho s (n + 2)).eval x ≠ 0 := by
  intro h0
  have hneg := monicOrtho_eval_mul_neg_of_root h n hx
  rw [h0, zero_mul] at hneg
  exact lt_irrefl 0 hneg

end HTGeometry
