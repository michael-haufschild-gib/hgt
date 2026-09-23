/-
# The critical-curve slice: a formalized bracket of the transition angle at modulus ≈ 3

The deliverable of the slice program: two parameters of modulus ≈ 3 in the second quadrant,
STRICTLY ordered by `Complex.arg`, about half a degree apart —

* `bv = −273/100 + (156/125)·I`   (`arg ≈ 155.43°`) — VIABLE: the closed unit disk escapes
  (`slice_viable_155`, a 461-node square-tree certificate);
* `bo = −2759/1024 + (77/64)·I`   (`arg ≈ 155.94°`) — OBSTRUCTED: `K_b` meets the closed unit
  disk (`slice_obstructed_156`, an exact-rational P1 instance).

Together with the closed-form sectors (`U0CurveSectors`: viable past `90°`, obstructed on the
Cassini region up to `180°`) and the intermediate grid verdicts (`slice_viable_105/125/140/150`,
`slice_obstructed_161/165/169/176/180`), this brackets the transition angle `θ*` of the
critical curve `ρ(arg b)` on the modulus-3 circle inside `(155.43°, 155.94°)` — the first
machine-checked slice of the curve.

The `arg` ordering is genuine (`Complex.arg`), certified through squared rational data in the
second quadrant (`arg_lt_arg_Q2`: arcsin monotonicity + a cross-multiplied tangent comparison).
-/
import GaloisForLFunctions.U0.U0SliceViableA
import GaloisForLFunctions.U0.U0SliceViableB
import GaloisForLFunctions.U0.U0DichotomySliceObstructed
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex Set Bottcher

namespace U0DichotomySlice

set_option maxHeartbeats 1600000

/-- Argument comparison in the second quadrant from squared rational data:
`o.im²·‖v‖² < v.im²·‖o‖²` (cross-multiplied tangents) gives `arg v < arg o`. -/
theorem arg_lt_arg_Q2 {v o : ℂ} (hvre : v.re < 0) (hvim : 0 < v.im)
    (hore : o.re < 0) (hoim : 0 < o.im)
    (hcross : o.im ^ (2 : ℕ) * (v.re ^ (2 : ℕ) + v.im ^ (2 : ℕ)) < v.im ^ (2 : ℕ) * (o.re ^ (2 : ℕ) + o.im ^ (2 : ℕ))) :
    v.arg < o.arg := by
  have hv0 : v ≠ 0 := fun h => by rw [h] at hvre; simp at hvre
  have ho0 : o ≠ 0 := fun h => by rw [h] at hore; simp at hore
  have hvn : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  have hon : (0 : ℝ) < ‖o‖ := norm_pos_iff.mpr ho0
  have hvsq : ‖v‖ ^ (2 : ℕ) = v.re ^ (2 : ℕ) + v.im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hosq : ‖o‖ ^ (2 : ℕ) = o.re ^ (2 : ℕ) + o.im ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hcross' : o.im * ‖v‖ < v.im * ‖o‖ := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hvim hon, mul_pos hoim hvn, hcross, hvsq, hosq,
      mul_self_le_mul_self (mul_nonneg hvim.le hon.le) hcon]
  have hdiv : (-v).im / ‖v‖ < (-o).im / ‖o‖ := by
    rw [Complex.neg_im, Complex.neg_im, div_lt_div_iff₀ hvn hon]
    nlinarith [hcross']
  have hvim_le : v.im ≤ ‖v‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm v)
  have h1 : -1 ≤ (-v).im / ‖v‖ := by
    rw [Complex.neg_im, neg_div]
    have : v.im / ‖v‖ ≤ 1 := by
      rw [div_le_one hvn]
      exact hvim_le
    linarith
  have h3 : (-o).im / ‖o‖ ≤ 1 := by
    rw [Complex.neg_im, neg_div]
    have : (0 : ℝ) ≤ o.im / ‖o‖ := div_nonneg hoim.le hon.le
    linarith
  rw [Complex.arg_of_re_neg_of_im_nonneg hvre hvim.le,
    Complex.arg_of_re_neg_of_im_nonneg hore hoim.le]
  have := Real.arcsin_lt_arcsin h1 hdiv h3
  linarith

/-- **The critical-curve bracket at modulus ≈ 3.**  Two parameters in the second quadrant,
strictly ordered by `Complex.arg` and ≈ 0.51° apart, with opposite machine-checked verdicts:
the transition angle of `ρ(arg b)` on the modulus-3 circle lies strictly between them. -/
theorem critical_curve_bracket :
    ∃ bv bo : ℂ,
      bv.arg < bo.arg ∧
      ‖bv‖ ^ (2 : ℕ) = 2252601 / 250000 ∧ ‖bo‖ ^ (2 : ℕ) = 9129905 / 1048576 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → z ∉ filledJulia bv) ∧
      (∃ x : ℂ, ‖x‖ ≤ 1 ∧ x ∈ filledJulia bo) := by
  refine ⟨(⟨(-273/100), (156/125)⟩ : ℂ), (⟨-(2759/1024), (77/64)⟩ : ℂ),
    ?_, ?_, ?_, slice_viable_155, slice_obstructed_156⟩
  · exact arg_lt_arg_Q2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num
  · rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    norm_num

end U0DichotomySlice
