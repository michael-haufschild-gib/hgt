import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Quadratic radial error of the logarithmic circle kernel

For a unit complex number `w`, the squared radial chord is
`r |1-w|²+(1-r)²`. Removing half the logarithm of `r` from the logarithmic
kernel leaves an exact logarithmic remainder. Its size is bounded by a
quadratic radial factor times the inverse squared chord length.
-/

noncomputable section
open Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- Radial displacement splits into tangential and normal squared lengths. -/
theorem radial_chord_sq (r : ℝ) (w : ℂ) (hw : ‖w‖ = 1) :
    ‖1 - (r : ℂ) * w‖ ^ 2 = r * ‖1 - w‖ ^ 2 + (1 - r) ^ 2 := by
  have hs : w.re ^ 2 + w.im ^ 2 = 1 := by
    simpa only [Complex.normSq_apply, pow_two, hw, one_mul] using
      (Complex.normSq_eq_norm_sq w)
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  linear_combination (r^2-r)*hs

/-- The remainder at positive radius `r` and nonzero squared chord `d`. -/
def radialChordError (r d : ℝ) : ℝ := Real.log (1 + (1-r)^2 / (r*d)) / 2

/-- Positivity and the explicit quadratic upper bound. -/
theorem radialChordError_bounds (r d : ℝ) (hr : 0 < r) (hd : 0 < d) :
    0 ≤ radialChordError r d ∧ radialChordError r d ≤ (1-r)^2 / (2*r*d) := by
  have hu : 0 ≤ (1-r)^2 / (r*d) := div_nonneg (sq_nonneg _) (mul_pos hr hd).le
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1 + (1-r)^2 / (r*d) by linarith)
  constructor
  · exact div_nonneg (Real.log_nonneg (by linarith)) (by norm_num)
  · dsimp [radialChordError]
    calc Real.log (1 + (1-r)^2 / (r*d)) / 2 ≤ ((1-r)^2 / (r*d)) / 2 := by linarith
      _ = (1-r)^2 / (2*r*d) := by ring

/-- The universal radial term is the only term of first order at radius one. -/
theorem radial_log_chord (r : ℝ) (hr : 0 < r) (w : ℂ)
    (hw : ‖w‖ = 1) (hne : w ≠ 1) :
    -Real.log ‖1 - (r : ℂ)*w‖ + Real.log r / 2 + Real.log ‖1-w‖ =
      -radialChordError r (‖1-w‖^2) := by
  have hd : 0 < ‖1-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have hd2 : 0 < ‖1-w‖^2 := sq_pos_of_pos hd
  have hu : 0 ≤ (1-r)^2 / (r*‖1-w‖^2) := div_nonneg (sq_nonneg _) (mul_pos hr hd2).le
  have hf : ‖1-(r:ℂ)*w‖^2 = r * ‖1-w‖^2 * (1+(1-r)^2/(r*‖1-w‖^2)) := by
    rw [radial_chord_sq r w hw]
    field_simp [hr.ne', hd.ne']
  have hl := congrArg Real.log hf
  rw [Real.log_pow, Real.log_mul (mul_pos hr hd2).ne' (by linarith),
    Real.log_mul hr.ne' hd2.ne', Real.log_pow] at hl
  dsimp [radialChordError]
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

#print axioms radial_chord_sq
#print axioms radialChordError_bounds
#print axioms radial_log_chord
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
