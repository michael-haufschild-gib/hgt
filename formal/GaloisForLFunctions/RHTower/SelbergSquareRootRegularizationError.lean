import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Uniform scalar error of the square-root spectral weight

A difference-of-squares identity controls sqrt(d)-d/sqrt(d+e²) by e/2 for every
nonnegative d and positive e, including d=0. The bound is uniform in source size.
-/

namespace GaloisForLFunctions.RHTower.SelbergSquareRootRegularizationError

/-- Adding a regulator square can only increase the real square root. -/
theorem sqrt_le_regularized (d e : ℝ) :
    Real.sqrt d ≤ Real.sqrt (d + e ^ 2) :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg e))

/-- Positive square-root regularization differs from the unregularized root by at most the regulator. -/
theorem regularized_le_sqrt_add {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e) :
    Real.sqrt (d + e ^ 2) ≤ Real.sqrt d + e := by
  have h1 := Real.sq_sqrt hd
  have h2 := Real.sq_sqrt (add_nonneg hd (sq_nonneg e))
  have h3 := Real.sqrt_nonneg d
  have h4 := Real.sqrt_nonneg (d + e ^ 2)
  nlinarith [mul_nonneg h3 he]

/-- The inverse-radius weighted square is bounded by its original square root. -/
theorem weighted_sqrt_le {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e) :
    d / Real.sqrt (d + e ^ 2) ≤ Real.sqrt d := by
  have hr := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hd (sq_pos_of_pos he))
  apply (div_le_iff₀ hr).mpr
  have h := mul_le_mul_of_nonneg_left (sqrt_le_regularized d e) (Real.sqrt_nonneg d)
  nlinarith [Real.sq_sqrt hd]

/-- Exact difference-of-squares control gives uniform spectral-weight error at most half the regulator. -/
theorem weighted_sqrt_error_le_half {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e) :
    Real.sqrt d - d / Real.sqrt (d + e ^ 2) ≤ e / 2 := by
  let a := Real.sqrt d
  let r := Real.sqrt (d + e ^ 2)
  have ha : 0 ≤ a := Real.sqrt_nonneg d
  have hr : 0 < r := Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos hd (sq_pos_of_pos he))
  have ha2 : a ^ 2 = d := Real.sq_sqrt hd
  have hr2 : r ^ 2 = d + e ^ 2 := Real.sq_sqrt (add_nonneg hd (sq_nonneg e))
  have hden : 0 < r * (r + a) := mul_pos hr (add_pos_of_pos_of_nonneg hr ha)
  have hid : (a - d / r) * (r * (r + a)) = a * e ^ 2 := by
    field_simp
    nlinarith [congrArg (fun t => a * t) hr2, congrArg (fun t => r * t) ha2]
  have hb : 2 * a * e ≤ r * (r + a) := by
    nlinarith [sq_nonneg (a - e), mul_nonneg ha hr.le]
  change a - d / r ≤ e / 2
  apply (mul_le_mul_iff_left₀ hden).mp
  rw [hid]
  nlinarith only [mul_le_mul_of_nonneg_right hb he.le]

/-- The spectral-weight regularization error is nonnegative, including at original zeros. -/
theorem weighted_sqrt_error_nonneg {d e : ℝ} (hd : 0 ≤ d) (he : 0 < e) :
    0 ≤ Real.sqrt d - d / Real.sqrt (d + e ^ 2) := sub_nonneg.mpr (weighted_sqrt_le hd he)

end GaloisForLFunctions.RHTower.SelbergSquareRootRegularizationError
