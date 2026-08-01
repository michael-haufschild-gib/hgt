import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Long-time averages of oscillating exponentials

The time average of `exp (i a t)` over `[0, T]` is bounded by `2 / (|a| T)`, so it tends to zero
for every nonzero real frequency.  This is the analytic input of Weyl's criterion: a character
with nonzero frequency has vanishing mean along a linear flow.

* `deningerExpAverage_norm_le` : the explicit bound on the average.
* `deningerExpAverage_tendsto_zero` : the average tends to zero.
-/

namespace RHTower

open Filter Topology

section ExpAverage

/-- The time average of an oscillating exponential over `[0, T]`. -/
noncomputable def deningerExpAverage (a : ℝ) (T : ℝ) : ℂ :=
  (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, Complex.exp ((a * t : ℝ) * Complex.I)

/-- **The average is bounded by `2 / (|a| T)`.**  The primitive of the exponential has modulus one
at each endpoint, so the integral is bounded by `2 / |a|`. -/
theorem deningerExpAverage_norm_le {a : ℝ} (ha : a ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖deningerExpAverage a T‖ ≤ 2 / (|a| * T) := by
  have hc : (a : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.ext_iff, ha]
  have hrw : ∀ t : ℝ, Complex.exp ((a * t : ℝ) * Complex.I)
      = Complex.exp (((a : ℂ) * Complex.I) * (t : ℂ)) := by
    intro t
    congr 1
    push_cast
    ring
  have hint : (∫ t in (0 : ℝ)..T, Complex.exp ((a * t : ℝ) * Complex.I))
      = (Complex.exp (((a : ℂ) * Complex.I) * (T : ℂ))
          - Complex.exp (((a : ℂ) * Complex.I) * (0 : ℝ))) / ((a : ℂ) * Complex.I) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      Complex.exp (((a : ℂ) * Complex.I) * (t : ℂ))) fun t _ => hrw t]
    exact integral_exp_mul_complex hc
  have hnum : ‖Complex.exp (((a : ℂ) * Complex.I) * (T : ℂ))
      - Complex.exp (((a : ℂ) * Complex.I) * (0 : ℝ))‖ ≤ 2 := by
    have h1 : ‖Complex.exp (((a : ℂ) * Complex.I) * (T : ℂ))‖ = 1 := by
      rw [show ((a : ℂ) * Complex.I) * (T : ℂ) = ((a * T : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have h2 : ‖Complex.exp (((a : ℂ) * Complex.I) * (0 : ℝ))‖ = 1 := by
      rw [show ((a : ℂ) * Complex.I) * ((0 : ℝ) : ℂ) = ((a * 0 : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    calc ‖Complex.exp (((a : ℂ) * Complex.I) * (T : ℂ))
        - Complex.exp (((a : ℂ) * Complex.I) * (0 : ℝ))‖
        ≤ ‖Complex.exp (((a : ℂ) * Complex.I) * (T : ℂ))‖
          + ‖Complex.exp (((a : ℂ) * Complex.I) * (0 : ℝ))‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num
  have hden : ‖((a : ℂ) * Complex.I)‖ = |a| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [deningerExpAverage, hint, norm_mul, norm_div, hden, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hT]
  have hTinv : (0 : ℝ) ≤ T⁻¹ := (inv_pos.mpr hT).le
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have hle : ‖Complex.exp (((a : ℂ) * Complex.I) * (T : ℂ))
      - Complex.exp (((a : ℂ) * Complex.I) * ((0 : ℝ) : ℂ))‖ / |a| ≤ 2 / |a| := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  have hfin : T⁻¹ * ((2 : ℝ) / |a|) = 2 / (|a| * T) := by
    field_simp
  refine le_trans ?_ (le_of_eq hfin)
  exact mul_le_mul_of_nonneg_left hle hTinv

/-- **The long-time average of an oscillating exponential vanishes.**  This is the analytic input
of Weyl's criterion: a character with nonzero frequency has zero mean along a linear flow. -/
theorem deningerExpAverage_tendsto_zero {a : ℝ} (ha : a ≠ 0) :
    Tendsto (deningerExpAverage a) atTop (nhds 0) := by
  have habs : (0 : ℝ) < |a| := abs_pos.mpr ha
  have hmaj : Tendsto (fun T : ℝ => 2 / (|a| * T)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (Filter.Tendsto.const_mul_atTop habs tendsto_id)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hmaj
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  exact deningerExpAverage_norm_le ha hT

end ExpAverage

end RHTower
