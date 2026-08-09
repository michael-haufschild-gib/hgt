import Mathlib

/-!
# The inverse square root at an endpoint

`(t-1)^{-1/2}` is not bounded at `t = 1` but is integrable there, and its primitive
`2 sqrt(x-1)` is continuous up to the endpoint.  The exact value of the endpoint integral is the
atom behind every second-order expansion of a Liouville–Green phase near a turning point: the phase
is the integral of a smooth function against this weight, so its leading behaviour is `2 g(1)
sqrt(x-1)`.

The fundamental theorem is applied in the form that only needs the derivative on the open interval,
since at the endpoint there is none.
-/

noncomputable section

open MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

theorem rpow_neg_half_eq_inv_sqrt {t : ℝ} (ht : 0 ≤ t) :
    t ^ (-(1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul ht]
  norm_num

theorem hasDerivAt_two_mul_sqrt_sub_one {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => 2 * Real.sqrt (u - 1)) ((t - 1) ^ (-(1 : ℝ) / 2)) t := by
  have hpos : (0 : ℝ) < t - 1 := by linarith
  have hne : t - 1 ≠ 0 := ne_of_gt hpos
  have hinner : HasDerivAt (fun u : ℝ => u - 1) 1 t := (hasDerivAt_id t).sub_const 1
  have hsqrt : HasDerivAt (fun u : ℝ => Real.sqrt (u - 1))
      (1 / (2 * Real.sqrt (t - 1)) * 1) t :=
    (Real.hasDerivAt_sqrt hne).comp t hinner
  have h := hsqrt.const_mul (2 : ℝ)
  have hval : (2 : ℝ) * (1 / (2 * Real.sqrt (t - 1)) * 1) = (t - 1) ^ (-(1 : ℝ) / 2) := by
    rw [rpow_neg_half_eq_inv_sqrt hpos.le]
    have hs : 0 < Real.sqrt (t - 1) := Real.sqrt_pos.mpr hpos
    field_simp
  rwa [hval] at h

/-- **The endpoint integral.**  `int_1^x (t-1)^{-1/2} dt = 2 sqrt(x-1)`. -/
theorem integral_rpow_neg_half_sub_one {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, (t - 1) ^ (-(1 : ℝ) / 2)) = 2 * Real.sqrt (x - 1) := by
  have hint : IntervalIntegrable (fun t : ℝ => (t - 1) ^ (-(1 : ℝ) / 2)) volume 1 x := by
    have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) volume 0 (x - 1) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h := hbase.comp_sub_right 1
    simpa using h
  have hcont : ContinuousOn (fun u : ℝ => 2 * Real.sqrt (u - 1)) (Icc 1 x) := by fun_prop
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
      HasDerivWithinAt (fun u : ℝ => 2 * Real.sqrt (u - 1)) ((t - 1) ^ (-(1 : ℝ) / 2)) (Ioi t) t :=
    fun t ht => (hasDerivAt_two_mul_sqrt_sub_one ht.1).hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx hcont hderiv hint
  simpa using h

theorem hasDerivAt_rpow_three_quarters_sub_one {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => (4 / 3) * (u - 1) ^ ((3 : ℝ) / 4))
      ((t - 1) ^ (-(1 : ℝ) / 4)) t := by
  have hpos : (0 : ℝ) < t - 1 := by linarith
  have hne : t - 1 ≠ 0 := ne_of_gt hpos
  have hinner : HasDerivAt (fun u : ℝ => u - 1) 1 t := (hasDerivAt_id t).sub_const 1
  have hrpow : HasDerivAt (fun y : ℝ => y ^ ((3 : ℝ) / 4))
      ((3 / 4) * (t - 1) ^ ((3 : ℝ) / 4 - 1)) (t - 1) :=
    Real.hasDerivAt_rpow_const (Or.inl hne)
  have hcomp := hrpow.comp t hinner
  have h := hcomp.const_mul (4 / 3 : ℝ)
  have hexp : (3 : ℝ) / 4 - 1 = -(1 : ℝ) / 4 := by norm_num
  rw [hexp] at h
  have hval : (4 : ℝ) / 3 * ((3 / 4) * (t - 1) ^ (-(1 : ℝ) / 4) * 1)
      = (t - 1) ^ (-(1 : ℝ) / 4) := by ring
  rw [hval] at h
  exact h

/-- The quarter-power endpoint integral: `int_1^x (t-1)^{-1/4} dt = (4/3)(x-1)^{3/4}`. -/
theorem integral_rpow_neg_quarter_sub_one {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, (t - 1) ^ (-(1 : ℝ) / 4)) = (4 / 3) * (x - 1) ^ ((3 : ℝ) / 4) := by
  have hint : IntervalIntegrable (fun t : ℝ => (t - 1) ^ (-(1 : ℝ) / 4)) volume 1 x := by
    have hbase : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ) / 4)) volume 0 (x - 1) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have h := hbase.comp_sub_right 1
    simpa using h
  have hcont : ContinuousOn (fun u : ℝ => (4 / 3) * (u - 1) ^ ((3 : ℝ) / 4)) (Icc 1 x) := by
    refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ fun u _ => Or.inr (by norm_num))
    exact (continuousOn_id.sub continuousOn_const)
  have hderiv : ∀ t ∈ Ioo (1 : ℝ) x,
      HasDerivWithinAt (fun u : ℝ => (4 / 3) * (u - 1) ^ ((3 : ℝ) / 4))
        ((t - 1) ^ (-(1 : ℝ) / 4)) (Ioi t) t :=
    fun t ht => (hasDerivAt_rpow_three_quarters_sub_one ht.1).hasDerivWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hx hcont hderiv hint
  simpa using h


theorem rpow_neg_quarter_eq_inv_sqrt_sqrt {t : ℝ} (ht : 0 ≤ t) :
    t ^ (-(1 : ℝ) / 4) = (Real.sqrt (Real.sqrt t))⁻¹ := by
  have hs : (0 : ℝ) ≤ Real.sqrt t := Real.sqrt_nonneg t
  rw [Real.sqrt_eq_rpow (Real.sqrt t), Real.sqrt_eq_rpow t, ← Real.rpow_neg_one,
    ← Real.rpow_mul (by positivity), ← Real.rpow_mul ht]
  norm_num


end GaloisForLFunctions.HTGeometry
