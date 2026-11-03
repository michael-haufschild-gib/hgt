import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Exact jump moments of an odd cubic window

The continuous odd source `x max(1−4x²,0)` has unit support length. Its positive-lag
correlation is a polynomial of degree seven. Exact logarithmic and polynomial
jump moments allow comparison with both bounds for the Gamma jump kernel.
-/

noncomputable section
open Real MeasureTheory Set intervalIntegral
namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- An odd continuous cubic supported on the unit window. -/
def cubicWindow (x : ℝ) : ℝ := x * max (1 - 4 * x ^ 2) 0

theorem continuous_cubicWindow : Continuous cubicWindow := by
  unfold cubicWindow
  fun_prop

theorem cubicWindow_inside {x : ℝ} (hl : -(1 / 2 : ℝ) ≤ x) (hr : x ≤ 1 / 2) :
    cubicWindow x = x * (1 - 4 * x ^ 2) := by
  unfold cubicWindow
  rw [max_eq_left]
  nlinarith only [mul_nonneg (by linarith : 0 ≤ x + 1 / 2)
    (by linarith : 0 ≤ 1 / 2 - x)]

theorem cubicWindow_outside {x : ℝ} (hx : x ∉ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    cubicWindow x = 0 := by
  have h : 1 - 4 * x ^ 2 ≤ 0 := by
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · nlinarith only [hx, sq_nonneg (x + 1 / 2)]
    · nlinarith only [hx, sq_nonneg (x - 1 / 2)]
  simp only [cubicWindow, max_eq_right h, mul_zero]

theorem compact_cubicWindow : HasCompactSupport cubicWindow :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => cubicWindow_outside hx)

theorem cubicWindow_odd (x : ℝ) : cubicWindow (-x) = -cubicWindow x := by
  simp only [cubicWindow, neg_sq, neg_mul]

/-- Positive-lag correlation of the cubic for `0 ≤ t ≤ 1`. -/
def cubicCorrPoly (t : ℝ) : ℝ :=
  2 / 105 - 2 / 5 * t ^ 2 + 2 / 3 * t ^ 3 - 2 / 5 * t ^ 5 + 4 / 35 * t ^ 7

private def cubicCorrAnti (t x : ℝ) : ℝ :=
  16 * x ^ 7 / 7 + 8 * t * x ^ 6 + (48 * t ^ 2 - 8) * x ^ 5 / 5 +
  (4 * t ^ 3 - 4 * t) * x ^ 4 + (1 - 12 * t ^ 2) * x ^ 3 / 3 +
  (t - 4 * t ^ 3) * x ^ 2 / 2

private theorem deriv_cubicCorrAnti (t x : ℝ) :
    HasDerivAt (cubicCorrAnti t)
      (x * (1 - 4 * x ^ 2) * ((x + t) * (1 - 4 * (x + t) ^ 2))) x := by
  have h1 := ((hasDerivAt_pow 7 x).const_mul 16).div_const 7
  have h2 := (hasDerivAt_pow 6 x).const_mul (8 * t)
  have h3 := ((hasDerivAt_pow 5 x).const_mul (48 * t ^ 2 - 8)).div_const 5
  have h4 := (hasDerivAt_pow 4 x).const_mul (4 * t ^ 3 - 4 * t)
  have h5 := ((hasDerivAt_pow 3 x).const_mul (1 - 12 * t ^ 2)).div_const 3
  have h6 := ((hasDerivAt_pow 2 x).const_mul (t - 4 * t ^ 3)).div_const 2
  have h := ((((h1.add h2).add h3).add h4).add h5).add h6
  exact h.congr_deriv (by ring)

/-- Integrating over the overlap gives the exact correlation polynomial. -/
theorem cubicWindow_autocorr {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x, cubicWindow x * cubicWindow (x + t)) = cubicCorrPoly t := by
  have he : (fun x => cubicWindow x * cubicWindow (x + t)) =
      (Icc (-(1 / 2 : ℝ)) (1 / 2 - t)).indicator
        (fun x => x * (1 - 4 * x ^ 2) * ((x + t) * (1 - 4 * (x + t) ^ 2))) := by
    funext x
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2 - t)
    · rw [indicator_of_mem hx, cubicWindow_inside hx.1 (by linarith [hx.2]),
        cubicWindow_inside (by linarith [hx.1]) (by linarith [hx.2])]
    · rw [indicator_of_notMem hx]
      by_cases hl : x < -(1 / 2 : ℝ)
      · rw [cubicWindow_outside (by simp only [mem_Icc]; intro h; linarith [h.1]), zero_mul]
      · have hr : 1 / 2 < x + t := by
          have := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          linarith
        rw [cubicWindow_outside (x := x + t)
          (by simp only [mem_Icc]; intro h; linarith [h.2]), mul_zero]
  rw [he, MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(1 / 2 : ℝ) ≤ 1 / 2 - t)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => deriv_cubicCorrAnti t x)
    ((by fun_prop : Continuous (fun x : ℝ => x * (1 - 4 * x ^ 2) *
      ((x + t) * (1 - 4 * (x + t) ^ 2)))).intervalIntegrable _ _)]
  unfold cubicCorrAnti cubicCorrPoly
  ring


/-- The cubic's correlation vanishes beyond its unit support length. -/
theorem cubicWindow_autocorr_tail {t : ℝ} (ht : 1 < t) :
    (∫ x, cubicWindow x * cubicWindow (x + t)) = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall fun x => by
    change cubicWindow x * cubicWindow (x + t) = 0
    by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
    · rw [cubicWindow_outside (x := x + t)
        (by intro h; linarith only [hx.1, h.2, ht]), mul_zero]
    · rw [cubicWindow_outside hx, zero_mul]

/-- The mass of the cubic on a unit window. -/
theorem cubicWindow_mass : (∫ x, cubicWindow x ^ 2) = 2 / 105 := by
  have h := cubicWindow_autocorr (t := 0) le_rfl (by norm_num)
  simpa [cubicCorrPoly, sq] using h

private def cubicLagQuotient (t : ℝ) : ℝ :=
  2 / 5 * t - 2 / 3 * t ^ 2 + 2 / 5 * t ^ 4 - 4 / 35 * t ^ 6

private theorem cubicCorrPoly_deficit (t : ℝ) :
    2 / 105 - cubicCorrPoly t = t * cubicLagQuotient t := by
  unfold cubicCorrPoly cubicLagQuotient
  ring

private theorem integral_cubicLagQuotient :
    (∫ t in (0 : ℝ)..1, cubicLagQuotient t) = 457 / 11025 := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ => s ^ 2 / 5 - 2 * s ^ 3 / 9 + 2 * s ^ 5 / 25 -
        4 * s ^ 7 / 245) (cubicLagQuotient t) t := by
    have h1 := (hasDerivAt_pow 2 t).div_const 5
    have h2 := ((hasDerivAt_pow 3 t).const_mul 2).div_const 9
    have h3 := ((hasDerivAt_pow 5 t).const_mul 2).div_const 25
    have h4 := ((hasDerivAt_pow 7 t).const_mul 4).div_const 245
    exact (((h1.sub h2).add h3).sub h4).congr_deriv (by unfold cubicLagQuotient; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by unfold cubicLagQuotient; fun_prop : Continuous cubicLagQuotient).intervalIntegrable _ _)]
  norm_num

/-- The logarithmic jump quotient is exactly `457/210` times the mass. -/
theorem cubicWindow_logarithmic_integral :
    (∫ t in Ioc (0 : ℝ) 1, (2 / 105 - cubicCorrPoly t) / t) = 457 / 11025 := by
  have he : (∫ t in Ioc (0 : ℝ) 1, (2 / 105 - cubicCorrPoly t) / t) =
      ∫ t in Ioc (0 : ℝ) 1, cubicLagQuotient t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    change (2 / 105 - cubicCorrPoly t) / t = cubicLagQuotient t
    rw [cubicCorrPoly_deficit, mul_div_cancel_left₀ _ ht.1.ne']
  rw [he, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact integral_cubicLagQuotient

/-- The apparent singularity of the logarithmic deficit is removable at zero. -/
theorem integrableOn_cubicWindow_logarithmic_deficit :
    IntegrableOn (fun t : ℝ => (2 / 105 - cubicCorrPoly t) / t) (Ioc (0 : ℝ) 1) := by
  have hc : Continuous cubicLagQuotient := by unfold cubicLagQuotient; fun_prop
  refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [cubicCorrPoly_deficit, mul_div_cancel_left₀ _ ht.1.ne']

/-- Oddness cancels the correlation over all positive lags. -/
theorem integral_cubicCorrPoly :
    (∫ t in (0 : ℝ)..1, cubicCorrPoly t) = 0 := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ => 2 * s / 105 - 2 * s ^ 3 / 15 + s ^ 4 / 6 -
        s ^ 6 / 15 + s ^ 8 / 70) (cubicCorrPoly t) t := by
    have h1 := ((hasDerivAt_id' t).const_mul 2).div_const 105
    have h2 := ((hasDerivAt_pow 3 t).const_mul 2).div_const 15
    have h3 := (hasDerivAt_pow 4 t).div_const 6
    have h4 := (hasDerivAt_pow 6 t).div_const 15
    have h5 := (hasDerivAt_pow 8 t).div_const 70
    exact ((((h1.sub h2).add h3).sub h4).add h5).congr_deriv (by unfold cubicCorrPoly; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by unfold cubicCorrPoly; fun_prop : Continuous cubicCorrPoly).intervalIntegrable _ _)]
  norm_num

/-- First moment of the cubic's jump deficit. -/
theorem cubicWindow_jump_first_moment :
    (∫ t in (0 : ℝ)..1, t * (2 / 105 - cubicCorrPoly t)) = 1 / 90 := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ => s ^ 4 / 10 - 2 * s ^ 5 / 15 + 2 * s ^ 7 / 35 -
        4 * s ^ 9 / 315) (t * (2 / 105 - cubicCorrPoly t)) t := by
    have h1 := (hasDerivAt_pow 4 t).div_const 10
    have h2 := ((hasDerivAt_pow 5 t).const_mul 2).div_const 15
    have h3 := ((hasDerivAt_pow 7 t).const_mul 2).div_const 35
    have h4 := ((hasDerivAt_pow 9 t).const_mul 4).div_const 315
    exact (((h1.sub h2).add h3).sub h4).congr_deriv (by unfold cubicCorrPoly; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by unfold cubicCorrPoly; fun_prop : Continuous (fun t : ℝ =>
      t * (2 / 105 - cubicCorrPoly t))).intervalIntegrable _ _)]
  norm_num

/-- Second moment of the cubic's jump deficit. -/
theorem cubicWindow_jump_second_moment :
    (∫ t in (0 : ℝ)..1, t ^ 2 * (2 / 105 - cubicCorrPoly t)) = 47 / 6300 := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun s : ℝ => 2 * s ^ 5 / 25 - s ^ 6 / 9 + s ^ 8 / 20 -
        2 * s ^ 10 / 175) (t ^ 2 * (2 / 105 - cubicCorrPoly t)) t := by
    have h1 := ((hasDerivAt_pow 5 t).const_mul 2).div_const 25
    have h2 := (hasDerivAt_pow 6 t).div_const 9
    have h3 := (hasDerivAt_pow 8 t).div_const 20
    have h4 := ((hasDerivAt_pow 10 t).const_mul 2).div_const 175
    exact (((h1.sub h2).add h3).sub h4).congr_deriv (by unfold cubicCorrPoly; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
    ((by unfold cubicCorrPoly; fun_prop : Continuous (fun t : ℝ =>
      t ^ 2 * (2 / 105 - cubicCorrPoly t))).intervalIntegrable _ _)]
  norm_num

end GaloisForLFunctions.WindowTowerOfSpecZ
