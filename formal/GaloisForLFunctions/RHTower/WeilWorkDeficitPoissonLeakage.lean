import GaloisForLFunctions.RHTower.WeilConeSpectralCounting
import GaloisForLFunctions.HTGeometry.GammaVerticalSharpBound

/-!
# Finite-height Poisson leakage

The discrepancy between the fixed-width Poisson window and its sharp indicator is bounded
by `π`, decays with distance from both endpoints, and has an inverse-square far tail.
These are scalar estimates used to transport linear-scale spectral averages.
-/

open Set MeasureTheory

noncomputable section

namespace RHTower.WeilSpectral

private theorem countKernel_le_pi (T r : ℝ) : countKernel T r ≤ Real.pi := by
  unfold countKernel
  linarith [Real.arctan_lt_pi_div_two ((T - r) / (3 / 2)),
    Real.arctan_lt_pi_div_two (r / (3 / 2))]

/-- Absolute error of the sharp positive-height window at Poisson width `3/2`. -/
def deficitPoissonLeakage (T r : ℝ) : ℝ :=
  |countKernel T r - (Ioc 0 T).indicator (fun _ => Real.pi) r|

theorem deficitPoissonLeakage_nonneg (T r : ℝ) : 0 ≤ deficitPoissonLeakage T r :=
  abs_nonneg _

theorem measurable_deficitPoissonLeakage (T : ℝ) : Measurable (deficitPoissonLeakage T) := by
  exact ((continuous_countKernel T).measurable.sub
    (measurable_const.indicator measurableSet_Ioc)).abs

theorem deficitPoissonLeakage_le_pi {T : ℝ} (hT : 0 ≤ T) (r : ℝ) :
    deficitPoissonLeakage T r ≤ Real.pi := by
  unfold deficitPoissonLeakage
  by_cases hr : r ∈ Ioc 0 T
  · rw [indicator_of_mem hr]
    exact abs_le.mpr ⟨by linarith [countKernel_nonneg hT r],
      by linarith [countKernel_le_pi T r, Real.pi_pos]⟩
  · rw [indicator_of_notMem hr, sub_zero, abs_of_nonneg (countKernel_nonneg hT r)]
    exact countKernel_le_pi T r

private theorem arctan_distance_lower {H x : ℝ} (hH : 0 < H) (hx : H ≤ x) :
    Real.pi / 2 - (3 / 2) / H ≤ Real.arctan (x / (3 / 2)) := by
  have h := GaloisForLFunctions.HTGeometry.pi_div_two_sub_inv_le_arctan
    (show 0 < H / (3 / 2 : ℝ) by positivity)
  rw [show 1 / (H / (3 / 2 : ℝ)) = (3 / 2) / H by field_simp] at h
  exact h.trans (Real.arctan_strictMono.monotone (by linarith))

/-- Away from both endpoints the leakage is bounded by the two Cauchy tails. -/
theorem deficitPoissonLeakage_le_endpoint {T H r : ℝ} (hT : 0 ≤ T) (hH : 0 < H)
    (hr : H ≤ |r|) (hTr : H ≤ |T - r|) :
    deficitPoissonLeakage T r ≤ 3 / H := by
  have hpos : 0 ≤ (3 / 2 : ℝ) / H := by positivity
  rw [show (3 : ℝ) / H = 2 * ((3 / 2) / H) by ring]
  by_cases hin : r ∈ Ioc 0 T
  · have hr0 := hin.1.le
    have hTr0 : 0 ≤ T - r := sub_nonneg.mpr hin.2
    rw [abs_of_nonneg hr0] at hr
    rw [abs_of_nonneg hTr0] at hTr
    have h1 := arctan_distance_lower hH hr
    have h2 := arctan_distance_lower hH hTr
    rw [deficitPoissonLeakage, indicator_of_mem hin,
      abs_of_nonpos (sub_nonpos.mpr (countKernel_le_pi T r))]
    unfold countKernel
    linarith
  · rw [deficitPoissonLeakage, indicator_of_notMem hin, sub_zero,
      abs_of_nonneg (countKernel_nonneg hT r)]
    by_cases hr0 : r ≤ 0
    · rw [abs_of_nonpos hr0] at hr
      have h1 := arctan_distance_lower hH hr
      rw [neg_div, Real.arctan_neg] at h1
      unfold countKernel
      linarith [Real.arctan_lt_pi_div_two ((T - r) / (3 / 2))]
    · have hTr0 : T < r := by
        by_contra h
        exact hin ⟨lt_of_not_ge hr0, le_of_not_gt h⟩
      rw [abs_of_neg (sub_neg.mpr hTr0)] at hTr
      have h1 := arctan_distance_lower hH hTr
      rw [neg_div, Real.arctan_neg] at h1
      unfold countKernel
      linarith [Real.arctan_lt_pi_div_two (r / (3 / 2))]

/-- Beyond twice the height, normalized leakage has a fixed integrable Cauchy bound. -/
theorem deficitPoissonLeakage_le_far {T r : ℝ} (hT : 1 ≤ T) (hr : 2 * T < |r|) :
    deficitPoissonLeakage T r ≤ 12 * T / (1 + r ^ 2) := by
  have hT0 : 0 ≤ T := by linarith
  have hout : r ∉ Ioc 0 T := by
    intro hin
    rw [abs_of_pos hin.1] at hr
    linarith [hin.2]
  rw [deficitPoissonLeakage, indicator_of_notMem hout, sub_zero,
    abs_of_nonneg (countKernel_nonneg hT0 r)]
  have hden : 0 < 1 + r ^ 2 := by positivity
  have hr1 : 1 ≤ r ^ 2 := by
    have : 1 ≤ |r| := by linarith
    nlinarith [sq_abs r]
  have hbound : ∀ t ∈ Icc 0 T,
      (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2) ≤ 12 / (1 + r ^ 2) := by
    intro t ht
    have htT : |t| ≤ T := by simpa only [abs_of_nonneg ht.1] using ht.2
    have hrt : |r| ≤ |r - t| + |t| := by simpa using abs_add_le (r - t) t
    have hhalf : |r| ≤ 2 * |r - t| := by linarith
    have hsq : r ^ 2 ≤ 4 * (r - t) ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg r) (by positivity : 0 ≤ 2 * |r - t|)).mpr hhalf
      norm_num [sq_abs, mul_pow] at this ⊢
      exact this
    rw [div_le_div_iff₀ (by positivity : 0 < (3 / 2 : ℝ) ^ 2 + (r - t) ^ 2) hden]
    nlinarith
  have hint : IntervalIntegrable
      (fun t : ℝ => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2)) volume 0 T :=
    (continuous_const.div (by fun_prop) (fun t => by positivity) :
      Continuous fun t : ℝ => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2)).intervalIntegrable _ _
  have h := intervalIntegral.integral_mono_on hT0 hint intervalIntegrable_const hbound
  rw [integral_poissonKernel_eq, intervalIntegral.integral_const] at h
  simp only [sub_zero, smul_eq_mul] at h
  convert h using 1
  ring

end RHTower.WeilSpectral

end
