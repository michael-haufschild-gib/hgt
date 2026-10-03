import GaloisForLFunctions.RHTower.SuzukiTaV2RawSourceProfile
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarSourceCancellation
import GaloisForLFunctions.RHTower.SuzukiMatchedOddMetricTransport
import GaloisForLFunctions.RHTower.SuzukiTaV2ActualDefectJet

open Filter MeasureTheory Set
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- Exact diagonal Gram entry at the actual V2 source parameter. -/
theorem norm_sq_ccmPolarApertureVector_one (a : SuzukiPositiveAperture) :
    ‖ccmPolarApertureVector a 1‖ ^ 2 = Real.sinh (2 * a.1) := by
  change ‖ccmPolarL2Vector a 1‖ ^ 2 = _
  rw [norm_sq_eq_integral]
  calc
    (∫ x : ℝ, ‖(ccmPolarL2Vector a 1 : ℝ → ℂ) x‖ ^ 2) =
        ∫ x in centralInterval a.1, Real.exp (2 * x) := by
      rw [← integral_indicator (measurableSet_centralInterval a.1)]
      apply integral_congr_ae
      filter_upwards [ccmPolarL2Vector_coeFn a 1] with x hx
      rw [hx]
      by_cases hmem : x ∈ centralInterval a.1
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        simp only [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        rw [← Real.exp_nat_mul]
        congr 1
        norm_num
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    _ = ∫ x in (-a.1)..a.1, Real.exp (2 * x) := by
      rw [intervalIntegral.integral_of_le (by linarith [a.property])]
      unfold centralInterval
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = Real.sinh (2 * a.1) := by
      rw [intervalIntegral.integral_comp_mul_left Real.exp (by norm_num : (2 : ℝ) ≠ 0),
        integral_exp, Real.sinh_eq]
      simp only [smul_eq_mul, mul_neg]
      ring

theorem norm_ccmPolarApertureVector_neg_one_le (a : SuzukiPositiveAperture) :
    ‖ccmPolarApertureVector a (-1)‖ ≤ Real.exp a.1 := by
  change ‖ccmPolarL2Vector a (-1)‖ ≤ _
  rw [← l2Reflection_ccmPolarL2Vector a 1]
  change ‖l2ReflectionIsometry (ccmPolarL2Vector a 1)‖ ≤ _
  rw [l2ReflectionIsometry.norm_map]
  exact norm_ccmPolarApertureVector_one_le a

/-- The actual V2 parity sum retains the literal positive-pole source pairing. -/
theorem suzukiTaV2_energy_sum_source (a : SuzukiPositiveAperture) :
    suzukiTaCoalescingEvenEnergy a 1 + suzukiTaCoalescingOddEnergy a 1 =
      (inner ℂ (ccmPolarApertureVector a 1) (ccmArchimedeanFormToAperture a
        (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)))).re := by
  have h := suzukiTaSourceResponse_inner a (ccmPolarApertureVector a 1) (suzukiTaRawDeficiency a 1)
  rw [suzukiTaSourceResponse_polar] at h
  rw [suzukiTaCoalescingEnergy_add_eq_norm_sq]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans (congrArg Complex.re h)

/-- The signed actual parity difference retains the opposite source pairing. -/
theorem suzukiTaV2_energy_sub_source (a : SuzukiPositiveAperture) :
    suzukiTaCoalescingEvenEnergy a 1 - suzukiTaCoalescingOddEnergy a 1 =
      (inner ℂ (ccmPolarApertureVector a (-1)) (ccmArchimedeanFormToAperture a
        (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)))).re := by
  have h := suzukiTaSourceResponse_inner a (ccmPolarApertureVector a (-1)) (suzukiTaRawDeficiency a 1)
  rw [suzukiTaSourceResponse_polar, inner_rawDeficiency_neg_eq_energy_sub] at h
  exact congrArg Complex.re h

/-- Source-profile error for both actual signed energy channels at their
common prescribed-shift scale. -/
theorem suzukiTaV2_scaled_energy_source_errors (a : SuzukiPositiveAperture) :
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
    let t := c * Real.exp (-2 * a.1)
    let δ := ‖ccmArchimedeanFormToAperture a
      (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)) -
        ccmSourceShiftProfile a (ccmPolarApertureVector a 1)‖
    let C := ‖ccmArchimedeanRemainderScalar‖ + 47
    |t * (suzukiTaCoalescingEvenEnergy a 1 + suzukiTaCoalescingOddEnergy a 1) -
      Real.exp (-2 * a.1) * Real.sinh (2 * a.1)| ≤ C * δ ∧
    |t * (suzukiTaCoalescingEvenEnergy a 1 - suzukiTaCoalescingOddEnergy a 1) -
      2 * a.1 * Real.exp (-2 * a.1)| ≤ C * δ := by
  let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
  let t := c * Real.exp (-2 * a.1)
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  let f := ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1))
  let p := ccmPolarApertureVector a 1
  let m := ccmPolarApertureVector a (-1)
  let q := ccmSourceShiftProfile a p
  have hc : 0 < c := boundedPerturbedFormShift_pos _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hscale : t * c⁻¹ = Real.exp (-2 * a.1) := by
    dsimp [t]
    rw [mul_right_comm, mul_inv_cancel₀ hc.ne', one_mul]
  have hexp : Real.exp a.1 * Real.exp (-2 * a.1) * Real.exp a.1 = 1 := by
    rw [← Real.exp_add, ← Real.exp_add,
      show a.1 + -2 * a.1 + a.1 = 0 by ring, Real.exp_zero]
  have hfactor : t * Real.exp a.1 ≤ C := by
    calc
      _ ≤ (C * Real.exp a.1) * Real.exp (-2 * a.1) * Real.exp a.1 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (suzukiWeilIntervalShift_le_exp a) (Real.exp_pos _).le)
          (Real.exp_pos _).le
      _ = C * (Real.exp a.1 * Real.exp (-2 * a.1) * Real.exp a.1) := by ring
      _ = C := by rw [hexp, mul_one]
  have hpair (v : suzukiApertureHilbert a) (hv : ‖v‖ ≤ Real.exp a.1) :
      t * |(inner ℂ v (f - q)).re| ≤ C * ‖f - q‖ := by
    calc
      _ ≤ t * ‖inner ℂ v (f - q)‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) ht
      _ ≤ t * (‖v‖ * ‖f - q‖) := mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) v (f - q)) ht
      _ ≤ t * (Real.exp a.1 * ‖f - q‖) := by gcongr
      _ = (t * Real.exp a.1) * ‖f - q‖ := by ring
      _ ≤ C * ‖f - q‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
  have hpp : (inner ℂ p q).re = c⁻¹ * Real.sinh (2 * a.1) := by
    change (inner ℂ p (((c⁻¹ : ℝ) : ℂ) • p)).re = _
    rw [inner_smul_right p p ((c⁻¹ : ℝ) : ℂ), Complex.re_ofReal_mul]
    apply congrArg (fun x : ℝ => c⁻¹ * x)
    exact (norm_sq_eq_re_inner (𝕜 := ℂ) p).symm.trans
      (norm_sq_ccmPolarApertureVector_one a)
  have hmp : (inner ℂ m q).re = c⁻¹ * (2 * a.1) := by
    change (inner ℂ m (((c⁻¹ : ℝ) : ℂ) • p)).re = _
    rw [inner_smul_right m p ((c⁻¹ : ℝ) : ℂ), Complex.re_ofReal_mul, inner_ccmPolarApertureVector_opposite,
      Complex.ofReal_re]
  have he := hpair p (norm_ccmPolarApertureVector_one_le a)
  have ho := hpair m (norm_ccmPolarApertureVector_neg_one_le a)
  rw [inner_sub_right, Complex.sub_re, hpp] at he
  rw [inner_sub_right, Complex.sub_re, hmp] at ho
  have hS := suzukiTaV2_energy_sum_source a
  have hD := suzukiTaV2_energy_sub_source a
  change _ = (inner ℂ p f).re at hS
  change _ = (inner ℂ m f).re at hD
  dsimp only
  change |t * _ - _| ≤ C * ‖f - q‖ ∧ |t * _ - _| ≤ C * ‖f - q‖
  constructor
  · calc
      _ = |t * ((inner ℂ p f).re - c⁻¹ * Real.sinh (2 * a.1))| := by
        rw [← hS, mul_sub, ← mul_assoc, hscale]
      _ = t * |(inner ℂ p f).re - c⁻¹ * Real.sinh (2 * a.1)| := by
        rw [abs_mul, abs_of_nonneg ht]
      _ ≤ _ := he
  · calc
      _ = |t * ((inner ℂ m f).re - c⁻¹ * (2 * a.1))| := by
        rw [← hD, ← hscale]
        congr 1
        ring
      _ = t * |(inner ℂ m f).re - c⁻¹ * (2 * a.1)| := by
        rw [abs_mul, abs_of_nonneg ht]
      _ ≤ _ := ho

end RHTower
end
