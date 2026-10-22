import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2MixedSourceGram
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2PrescribedParityLimit

open Filter
open scoped Topology InnerProduct
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

/-- The common scale appropriate to a mixed imaginary spectral test. -/
def suzukiTaV2MixedSourceScale (a : SuzukiPositiveAperture) (s : ℝ) : ℝ :=
  boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a) *
    Real.exp (-(1 + s) * a.1)

/-- Actual completed source tested against a literal real exponential. -/
def suzukiTaV2MixedSourcePairing (a : SuzukiPositiveAperture) (s : ℝ) : ℂ :=
  inner ℂ (ccmPolarApertureVector a s)
    (ccmArchimedeanFormToAperture a (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1)))

/-- The full complex pairing error vanishes for both signs; no reality
assumption on the actual covariance response is used. -/
theorem tendsto_suzukiTaV2_scaled_mixed_source_errors (s : ℝ) (hs : 1 / 2 ≤ s) :
    Tendsto (fun a : SuzukiPositiveAperture =>
      (suzukiTaV2MixedSourceScale a s : ℂ) * suzukiTaV2MixedSourcePairing a s -
        (Real.exp (-(1 + s) * a.1) : ℂ) *
          inner ℂ (ccmPolarApertureVector a s) (ccmPolarApertureVector a 1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) ∧
    Tendsto (fun a : SuzukiPositiveAperture =>
      (suzukiTaV2MixedSourceScale a s : ℂ) * suzukiTaV2MixedSourcePairing a (-s) -
        (Real.exp (-(1 + s) * a.1) : ℂ) *
          inner ℂ (ccmPolarApertureVector a (-s)) (ccmPolarApertureVector a 1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  let l := comap (fun a : SuzukiPositiveAperture => a.1) atTop
  let C := ‖ccmArchimedeanRemainderScalar‖ + 47
  let f := fun a : SuzukiPositiveAperture => ccmArchimedeanFormToAperture a
    (suzukiTaToFormCLM a (suzukiTaRawDeficiency a 1))
  let p := fun a : SuzukiPositiveAperture => ccmPolarApertureVector a 1
  let q := fun a : SuzukiPositiveAperture => ccmSourceShiftProfile a (p a)
  have hbound : Tendsto (fun a => C * ‖f a - q a‖) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_suzukiTaV2_rawSource_profile_norm.const_mul C
  have herr (v : (a : SuzukiPositiveAperture) → suzukiApertureHilbert a)
      (hv : ∀ a, ‖v a‖ ≤ Real.exp (s * a.1)) :
      Tendsto (fun a => (suzukiTaV2MixedSourceScale a s : ℂ) * inner ℂ (v a) (f a) -
        (Real.exp (-(1 + s) * a.1) : ℂ) * inner ℂ (v a) (p a)) l (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    simp only [sub_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    apply Eventually.of_forall
    intro a
    let c := boundedPerturbedFormShift (suzukiWeilIntervalBoundedRemainder a)
    let r := suzukiTaV2MixedSourceScale a s
    have hc : 0 < c := boundedPerturbedFormShift_pos _
    have hr : 0 ≤ r := by dsimp [r, suzukiTaV2MixedSourceScale]; positivity
    have hscale : r * c⁻¹ = Real.exp (-(1 + s) * a.1) := by
      dsimp [r, suzukiTaV2MixedSourceScale, c]
      rw [mul_right_comm, mul_inv_cancel₀ hc.ne', one_mul]
    have hscaleC : (r : ℂ) * ((c⁻¹ : ℝ) : ℂ) =
        (Real.exp (-(1 + s) * a.1) : ℂ) := by
      rw [← Complex.ofReal_mul, hscale]
    have hfactor : r * Real.exp (s * a.1) ≤ C := by
      calc
        _ ≤ (C * Real.exp a.1) * Real.exp (-(1 + s) * a.1) *
            Real.exp (s * a.1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (suzukiWeilIntervalShift_le_exp a)
              (Real.exp_pos _).le) (Real.exp_pos _).le
        _ = C * Real.exp (a.1 + -(1 + s) * a.1 + s * a.1) := by
          rw [Real.exp_add, Real.exp_add]
          ring
        _ = C := by rw [show a.1 + -(1 + s) * a.1 + s * a.1 = 0 by ring,
          Real.exp_zero, mul_one]
    have heq : (r : ℂ) * inner ℂ (v a) (f a - q a) =
        (r : ℂ) * inner ℂ (v a) (f a) -
          (Real.exp (-(1 + s) * a.1) : ℂ) * inner ℂ (v a) (p a) := by
      change (r : ℂ) * inner ℂ (v a) (f a - (((c⁻¹ : ℝ) : ℂ) • p a)) = _
      rw [inner_sub_right, inner_smul_right (v a) (p a) ((c⁻¹ : ℝ) : ℂ),
        mul_sub, ← mul_assoc, hscaleC]
    change ‖(r : ℂ) * inner ℂ (v a) (f a) - _‖ ≤ C * ‖f a - q a‖
    rw [← heq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    calc
      _ ≤ r * (‖v a‖ * ‖f a - q a‖) :=
        mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) (v a) (f a - q a)) hr
      _ ≤ r * (Real.exp (s * a.1) * ‖f a - q a‖) := by
        gcongr
        exact hv a
      _ = (r * Real.exp (s * a.1)) * ‖f a - q a‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)
  exact ⟨herr (fun a => ccmPolarApertureVector a s)
      (fun a => norm_ccmPolarApertureVector_le_exp_of_half_le a s hs),
    herr (fun a => ccmPolarApertureVector a (-s))
      (fun a => norm_ccmPolarApertureVector_neg_le_exp_of_half_le a s hs)⟩

private theorem tendsto_exp_neg_slope (r : ℝ) (hr : 0 < r) :
    Tendsto (fun a : SuzukiPositiveAperture => Real.exp (-r * a.1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  have hv : Tendsto (fun a : SuzukiPositiveAperture => a.1)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) atTop := tendsto_comap
  simpa only [Function.comp_def, pow_zero, one_mul, neg_mul] using
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp (hv.const_mul_atTop hr)

/-- Exact normalization of the two literal mixed Gram entries. -/
theorem suzukiTaV2_scaled_mixed_gram
    (a : SuzukiPositiveAperture) (s : Set.Ioo (1 / 2 : ℝ) 1) :
    (Real.exp (-(1 + s.1) * a.1) : ℂ) *
        inner ℂ (ccmPolarApertureVector a s.1) (ccmPolarApertureVector a 1) =
      (((1 - Real.exp (-(2 * (1 + s.1)) * a.1)) / (1 + s.1) : ℝ) : ℂ) ∧
    (Real.exp (-(1 + s.1) * a.1) : ℂ) *
        inner ℂ (ccmPolarApertureVector a (-s.1)) (ccmPolarApertureVector a 1) =
      (((Real.exp (-(2 * s.1) * a.1) - Real.exp (-2 * a.1)) / (1 - s.1) : ℝ) : ℂ) := by
  have hp : s.1 + 1 ≠ 0 := by linarith [s.2.1]
  have hm : -s.1 + 1 ≠ 0 := by linarith [s.2.2]
  have hexp (u v : ℝ) : Real.exp u * Real.exp v = Real.exp (u + v) :=
    (Real.exp_add u v).symm
  constructor
  · rw [inner_ccmPolarApertureVector_eq_exp_quotient a s.1 1 hp, ← Complex.ofReal_mul]
    congr 1
    rw [← mul_div_assoc, mul_sub, hexp, hexp,
      show -(1 + s.1) * a.1 + (s.1 + 1) * a.1 = 0 by ring,
      show -(1 + s.1) * a.1 + -(s.1 + 1) * a.1 = -(2 * (1 + s.1)) * a.1 by ring,
      Real.exp_zero]
    rw [add_comm s.1 1]
  · rw [inner_ccmPolarApertureVector_eq_exp_quotient a (-s.1) 1 hm, ← Complex.ofReal_mul]
    congr 1
    rw [← mul_div_assoc, mul_sub, hexp, hexp,
      show -(1 + s.1) * a.1 + (-s.1 + 1) * a.1 = -(2 * s.1) * a.1 by ring,
      show -(1 + s.1) * a.1 + -(-s.1 + 1) * a.1 = -2 * a.1 by ring]
    congr 1
    ring

/-- Actual complex mixed pairings on an interior spectral segment. The same
scale leaves a nonzero denominator limit and annihilates the opposite source. -/
theorem tendsto_suzukiTaV2_scaled_mixed_source_pairings
    (s : Set.Ioo (1 / 2 : ℝ) 1) :
    Tendsto (fun a : SuzukiPositiveAperture =>
      (suzukiTaV2MixedSourceScale a s.1 : ℂ) * suzukiTaV2MixedSourcePairing a s.1)
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop)
      (𝓝 ((1 / (1 + s.1) : ℝ) : ℂ)) ∧
    Tendsto (fun a : SuzukiPositiveAperture =>
      (suzukiTaV2MixedSourceScale a s.1 : ℂ) * suzukiTaV2MixedSourcePairing a (-s.1))
      (comap (fun a : SuzukiPositiveAperture => a.1) atTop) (𝓝 0) := by
  let l := comap (fun a : SuzukiPositiveAperture => a.1) atTop
  have hp := tendsto_exp_neg_slope (2 * (1 + s.1)) (by linarith [s.2.1])
  have hm := tendsto_exp_neg_slope (2 * s.1) (by linarith [s.2.1])
  have h2 := tendsto_exp_neg_slope 2 (by norm_num)
  have hmainP : Tendsto (fun a : SuzukiPositiveAperture =>
      (Real.exp (-(1 + s.1) * a.1) : ℂ) *
        inner ℂ (ccmPolarApertureVector a s.1) (ccmPolarApertureVector a 1)) l
      (𝓝 ((1 / (1 + s.1) : ℝ) : ℂ)) := by
    have h := ((tendsto_const_nhds : Tendsto
      (fun _ : SuzukiPositiveAperture => (1 : ℝ)) l (𝓝 1)).sub hp).div_const (1 + s.1)
    have hc := (Complex.continuous_ofReal.tendsto ((1 - 0) / (1 + s.1))).comp h
    simpa only [Function.comp_def, sub_zero, (suzukiTaV2_scaled_mixed_gram _ s).1] using hc
  have hmainM : Tendsto (fun a : SuzukiPositiveAperture =>
      (Real.exp (-(1 + s.1) * a.1) : ℂ) *
        inner ℂ (ccmPolarApertureVector a (-s.1)) (ccmPolarApertureVector a 1)) l (𝓝 0) := by
    have h := (hm.sub h2).div_const (1 - s.1)
    have hc := (Complex.continuous_ofReal.tendsto ((0 - 0) / (1 - s.1))).comp h
    simpa only [Function.comp_def, sub_self, zero_div, Complex.ofReal_zero,
      (suzukiTaV2_scaled_mixed_gram _ s).2] using hc
  obtain ⟨heP, heM⟩ := tendsto_suzukiTaV2_scaled_mixed_source_errors s.1 s.2.1.le
  constructor
  · simpa only [sub_add_cancel, zero_add] using heP.add hmainP
  · simpa only [sub_add_cancel, zero_add] using heM.add hmainM

end RHTower
end
