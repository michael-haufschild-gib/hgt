import GaloisForLFunctions.RHTower.ThetaCuspCurvatureDefectGrowthSignedSectors
import GaloisForLFunctions.RHTower.ThetaCuspC5SharpTailMeasures

/-!
# Literal stable components of the growth transfer

The dominant single component cancels exactly, leaving only the deep-tail
transfer, which is nonnegative and bounded by the leading eighth moment.
Every non-dominant pair has stable support, so the complete pair transfer
is at least its positive dominant self-pair. The final signed absorption
is a separate open inequality.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory
noncomputable section

def componentTilt (q : ℝ) (μ : Measure ℝ) : Measure ℝ :=
  μ.withDensity (fun t => ((thetaCuspHigherLikelihoodTiltDensity q t : NNReal) : ENNReal))

theorem integrable_pow_componentTilt (q : ℝ) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j*Real.exp (-q*t)) μ) (j : ℕ) :
    Integrable (fun t : ℝ => t^j) (componentTilt q μ) := by
  rw [componentTilt,integrable_withDensity_iff_integrable_smul
    (measurable_thetaCuspHigherLikelihoodTiltDensity q)]
  convert hμ j using 1
  funext t
  rw [NNReal.smul_def]
  change (thetaCuspHigherLikelihoodTiltDensity q t:ℝ)*t^j=t^j*Real.exp (-q*t)
  rw [thetaCuspHigherLikelihoodTiltDensity,Real.coe_toNNReal _ (Real.exp_pos _).le]
  ring

theorem componentTilt_finite (q : ℝ) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j*Real.exp (-q*t)) μ) :
    IsFiniteMeasure (componentTilt q μ) := by
  have h := integrable_pow_componentTilt q μ hμ 0
  simp only [pow_zero] at h
  exact (integrable_const_iff.mp h).resolve_left one_ne_zero

theorem measureMoment_componentTilt (q : ℝ) (μ : Measure ℝ) (j : ℕ) :
    measureMoment (componentTilt q μ) j=∫ t : ℝ, t^j*Real.exp (-q*t) ∂μ := by
  unfold measureMoment componentTilt
  rw [integral_withDensity_eq_integral_smul (measurable_thetaCuspHigherLikelihoodTiltDensity q)]
  apply integral_congr_ae
  filter_upwards with t
  rw [NNReal.smul_def]
  change (thetaCuspHigherLikelihoodTiltDensity q t:ℝ)*t^j=t^j*Real.exp (-q*t)
  rw [thetaCuspHigherLikelihoodTiltDensity,Real.coe_toNNReal _ (Real.exp_pos _).le]
  ring

theorem ae_lower_componentTilt (q : ℝ) (μ : Measure ℝ) {a : ℝ}
    (hμ : ∀ᵐ t ∂μ, a ≤ t) : ∀ᵐ t ∂componentTilt q μ, a ≤ t := by
  rw [componentTilt,ae_withDensity_iff
    (measurable_thetaCuspHigherLikelihoodTiltDensity q).coe_nnreal_ennreal]
  filter_upwards [hμ] with t ht _
  exact ht

theorem component_transfer_bounds {q : ℝ} (hq : 3/2 ≤ q) (μ : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j*Real.exp (-q*t)) μ)
    (hs : ∀ᵐ t ∂μ, 8 ≤ t) :
    0 ≤ growthTransferFunctional q (measureMoment (componentTilt q μ)) ∧
      growthTransferFunctional q (measureMoment (componentTilt q μ)) ≤
        growthTransferLeadingCoefficient q*measureMoment (componentTilt q μ) 8 := by
  rw [←integral_growthTransferKernel q _ (integrable_pow_componentTilt q μ hμ)]
  have hs' := ae_lower_componentTilt q μ hs
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [hs'] with t ht
    exact (growthTransferKernel_pos hq ht).le
  · rw [measureMoment,←integral_const_mul]
    apply integral_mono_ae
      (integrable_growthTransferKernel q _ (integrable_pow_componentTilt q μ hμ))
      ((integrable_pow_componentTilt q μ hμ 8).const_mul _)
    filter_upwards [hs'] with t ht
    exact growthTransferKernel_le_monomial hq ht

theorem deepTransfer_bounds {q : ℝ} (hq : 3/2 ≤ q) :
    0 ≤ growthTransferFunctional q (thetaCuspDeepTailMoment q) ∧
      growthTransferFunctional q (thetaCuspDeepTailMoment q) ≤
        growthTransferLeadingCoefficient q*thetaCuspDeepTailMoment q 8 := by
  have hq0 : 0 < q := by linarith
  have h := component_transfer_bounds hq thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
    ae_eight_le_thetaCuspDeepTailSpectralMeasure
  have he : measureMoment (componentTilt q thetaCuspDeepTailSpectralMeasure)=thetaCuspDeepTailMoment q := by
    funext j
    exact measureMoment_componentTilt q _ j
  rwa [he] at h

theorem growthTransferFunctional_add (q : ℝ) (m n : ℕ → ℝ) :
    growthTransferFunctional q (fun j => m j+n j)=
      growthTransferFunctional q m+growthTransferFunctional q n := by
  unfold growthTransferFunctional
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem sourceTransfer_single_eq_deep {q : ℝ} (hq : 0 < q) :
    growthTransferFunctional q
      (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) 1)=
      growthTransferFunctional q (thetaCuspDeepTailMoment q) := by
  have hm : thetaCuspHigherLikelihoodSpectralMoment q=
      fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq j
  have hs : growthTransferFunctional q
      (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) 1)=
        growthTransferFunctional q (thetaCuspHigherLikelihoodSpectralMoment q) := by
    unfold growthTransferFunctional
    apply Finset.sum_congr rfl
    intro j hj
    have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
    rw [spectralPowerMoment_one _ (by omega : j+2 ≤ 8),
      spectralPowerMoment_one _ (by omega : j+3 ≤ 8)]
  rw [hs,hm,growthTransferFunctional_add,growthTransferFunctional_dominant_zero hq,zero_add]

theorem componentPair_transfer_nonneg {q a b : ℝ} (hq : 3/2 ≤ q) (hab : 8 ≤ a+b)
    (μ ν : Measure ℝ)
    (hμ : ∀ j : ℕ, Integrable (fun t : ℝ => t^j*Real.exp (-q*t)) μ)
    (hν : ∀ j : ℕ, Integrable (fun t : ℝ => t^j*Real.exp (-q*t)) ν)
    (hsμ : ∀ᵐ t ∂μ, a ≤ t) (hsν : ∀ᵐ t ∂ν, b ≤ t) :
    0 ≤ growthTransferFunctional q
      (momentConvolution (measureMoment (componentTilt q μ)) (measureMoment (componentTilt q ν))) := by
  letI := componentTilt_finite q μ hμ
  letI := componentTilt_finite q ν hν
  have hm : momentConvolution (measureMoment (componentTilt q μ)) (measureMoment (componentTilt q ν))=
      measureMoment (componentTilt q μ ∗ componentTilt q ν) := by
    funext j
    exact (measureMoment_conv _ _ (integrable_pow_componentTilt q μ hμ)
      (integrable_pow_componentTilt q ν hν) j).symm
  rw [hm,←integral_growthTransferKernel q _
    (integrable_pow_measure_conv _ _ (integrable_pow_componentTilt q μ hμ)
      (integrable_pow_componentTilt q ν hν))]
  have hs := ae_add_lower_measure_conv _ _
    (ae_lower_componentTilt q μ hsμ) (ae_lower_componentTilt q ν hsν)
  apply integral_nonneg_of_ae
  filter_upwards [hs] with t ht
  exact (growthTransferKernel_pos hq (hab.trans ht)).le

theorem momentConvolution_add_self (m n : ℕ → ℝ) :
    momentConvolution (fun j => m j+n j) (fun j => m j+n j)=
      fun j => ((momentConvolution m m j+momentConvolution m n j)+
        momentConvolution n m j)+momentConvolution n n j := by
  funext j
  unfold momentConvolution
  simp only [mul_add,add_mul,Finset.sum_add_distrib]
  ring

theorem growthTransferFunctional_power_two (q : ℝ) (m : ℕ → ℝ) :
    growthTransferFunctional q (spectralPowerMoment m 2)=
      growthTransferFunctional q (momentConvolution m m) := by
  unfold growthTransferFunctional
  apply Finset.sum_congr rfl
  intro j hj
  have hj5 : j ≤ 5 := by have := Finset.mem_range.mp hj; omega
  rw [spectralPowerMoment_two _ (by omega : j+2 ≤ 8),
    spectralPowerMoment_two _ (by omega : j+3 ≤ 8)]

theorem sourceTransfer_pair_dominant_le {q : ℝ} (hq : 3/2 ≤ q) :
    growthTransferFunctional q (spectralPowerMoment (atomMoment 2 q) 2) ≤
      growthTransferFunctional q
        (spectralPowerMoment (thetaCuspHigherLikelihoodSpectralMoment q) 2) := by
  have hq0 : 0 < q := by linarith
  have hA : measureMoment (componentTilt q thetaCuspSecondAtomSpectralMeasure)=atomMoment 2 q := by
    funext j
    rw [measureMoment_componentTilt]
    simp only [atomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul]
  have hD : measureMoment (componentTilt q thetaCuspDeepTailSpectralMeasure)=thetaCuspDeepTailMoment q := by
    funext j
    exact measureMoment_componentTilt q _ j
  have hsA : ∀ᵐ t ∂thetaCuspSecondAtomSpectralMeasure, (3:ℝ) ≤ t :=
    ae_three_le_thetaCuspHigherLikelihoodSpectralMeasure.filter_mono
      (ae_mono thetaCuspSecondAtomSpectralMeasure_le)
  have hAD := componentPair_transfer_nonneg hq (a := 3) (b := 8) (by norm_num)
    thetaCuspSecondAtomSpectralMeasure thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq0)
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
    hsA ae_eight_le_thetaCuspDeepTailSpectralMeasure
  have hDA := componentPair_transfer_nonneg hq (a := 8) (b := 3) (by norm_num)
    thetaCuspDeepTailSpectralMeasure thetaCuspSecondAtomSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
    (fun j => integrable_pow_mul_exp_neg_thetaCuspSecondAtomSpectralMeasure j hq0)
    ae_eight_le_thetaCuspDeepTailSpectralMeasure hsA
  have hDD := componentPair_transfer_nonneg hq (a := 8) (b := 8) (by norm_num)
    thetaCuspDeepTailSpectralMeasure thetaCuspDeepTailSpectralMeasure
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
    (fun j => integrable_pow_mul_exp_neg_thetaCuspDeepTailSpectralMeasure j hq0)
    ae_eight_le_thetaCuspDeepTailSpectralMeasure ae_eight_le_thetaCuspDeepTailSpectralMeasure
  rw [hA,hD] at hAD hDA
  rw [hD] at hDD
  have hm : thetaCuspHigherLikelihoodSpectralMoment q=
      fun j => atomMoment 2 q j+thetaCuspDeepTailMoment q j := by
    funext j
    simpa only [atomMoment,thetaCuspSecondAtomMoment,thetaCuspSecondAtomSpectralMeasure,neg_mul] using
      thetaCuspHigherLikelihoodSpectralMoment_eq_second_add_deep hq0 j
  rw [growthTransferFunctional_power_two,growthTransferFunctional_power_two,hm,momentConvolution_add_self]
  simp only [growthTransferFunctional_add]
  linarith


end
end RHTower.ThetaCuspDefect
