import GaloisForLFunctions.RHTower.Deninger.DeningerMixedPrimeBanach
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompactL2Fourier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFunctionCriterion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Suzuki's literal Hermitian form on `L²(-a,a)`

This file formalizes equation (1.10) and the strict `L²` clause of Suzuki (2022), Theorem 1.3.
The interval space is represented exactly by the fixed points of physical zero extension to
`[-a,a]`.  Under RH, the literal iterated kernel integral is the Gram form of the doubled critical
Xi screw feature.  Vanishing of that Gram vector makes the compact Fourier transform constant at
every centered Xi zero; `SuzukiCompactL2Fourier` then forces the original `L²` vector to vanish.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Exact zero-extended model of Suzuki's `L²(-a,a)`. -/
abbrev SuzukiApertureL2 (a : ℝ) := {f : SoninL2 // suzukiCutoff a f = f}

/-- Hilbert space carrying the doubled critical-Xi screw feature. -/
abbrev SuzukiScrewFeatureSpace :=
  WithLp 2
    (lp (fun _ : XiZeroCopy => ℂ) 2 × lp (fun _ : XiZeroCopy => ℂ) 2)

/-- Suzuki (2022), equation (1.10), on zero-extended `L²` representatives. -/
def suzukiScrewL2Form (a : ℝ) (f₁ f₂ : SoninL2) : ℂ :=
  ∫ t : ℝ, ∫ u : ℝ,
    suzukiScrewKernel t u * (suzukiCutoff a f₁) u *
      (starRingEnd ℂ) ((suzukiCutoff a f₂) t)

/-- Square distance of the doubled feature is twice the critical screw series. -/
theorem sq_norm_xiCriticalScrewDoubledPoint_sub
    (hRH : RiemannHypothesis) (t u : ℝ) :
    ‖xiCriticalScrewDoubledPoint hRH t - xiCriticalScrewDoubledPoint hRH u‖ ^ 2 =
      2 * xiCriticalScrewSeries (t - u) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  rw [WithLp.sub_fst, WithLp.sub_snd]
  simp only [xiCriticalScrewDoubledPoint, WithLp.toLp_fst, WithLp.toLp_snd]
  have hstar :
      star (xiCriticalScrewHilbertPoint hRH t) -
          star (xiCriticalScrewHilbertPoint hRH u) =
        star (xiCriticalScrewHilbertPoint hRH t -
          xiCriticalScrewHilbertPoint hRH u) := by
    simp
  rw [hstar, norm_star,
    sq_norm_xiCriticalScrewHilbertPoint_sub hRH t u]
  ring

/-- The doubled critical-Xi screw feature is norm-continuous. -/
theorem continuous_xiCriticalScrewDoubledPoint (hRH : RiemannHypothesis) :
    Continuous (xiCriticalScrewDoubledPoint hRH) := by
  rw [continuous_iff_continuousAt]
  intro t
  change Tendsto (xiCriticalScrewDoubledPoint hRH) (nhds t)
    (nhds (xiCriticalScrewDoubledPoint hRH t))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun u : ℝ => 2 * xiCriticalScrewSeries (u - t))
      (nhds t) (nhds 0) := by
    have hc : Continuous (fun u : ℝ => 2 * xiCriticalScrewSeries (u - t)) :=
      continuous_const.mul
        ((xiCriticalScrewSeries_continuous_of_rh hRH).comp
          (continuous_id.sub continuous_const))
    have hcAt : Tendsto (fun u : ℝ => 2 * xiCriticalScrewSeries (u - t))
        (nhds t) (nhds (2 * xiCriticalScrewSeries (t - t))) := hc.continuousAt
    simpa [xiCriticalScrewSeries, screwSeries] using hcAt
  have hsqrt : Tendsto (fun u : ℝ => Real.sqrt
      (2 * xiCriticalScrewSeries (u - t))) (nhds t) (nhds 0) := by
    convert (Real.continuous_sqrt.tendsto 0).comp hsq using 1
    · rfl
    · rw [Real.sqrt_zero]
  apply hsqrt.congr'
  filter_upwards with u
  rw [← sq_norm_xiCriticalScrewDoubledPoint_sub hRH u t,
    Real.sqrt_sq (norm_nonneg _)]

/-- The Hilbert-valued integrand obtained by multiplying the screw feature by arbitrary compactly
supported `L²` data is Bochner integrable. -/
theorem integrable_suzukiScrewFeature
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f : SoninL2) :
    Integrable fun t : ℝ =>
      (suzukiCutoff a f t) • xiCriticalScrewDoubledPoint hRH t := by
  let g : ℝ → ℂ := (suzukiCutoff a f : ℝ → ℂ)
  let V : ℝ → SuzukiScrewFeatureSpace := xiCriticalScrewDoubledPoint hRH
  have hg : Integrable g := integrable_suzukiCutoff a f
  have hV : Continuous V := continuous_xiCriticalScrewDoubledPoint hRH
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := V) hV.continuousOn
  have hC0 : 0 ≤ C := by
    have hzero : (0 : ℝ) ∈ Icc (-a) a := ⟨by linarith, ha⟩
    exact (norm_nonneg (V 0)).trans (hC 0 hzero)
  refine Integrable.mono' (hg.norm.const_mul C)
    (hg.aestronglyMeasurable.smul hV.aestronglyMeasurable) ?_
  filter_upwards [suzukiCutoff_ae_eq_zero_off a f] with t ht
  by_cases hmem : t ∈ Icc (-a) a
  · rw [norm_smul]
    calc
      ‖g t‖ * ‖V t‖ ≤ ‖g t‖ * C :=
        mul_le_mul_of_nonneg_left (hC t hmem) (norm_nonneg _)
      _ = C * ‖g t‖ := by ring
  · have hzero : (suzukiCutoff a f) t = 0 := ht hmem
    rw [hzero]
    simpa only [zero_smul, norm_zero] using
      mul_nonneg hC0 (norm_nonneg (g t))

/-- Bochner integral of the critical-Xi screw feature against compactly supported `L²` data. -/
def suzukiScrewFeatureIntegral
    (hRH : RiemannHypothesis) (a : ℝ) (f : SoninL2) : SuzukiScrewFeatureSpace :=
  ∫ t : ℝ, (suzukiCutoff a f t) • xiCriticalScrewDoubledPoint hRH t

private theorem suzukiScrewForm_integrand_eq_inner
    (hRH : RiemannHypothesis) (a : ℝ) (f₁ f₂ : SoninL2) (t u : ℝ) :
    suzukiScrewKernel t u * (suzukiCutoff a f₁) u *
        (starRingEnd ℂ) ((suzukiCutoff a f₂) t) =
      inner ℂ
        ((suzukiCutoff a f₂ t) • xiCriticalScrewDoubledPoint hRH t)
        ((suzukiCutoff a f₁ u) • xiCriticalScrewDoubledPoint hRH u) := by
  rw [suzukiScrewKernel_eq_inner_of_rh hRH, inner_smul_left, inner_smul_right]
  ring

/-- Absolute convergence of Suzuki's full two-variable kernel integrand under RH. -/
theorem integrable_suzukiScrewL2Form_prod_of_rh
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f₁ f₂ : SoninL2) :
    Integrable (fun p : ℝ × ℝ =>
      suzukiScrewKernel p.1 p.2 * (suzukiCutoff a f₁) p.2 *
        (starRingEnd ℂ) ((suzukiCutoff a f₂) p.1)) (volume.prod volume) := by
  let F₁ : ℝ → SuzukiScrewFeatureSpace := fun u =>
    (suzukiCutoff a f₁ u) • xiCriticalScrewDoubledPoint hRH u
  let F₂ : ℝ → SuzukiScrewFeatureSpace := fun t =>
    (suzukiCutoff a f₂ t) • xiCriticalScrewDoubledPoint hRH t
  have hF₁ : Integrable F₁ := integrable_suzukiScrewFeature ha hRH f₁
  have hF₂ : Integrable F₂ := integrable_suzukiScrewFeature ha hRH f₂
  have hinner : Integrable (fun p : ℝ × ℝ => inner ℂ (F₂ p.1) (F₁ p.2))
      (volume.prod volume) :=
    Integrable.op_fst_snd (by fun_prop)
      ⟨1, fun (x y : SuzukiScrewFeatureSpace) => by
        simpa only [one_mul] using (norm_inner_le_norm (𝕜 := ℂ) x y)⟩ hF₂ hF₁
  exact hinner.congr (ae_of_all _ fun p => by
    symm
    exact suzukiScrewForm_integrand_eq_inner hRH a f₁ f₂ p.1 p.2)

/-- Under RH, Suzuki's literal Hermitian form is exactly the Gram inner product of the integrated
doubled screw features. -/
theorem suzukiScrewL2Form_eq_inner_featureIntegral_of_rh
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f₁ f₂ : SoninL2) :
    suzukiScrewL2Form a f₁ f₂ =
      inner ℂ (suzukiScrewFeatureIntegral hRH a f₂)
        (suzukiScrewFeatureIntegral hRH a f₁) := by
  let F₁ : ℝ → SuzukiScrewFeatureSpace := fun u =>
    (suzukiCutoff a f₁ u) • xiCriticalScrewDoubledPoint hRH u
  let F₂ : ℝ → SuzukiScrewFeatureSpace := fun t =>
    (suzukiCutoff a f₂ t) • xiCriticalScrewDoubledPoint hRH t
  have hF₁ : Integrable F₁ := integrable_suzukiScrewFeature ha hRH f₁
  have hF₂ : Integrable F₂ := integrable_suzukiScrewFeature ha hRH f₂
  have hslice (t : ℝ) :
      (∫ u : ℝ, suzukiScrewKernel t u * (suzukiCutoff a f₁) u *
        (starRingEnd ℂ) ((suzukiCutoff a f₂) t)) =
        inner ℂ (F₂ t) (∫ u : ℝ, F₁ u) := by
    rw [← integral_inner hF₁ (F₂ t)]
    apply integral_congr_ae
    filter_upwards with u
    exact suzukiScrewForm_integrand_eq_inner hRH a f₁ f₂ t u
  rw [suzukiScrewL2Form, integral_congr_ae (ae_of_all _ hslice)]
  have hconj :
      (∫ t : ℝ, inner ℂ (F₂ t) (∫ u : ℝ, F₁ u)) =
        (starRingEnd ℂ) (∫ t : ℝ,
          inner ℂ (∫ u : ℝ, F₁ u) (F₂ t)) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards with t
    exact (inner_conj_symm (𝕜 := ℂ) (F₂ t) (∫ u : ℝ, F₁ u)).symm
  rw [hconj, integral_inner hF₂ (∫ u : ℝ, F₁ u)]
  exact inner_conj_symm (𝕜 := ℂ) (∫ t : ℝ, F₂ t) (∫ u : ℝ, F₁ u)

/-- RH makes Suzuki's literal `L²` form nonnegative. -/
theorem suzukiScrewL2Form_nonneg_of_rh
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f : SoninL2) :
    0 ≤ (suzukiScrewL2Form a f f).re := by
  rw [suzukiScrewL2Form_eq_inner_featureIntegral_of_rh ha hRH]
  rw [inner_self_eq_norm_sq_to_K]
  change 0 ≤ (((‖suzukiScrewFeatureIntegral hRH a f‖ : ℝ) : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_nonneg _

private theorem screwCoord_screwPhase_eq_exp
    (omega : XiZeroCopy → ℝ) (t : ℝ) (q : XiZeroCopy) :
    screwCoord (screwPhase omega t q) =
      Complex.exp (I * ((omega q : ℝ) : ℂ) * (t : ℂ)) := by
  rw [screwPhase, screwCoord_ofReal]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- One coordinate of the RH screw vector is the literal divided exponential feature. -/
theorem xiCriticalScrewHilbertPoint_apply
    (hRH : RiemannHypothesis) (t : ℝ) (q : XiZeroCopy) :
    xiCriticalScrewHilbertPoint hRH t q =
      (Real.sqrt (xiCriticalScrewWeight q / 2) : ℂ) *
        (1 - Complex.exp (I * (xiRealSpectralPoint q : ℂ) * (t : ℂ))) := by
  rw [xiCriticalScrewHilbertPoint, screwEmbed_coe]
  change screwEmbedFun xiCriticalScrewWeight
      (screwPhase xiRealSpectralPoint t) q = _
  rw [screwEmbedFun, screwCoord_screwPhase_eq_exp]

/-- The first coordinate integral is exactly the Fourier difference in Suzuki's equation (3.2),
with its reciprocal-zero square-root weight left visible. -/
theorem integral_suzukiScrewFeature_fst_coordinate
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f : SoninL2)
    (q : XiZeroCopy) :
    (∫ t : ℝ,
      ((suzukiCutoff a f t) • xiCriticalScrewDoubledPoint hRH t).fst q) =
      (Real.sqrt (xiCriticalScrewWeight q / 2) : ℂ) *
        (suzukiCompactL2Fourier a f 0 -
          suzukiCompactL2Fourier a f (xiRealSpectralPoint q : ℂ)) := by
  let g : ℝ → ℂ := (suzukiCutoff a f : ℝ → ℂ)
  let c : ℂ := (Real.sqrt (xiCriticalScrewWeight q / 2) : ℂ)
  let gamma : ℂ := (xiRealSpectralPoint q : ℂ)
  have hg : Integrable g := integrable_suzukiCutoff a f
  have hgamma : Integrable fun t : ℝ =>
      g t * Complex.exp (I * gamma * (t : ℂ)) := by
    simpa [g, gamma] using
      integrable_suzukiCompactL2Fourier_integrand ha f gamma
  have hpoint (t : ℝ) :
      ((suzukiCutoff a f t) • xiCriticalScrewDoubledPoint hRH t).fst q =
        c * (g t - g t * Complex.exp (I * gamma * (t : ℂ))) := by
    rw [WithLp.smul_fst]
    change (suzukiCutoff a f t) * xiCriticalScrewHilbertPoint hRH t q = _
    rw [xiCriticalScrewHilbertPoint_apply]
    dsimp only [c, g, gamma]
    ring
  rw [integral_congr_ae (ae_of_all _ hpoint), integral_const_mul,
    integral_sub hg hgamma]
  have hzero : suzukiCompactL2Fourier a f 0 = ∫ t : ℝ, g t := by
    rw [suzukiCompactL2Fourier]
    apply integral_congr_ae
    filter_upwards with t
    simp [g]
  rw [← hzero]
  rfl

/-- Coordinate formula for the integrated doubled screw feature. -/
theorem suzukiScrewFeatureIntegral_fst_coordinate
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f : SoninL2)
    (q : XiZeroCopy) :
    (suzukiScrewFeatureIntegral hRH a f).fst q =
      (Real.sqrt (xiCriticalScrewWeight q / 2) : ℂ) *
        (suzukiCompactL2Fourier a f 0 -
          suzukiCompactL2Fourier a f (xiRealSpectralPoint q : ℂ)) := by
  let F : ℝ → SuzukiScrewFeatureSpace := fun t =>
    (suzukiCutoff a f t) • xiCriticalScrewDoubledPoint hRH t
  have hF : Integrable F := integrable_suzukiScrewFeature ha hRH f
  have hFfst : Integrable fun t => (F t).fst := hF.prodLp_fst
  rw [suzukiScrewFeatureIntegral, fst_integral_withLp hF]
  change (deningerLpEval 2 q) (∫ t : ℝ, (F t).fst) = _
  rw [← (deningerLpEval 2 q).integral_comp_comm hFfst]
  simpa only [deningerLpEval_apply] using
    integral_suzukiScrewFeature_fst_coordinate ha hRH f q

/-- A zero integrated feature makes the compact Fourier transform take its central value at each
real Xi spectral coordinate. -/
theorem suzukiCompactL2Fourier_eq_zeroValue_of_featureIntegral_eq_zero
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f : SoninL2)
    (hfeature : suzukiScrewFeatureIntegral hRH a f = 0) (q : XiZeroCopy) :
    suzukiCompactL2Fourier a f (xiRealSpectralPoint q : ℂ) =
      suzukiCompactL2Fourier a f 0 := by
  have hcoord := suzukiScrewFeatureIntegral_fst_coordinate ha hRH f q
  have hcoordZero : (suzukiScrewFeatureIntegral hRH a f).fst q = 0 := by
    rw [hfeature]
    simp
  rw [hcoord] at hcoordZero
  have hweight : 0 < xiCriticalScrewWeight q / 2 := by
    positivity [xiCriticalScrewWeight_pos_of_rh hRH q]
  have hsqrt : (Real.sqrt (xiCriticalScrewWeight q / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hweight).ne'
  have hdiff := (mul_eq_zero.mp hcoordZero).resolve_left hsqrt
  exact (sub_eq_zero.mp hdiff).symm

/-- Vanishing of the integrated screw feature forces the physical cutoff itself to vanish.  The
proof passes from all Xi coordinates to all zeros of `xi(1/2-Iz)` and invokes Suzuki Lemma 2.1 via
the compact-`L²` Fourier uniqueness theorem. -/
theorem suzukiCutoff_eq_zero_of_featureIntegral_eq_zero
    {a : ℝ} (ha : 0 ≤ a) (hRH : RiemannHypothesis) (f : SoninL2)
    (hfeature : suzukiScrewFeatureIntegral hRH a f = 0) :
    suzukiCutoff a f = 0 := by
  apply suzukiCutoff_eq_zero_of_fourier_constant_on_xiZeros ha f
    (c := suzukiCompactL2Fourier a f 0)
  intro z hz
  have hnegXi : XiC (-z) = 0 := by
    rw [XiC]
    convert hz using 1 <;> ring
  have hXi : XiC z = 0 := by
    rw [XiC_even] at hnegXi
    exact hnegXi
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hXi
  have hreal := xiSpectralPoint_eq_ofReal_of_rh hRH q
  have hgamma : ((xiRealSpectralPoint q : ℝ) : ℂ) = z := hreal.symm.trans hq
  rw [← hgamma]
  exact suzukiCompactL2Fourier_eq_zeroValue_of_featureIntegral_eq_zero
    ha hRH f hfeature q

/-- **Suzuki (2022), Theorem 1.3, strict `L²` clause.**  Assuming RH, the paper's literal
Hermitian form is strictly positive on every nonzero element of `L²(-a,a)`, for every finite
positive aperture. -/
theorem suzuki_theorem_one_three_strict_l2
    (hRH : RiemannHypothesis) {a : ℝ} (ha : 0 < a)
    (f : SuzukiApertureL2 a) (hf : (f : SoninL2) ≠ 0) :
    0 < (suzukiScrewL2Form a f f).re := by
  have hfeature : suzukiScrewFeatureIntegral hRH a (f : SoninL2) ≠ 0 := by
    intro hzero
    have hcut := suzukiCutoff_eq_zero_of_featureIntegral_eq_zero ha.le hRH f hzero
    have hfzero : (f : SoninL2) = 0 := by rw [← f.property, hcut]
    exact hf hfzero
  rw [suzukiScrewL2Form_eq_inner_featureIntegral_of_rh ha.le hRH]
  rw [inner_self_eq_norm_sq_to_K]
  change 0 < (((‖suzukiScrewFeatureIntegral hRH a (f : SoninL2)‖ : ℝ) : ℂ) ^ 2).re
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  exact sq_pos_of_pos (norm_pos_iff.mpr hfeature)

end RHTower
