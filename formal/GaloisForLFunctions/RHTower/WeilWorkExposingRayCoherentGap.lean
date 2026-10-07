import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityHalfLogTwo
import GaloisForLFunctions.RHTower.WeilPositivityPrimeBlindDuality
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import GaloisForLFunctions.RHTower.WeilPositivitySparseWeightsObstruction

/-!
# C2 admission and the short-source energy gap

The exact weighted CCM form domain admits every literal compact C2 source. At aperture
`log(2)/2`, the corpus's one-tenth pole-vanishing ground gap therefore gives
`archEnergy(f) >= (pi/5) * integral norm(f)^2` in the actual paper Fourier convention.

The actual short far-polar Fejer source has a fixed plateau on `[-3/10,3/10]`.
This yields an explicit energy floor for every step in `[0,1/200]`, including steps tending
to zero. The finite geometric completion consumes this bound through its exact mass-defect
identity. No global Weil positivity or Riemann-hypothesis assumption is made.
-/

open MeasureTheory Real Set Filter Complex Topology Zeta23
open scoped FourierTransform ENNReal InnerProduct
noncomputable section
namespace RHTower.ExposingRayCoherentGap

private theorem compact_source {a : ℝ} {f : ℝ → ℂ} (hfs : tsupport f ⊆ Icc (-a) a) :
    HasCompactSupport f := isCompact_Icc.of_isClosed_subset isClosed_closure hfs

private theorem arch_even (x : ℝ) : archimedeanWeilSymbol (-x) = archimedeanWeilSymbol x := by
  unfold archimedeanWeilSymbol
  rw [mul_neg, gammaHardyPhaseRate_neg]

private theorem fourier_arch_point (f : ℝ → ℂ) (x : ℝ) :
    ‖paperFT f (((-(2*π))*x : ℝ) : ℂ)‖^2 * archimedeanWeilSymbol ((-(2*π))*x/(2*π)) =
      archimedeanWeilSymbol x * ‖𝓕 f x‖^2 := by
  rw [WeilDeletion.fourier_eq_paperFT]
  have harg : (-(2*π))*x/(2*π) = -x := by field_simp
  rw [harg, arch_even]
  push_cast
  ring_nf

private theorem weighted_fourier {a : ℝ} {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-a) a) : MemLp (𝓕 f) 2 ccmArchimedeanFormMeasure := by
  have hfc := compact_source hfs
  have hf1 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hc := GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hf1
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  unfold ccmArchimedeanFormMeasure
  rw [integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal]
  have hk : -(2*π) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have i0 := (integrable_normSq_paperFT hf hfs).comp_mul_left' hk
  have ia := (integrable_normSq_paperFT_mul_arch hf hfs).comp_mul_left' hk
  apply (ia.add (i0.const_mul (1-2*gammaHardyPhaseRate 0))).congr
  filter_upwards with x
  simp only [Pi.add_apply, NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]
  rw [fourier_arch_point, ccmArchimedeanFormWeight_eq_linearArgument, WeilDeletion.fourier_eq_paperFT]
  rw [show (-(2*π))*x = -(2*π*x) by ring]
  unfold archimedeanWeilSymbol
  push_cast
  ring

/-- Direct admission of a literal compact C2 source into the exact weighted CCM form domain. -/
theorem c2_source_admission (a : SuzukiPositiveAperture) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a.1) a.1) :
    ∃ u : CCMArchimedeanFormDomain a,
      ((u.1 : ℝ → ℂ) =ᵐ[volume] 𝓕 f) ∧
      (((ccmArchimedeanFormToAperture a u : SoninL2) : ℝ → ℂ) =ᵐ[volume] f) := by
  have hfc := compact_source hfs
  have hf1 : Integrable f := hf.continuous.integrable_of_hasCompactSupport hfc
  have hf2 : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport hfc
  let hF := weighted_fourier hf hfs
  let w : CCMArchimedeanFourierL2 := hF.toLp (𝓕 f)
  have hwF : (w : ℝ → ℂ) =ᵐ[volume] 𝓕 f :=
    hF.coeFn_toLp.filter_mono (ae_mono volume_le_ccmArchimedeanFormMeasure)
  have hwToL2 : ccmArchimedeanWeightedToL2 w = fourierUnitary (hf2.toLp f) := by
    apply Lp.ext
    have hfl := GaloisForLFunctions.RHTower.coeFn_fourier_toLp hf1 hf2
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn w, hwF, hfl] with x h1 h2 h3
    exact h1.trans (h2.trans h3.symm)
  have htime : ccmArchimedeanFourierToTime w = hf2.toLp f := by
    apply fourierUnitary.injective
    rw [fourierUnitary_ccmArchimedeanFourierToTime, hwToL2]
  have hfix : indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
      (hf2.toLp f) = hf2.toLp f := by
    apply Lp.ext
    filter_upwards [indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1)
      (hf2.toLp f), hf2.coeFn_toLp] with x hcut hcoe
    rw [hcut]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hcoe]
      symm
      apply Function.notMem_support.mp
      intro h
      exact hx (hfs (subset_tsupport f h))
  have hwker : w ∈ (ccmArchimedeanSupportDefect a).ker := by
    rw [LinearMap.mem_ker]
    change (1-indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1))
      (ccmArchimedeanFourierToTime w) = 0
    rw [htime, sub_apply, one_apply_eq_self, hfix, sub_self]
  refine ⟨⟨w,hwker⟩, hwF, ?_⟩
  change (ccmArchimedeanFourierToTime w : ℝ → ℂ) =ᵐ[volume] f
  rw [htime]
  exact hf2.coeFn_toLp

private theorem polar_moment {a : SuzukiPositiveAperture} {f : ℝ → ℂ}
    (hfs : tsupport f ⊆ Icc (-a.1) a.1) (u : CCMArchimedeanFormDomain a)
    (hu : ((ccmArchimedeanFormToAperture a u : SoninL2) : ℝ → ℂ) =ᵐ[volume] f) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s) (ccmArchimedeanFormToAperture a u) =
      paperFT f (-(s : ℂ)*I) := by
  have hp := ccmPolarL2Vector_coeFn a s
  change inner ℂ (ccmPolarL2Vector a s) (ccmArchimedeanFormToAperture a u : SoninL2) = _
  rw [L2.inner_def]
  unfold paperFT
  apply integral_congr_ae
  filter_upwards [hp,hu] with x hpx hfx
  rw [hpx,hfx]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    simp only [ccmPolarProfile, RCLike.inner_apply]
    rw [Complex.conj_ofReal]
    have he : I * (-(s : ℂ)*I) * (x : ℂ) = ((s*x : ℝ) : ℂ) := by
      calc _ = -(s : ℂ)*(x : ℂ)*(I*I) := by ring
        _ = _ := by rw [I_mul_I]; push_cast; ring
    rw [he, Complex.ofReal_exp]
  · rw [indicator_of_notMem hx]
    have hz : f x = 0 := by
      apply Function.notMem_support.mp
      intro h
      exact hx (hfs (subset_tsupport f h))
    simp [hz]

private theorem archEnergy_eq_scaled_fourier (f : ℝ → ℂ) :
    archEnergy f = (2*π) * (∫ x : ℝ, archimedeanWeilSymbol x * ‖𝓕 f x‖^2) := by
  have h := Measure.integral_comp_mul_left
    (fun t : ℝ => ‖paperFT f t‖^2*archimedeanWeilSymbol (t/(2*π))) (-(2*π))
  have heq : (∫ x : ℝ, ‖paperFT f (((-(2*π))*x : ℝ) : ℂ)‖^2 *
      archimedeanWeilSymbol ((-(2*π))*x/(2*π))) =
      ∫ x : ℝ, archimedeanWeilSymbol x * ‖𝓕 f x‖^2 := by
    exact integral_congr_ae (Eventually.of_forall (fourier_arch_point f))
  rw [heq] at h
  have habs : |(-(2*π))⁻¹| = (2*π)⁻¹ := by
    rw [inv_neg,abs_neg,abs_of_pos (by positivity)]
  rw [habs,smul_eq_mul] at h
  change _ = (2*π)⁻¹ * archEnergy f at h
  have hp : 2*π ≠ 0 := by positivity
  field_simp at h
  linarith

private theorem physical_norm {a : SuzukiPositiveAperture} {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a.1) a.1)
    (u : CCMArchimedeanFormDomain a) (huF : (u.1 : ℝ → ℂ) =ᵐ[volume] 𝓕 f) :
    ‖ccmArchimedeanFormToAperture a u‖^2 = ∫ x : ℝ, ‖f x‖^2 := by
  have hfc := compact_source hfs
  rw [← integral_norm_sq_ccmFormDomain]
  calc _ = ∫ x : ℝ, ‖𝓕 f x‖^2 := integral_congr_ae (huF.fun_comp (fun z : ℂ => ‖z‖^2))
    _ = _ := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
      (hf.continuous.integrable_of_hasCompactSupport hfc)
      (hf.continuous.memLp_of_hasCompactSupport hfc)

/-- The established one-tenth polar ground gap applies to the literal C2 test class. -/
theorem c2_halfLogTwo_coercivity {f : ℝ → ℂ}
    (hf : IsPolarTest (Real.log 2/2) f) :
    (π/5) * (∫ x : ℝ, ‖f x‖^2) ≤ archEnergy f := by
  obtain ⟨u,huF,huf⟩ := c2_source_admission halfLogTwoAperture hf.2.1 hf.2.2.1
  have hpol : IsPolarConstrained halfLogTwoAperture u := by
    constructor
    · rw [polar_moment hf.2.2.1 u huf]
      have he : -((1/2 : ℝ) : ℂ)*I = -(I/2) := by push_cast; ring
      rw [he]
      exact hf.2.2.2.2
    · rw [polar_moment hf.2.2.1 u huf]
      have he : -((-1/2 : ℝ) : ℂ)*I = I/2 := by push_cast; ring
      rw [he]
      exact hf.2.2.2.1
  have hlo := (mul_le_mul_of_nonneg_right one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo
    (sq_nonneg ‖ccmArchimedeanFormToAperture halfLogTwoAperture u‖)).trans
      (ccmRestrictedWeilPolarGroundEnergy_mul_le halfLogTwoAperture u hpol)
  rw [physical_norm hf.2.1 hf.2.2.1 u huF, ccmRestrictedWeilSourceQuadratic_halfLogTwo_eq u hpol] at hlo
  have heq : (∫ x : ℝ, archimedeanWeilSymbol x * ‖(u.1 : ℝ → ℂ) x‖^2) =
      ∫ x : ℝ, archimedeanWeilSymbol x * ‖𝓕 f x‖^2 := by
    apply integral_congr_ae
    filter_upwards [huF] with x hx
    rw [hx]
  rw [heq] at hlo
  have hm := mul_le_mul_of_nonneg_left hlo (by positivity : 0 ≤ 2*π)
  rw [archEnergy_eq_scaled_fourier]
  nlinarith

private theorem far_plateau {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/200)
    {x : ℝ} (hx : x ∈ Icc (-(3/10)) (3/10)) :
    farPolarTest s x = ((1-farPolarCoeff s : ℝ) : ℂ) := by
  have hψ : ∀ y : ℝ, |y| ≤ 61/200 → fejerTest y = 1 := by
    intro y hy
    unfold fejerTest
    rw [flatBump_eq_one (by norm_num : (0 : ℝ) < 17/1000) (by linarith)]
    norm_num
  have hx0 : |x| ≤ (61/200 : ℝ) := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hxm : |x-s| ≤ (61/200 : ℝ) := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  have hxp : |x+s| ≤ (61/200 : ℝ) := abs_le.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
  rw [farPolarTest,hψ x hx0,hψ (x-s) hxm,hψ (x+s) hxp]
  push_cast
  ring

/-- The literal short polar source retains a fixed plateau after normalization. -/
theorem short_source_norm_floor {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/200) :
    (3/5 : ℝ)*(1-farPolarCoeff s)^2 ≤ ∫ x : ℝ, ‖farPolarTest s x‖^2 := by
  have hf2 : MemLp (farPolarTest s) 2 volume :=
    (contDiff_farPolarTest s).continuous.memLp_of_hasCompactSupport
      (compact_source (tsupport_farPolarTest hs0))
  have hi : Integrable (fun x : ℝ => ‖farPolarTest s x‖^2) :=
    (memLp_two_iff_integrable_sq_norm hf2.aestronglyMeasurable).1 hf2
  have hle := setIntegral_le_integral (s := Icc (-(3/10 : ℝ)) (3/10)) hi
    (Eventually.of_forall (fun x => sq_nonneg ‖farPolarTest s x‖))
  have heq : (∫ x in Icc (-(3/10 : ℝ)) (3/10), ‖farPolarTest s x‖^2) =
      (3/5 : ℝ)*(1-farPolarCoeff s)^2 := by
    calc _ = ∫ _ in Icc (-(3/10 : ℝ)) (3/10), (1-farPolarCoeff s)^2 := by
          apply setIntegral_congr_fun measurableSet_Icc
          intro x hx
          change ‖farPolarTest s x‖^2 = (1-farPolarCoeff s)^2
          rw [far_plateau hs0 hs hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      _ = _ := by rw [setIntegral_const,Real.volume_real_Icc]; norm_num
  rwa [heq] at hle

/-- The existing one-tenth ground gap gives an explicit bound for every short step. -/
theorem short_source_energy_floor {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1/200) :
    (3*π/25)*(1-farPolarCoeff s)^2 ≤ archEnergy (farPolarTest s) := by
  have ha : s+17/50 ≤ Real.log 2/2 := by have := Real.log_two_gt_d9; linarith
  have hf : IsPolarTest (Real.log 2/2) (farPolarTest s) := by
    refine ⟨by positivity,contDiff_farPolarTest s,?_,paperFT_farPolarTest_half_I s,
      paperFT_farPolarTest_neg_half_I s⟩
    intro x hx
    have h := tsupport_farPolarTest hs0 hx
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  have h := mul_le_mul_of_nonneg_left (short_source_norm_floor hs0 hs) (by positivity : 0 ≤ π/5)
  calc _ = (π/5)*((3/5 : ℝ)*(1-farPolarCoeff s)^2) := by ring
    _ ≤ _ := h.trans (c2_halfLogTwo_coercivity hf)

end RHTower.ExposingRayCoherentGap
