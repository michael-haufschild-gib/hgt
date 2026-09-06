import GaloisForLFunctions.RHTower.CCMRestrictedWeilGammaPolarAbsoluteBound
import GaloisForLFunctions.RHTower.CCMRestrictedWeilGammaMixedJump
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarOperatorDomain

/-!
# Physical Gamma operator action on the truncated positive pole

The actual compressed Gamma multiplier image equals the explicit exponential
profile times a linear bulk term, the Hardy-phase constant, and two logarithmic
boundary tails. The identification uses the absolute jump bound to prove joint
integrability against strict-interior tests, Fubini, the complete mixed Gamma
form identity, and smooth-test separation of locally integrable coefficients.
The existing operator representative supplies global L² membership; no endpoint
regularity or unproved interchange is assumed.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

private def massBound (a : SuzukiPositiveAperture) (x : ℝ) : ℝ :=
  -(Complex.digamma (1/4)).re - Real.eulerMascheroniConstant - Real.log 2 + (a.1-x) +
    ccmGammaPolarBoundary (a.1-x) (a.1+x)

private theorem boundary_continuousOn (a : SuzukiPositiveAperture) :
    ContinuousOn (fun x => ccmGammaPolarBoundary (a.1-x) (a.1+x)) (Ioo (-a.1) a.1) := by
  intro x hx
  have hR : 1-Real.exp (-(2*(a.1-x))) ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (by linarith [hx.2])))
  have hL : 1-Real.exp (-(a.1+x)) ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (by linarith [hx.1])))
  have hL2 : 1-Real.exp (-(2*(a.1+x))) ≠ 0 := ne_of_gt (sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (by linarith [hx.1])))
  apply ContinuousAt.continuousWithinAt
  unfold ccmGammaPolarBoundary
  fun_prop

private def testKernel (a : SuzukiPositiveAperture) (g : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  (g p.2 * Real.exp (p.2/2) * ccmGammaPolarJumpKernel (a.1-p.2) (a.1+p.2) p.1 : ℝ)

private theorem testKernel_measurable (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hg : Continuous g) : Measurable (testKernel a g) := by
  have hR : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a.1-p.2} :=
    measurableSet_le measurable_fst (measurable_const.sub measurable_snd)
  have hL : MeasurableSet {p : ℝ × ℝ | p.1 ≤ a.1+p.2} :=
    measurableSet_le measurable_fst (measurable_const.add measurable_snd)
  have hp : Measurable (fun p : ℝ × ℝ => if p.1 ≤ a.1-p.2 then Real.exp (p.1/2) else 0) :=
    Measurable.ite hR (by fun_prop) measurable_const
  have hm : Measurable (fun p : ℝ × ℝ => if p.1 ≤ a.1+p.2 then Real.exp (-(p.1/2)) else 0) :=
    Measurable.ite hL (by fun_prop) measurable_const
  unfold testKernel ccmGammaPolarJumpKernel ccmGammaTranslationDensity
  fun_prop

private theorem testKernel_integrable (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo (-a.1) a.1) :
    Integrable (testKernel a g) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
  have hmeas := testKernel_measurable a g hg
  have hcont : ContinuousOn (fun x => Real.exp (x/2)*massBound a x) (tsupport g) := by
    apply ContinuousOn.mul (by fun_prop)
    exact ((continuousOn_const.add (continuousOn_const.sub continuousOn_id)).add
      ((boundary_continuousOn a).mono hgs))
  obtain ⟨M,hM⟩ := hgc.exists_bound_of_continuousOn hcont
  have hslices (x : ℝ) : IntegrableOn (fun h => testKernel a g (h,x)) (Ioi (0:ℝ)) := by
    by_cases hx : g x = 0
    · simp [testKernel, hx]
    · have hxin := hgs (subset_tsupport g (Function.mem_support.mpr hx))
      exact Complex.ofRealCLM.integrable_comp
        ((integrableOn_ccmGammaPolarJumpKernel (R:=a.1-x) (L:=a.1+x) (by linarith [hxin.2])
          (by linarith [hxin.1])).const_mul (g x * Real.exp (x/2)))
  apply (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hslices, ?_⟩
  have hdom : Integrable (fun x => |M| * ‖g x‖) (volume : Measure ℝ) :=
    (hg.norm.integrable_of_hasCompactSupport hgc.norm).const_mul |M|
  apply hdom.mono' hmeas.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  by_cases hx : g x = 0
  · simp [testKernel, hx]
  · have hxK : x ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hx)
    have hxin := hgs hxK
    have hmass := integral_abs_ccmGammaPolarJumpKernel_le
      (show 0<a.1-x by linarith [hxin.2]) (show 0<a.1+x by linarith [hxin.1])
    norm_num at hmass
    change (∫ h in Ioi (0:ℝ), |ccmGammaPolarJumpKernel (a.1-x) (a.1+x) h|) ≤ massBound a x at hmass
    have hnorm : (∫ h in Ioi (0:ℝ), ‖testKernel a g (h,x)‖) =
        |g x| * Real.exp (x/2) * ∫ h in Ioi (0:ℝ),
          |ccmGammaPolarJumpKernel (a.1-x) (a.1+x) h| := by
      simp only [testKernel, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      rw [integral_const_mul]
    rw [hnorm]
    calc
      |g x| * Real.exp (x/2) * (∫ h in Ioi (0:ℝ),
          |ccmGammaPolarJumpKernel (a.1-x) (a.1+x) h|) ≤
          |g x| * (Real.exp (x/2)*massBound a x) := by
        nlinarith [mul_le_mul_of_nonneg_left hmass
          (mul_nonneg (abs_nonneg (g x)) (Real.exp_pos (x/2)).le)]
      _ ≤ |g x| * |M| := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans ((hM x hxK).trans (le_abs_self M))) (abs_nonneg _)
      _ = _ := by simp only [Real.norm_eq_abs]; ring

private def excessProfile (a : SuzukiPositiveAperture) (x : ℝ) : ℂ :=
  (Real.exp (x/2) * (-(a.1-x) - (Complex.digamma (1/4)).re - Real.eulerMascheroniConstant -
    Real.log 2 + ccmGammaPolarBoundary (a.1-x) (a.1+x)) : ℝ)

private theorem excessProfile_continuousOn (a : SuzukiPositiveAperture) :
    ContinuousOn (excessProfile a) (Ioo (-a.1) a.1) := by
  have hB := boundary_continuousOn a
  unfold excessProfile
  fun_prop

private theorem integral_testKernel_right (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hgs : tsupport g ⊆ Ioo (-a.1) a.1) (x : ℝ) :
    (∫ h in Ioi (0:ℝ), testKernel a g (h,x)) = g x • excessProfile a x := by
  by_cases hx : g x = 0
  · simp [testKernel, hx]
  · have hxin := hgs (subset_tsupport g (Function.mem_support.mpr hx))
    simp only [testKernel]
    rw [integral_complex_ofReal, integral_const_mul,
      integral_ccmGammaPolarJumpKernel (show 0<a.1-x by linarith [hxin.2])
        (show 0<a.1+x by linarith [hxin.1])]
    simp only [excessProfile, Complex.real_smul]
    push_cast
    ring!

private theorem testProfile_integrable (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ Ioo (-a.1) a.1) :
    Integrable (fun x => g x • excessProfile a x) := by
  have h := (testKernel_integrable a g hg hgc hgs).integral_prod_right
  simpa only [integral_testKernel_right a g hgs] using h

private def excessVector (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ccmPolarArchimedeanRepresentative a (1/2) - ccmPolarApertureVector a (1/2)

private theorem excessVector_pair_test (a : SuzukiPositiveAperture) (g : ℝ → ℝ)
    (hgd : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hgs : tsupport g ⊆ Ioo (-a.1) a.1) :
    inner ℂ (excessVector a).1 (suzukiRealTestL2 g hgd hgc) =
      ∫ x : ℝ, g x • excessProfile a x := by
  obtain ⟨v,hv⟩ := exists_ccmArchimedeanFormDomain_eq_smoothRealTest a g hgd hgc hgs
  have hvcoe : ((ccmArchimedeanFormToAperture a v : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (fun x => (g x : ℂ)) := by
    rw [ccmArchimedeanFormToAperture_coe, hv]
    exact suzukiRealTestL2_coeFn g hgd hgc
  have hpoint (h : ℝ) (hh : 0<h) :
      inner ℂ ((ccmGammaTranslationDensity h : ℂ) •
        ((2:ℂ) • ccmPolarApertureVector a (1/2) -
          ccmApertureCompression a (ccmSymmetricLogTranslation h) (ccmPolarApertureVector a (1/2))))
            (ccmArchimedeanFormToAperture a v) = ∫ x : ℝ, testKernel a g (h,x) := by
    change inner ℂ
      (((ccmGammaTranslationDensity h : ℂ) • ((2:ℂ) • ccmPolarApertureVector a (1/2) -
        ccmApertureCompression a (ccmSymmetricLogTranslation h) (ccmPolarApertureVector a (1/2))) :
          suzukiApertureHilbert a) : SoninL2)
      (ccmArchimedeanFormToAperture a v : SoninL2) = _
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ccmGammaPolarJump_source_coeFn a hh, hvcoe] with x hj hg
    rw [hj, hg]
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx]
      simp only [testKernel, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
      push_cast
      ring!
    · have hgzero : g x=0 := by
        by_contra hne
        exact hx (Ioo_subset_Icc_self (hgs (subset_tsupport g (Function.mem_support.mpr hne))))
      simp [indicator_of_notMem hx, hgzero, testKernel]
  have hpair := integral_ccmGammaCompressedJump_pair a (ccmPolarFormVector a (1/2)) v
  rw [ccmArchimedeanFormToAperture_polar] at hpair
  have hi : (∫ h in Ioi (0:ℝ), inner ℂ ((ccmGammaTranslationDensity h : ℂ) •
      ((2:ℂ) • ccmPolarApertureVector a (1/2) -
        ccmApertureCompression a (ccmSymmetricLogTranslation h) (ccmPolarApertureVector a (1/2))))
          (ccmArchimedeanFormToAperture a v)) =
      ∫ x : ℝ, g x • excessProfile a x := by
    calc
      _ = ∫ h in Ioi (0:ℝ), ∫ x : ℝ, testKernel a g (h,x) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
        exact hpoint h hh
      _ = ∫ x : ℝ, ∫ h in Ioi (0:ℝ), testKernel a g (h,x) :=
        integral_integral_swap (f := fun h x => testKernel a g (h,x))
          (testKernel_integrable a g hgd.continuous hgc hgs)
      _ = _ := by simp only [integral_testKernel_right a g hgs]
  rw [hpair] at hi
  rw [inner_ccmPolarArchimedeanRepresentative] at hi
  have h : inner ℂ (excessVector a) (ccmArchimedeanFormToAperture a v) =
      ∫ x : ℝ, g x • excessProfile a x := by
    rw [excessVector, inner_sub_left]
    exact hi
  change inner ℂ (excessVector a).1 (ccmArchimedeanFormEmbedding a v) = _ at h
  rwa [hv] at h

private theorem excessVector_coeFn_inside (a : SuzukiPositiveAperture) :
    ∀ᵐ x : ℝ, x ∈ Ioo (-a.1) a.1 → ((excessVector a).1 : ℝ → ℂ) x = excessProfile a x := by
  let r : SoninL2 := (excessVector a).1
  have hr : LocallyIntegrableOn (r : ℝ → ℂ) (Ioo (-a.1) a.1) volume :=
    ((Lp.memLp r).locallyIntegrable (by norm_num)).locallyIntegrableOn _
  have hrc : LocallyIntegrableOn (fun x => (starRingEnd ℂ) (r x)) (Ioo (-a.1) a.1) volume :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).locallyIntegrableOn_comp hr
  have he : LocallyIntegrableOn (excessProfile a) (Ioo (-a.1) a.1) volume :=
    (excessProfile_continuousOn a).locallyIntegrableOn measurableSet_Ioo
  have hzero : ∀ᵐ x : ℝ, x ∈ Ioo (-a.1) a.1 → (starRingEnd ℂ) (r x) - excessProfile a x = 0 := by
    apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hrc.sub he)
    intro g hgd hgc hgs
    have htcoe := suzukiRealTestL2_coeFn g hgd hgc
    have hfun : (fun x => inner ℂ (r x) ((suzukiRealTestL2 g hgd hgc : SoninL2) x)) =ᵐ[volume]
        (fun x => g x • (starRingEnd ℂ) (r x)) := by
      filter_upwards [htcoe] with x hx
      rw [hx]
      simp only [suzukiRealTestComplex, RCLike.inner_apply, Complex.real_smul]
    have hri := (MeasureTheory.L2.integrable_inner (𝕜:=ℂ) r (suzukiRealTestL2 g hgd hgc)).congr hfun
    have hei := testProfile_integrable a g hgd.continuous hgc hgs
    have hi := excessVector_pair_test a g hgd hgc hgs
    change inner ℂ r (suzukiRealTestL2 g hgd hgc) = _ at hi
    rw [MeasureTheory.L2.inner_def, integral_congr_ae hfun] at hi
    change (∫ x : ℝ, g x • ((starRingEnd ℂ) (r x) - excessProfile a x)) = 0
    simp_rw [smul_sub]
    rw [integral_sub hri hei, hi, sub_self]
  filter_upwards [hzero] with x hx
  intro hxin
  have h := congrArg (starRingEnd ℂ) (sub_eq_zero.mp (hx hxin))
  simpa only [starRingEnd_self_apply, excessProfile, Complex.conj_ofReal] using h

private theorem excessVector_coeFn (a : SuzukiPositiveAperture) :
    ((excessVector a).1 : ℝ → ℂ) =ᵐ[volume] (centralInterval a.1).indicator (excessProfile a) := by
  let r := excessVector a
  have hfix := indicatorCutoff_suzukiApertureHilbert a r
  have hout : ∀ᵐ x : ℝ, x ∉ centralInterval a.1 → (r.1 : ℝ → ℂ) x = 0 := by
    have hae := indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) r.1
    rw [hfix] at hae
    filter_upwards [hae] with x hx
    intro hxin
    rw [hx, indicator_of_notMem hxin]
  have hleft : ∀ᵐ x : ℝ, x ≠ -a.1 := by rw [ae_iff]; simp
  have hright : ∀ᵐ x : ℝ, x ≠ a.1 := by rw [ae_iff]; simp
  filter_upwards [excessVector_coeFn_inside a, hout, hleft, hright] with x hi ho hl hr
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    exact hi ⟨lt_of_le_of_ne hx.1 (Ne.symm hl), lt_of_le_of_ne hx.2 hr⟩
  · rw [indicator_of_notMem hx]
    exact ho hx

/-- The exact compressed Gamma multiplier image of the positive pole, with its physical normalization. -/
def ccmPolarGammaImage (a : SuzukiPositiveAperture) : suzukiApertureHilbert a :=
  ccmPolarArchimedeanRepresentative a (1/2) +
    ccmArchimedeanRemainderScalar • ccmPolarApertureVector a (1/2)

/-- The physical Gamma operator action on the actual truncated pole profile, including both boundaries. -/
theorem ccmPolarGammaImage_coeFn (a : SuzukiPositiveAperture) :
    ((ccmPolarGammaImage a : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a.1).indicator (fun x =>
        (Real.exp (x/2) * (-(a.1-x) - Real.eulerMascheroniConstant - Real.log (2*Real.pi) +
          ccmGammaPolarBoundary (a.1-x) (a.1+x)) : ℝ)) := by
  have hid : ccmPolarGammaImage a = excessVector a +
      ((2*gammaHardyPhaseRate 0 : ℝ) : ℂ) • ccmPolarApertureVector a (1/2) := by
    unfold ccmPolarGammaImage excessVector ccmArchimedeanRemainderScalar
    push_cast
    module
  have hidL : (ccmPolarGammaImage a : SoninL2) = (excessVector a).1 +
      ((2*gammaHardyPhaseRate 0 : ℝ) : ℂ) • ccmPolarL2Vector a (1/2) :=
    congrArg Subtype.val hid
  rw [hidL]
  have hphase : 2*gammaHardyPhaseRate 0 = (Complex.digamma (1/4:ℂ)).re - Real.log Real.pi := by
    unfold gammaHardyPhaseRate linePt
    norm_num
    ring
  have hlog := Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_pos.ne'
  filter_upwards [Lp.coeFn_add (excessVector a).1
      (((2*gammaHardyPhaseRate 0 : ℝ) : ℂ) • ccmPolarL2Vector a (1/2)),
    Lp.coeFn_smul ((2*gammaHardyPhaseRate 0 : ℝ) : ℂ) (ccmPolarL2Vector a (1/2)),
    excessVector_coeFn a, ccmPolarL2Vector_coeFn a (1/2)] with x ha hs he hp
  simp only [Pi.add_apply, Pi.smul_apply] at ha hs
  rw [ha, hs, he, hp]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
    simp only [excessProfile, ccmPolarProfile, smul_eq_mul,
      show (1/2:ℝ)*x=x/2 from by ring]
    have hreal : Real.exp (x/2) * (-(a.1-x) - (Complex.digamma (1/4:ℂ)).re -
        Real.eulerMascheroniConstant - Real.log 2 + ccmGammaPolarBoundary (a.1-x) (a.1+x)) +
        (2*gammaHardyPhaseRate 0)*Real.exp (x/2) =
      Real.exp (x/2) * (-(a.1-x) - Real.eulerMascheroniConstant - Real.log (2*Real.pi) +
        ccmGammaPolarBoundary (a.1-x) (a.1+x)) := by rw [hphase, hlog]; ring
    exact_mod_cast hreal
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, indicator_of_notMem hx]
    simp

/-- Exact Gamma–polar–prime splitting of the actual unrestricted Weil operator on the positive pole. -/
theorem ccmRestrictedWeilOperator_polarHalf_eq_gamma_polar_prime (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilOperator a
      ⟨ccmPolarApertureVector a (1/2), ccmPolarApertureVector_mem_weilOperator_domain a (1/2)⟩ =
      ccmPolarGammaImage a + ccmPolarOperator a (ccmPolarApertureVector a (1/2)) -
        ccmFinitePrimeOperator a (ccmPolarApertureVector a (1/2)) := by
  rw [ccmRestrictedWeilOperator_polar_apply]
  unfold ccmPolarWeilRepresentative ccmRestrictedWeilBoundedRemainder ccmPolarGammaImage
  simp only [add_apply, sub_apply, smul_apply, one_apply_eq_self]
  module
end RHTower
