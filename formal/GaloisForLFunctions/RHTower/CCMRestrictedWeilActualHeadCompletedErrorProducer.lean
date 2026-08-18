import GaloisForLFunctions.RHTower.CCMRestrictedWeilCanonicalHeadCompletedErrorControl
import GaloisForLFunctions.RHTower.SuzukiCanonicalL1Translation
import GaloisForLFunctions.RHTower.SuzukiCCMMixedPolarFactorization
import GaloisForLFunctions.RHTower.SuzukiRayleighInfimum
import GaloisForLFunctions.RHTower.L2FourierEndpointOrthogonality

/-!
# Actual-head completed-error producer

This module closes the regularity and cancellation gap in the Route O producer.  For every actual
complex `L²` aperture head `f`, the polar autocorrelation debt is exactly

`integral_[0,2a] 2 cosh(h/2) * ||U_h f - f||^2 dh`.

The proof starts from the literal mixed CCM polar factorization on strict-interior smooth sources,
proves continuity of the translation-defect integral on the full aperture Hilbert space, and uses
the already-certified dense source range.  It therefore introduces no differentiability of the
head autocorrelation.  Exact null overlap at the aperture-diameter translate also gives

`||U_(2a) f - f||^2 = 2 ||f||^2`.

Consequently the prime atoms, polar continuum, and completed endpoint combine into one signed
quadrature of the same actual-head defect profile.  On canonical finite Gamma--Slepian heads this
numeric producer is exactly the restricted-Weil quadratic, hence exactly the literal reverse-prime
target, while retaining the known nonnegative vanishing head-tail defect.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

def realL2Translate (t : ℝ) (f : SoninL2) : SoninL2 :=
  Lp.compMeasurePreserving (realAddTranslationFamily t)
    (measurePreserving_realAddTranslationFamily t) f

theorem realL2Translate_eq_logTranslationCLM (t : ℝ) (f : SoninL2) :
    realL2Translate t f = logTranslationCLM t f := by
  change Lp.compMeasurePreserving (realAddTranslationFamily t)
      (measurePreserving_realAddTranslationFamily t) f =
    Lp.compMeasurePreserving (MellinL2.realTranslationEquiv t)
      (MellinL2.realTranslation_measurePreserving t) f
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      (measurePreserving_realAddTranslationFamily t),
    Lp.coeFn_compMeasurePreserving f
      (MellinL2.realTranslation_measurePreserving t)] with x hleft hright
  rw [hleft, hright]
  simp only [Function.comp_apply, realAddTranslationFamily_apply,
    MellinL2.realTranslationEquiv]
  change f (t + x) = f (x + t)
  rw [add_comm]

theorem continuous_realL2Translate_joint :
    Continuous fun p : ℝ × SoninL2 => realL2Translate p.1 p.2 := by
  exact (continuous_snd : Continuous fun p : ℝ × SoninL2 => p.2).compMeasurePreservingLp
    (realAddTranslationFamily.continuous.comp continuous_fst)
    (fun p => measurePreserving_realAddTranslationFamily p.1) (by norm_num)

theorem continuous_realL2Translate (f : SoninL2) :
    Continuous fun t : ℝ => realL2Translate t f := by
  exact (continuous_const : Continuous fun _ : ℝ => f).compMeasurePreservingLp
    realAddTranslationFamily.continuous
    measurePreserving_realAddTranslationFamily (by norm_num)

theorem continuous_logTranslationCLM (f : SoninL2) :
    Continuous fun t : ℝ => logTranslationCLM t f := by
  rw [show (fun t : ℝ => logTranslationCLM t f) =
      fun t => realL2Translate t f by
    funext t
    exact (realL2Translate_eq_logTranslationCLM t f).symm]
  exact continuous_realL2Translate f

theorem continuous_logTranslationCLM_joint :
    Continuous fun p : ℝ × SoninL2 => logTranslationCLM p.1 p.2 := by
  rw [show (fun p : ℝ × SoninL2 => logTranslationCLM p.1 p.2) =
      fun p => realL2Translate p.1 p.2 by
    funext p
    exact (realL2Translate_eq_logTranslationCLM p.1 p.2).symm]
  exact continuous_realL2Translate_joint

def ccmActualHeadTranslationDefect (h : ℝ) (f : SoninL2) : ℝ :=
  ‖logTranslationCLM h f - f‖ ^ 2

theorem continuous_ccmActualHeadTranslationDefect_joint :
    Continuous fun p : ℝ × SoninL2 => ccmActualHeadTranslationDefect p.1 p.2 := by
  unfold ccmActualHeadTranslationDefect
  exact ((continuous_logTranslationCLM_joint.sub continuous_snd).norm).pow 2

def ccmContinuousPolarTranslationDefectEnergy
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  ∫ h in Icc (0 : ℝ) (2 * a.1),
    2 * Real.cosh (h / 2) * ccmActualHeadTranslationDefect h f.1

theorem ccmActualHeadTranslationDefect_le
    (h : ℝ) (f : SoninL2) :
    ccmActualHeadTranslationDefect h f ≤ 4 * ‖f‖ ^ 2 := by
  unfold ccmActualHeadTranslationDefect
  have hnorm : ‖logTranslationCLM h f - f‖ ≤ 2 * ‖f‖ := by
    calc
      ‖logTranslationCLM h f - f‖ ≤
          ‖logTranslationCLM h f‖ + ‖f‖ := norm_sub_le _ _
      _ = 2 * ‖f‖ := by rw [logTranslation_norm]; ring
  nlinarith [norm_nonneg (logTranslationCLM h f - f), norm_nonneg f]

theorem continuous_ccmContinuousPolarTranslationDefectEnergy
    (a : SuzukiPositiveAperture) :
    Continuous (ccmContinuousPolarTranslationDefectEnergy a) := by
  rw [continuous_iff_continuousAt]
  intro f₀
  let F : suzukiApertureHilbert a → ℝ → ℝ := fun f h =>
    2 * Real.cosh (h / 2) * ccmActualHeadTranslationDefect h f.1
  let B : ℝ → ℝ := fun h =>
    8 * Real.cosh (h / 2) * (‖f₀‖ + 1) ^ 2
  change ContinuousAt (fun f =>
    ∫ h, F f h ∂(volume.restrict (Icc (0 : ℝ) (2 * a.1)))) f₀
  apply continuousAt_of_dominated (bound := B)
  · filter_upwards with f
    have hdefect : Continuous fun h : ℝ =>
        ccmActualHeadTranslationDefect h f.1 := by
      unfold ccmActualHeadTranslationDefect
      exact (((continuous_logTranslationCLM f.1).sub continuous_const).norm).pow 2
    have hweight : Continuous fun h : ℝ => 2 * Real.cosh (h / 2) := by
      fun_prop
    exact (hweight.mul hdefect).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds f₀ one_pos] with f hf
    filter_upwards with h
    have hdist : ‖f - f₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hf
    have hfnorm : ‖f‖ ≤ ‖f₀‖ + 1 := by
      calc
        ‖f‖ ≤ ‖f - f₀‖ + ‖f₀‖ := by
          simpa only [sub_add_cancel] using norm_add_le (f - f₀) f₀
        _ ≤ ‖f₀‖ + 1 := by linarith
    have hdef := ccmActualHeadTranslationDefect_le h f.1
    have hdef' : ccmActualHeadTranslationDefect h f.1 ≤ 4 * ‖f‖ ^ 2 := by
      simpa using hdef
    have hcosh : 0 ≤ Real.cosh (h / 2) := (Real.cosh_pos _).le
    have hdefnonneg : 0 ≤ ccmActualHeadTranslationDefect h f.1 := by
      unfold ccmActualHeadTranslationDefect
      positivity
    have hsq : ‖f‖ ^ 2 ≤ (‖f₀‖ + 1) ^ 2 := by
      nlinarith [norm_nonneg f, norm_nonneg f₀]
    dsimp only [F, B]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hcosh) hdefnonneg)]
    calc
      2 * Real.cosh (h / 2) * ccmActualHeadTranslationDefect h f.1 ≤
          2 * Real.cosh (h / 2) * (4 * ‖f‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdef'
          (mul_nonneg (by norm_num) hcosh)
      _ = 8 * Real.cosh (h / 2) * ‖f‖ ^ 2 := by ring
      _ ≤ 8 * Real.cosh (h / 2) * (‖f₀‖ + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq
          (mul_nonneg (by norm_num) hcosh)
  · have hB : Continuous B := by
      dsimp only [B]
      exact (continuous_const.mul
        (Real.continuous_cosh.comp (continuous_id.div_const 2))).mul continuous_const
    exact hB.integrableOn_Icc
  · filter_upwards with h
    dsimp only [F]
    have hdefect : Continuous fun f : suzukiApertureHilbert a =>
        ccmActualHeadTranslationDefect h f.1 := by
      unfold ccmActualHeadTranslationDefect
      exact ((((logTranslationCLM h).continuous.comp continuous_subtype_val).sub
        continuous_subtype_val).norm).pow 2
    exact (continuous_const.mul hdefect).continuousAt

theorem re_inner_ccmPolarOperator_ccmComplexSmooth_eq_translationIntegral
    {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    let f := ccmArchimedeanFormToAperture a u.toCCMFormVector
    (inner ℂ (ccmPolarOperator a f) f).re =
      ∫ h in Icc (0 : ℝ) (2 * a.1),
        2 * Real.cosh (h / 2) *
          (inner ℂ (logTranslationCLM h f.1) f.1 +
            inner ℂ (logTranslationCLM (-h) f.1) f.1).re := by
  dsimp only
  let H : ℝ → ℂ := ccmComplexSmoothCrossCorrelation u u
  have hsource := ccmComplexSmoothPolarPrimeSource_eq_restrictedPolarPrimeFull u u
  unfold ccmComplexSmoothPolarPrimeSource ccmRestrictedPolarPrimeFull at hsource
  have hpolar :
      inner ℂ
          (ccmPolarOperator a
            (ccmArchimedeanFormToAperture a u.toCCMFormVector))
          (ccmArchimedeanFormToAperture a u.toCCMFormVector) =
        ∫ h in Ioc (0 : ℝ) (2 * a.1),
          (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ) := by
    rw [inner_ccmPolarOperator]
    simp_rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector]
    dsimp only [H]
    exact sub_left_injective hsource
  have hint : IntegrableOn
      (fun h : ℝ => (H h + H (-h)) *
        (2 * Real.cosh (h / 2) : ℂ)) (Ioc (0 : ℝ) (2 * a.1)) := by
    have hcont : Continuous fun h : ℝ =>
        (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ) := by
      dsimp only [H]
      fun_prop
    exact (hcont.integrableOn_Icc.mono_set (Ioc_subset_Icc_self))
  have hre :
      (inner ℂ
          (ccmPolarOperator a
            (ccmArchimedeanFormToAperture a u.toCCMFormVector))
          (ccmArchimedeanFormToAperture a u.toCCMFormVector)).re =
        ∫ h in Ioc (0 : ℝ) (2 * a.1),
          ((H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ)).re := by
    calc
      _ = (∫ h in Ioc (0 : ℝ) (2 * a.1),
          (H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ)).re :=
        congrArg Complex.re hpolar
      _ = _ := (integral_re (𝕜 := ℂ) hint).symm
  calc
    _ = ∫ h in Ioc (0 : ℝ) (2 * a.1),
          ((H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ)).re := hre
    _ = ∫ h in Icc (0 : ℝ) (2 * a.1),
          ((H h + H (-h)) * (2 * Real.cosh (h / 2) : ℂ)).re := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with h
      rw [inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation
          u u h,
        inner_logTranslationCLM_ccmComplexSmoothFormVector_eq_crossCorrelation
          u u (-h)]
      dsimp only [H]
      simp only [neg_neg, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re]
      norm_num
      have harg : ((h : ℂ) / 2) = ((h / 2 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [harg, ← Complex.ofReal_cosh]
      simp only [Complex.ofReal_im]
      ring

theorem integral_Icc_two_mul_cosh_half
    (a : SuzukiPositiveAperture) :
    (∫ h in Icc (0 : ℝ) (2 * a.1), 2 * Real.cosh (h / 2)) =
      4 * Real.sinh a.1 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [a.property])]
  let P : ℝ → ℝ := fun h => 4 * Real.sinh (h / 2)
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) (2 * a.1),
      HasDerivAt P (2 * Real.cosh (x / 2)) x := by
    intro x hx
    dsimp only [P]
    apply (((Real.hasDerivAt_sinh (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)).const_mul 4).congr_deriv
    ring
  have hint : IntervalIntegrable (fun h : ℝ => 2 * Real.cosh (h / 2))
      volume 0 (2 * a.1) := by
    exact (by fun_prop : Continuous fun h : ℝ =>
      2 * Real.cosh (h / 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp only [P]
  simp only [zero_div, Real.sinh_zero, mul_zero, sub_zero]
  congr 1
  ring

theorem ccmPolarAutocorrelationDefect_ccmComplexSmooth_eq_continuousEnergy
    {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    let f := ccmArchimedeanFormToAperture a u.toCCMFormVector
    ccmPolarAutocorrelationDefect a f =
      ccmContinuousPolarTranslationDefectEnergy a f := by
  dsimp only
  let f := ccmArchimedeanFormToAperture a u.toCCMFormVector
  let W : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2)
  let S : ℝ → ℝ := fun h =>
    (inner ℂ (logTranslationCLM h f.1) f.1 +
      inner ℂ (logTranslationCLM (-h) f.1) f.1).re
  have hW : Continuous W := by
    dsimp only [W]
    fun_prop
  have htrans : Continuous fun h : ℝ => logTranslationCLM h f.1 :=
    continuous_logTranslationCLM f.1
  have htransNeg : Continuous fun h : ℝ => logTranslationCLM (-h) f.1 :=
    htrans.comp continuous_neg
  have hS : Continuous S := by
    dsimp only [S]
    exact Complex.continuous_re.comp
      ((htrans.inner continuous_const).add
        (htransNeg.inner continuous_const))
  have hmassInt : IntegrableOn (fun h => (2 * ‖f‖ ^ 2) * W h)
      (Icc (0 : ℝ) (2 * a.1)) :=
    (continuous_const.mul hW).integrableOn_Icc
  have hcorrInt : IntegrableOn (fun h => W h * S h)
      (Icc (0 : ℝ) (2 * a.1)) :=
    (hW.mul hS).integrableOn_Icc
  have henergy : ccmContinuousPolarTranslationDefectEnergy a f =
      ∫ h in Icc (0 : ℝ) (2 * a.1),
        (2 * ‖f‖ ^ 2) * W h - W h * S h := by
    unfold ccmContinuousPolarTranslationDefectEnergy
    apply integral_congr_ae
    filter_upwards with h
    rw [ccmActualHeadTranslationDefect, logTranslation_defect_eq]
    dsimp only [W, S]
    rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl]
    ring
  rw [henergy, integral_sub hmassInt hcorrInt, integral_const_mul,
    integral_Icc_two_mul_cosh_half]
  have hpolar :=
    re_inner_ccmPolarOperator_ccmComplexSmooth_eq_translationIntegral u
  dsimp only [f, W, S] at hpolar ⊢
  rw [← hpolar]
  unfold ccmPolarAutocorrelationDefect
  ring

theorem denseRange_ccmComplexSmoothPhysicalAperture
    (a : SuzukiPositiveAperture) :
    DenseRange (fun u : CCMComplexSmoothInteriorSource a =>
      ccmArchimedeanFormToAperture a u.toCCMFormVector) := by
  exact (denseRange_ccmArchimedeanFormToAperture a).comp
    (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a)
    (ccmArchimedeanFormToAperture a).continuous

theorem continuous_ccmPolarAutocorrelationDefect
    (a : SuzukiPositiveAperture) :
    Continuous (ccmPolarAutocorrelationDefect a) := by
  unfold ccmPolarAutocorrelationDefect
  have hpolar : Continuous fun f : suzukiApertureHilbert a =>
      (inner ℂ (ccmPolarOperator a f) f).re :=
    Complex.continuous_re.comp
      ((ccmPolarOperator a).continuous.inner continuous_id)
  exact (continuous_const.mul (continuous_norm.pow 2)).sub hpolar

/-- Exact all-`L²` polar-debt law on the actual physical aperture head. -/
theorem ccmPolarAutocorrelationDefect_eq_continuousEnergy
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmPolarAutocorrelationDefect a f =
      ccmContinuousPolarTranslationDefectEnergy a f := by
  have hfunctions : ccmPolarAutocorrelationDefect a =
      ccmContinuousPolarTranslationDefectEnergy a :=
    (denseRange_ccmComplexSmoothPhysicalAperture a).equalizer
      (continuous_ccmPolarAutocorrelationDefect a)
      (continuous_ccmContinuousPolarTranslationDefectEnergy a) (by
        funext u
        exact
          ccmPolarAutocorrelationDefect_ccmComplexSmooth_eq_continuousEnergy u)
  exact congrFun hfunctions f

theorem suzukiApertureHilbert_ae_zero_outside
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ∀ᵐ x : ℝ ∂volume, a.1 < |x| → (f.1 : ℝ → ℂ) x = 0 := by
  have hfix := indicatorCutoff_suzukiApertureHilbert a f
  have hfixae :
      (indicatorCutoff (centralInterval a.1)
        (measurableSet_centralInterval a.1) f.1 : ℝ → ℂ) =ᵐ[volume]
        (f.1 : ℝ → ℂ) := by
    rw [hfix]
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) f.1, hfixae] with x hcut hfae
  intro hx
  have hnot : x ∉ centralInterval a.1 := by
    intro hmem
    rw [centralInterval, mem_Icc] at hmem
    exact (not_lt_of_ge (abs_le.mpr hmem)) hx
  rw [← hfae, hcut, indicator_of_notMem hnot]

/-- Endpoint overlap is null: an actual aperture head is orthogonal to its diameter translate. -/
theorem inner_logTranslationCLM_two_aperture_eq_zero
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    inner ℂ (logTranslationCLM (2 * a.1) f.1) f.1 = 0 := by
  have hforward :=
    MellinL2.inner_additiveTranslation_two_mul_eq_zero_of_bandSupport
      a.property.le f.1 (suzukiApertureHilbert_ae_zero_outside a f)
  have hreverse :
      inner ℂ (MellinL2.additiveTranslationUnitary (2 * a.1) f.1) f.1 = 0 :=
    inner_eq_zero_symm.mp hforward
  exact hreverse

theorem ccmActualHeadTranslationDefect_two_aperture
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    ccmActualHeadTranslationDefect (2 * a.1) f.1 = 2 * ‖f‖ ^ 2 := by
  have hpos := inner_logTranslationCLM_two_aperture_eq_zero a f
  have hneg : inner ℂ (logTranslationCLM (-(2 * a.1)) f.1) f.1 = 0 := by
    rw [inner_logTranslationCLM (-(2 * a.1))]
    simp only [neg_neg]
    exact inner_eq_zero_symm.mpr hpos
  unfold ccmActualHeadTranslationDefect
  rw [logTranslation_defect_eq, hpos, hneg]
  simp only [add_zero, Complex.zero_re, sub_zero]
  rw [show ‖(f.1 : SoninL2)‖ = ‖f‖ by rfl]

/-- Signed completed-error quadrature on one actual physical head.  Prime atoms, continuous polar
mass, and the completed endpoint use the same translation-defect profile. -/
def ccmActualHeadCompletedErrorQuadrature
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  criticalMellinCompletedError (2 * a.1) *
      ccmActualHeadTranslationDefect (2 * a.1) f.1 +
    ccmPrimeTranslationDefectEnergy a f -
      ccmContinuousPolarTranslationDefectEnergy a f

/-- The Route O producer after preserving prime--polar--completed-error cancellation on the
literal source physical head. -/
def ccmRestrictedWeilActualHeadCompletedErrorProducer
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  ‖u‖ ^ 2 + (2 * gammaHardyPhaseRate 0 - 1) *
      ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
    ccmActualHeadCompletedErrorQuadrature a
      (ccmArchimedeanFormToAperture a u)

/-- Exact source law for the new producer; no autocorrelation derivative or head regularity is
used. -/
theorem ccmRestrictedWeilActualHeadCompletedErrorProducer_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilActualHeadCompletedErrorProducer a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_completedError_defects]
  rw [ccmPolarAutocorrelationDefect_eq_continuousEnergy]
  unfold ccmRestrictedWeilActualHeadCompletedErrorProducer
  unfold ccmActualHeadCompletedErrorQuadrature
  rw [ccmActualHeadTranslationDefect_two_aperture]
  ring

/-- On each literal canonical finite Gamma--Slepian head, the producer is the true restricted-Weil
ground part plus the certified nonnegative tail defect. -/
theorem ccmRestrictedWeilCanonicalGroundHead_actualHeadProducer_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilActualHeadCompletedErrorProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilActualHeadCompletedErrorProducer_eq_sourceQuadratic]
  unfold ccmRestrictedWeilCanonicalGroundHeadDefect
  ring

/-- Literal reverse-prime control on a canonical Gamma--Slepian head is exactly nonnegativity of
the cancellation-preserving producer. -/
theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_actualHeadProducer_nonneg
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      0 ≤ ccmRestrictedWeilActualHeadCompletedErrorProducer a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg]
  rw [ccmRestrictedWeilActualHeadCompletedErrorProducer_eq_sourceQuadratic]

end RHTower
