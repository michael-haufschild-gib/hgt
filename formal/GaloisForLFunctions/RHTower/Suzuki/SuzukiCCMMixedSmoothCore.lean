import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanComplexSmoothCore
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseWeilBridge

/-!
# Mixed complex smooth Suzuki--CCM source core

This module bundles strict-interior complex smooth sources, constructs their exact CCM vectors,
and identifies every mixed spectral, translation, and polar coordinate needed by the restricted
Weil form.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap
noncomputable section
namespace RHTower

/-- Literal complex `C_c^∞` source with support strictly inside a positive aperture. -/
structure CCMComplexSmoothInteriorSource (a : SuzukiPositiveAperture) where
  toFun : ℝ → ℂ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  hasCompactSupport : HasCompactSupport toFun
  tsupport_subset : tsupport toFun ⊆ Ioo (-a.1) a.1

instance (a : SuzukiPositiveAperture) :
    CoeFun (CCMComplexSmoothInteriorSource a) (fun _ => ℝ → ℂ) :=
  ⟨CCMComplexSmoothInteriorSource.toFun⟩

theorem CCMComplexSmoothInteriorSource.continuous
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    Continuous u := u.smooth.continuous

theorem CCMComplexSmoothInteriorSource.integrable
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    Integrable u := u.continuous.integrable_of_hasCompactSupport u.hasCompactSupport

theorem CCMComplexSmoothInteriorSource.support_subset
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    Function.support u ⊆ Ioo (-a.1) a.1 :=
  subset_tsupport u |>.trans u.tsupport_subset

/-- Schwartz realization of a strict-interior complex source. -/
def CCMComplexSmoothInteriorSource.toSchwartz
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    SchwartzMap ℝ ℂ :=
  suzukiComplexTestSchwartz u u.smooth u.hasCompactSupport

@[simp] theorem CCMComplexSmoothInteriorSource.toSchwartz_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    u.toSchwartz x = u x := rfl

/-- Exact CCM form vector of a strict-interior complex source. -/
def CCMComplexSmoothInteriorSource.toCCMFormVector
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    CCMArchimedeanFormDomain a :=
  ccmComplexSmoothFormVector a u u.smooth u.hasCompactSupport u.tsupport_subset

theorem CCMComplexSmoothInteriorSource.toCCMFormVector_physical_coeFn
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ((ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] u :=
  ccmArchimedeanFormToAperture_ccmComplexSmoothFormVector_coeFn
    a u u.smooth u.hasCompactSupport u.tsupport_subset

theorem CCMComplexSmoothInteriorSource.toCCMFormVector_fourier_coeFn
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ((u.toCCMFormVector).1 : ℝ → ℂ) =ᵐ[volume]
      𝓕 (u.toSchwartz : ℝ → ℂ) :=
  ccmComplexSmoothFormVector_coeFn
    a u u.smooth u.hasCompactSupport u.tsupport_subset

/-- Hermitian cross-correlation in the orientation of the mixed CCM source form. -/
def ccmComplexSmoothCrossCorrelation
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) : SchwartzMap ℝ ℂ :=
  SchwartzMap.crossCorrelationSchwartz v.toSchwartz u.toSchwartz

@[simp] theorem fourier_ccmComplexSmoothCrossCorrelation
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (ξ : ℝ) :
    𝓕 (ccmComplexSmoothCrossCorrelation u v : ℝ → ℂ) ξ =
      star (𝓕 (u.toSchwartz : ℝ → ℂ) ξ) *
        𝓕 (v.toSchwartz : ℝ → ℂ) ξ := by
  change 𝓕 (SchwartzMap.crossCorrelationSchwartz
      v.toSchwartz u.toSchwartz) ξ = _
  simpa only [starRingEnd_apply, SchwartzMap.fourier_coe, mul_comm] using
    SchwartzMap.fourier_crossCorrelationSchwartz v.toSchwartz u.toSchwartz ξ

/-- Compact Schwartz test bundling the mixed Hermitian correlation. -/
def ccmComplexSmoothCrossCorrelationTest
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) : CCMCompactSchwartzLogTest where
  toSchwartzMap := ccmComplexSmoothCrossCorrelation u v
  radius := 2 * a.1 + 2
  one_lt_radius := by linarith [a.property]
  eq_zero_of_radius_le_abs := by
    intro x hx
    rw [ccmComplexSmoothCrossCorrelation,
      SchwartzMap.crossCorrelationSchwartz, SchwartzMap.convolution_apply,
      MeasureTheory.convolution_def]
    apply integral_eq_zero_of_ae
    filter_upwards with y
    simp only [Pi.zero_apply, SchwartzMap.conjugateReflectionSchwartz_apply, neg_sub]
    by_cases hv : v y = 0
    · simp [hv]
    by_cases hu : u (y - x) = 0
    · simp [hu]
    have hyv := v.support_subset hv
    have hyu := u.support_subset hu
    have hxlower : -(2 * a.1) < x := by linarith [hyv.1, hyv.2, hyu.1, hyu.2]
    have hxupper : x < 2 * a.1 := by linarith [hyv.1, hyv.2, hyu.1, hyu.2]
    have hxabs : |x| < 2 * a.1 := (abs_lt).2 ⟨hxlower, hxupper⟩
    exfalso
    linarith

@[simp] theorem fourier_ccmComplexSmoothCrossCorrelationTest
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (ξ : ℝ) :
    𝓕 ((ccmComplexSmoothCrossCorrelationTest u v).toSchwartzMap : ℝ → ℂ) ξ =
      star (𝓕 (u.toSchwartz : ℝ → ℂ) ξ) *
        𝓕 (v.toSchwartz : ℝ → ℂ) ξ := by
  exact fourier_ccmComplexSmoothCrossCorrelation u v ξ

/-- Exact complex mixed phase--Weil identity. -/
theorem integral_two_gammaHardyPhaseRate_mul_fourier_cross_eq_neg_weilDistribution
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    (∫ ξ : ℝ,
        ((2 * gammaHardyPhaseRate (2 * Real.pi * ξ) : ℝ) : ℂ) *
          star (𝓕 (u.toSchwartz : ℝ → ℂ) ξ) *
            𝓕 (v.toSchwartz : ℝ → ℂ) ξ) =
      -ccmArchimedeanWeilDistribution
        (ccmComplexSmoothCrossCorrelationTest u v) := by
  let H := ccmComplexSmoothCrossCorrelationTest u v
  have hWeil :=
    integral_fourier_mul_logPi_sub_re_quarterDigamma_eq_weilDistribution H
  calc
    (∫ ξ : ℝ,
        ((2 * gammaHardyPhaseRate (2 * Real.pi * ξ) : ℝ) : ℂ) *
          star (𝓕 (u.toSchwartz : ℝ → ℂ) ξ) *
            𝓕 (v.toSchwartz : ℝ → ℂ) ξ) =
        -∫ ξ : ℝ,
          (𝓕 (H.toSchwartzMap : ℝ → ℂ)) ξ *
            ((Real.log Real.pi -
              (Complex.digamma (ccmQuarterPiDigammaPoint ξ)).re : ℝ) : ℂ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with ξ
      rw [show 𝓕 (H.toSchwartzMap : ℝ → ℂ) ξ =
          star (𝓕 (u.toSchwartz : ℝ → ℂ) ξ) *
            𝓕 (v.toSchwartz : ℝ → ℂ) ξ by
        exact fourier_ccmComplexSmoothCrossCorrelationTest u v ξ]
      have hpoint : linePt ((2 * Real.pi) * ξ) / 2 =
          ccmQuarterPiDigammaPoint ξ := by
        unfold linePt ccmQuarterPiDigammaPoint
        push_cast
        ring
      unfold gammaHardyPhaseRate
      rw [hpoint]
      push_cast
      ring
    _ = -ccmArchimedeanWeilDistribution H := congrArg Neg.neg hWeil

/-- Mixed logarithmic translation coefficient is the literal shifted source pairing. -/
theorem inner_logTranslationCLM_ccmComplexSmoothFormVector
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) (h : ℝ) :
    inner ℂ
        (logTranslationCLM h
          (ccmArchimedeanFormToAperture a u.toCCMFormVector).1)
        (ccmArchimedeanFormToAperture a v.toCCMFormVector).1 =
      ∫ x : ℝ, star (u (x + h)) * v x := by
  let f : SoninL2 := (ccmArchimedeanFormToAperture a u.toCCMFormVector).1
  let g : SoninL2 := (ccmArchimedeanFormToAperture a v.toCCMFormVector).1
  have hf : (f : ℝ → ℂ) =ᵐ[volume] u :=
    u.toCCMFormVector_physical_coeFn
  have hg : (g : ℝ → ℂ) =ᵐ[volume] v :=
    v.toCCMFormVector_physical_coeFn
  have hfshift := hf.comp_tendsto
    (MellinL2.realTranslation_measurePreserving h).quasiMeasurePreserving.tendsto_ae
  have htrans := Lp.coeFn_compMeasurePreserving f
    (MellinL2.realTranslation_measurePreserving h)
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [htrans, hg, hfshift] with x htx hgx hfx
  change inner ℂ ((logTranslationCLM h f : SoninL2) x) (g x) = _
  change inner ℂ
      (Lp.compMeasurePreserving (MellinL2.realTranslationEquiv h)
        (MellinL2.realTranslation_measurePreserving h) f x) (g x) = _
  rw [htx, hgx, hfx]
  simp [RCLike.inner_apply, MellinL2.realTranslationEquiv,
    Function.comp_apply, mul_comm]

/-- Each polar Riesz coefficient is the literal complex exponential moment. -/
theorem inner_ccmPolarApertureVector_ccmComplexSmoothFormVector
    {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (s : ℝ) :
    inner ℂ (ccmPolarApertureVector a s)
        (ccmArchimedeanFormToAperture a u.toCCMFormVector) =
      ∫ x : ℝ, (Real.exp (s * x) : ℂ) * u x := by
  let f : SoninL2 := (ccmArchimedeanFormToAperture a u.toCCMFormVector).1
  have hf : (f : ℝ → ℂ) =ᵐ[volume] u :=
    u.toCCMFormVector_physical_coeFn
  have hp := ccmPolarL2Vector_coeFn a s
  change inner ℂ (ccmPolarL2Vector a s) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hp, hf] with x hpx hfx
  change inner ℂ (ccmPolarL2Vector a s x) (f x) = _
  rw [hpx, hfx]
  by_cases hx : x ∈ centralInterval a.1
  · rw [indicator_of_mem hx]
    simp [ccmPolarProfile, RCLike.inner_apply]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, Complex.conj_ofReal]
    ring
  · rw [indicator_of_notMem hx]
    have hux : u x = 0 := by
      apply Function.notMem_support.mp
      intro hmem
      exact hx (Ioo_subset_Icc_self (u.support_subset hmem))
    simp [hux]

end RHTower
