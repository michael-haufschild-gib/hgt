import GaloisForLFunctions.RHTower.SuzukiCCMMixedPolarFactorization
import GaloisForLFunctions.RHTower.SuzukiCCMExactSourceIdentification
import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilComplexCore
import GaloisForLFunctions.RHTower.SuzukiScrewWeilIdentity

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct FourierTransform SchwartzMap BigOperators
noncomputable section
namespace RHTower

attribute [local instance] Measure.Subtype.measureSpace

local instance (a : SuzukiPositiveAperture) : CompleteSpace (SuzukiApertureZeroMean a) :=
  (suzukiApertureZeroMean_isClosed a).completeSpace_coe

theorem ccmArchimedeanWeilSharpDistribution_im_eq_zero_of_real
    (F : CCMCompactSchwartzLogTest) (hF : ∀ x : ℝ, (F x).im = 0) :
    (ccmArchimedeanWeilSharpDistribution F).im = 0 := by
  have hint := ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F
  have himIntegral :
      (∫ h : ℝ in Ioi (0 : ℝ),
        ccmArchimedeanWeilSharpIntegrand F h).im =
      ∫ h : ℝ in Ioi (0 : ℝ),
        (ccmArchimedeanWeilSharpIntegrand F h).im :=
    (integral_im hint).symm
  rw [ccmArchimedeanWeilSharpDistribution, Complex.add_im, himIntegral]
  have hconst :
      (F 0 / 2 *
        (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ)).im = 0 := by
    simp [Complex.mul_im, hF]
  rw [hconst, zero_add]
  apply integral_eq_zero_of_ae
  filter_upwards with h
  have hnum : (ccmArchimedeanWeilSharpNumerator F h).im = 0 := by
    unfold ccmArchimedeanWeilSharpNumerator
    rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, hF, hF]
    ring
  unfold ccmArchimedeanWeilSharpIntegrand
  change (ccmArchimedeanWeilSharpNumerator F h /
    ((Real.exp h - Real.exp (-h) : ℝ) : ℂ)).im = 0
  rw [Complex.div_ofReal_im, hnum, zero_div]

theorem ccmArchimedeanWeilDistribution_im_eq_zero_of_real
    (H : CCMCompactSchwartzLogTest) (hH : ∀ x : ℝ, (H x).im = 0) :
    (ccmArchimedeanWeilDistribution H).im = 0 := by
  unfold ccmArchimedeanWeilDistribution
  apply ccmArchimedeanWeilSharpDistribution_im_eq_zero_of_real
  intro x
  rw [ccmCompactSchwartzLogEvenization_apply, Complex.add_im, hH, hH]
  ring

open GaloisForLFunctions.RHTower

/-- Real Suzuki source core, regarded as a strict-interior complex CCM source. -/
def ccmComplexSmoothInteriorSourceOfRealCore
    (a : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    CCMComplexSmoothInteriorSource a where
  toFun x := (u x : ℂ)
  smooth := suzukiRestrictedWeilCore_contDiff_ofReal u
  hasCompactSupport := suzukiRestrictedWeilCore_hasCompactSupport_ofReal u
  tsupport_subset := suzukiRestrictedWeilCore_tsupport_ofReal_subset_aperture a u

@[simp] theorem ccmComplexSmoothInteriorSourceOfRealCore_apply
    (a : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) (x : ℝ) :
    ccmComplexSmoothInteriorSourceOfRealCore a u x = (u x : ℂ) := rfl

theorem ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector
    (a : SuzukiPositiveAperture) (u : SuzukiRestrictedWeilCore a.1) :
    (ccmComplexSmoothInteriorSourceOfRealCore a u).toCCMFormVector =
      suzukiRestrictedWeilCoreCCMFormVector a u := by
  apply ccmArchimedeanFormEmbedding_injective a
  rw [CCMComplexSmoothInteriorSource.toCCMFormVector,
    ccmArchimedeanFormEmbedding_ccmComplexSmoothFormVector,
    ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector]
  apply Lp.ext
  filter_upwards [suzukiComplexTestL2_coeFn
      (fun x : ℝ => (u x : ℂ))
      (suzukiRestrictedWeilCore_contDiff_ofReal u)
      (suzukiRestrictedWeilCore_hasCompactSupport_ofReal u),
    suzukiRealTestL2_coeFn u u.smooth u.hasCompactSupport] with x hx hy
  calc
    ((suzukiComplexTestL2
        (ccmComplexSmoothInteriorSourceOfRealCore a u).toFun
        (ccmComplexSmoothInteriorSourceOfRealCore a u).smooth
        (ccmComplexSmoothInteriorSourceOfRealCore a u).hasCompactSupport : SoninL2) x) =
        (u x : ℂ) := by
      simpa only [ccmComplexSmoothInteriorSourceOfRealCore] using hx
    _ = (suzukiRealTestL2 u u.smooth u.hasCompactSupport : SoninL2) x := by
      symm
      simpa only [suzukiRealTestComplex] using hy

theorem ccmComplexSmoothCrossCorrelation_realCore_eq_ofReal
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) (h : ℝ) :
    ccmComplexSmoothCrossCorrelation
        (ccmComplexSmoothInteriorSourceOfRealCore a u)
        (ccmComplexSmoothInteriorSourceOfRealCore a v) h =
      ((∫ x : ℝ, v x * u (x - h) : ℝ) : ℂ) := by
  rw [ccmComplexSmoothCrossCorrelation_apply]
  calc
    (∫ x : ℝ, ((v x : ℝ) : ℂ) * star (((u (x - h) : ℝ) : ℂ))) =
        ∫ x : ℝ, ((v x * u (x - h) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [RCLike.star_def, Complex.conj_ofReal, Complex.ofReal_mul]
    _ = _ := _root_.integral_ofReal

theorem ccmComplexSmoothPolarPrimeSource_realCore_im_eq_zero
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) :
    (ccmComplexSmoothPolarPrimeSource
      (ccmComplexSmoothInteriorSourceOfRealCore a u)
      (ccmComplexSmoothInteriorSourceOfRealCore a v)).im = 0 := by
  let U := ccmComplexSmoothInteriorSourceOfRealCore a u
  let V := ccmComplexSmoothInteriorSourceOfRealCore a v
  have hu (s : ℝ) :
      (∫ x : ℝ, (Real.exp (s * x) : ℂ) * U x) =
        ((∫ x : ℝ, Real.exp (s * x) * u x : ℝ) : ℂ) := by
    calc
      _ = ∫ x : ℝ, ((Real.exp (s * x) * u x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        change ((Real.exp (s * x) : ℝ) : ℂ) * ((u x : ℝ) : ℂ) = _
        rw [← Complex.ofReal_mul]
      _ = _ := _root_.integral_ofReal
  have hv (s : ℝ) :
      (∫ x : ℝ, (Real.exp (s * x) : ℂ) * V x) =
        ((∫ x : ℝ, Real.exp (s * x) * v x : ℝ) : ℂ) := by
    calc
      _ = ∫ x : ℝ, ((Real.exp (s * x) * v x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards with x
        change ((Real.exp (s * x) : ℝ) : ℂ) * ((v x : ℝ) : ℂ) = _
        rw [← Complex.ofReal_mul]
      _ = _ := _root_.integral_ofReal
  unfold ccmComplexSmoothPolarPrimeSource
  rw [hu, hu, hv, hv]
  simp_rw [ccmComplexSmoothCrossCorrelation_realCore_eq_ofReal]
  simp

theorem ccmRestrictedWeilForm_realCore_mixed_im_eq_zero
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) :
    (ccmRestrictedWeilForm a
      (suzukiRestrictedWeilCoreCCMFormVector a u)
      (suzukiRestrictedWeilCoreCCMFormVector a v)).im = 0 := by
  let U := ccmComplexSmoothInteriorSourceOfRealCore a u
  let V := ccmComplexSmoothInteriorSourceOfRealCore a v
  have hform := ccmRestrictedWeilForm_ccmComplexSmooth_eq_explicitDistribution U V
  have hU := ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector a u
  have hV := ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector a v
  rw [hU, hV] at hform
  rw [hform, Complex.sub_im,
    ccmComplexSmoothPolarPrimeSource_realCore_im_eq_zero]
  have harch :
      (ccmArchimedeanWeilDistribution
        (ccmComplexSmoothCrossCorrelationTest U V)).im = 0 := by
    apply ccmArchimedeanWeilDistribution_im_eq_zero_of_real
    intro h
    change (ccmComplexSmoothCrossCorrelation U V h).im = 0
    dsimp only [U, V]
    rw [ccmComplexSmoothCrossCorrelation_realCore_eq_ofReal]
    simp
  rw [harch, sub_zero]

/-- Sum inside the literal real strict-interior Suzuki core. -/
def suzukiRestrictedWeilCoreAdd {a : ℝ}
    (u v : SuzukiRestrictedWeilCore a) : SuzukiRestrictedWeilCore a where
  toFun x := u x + v x
  smooth := u.smooth.add v.smooth
  supportRadius := max u.supportRadius v.supportRadius
  supportRadius_nonneg :=
    u.supportRadius_nonneg.trans (le_max_left u.supportRadius v.supportRadius)
  supportRadius_lt_aperture := max_lt u.supportRadius_lt_aperture v.supportRadius_lt_aperture
  support_subset := by
    intro x hx
    by_cases hu : u x = 0
    · have hv : v x ≠ 0 := by
        intro hv
        exact hx (by simp [hu, hv])
      have hvr := v.support_subset hv
      exact ⟨(neg_le_neg (le_max_right u.supportRadius v.supportRadius)).trans hvr.1,
        hvr.2.trans (le_max_right u.supportRadius v.supportRadius)⟩
    · have hur := u.support_subset hu
      exact ⟨(neg_le_neg (le_max_left u.supportRadius v.supportRadius)).trans hur.1,
        hur.2.trans (le_max_left u.supportRadius v.supportRadius)⟩

@[simp] theorem suzukiRestrictedWeilCoreAdd_apply {a : ℝ}
    (u v : SuzukiRestrictedWeilCore a) (x : ℝ) :
    suzukiRestrictedWeilCoreAdd u v x = u x + v x := rfl

theorem suzukiRestrictedWeilCoreCCMFormVector_add
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) :
    suzukiRestrictedWeilCoreCCMFormVector a (suzukiRestrictedWeilCoreAdd u v) =
      suzukiRestrictedWeilCoreCCMFormVector a u +
        suzukiRestrictedWeilCoreCCMFormVector a v := by
  apply ccmArchimedeanFormEmbedding_injective a
  rw [map_add]
  simp_rw [ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector]
  apply Lp.ext
  filter_upwards [suzukiRealTestL2_coeFn
      (suzukiRestrictedWeilCoreAdd u v)
      (suzukiRestrictedWeilCoreAdd u v).smooth
      (suzukiRestrictedWeilCoreAdd u v).hasCompactSupport,
    suzukiRealTestL2_coeFn u u.smooth u.hasCompactSupport,
    suzukiRealTestL2_coeFn v v.smooth v.hasCompactSupport,
    Lp.coeFn_add (suzukiRealTestL2 u u.smooth u.hasCompactSupport)
      (suzukiRealTestL2 v v.smooth v.hasCompactSupport)] with x huv hu hv hadd
  rw [huv, hadd, Pi.add_apply, hu, hv]
  simp [suzukiRealTestComplex]

theorem suzukiRestrictedWeilCoreDerivativeZeroMean_add
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) :
    suzukiRestrictedWeilCoreDerivativeZeroMean a (suzukiRestrictedWeilCoreAdd u v) =
      suzukiRestrictedWeilCoreDerivativeZeroMean a u +
        suzukiRestrictedWeilCoreDerivativeZeroMean a v := by
  apply Subtype.ext
  change (suzukiRestrictedWeilCoreDerivativeZeroMean a
      (suzukiRestrictedWeilCoreAdd u v) : SuzukiApertureIntervalL2 a.1) =
    (suzukiRestrictedWeilCoreDerivativeZeroMean a u : SuzukiApertureIntervalL2 a.1) +
      (suzukiRestrictedWeilCoreDerivativeZeroMean a v : SuzukiApertureIntervalL2 a.1)
  apply Lp.ext
  filter_upwards [suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a
      (suzukiRestrictedWeilCoreAdd u v),
    suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a u,
    suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a v,
    Lp.coeFn_add
      (suzukiRestrictedWeilCoreDerivativeZeroMean a u : SuzukiApertureIntervalL2 a.1)
      (suzukiRestrictedWeilCoreDerivativeZeroMean a v : SuzukiApertureIntervalL2 a.1)]
      with x huv hu hv haddCoe
  rw [huv, haddCoe, Pi.add_apply, hu, hv]
  have hdu : HasDerivAt u.toFun (deriv u.toFun (x : ℝ)) (x : ℝ) :=
    (u.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hdv : HasDerivAt v.toFun (deriv v.toFun (x : ℝ)) (x : ℝ) :=
    (v.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hadd := (hdu.add hdv).deriv
  have hadd' : deriv (fun y : ℝ => u y + v y) (x : ℝ) =
      deriv u.toFun (x : ℝ) + deriv v.toFun (x : ℝ) := by
    have hfun : (fun y : ℝ => u y + v y) = u.toFun + v.toFun := by
      funext y
      rfl
    rw [hfun]
    exact hadd
  change ((deriv (fun y : ℝ => u y + v y) (x : ℝ) : ℝ) : ℂ) =
    ((deriv u.toFun (x : ℝ) : ℝ) : ℂ) + ((deriv v.toFun (x : ℝ) : ℝ) : ℂ)
  rw [hadd']
  push_cast
  rfl

theorem ccmRestrictedWeilForm_add_add
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (u + v) (u + v) =
      ccmRestrictedWeilForm a u u + ccmRestrictedWeilForm a u v +
        ccmRestrictedWeilForm a v u + ccmRestrictedWeilForm a v v := by
  unfold ccmRestrictedWeilForm
  simp only [map_add, inner_add_left, inner_add_right]
  ring

theorem star_ccmRestrictedWeilForm_swap
    (a : SuzukiPositiveAperture) (u v : CCMArchimedeanFormDomain a) :
    star (ccmRestrictedWeilForm a u v) = ccmRestrictedWeilForm a v u := by
  let f := ccmArchimedeanFormToAperture a u
  let g := ccmArchimedeanFormToAperture a v
  have hR := (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric g f
  unfold ccmRestrictedWeilForm
  change (starRingEnd ℂ) (inner ℂ u v +
      inner ℂ (ccmRestrictedWeilBoundedRemainder a f) g) =
    inner ℂ v u + inner ℂ (ccmRestrictedWeilBoundedRemainder a g) f
  rw [map_add, inner_conj_symm v u,
    inner_conj_symm g (ccmRestrictedWeilBoundedRemainder a f)]
  exact congrArg (fun z => inner ℂ v u + z) hR.symm

theorem inner_suzukiScrewZeroMeanOperator_realCore_mixed_im_eq_zero
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) :
    (inner ℂ (suzukiRestrictedWeilCoreDerivativeZeroMean a u)
      (suzukiScrewZeroMeanOperator a
        (suzukiRestrictedWeilCoreDerivativeZeroMean a v))).im = 0 := by
  let f : SuzukiApertureZeroMean a := suzukiRestrictedWeilCoreDerivativeZeroMean a v
  let g : SuzukiApertureZeroMean a := suzukiRestrictedWeilCoreDerivativeZeroMean a u
  rw [inner_suzukiScrewZeroMeanOperator_eq_raw]
  unfold suzukiRawScrewIntervalForm
  let F : SuzukiApertureInterval a.1 × SuzukiApertureInterval a.1 → ℂ := fun p =>
    suzukiScrewG ((p.1 : ℝ) - (p.2 : ℝ)) *
      (f : SuzukiApertureIntervalL2 a.1) p.2 *
        star ((g : SuzukiApertureIntervalL2 a.1) p.1)
  have hF : Integrable F
      ((volume : Measure (SuzukiApertureInterval a.1)).prod volume) := by
    simpa only [F, f, g, RCLike.star_def] using
      integrable_suzukiRawScrewKernel_pair a.1
        (f : SuzukiApertureIntervalL2 a.1)
        (g : SuzukiApertureIntervalL2 a.1)
  have houter : Integrable (fun t : SuzukiApertureInterval a.1 =>
      ∫ y : SuzukiApertureInterval a.1, F (t, y)) := hF.integral_prod_left
  have himOuter :
      (∫ t : SuzukiApertureInterval a.1,
        ∫ y : SuzukiApertureInterval a.1, F (t, y)).im =
      ∫ t : SuzukiApertureInterval a.1,
        (∫ y : SuzukiApertureInterval a.1, F (t, y)).im := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im houter).symm
  change (∫ t : SuzukiApertureInterval a.1,
      ∫ y : SuzukiApertureInterval a.1, F (t, y)).im = 0
  rw [himOuter]
  apply integral_eq_zero_of_ae
  have hg := suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a u
  have hf := suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a v
  filter_upwards [hF.prod_right_ae, hg] with t ht hgt
  change (∫ y : SuzukiApertureInterval a.1, F (t, y)).im = (0 : ℝ)
  have himInner :
      (∫ y : SuzukiApertureInterval a.1, F (t, y)).im =
        ∫ y : SuzukiApertureInterval a.1, (F (t, y)).im := by
    simpa only [RCLike.im_eq_complex_im] using (integral_im ht).symm
  rw [himInner]
  apply integral_eq_zero_of_ae
  filter_upwards [hf] with y hfy
  dsimp only [F, f, g]
  rw [hfy, hgt, suzukiScrewG_eq_sourceScrew,
    RCLike.star_def, Complex.conj_ofReal]
  simp

theorem ccmRestrictedWeilForm_realCore_mixed_eq_screw
    (a : SuzukiPositiveAperture) (u v : SuzukiRestrictedWeilCore a.1) :
    ccmRestrictedWeilForm a
        (suzukiRestrictedWeilCoreCCMFormVector a u)
        (suzukiRestrictedWeilCoreCCMFormVector a v) =
      inner ℂ (suzukiRestrictedWeilCoreDerivativeZeroMean a u)
        (suzukiScrewZeroMeanOperator a
          (suzukiRestrictedWeilCoreDerivativeZeroMean a v)) := by
  let qu := suzukiRestrictedWeilCoreCCMFormVector a u
  let qv := suzukiRestrictedWeilCoreCCMFormVector a v
  let xu := suzukiRestrictedWeilCoreDerivativeZeroMean a u
  let xv := suzukiRestrictedWeilCoreDerivativeZeroMean a v
  let G := suzukiScrewZeroMeanOperator a
  have hu := inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_ccmRestrictedWeilForm a u
  have hv := inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_ccmRestrictedWeilForm a v
  have huv := inner_suzukiScrewZeroMeanOperator_coreDerivative_eq_ccmRestrictedWeilForm a
    (suzukiRestrictedWeilCoreAdd u v)
  rw [suzukiRestrictedWeilCoreDerivativeZeroMean_add,
    suzukiRestrictedWeilCoreCCMFormVector_add] at huv
  simp only [map_add, inner_add_left, inner_add_right] at huv
  rw [ccmRestrictedWeilForm_add_add] at huv
  have hsum :
      inner ℂ xu (G xv) + inner ℂ xv (G xu) =
        ccmRestrictedWeilForm a qu qv + ccmRestrictedWeilForm a qv qu := by
    dsimp only [xu, xv, G, qu, qv]
    linear_combination huv - hu - hv
  have hAstar : star (inner ℂ xu (G xv)) = inner ℂ xv (G xu) := by
    calc
      star (inner ℂ xu (G xv)) = inner ℂ (G xv) xu :=
        inner_conj_symm (G xv) xu
      _ = inner ℂ xv (G xu) :=
        (suzukiScrewZeroMeanOperator_isSelfAdjoint a).isSymmetric xv xu
  have hAim : (inner ℂ xu (G xv)).im = 0 := by
    exact inner_suzukiScrewZeroMeanOperator_realCore_mixed_im_eq_zero a u v
  have hAsymm : inner ℂ xv (G xu) = inner ℂ xu (G xv) := by
    rw [← hAstar]
    exact Complex.conj_eq_iff_im.mpr hAim
  have hCstar : star (ccmRestrictedWeilForm a qu qv) =
      ccmRestrictedWeilForm a qv qu := star_ccmRestrictedWeilForm_swap a qu qv
  have hCim : (ccmRestrictedWeilForm a qu qv).im = 0 := by
    exact ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a u v
  have hCsymm : ccmRestrictedWeilForm a qv qu =
      ccmRestrictedWeilForm a qu qv := by
    rw [← hCstar]
    exact Complex.conj_eq_iff_im.mpr hCim
  rw [hAsymm, hCsymm] at hsum
  dsimp only [qu, qv, xu, xv, G] at hsum ⊢
  linear_combination (-1 / 2 : ℂ) * hsum

/-- Strict-interior CCM source as mathlib's literal complex test function. -/
def CCMComplexSmoothInteriorSource.toRestrictedWeilComplexTest
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    SuzukiRestrictedWeilComplexTest a.1 where
  toFun := u
  contDiff' := u.smooth
  hasCompactSupport' := u.hasCompactSupport
  tsupport_subset' := u.tsupport_subset

/-- Real component in Suzuki's strict real source core. -/
def CCMComplexSmoothInteriorSource.realCore
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    SuzukiRestrictedWeilCore a.1 :=
  suzukiRestrictedWeilRealTestToCore a u.toRestrictedWeilComplexTest.realPart

/-- Imaginary component in Suzuki's strict real source core. -/
def CCMComplexSmoothInteriorSource.imagCore
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    SuzukiRestrictedWeilCore a.1 :=
  suzukiRestrictedWeilRealTestToCore a u.toRestrictedWeilComplexTest.imagPart

@[simp] theorem CCMComplexSmoothInteriorSource.realCore_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    u.realCore x = (u x).re := rfl

@[simp] theorem CCMComplexSmoothInteriorSource.imagCore_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    u.imagCore x = (u x).im := rfl

/-- Exact real--imaginary decomposition of the canonical CCM form vector. -/
theorem CCMComplexSmoothInteriorSource.toCCMFormVector_eq_real_add_I_imag
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    u.toCCMFormVector =
      suzukiRestrictedWeilCoreCCMFormVector a u.realCore +
        I • suzukiRestrictedWeilCoreCCMFormVector a u.imagCore := by
  apply ccmArchimedeanFormEmbedding_injective a
  rw [map_add, map_smul, CCMComplexSmoothInteriorSource.toCCMFormVector,
    ccmArchimedeanFormEmbedding_ccmComplexSmoothFormVector,
    ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector,
    ccmArchimedeanFormEmbedding_suzukiRestrictedWeilCoreCCMFormVector]
  apply Lp.ext
  let qr := suzukiRealTestL2 u.realCore u.realCore.smooth u.realCore.hasCompactSupport
  let qi := suzukiRealTestL2 u.imagCore u.imagCore.smooth u.imagCore.hasCompactSupport
  filter_upwards [suzukiComplexTestL2_coeFn u u.smooth u.hasCompactSupport,
    suzukiRealTestL2_coeFn u.realCore u.realCore.smooth u.realCore.hasCompactSupport,
    suzukiRealTestL2_coeFn u.imagCore u.imagCore.smooth u.imagCore.hasCompactSupport,
    Lp.coeFn_smul I qi, Lp.coeFn_add qr (I • qi)] with x hu hr hi hsmul hadd
  dsimp only [qr, qi] at hsmul hadd
  rw [hu, hadd, Pi.add_apply, hsmul, Pi.smul_apply, hr, hi]
  simpa [suzukiRealTestComplex, mul_comm] using (Complex.re_add_im (u x)).symm

/-- Exact zero-mean interval derivative of a strict complex source. -/
def CCMComplexSmoothInteriorSource.toDerivativeZeroMean
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    SuzukiApertureZeroMean a :=
  suzukiSmoothDerivativeZeroMean a u u.smooth u.hasCompactSupport u.tsupport_subset

theorem CCMComplexSmoothInteriorSource.toDerivativeZeroMean_coeFn
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ((u.toDerivativeZeroMean : SuzukiApertureZeroMean a) :
      SuzukiApertureIntervalL2 a.1) =ᵐ[volume]
        fun x => deriv u (x : ℝ) :=
  suzukiSmoothDerivativeCoordinate_coeFn a u u.smooth u.hasCompactSupport

/-- Derivative coordinate respects the real--imaginary decomposition exactly. -/
theorem CCMComplexSmoothInteriorSource.toDerivativeZeroMean_eq_real_add_I_imag
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    u.toDerivativeZeroMean =
      suzukiRestrictedWeilCoreDerivativeZeroMean a u.realCore +
        I • suzukiRestrictedWeilCoreDerivativeZeroMean a u.imagCore := by
  apply Subtype.ext
  change (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) =
    (suzukiRestrictedWeilCoreDerivativeZeroMean a u.realCore :
        SuzukiApertureIntervalL2 a.1) +
      I • (suzukiRestrictedWeilCoreDerivativeZeroMean a u.imagCore :
        SuzukiApertureIntervalL2 a.1)
  apply Lp.ext
  let xr : SuzukiApertureIntervalL2 a.1 :=
    suzukiRestrictedWeilCoreDerivativeZeroMean a u.realCore
  let xi : SuzukiApertureIntervalL2 a.1 :=
    suzukiRestrictedWeilCoreDerivativeZeroMean a u.imagCore
  filter_upwards [u.toDerivativeZeroMean_coeFn,
    suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a u.realCore,
    suzukiRestrictedWeilCoreDerivativeZeroMean_coeFn a u.imagCore,
    Lp.coeFn_smul I xi, Lp.coeFn_add xr (I • xi)] with x hu hr hi hsmul hadd
  dsimp only [xr, xi] at hsmul hadd
  rw [hu, hadd, Pi.add_apply, hsmul, Pi.smul_apply, hr, hi]
  have hdu : HasDerivAt u (deriv u (x : ℝ)) (x : ℝ) :=
    (u.smooth.differentiable (by simp)).differentiableAt.hasDerivAt
  have hre : HasDerivAt (fun y : ℝ => (u y).re) (deriv u (x : ℝ)).re (x : ℝ) :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt (x : ℝ) hdu
  have him : HasDerivAt (fun y : ℝ => (u y).im) (deriv u (x : ℝ)).im (x : ℝ) :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (x : ℝ) hdu
  have hre' := hre.deriv
  have him' := him.deriv
  change deriv u (x : ℝ) =
    ((deriv (fun y : ℝ => (u y).re) (x : ℝ) : ℝ) : ℂ) +
      I * ((deriv (fun y : ℝ => (u y).im) (x : ℝ) : ℝ) : ℂ)
  rw [hre', him']
  rw [show I * ((deriv u (x : ℝ)).im : ℂ) =
      ((deriv u (x : ℝ)).im : ℂ) * I by ring,
    Complex.re_add_im]

theorem ccmRestrictedWeilForm_realImag_expansion
    (a : SuzukiPositiveAperture)
    (ur ui vr vi : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (ur + I • ui) (vr + I • vi) =
      ccmRestrictedWeilForm a ur vr + I * ccmRestrictedWeilForm a ur vi -
        I * ccmRestrictedWeilForm a ui vr + ccmRestrictedWeilForm a ui vi := by
  unfold ccmRestrictedWeilForm
  simp only [map_add, map_smul, inner_add_left, inner_add_right]
  simp only [Submodule.coe_inner, Submodule.coe_smul]
  simp_rw [inner_smul_left, inner_smul_right]
  simp only [Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem inner_suzukiScrewZeroMeanOperator_realImag_expansion
    (a : SuzukiPositiveAperture)
    (ur ui vr vi : SuzukiApertureZeroMean a) :
    inner ℂ (ur + I • ui)
        (suzukiScrewZeroMeanOperator a (vr + I • vi)) =
      inner ℂ ur (suzukiScrewZeroMeanOperator a vr) +
        I * inner ℂ ur (suzukiScrewZeroMeanOperator a vi) -
        I * inner ℂ ui (suzukiScrewZeroMeanOperator a vr) +
        inner ℂ ui (suzukiScrewZeroMeanOperator a vi) := by
  simp only [map_add, map_smul, inner_add_left, inner_add_right]
  simp only [Submodule.coe_inner, Submodule.coe_smul]
  simp_rw [inner_smul_left, inner_smul_right]
  simp only [Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Arbitrary complex strict-source CCM form equals Suzuki's literal compressed screw pairing. -/
theorem ccmRestrictedWeilForm_complexSmooth_eq_screwOperator
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector =
      inner ℂ u.toDerivativeZeroMean
        (suzukiScrewZeroMeanOperator a v.toDerivativeZeroMean) := by
  rw [u.toCCMFormVector_eq_real_add_I_imag,
    v.toCCMFormVector_eq_real_add_I_imag,
    u.toDerivativeZeroMean_eq_real_add_I_imag,
    v.toDerivativeZeroMean_eq_real_add_I_imag,
    ccmRestrictedWeilForm_realImag_expansion,
    inner_suzukiScrewZeroMeanOperator_realImag_expansion]
  rw [ccmRestrictedWeilForm_realCore_mixed_eq_screw,
    ccmRestrictedWeilForm_realCore_mixed_eq_screw,
    ccmRestrictedWeilForm_realCore_mixed_eq_screw,
    ccmRestrictedWeilForm_realCore_mixed_eq_screw]

/-- A strict CCM source as Suzuki's literal source test in `C(a)`. -/
def CCMComplexSmoothInteriorSource.toSuzukiSmoothCompactTest
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    SuzukiSmoothCompactTest a.1 where
  toFun := u
  smooth := u.smooth
  support_subset := u.support_subset.trans Ioo_subset_Icc_self

@[simp] theorem CCMComplexSmoothInteriorSource.toSuzukiSmoothCompactTest_apply
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) (x : ℝ) :
    u.toSuzukiSmoothCompactTest x = u x := rfl

/-- Whole-line derivative test is exactly zero extension of the interval derivative coordinate. -/
theorem CCMComplexSmoothInteriorSource.zeroExtend_toDerivativeZeroMean_eq_toSoninL2
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    suzukiApertureZeroExtendL2
        (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1) =
      u.toSuzukiSmoothCompactTest.toDerivativeZeroMean.toSoninL2 := by
  apply Lp.ext
  filter_upwards [suzukiApertureZeroExtendL2_coeFn
      (u.toDerivativeZeroMean : SuzukiApertureIntervalL2 a.1),
    suzukiApertureZeroExtend_smoothDerivativeCoordinate
      a u u.smooth u.hasCompactSupport u.tsupport_subset,
    u.toSuzukiSmoothCompactTest.toDerivativeZeroMean.coeFn_toSoninL2]
      with x hzero hderiv hsmooth
  rw [hzero, hsmooth]
  change suzukiApertureZeroExtend
      (suzukiSmoothDerivativeCoordinate a u u.smooth u.hasCompactSupport) x =
    deriv u x
  exact hderiv

/-- Mixed zero-extension bridge for Suzuki's literal `L²` screw form. -/
theorem suzukiScrewL2Form_zeroExtend_eq_intervalForm_pair
    {a : ℝ} (f g : SuzukiApertureIntervalL2 a) :
    suzukiScrewL2Form a (suzukiApertureZeroExtendL2 f)
        (suzukiApertureZeroExtendL2 g) =
      suzukiScrewIntervalForm a f g := by
  rw [suzukiScrewL2Form, suzukiApertureZeroExtendL2_cutoff f,
    suzukiApertureZeroExtendL2_cutoff g]
  have hf := suzukiApertureZeroExtendL2_coeFn f
  have hg := suzukiApertureZeroExtendL2_coeFn g
  calc
    (∫ t : ℝ, ∫ u : ℝ,
        suzukiScrewKernel t u * (suzukiApertureZeroExtendL2 f) u *
          (starRingEnd ℂ) ((suzukiApertureZeroExtendL2 g) t)) =
      ∫ t : ℝ, ∫ u : ℝ,
        suzukiScrewKernel t u * suzukiApertureZeroExtend f u *
          (starRingEnd ℂ) (suzukiApertureZeroExtend g t) := by
        apply integral_congr_ae
        filter_upwards [hg] with t hgt
        rw [hgt]
        apply integral_congr_ae
        filter_upwards [hf] with u hfu
        rw [hfu]
    _ = suzukiScrewIntervalForm a f g := by
      rw [suzukiScrewIntervalForm,
        ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
      · rw [← integral_subtype measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards [suzukiApertureRepresentative_ae g] with t hgt
        rw [suzukiApertureZeroExtend_apply, hgt]
        rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
        · rw [← integral_subtype measurableSet_Icc]
          apply integral_congr_ae
          filter_upwards [suzukiApertureRepresentative_ae f] with u hfu
          rw [suzukiApertureZeroExtend_apply, hfu]
        · intro u hu
          rw [suzukiApertureZeroExtend_eq_zero_of_notMem f hu]
          ring
      · intro t ht
        rw [suzukiApertureZeroExtend_eq_zero_of_notMem g ht]
        simp

/-- Compressed Suzuki pairing equals the paper's literal differentiated smooth form. -/
theorem inner_suzukiScrewZeroMeanOperator_complexSmoothDerivative_eq_smoothForm
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    inner ℂ u.toDerivativeZeroMean
        (suzukiScrewZeroMeanOperator a v.toDerivativeZeroMean) =
      suzukiScrewSmoothForm
        v.toSuzukiSmoothCompactTest.toDerivativeZeroMean
        u.toSuzukiSmoothCompactTest.toDerivativeZeroMean := by
  rw [suzukiScrewZeroMeanOperator,
    inner_suzukiCenteredScrewZeroMeanOperator_eq_intervalForm,
    suzukiScrewSmoothForm_eq_l2,
    ← v.zeroExtend_toDerivativeZeroMean_eq_toSoninL2,
    ← u.zeroExtend_toDerivativeZeroMean_eq_toSoninL2,
    suzukiScrewL2Form_zeroExtend_eq_intervalForm_pair]

/-- Exact mixed CCM source form as Suzuki's actual Xi-zero Weil distribution. -/
theorem ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution
    {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector =
      suzukiWeilDistribution
        (suzukiHermitianConvolution
          v.toSuzukiSmoothCompactTest u.toSuzukiSmoothCompactTest) := by
  rw [ccmRestrictedWeilForm_complexSmooth_eq_screwOperator,
    inner_suzukiScrewZeroMeanOperator_complexSmoothDerivative_eq_smoothForm,
    suzuki_proposition_three_one a.property]

end RHTower

