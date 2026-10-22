import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauSecondOrder
import GaloisForLFunctions.RHTower.ConstrainedWeilApertureWindowMean
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarMultiplier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiPolarTranslateMultiplier

/-!
# The pole-vanishing derivative test `D φ = φ'' − φ/4`

For a smooth zero-mean test `φ` the function `D φ = φ'' − φ/4` is again a smooth zero-mean test, and
its ray coefficients are those of `φ` multiplied by `−(z_q² + 1/4)`:

`Coef_q(Dφ) = −(z_q² + ¼) Coef_q(φ)`,  `Bar_q(Dφ) = −(z_q² + ¼) Bar_q(φ)`,

by two integrations by parts (`∫ e^{−izu} φ'' = −z² ∫ e^{−izu} φ`) and `∫ φ = 0`.  Hence the screw
form of `Dφ` is the ray energy of `φ` weighted by `(z_q² + ¼)²`.  The primitive of `Dφ` is
`D Φ` with `Φ` the zero-mean primitive of `φ`, which is pole-vanishing at every aperture containing
the support of `φ`; therefore the pole-vanishing ground energy `μ₀` satisfies

`μ₀(A) ‖DΦ‖² ≤ Re Q(Dφ)`.

For the twisted plateau test the source `DΦ = φ' − Φ/4` is bounded by `|γ| + 4K + (2a + 1)/4`
on `[−a, a]` and vanishes outside, so `‖DΦ‖² ≤ 2a (|γ| + 4K + (2a+1)/4)²`.
-/

open MeasureTheory Complex Set intervalIntegral

namespace RHTower

noncomputable section

/-! ## Conjugation commutes with differentiation -/

theorem hasDerivAt_conj_comp {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun y => (starRingEnd ℂ) (f y)) ((starRingEnd ℂ) f') x := by
  have := Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hf
  simpa [Function.comp_def] using this

theorem deriv_conj_comp {f : ℝ → ℂ} (hf : Differentiable ℝ f) :
    deriv (fun y => (starRingEnd ℂ) (f y)) = fun y => (starRingEnd ℂ) (deriv f y) := by
  funext y
  exact (hasDerivAt_conj_comp (hf y).hasDerivAt).deriv

theorem contDiff_conj_comp {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (starRingEnd ℂ) (f y)) :=
  Complex.conjCLE.contDiff.comp hf

/-! ## The derivative test -/

theorem SuzukiSmoothZeroMeanTest.deriv_contDiff {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv φ) :=
  (contDiff_infty_iff_deriv.mp φ.smooth).2

theorem SuzukiSmoothZeroMeanTest.deriv_deriv_contDiff {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv φ)) :=
  (contDiff_infty_iff_deriv.mp φ.deriv_contDiff).2

theorem SuzukiSmoothZeroMeanTest.tsupport_subset {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    tsupport φ ⊆ Icc (-a) a :=
  closure_minimal φ.support_subset isClosed_Icc

theorem SuzukiSmoothZeroMeanTest.deriv_support_subset {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    Function.support (deriv φ) ⊆ Icc (-a) a :=
  support_deriv_subset.trans φ.tsupport_subset

theorem SuzukiSmoothZeroMeanTest.deriv_deriv_support_subset {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) :
    Function.support (deriv (deriv φ)) ⊆ Icc (-a) a :=
  support_deriv_subset.trans (tsupport_deriv_subset.trans φ.tsupport_subset)

/-- The first derivative of a zero-mean test as a compact test. -/
def SuzukiSmoothZeroMeanTest.derivCompactTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    SuzukiSmoothCompactTest a where
  toFun := deriv φ
  smooth := φ.deriv_contDiff
  support_subset := φ.deriv_support_subset

theorem SuzukiSmoothZeroMeanTest.integral_deriv_deriv {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    ∫ x : ℝ, deriv (deriv φ) x = 0 :=
  φ.derivCompactTest.integral_deriv_eq_zero

theorem SuzukiSmoothZeroMeanTest.hasCompactSupport_deriv_deriv {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) : HasCompactSupport (deriv (deriv φ)) :=
  φ.hasCompactSupport.deriv.deriv

/-- The pole-vanishing derivative test `D φ = φ'' − φ/4`. -/
def SuzukiSmoothZeroMeanTest.polarDerivativeTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    SuzukiSmoothZeroMeanTest a where
  toFun := fun x => deriv (deriv φ) x - (φ : ℝ → ℂ) x / 4
  smooth := φ.deriv_deriv_contDiff.sub (φ.smooth.div_const 4)
  support_subset := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    apply hx
    have h1 : deriv (deriv φ) x = 0 := by
      by_contra h
      exact hmem (φ.deriv_deriv_support_subset h)
    have h2 : (φ : ℝ → ℂ) x = 0 := by
      by_contra h
      exact hmem (φ.support_subset h)
    rw [h1, h2]
    ring
  integral_zero := by
    show ∫ x : ℝ, (deriv (deriv φ) x - (φ : ℝ → ℂ) x / 4) = 0
    have hint1 : Integrable (deriv (deriv φ)) :=
      φ.deriv_deriv_contDiff.continuous.integrable_of_hasCompactSupport
        φ.hasCompactSupport_deriv_deriv
    have hint2 : Integrable (fun x : ℝ => (φ : ℝ → ℂ) x / 4) :=
      (integrable_suzukiSmoothZeroMeanTest φ).div_const 4
    rw [integral_sub hint1 hint2, φ.integral_deriv_deriv, MeasureTheory.integral_div, φ.integral_zero]
    simp

theorem SuzukiSmoothZeroMeanTest.polarDerivativeTest_apply {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (x : ℝ) :
    (φ.polarDerivativeTest : ℝ → ℂ) x = deriv (deriv φ) x - (φ : ℝ → ℂ) x / 4 := rfl

/-! ## Ray coefficients of the derivative test -/

/-- `∫ e^{w u} φ''(u) du = w² ∫ e^{w u} φ(u) du` for a smooth compactly supported `φ`. -/
theorem integral_cexp_mul_deriv_deriv {φ : ℝ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : HasCompactSupport φ) (w : ℂ) :
    ∫ u : ℝ, Complex.exp (w * (u : ℂ)) * deriv (deriv φ) u
      = w ^ 2 * ∫ u : ℝ, Complex.exp (w * (u : ℂ)) * φ u := by
  have h := GaloisForLFunctions.HTGeometry.testTransform_ibp_two hφ hs (-(I * w))
  unfold GaloisForLFunctions.HTGeometry.testTransform at h
  have e : ∀ L : ℝ, Complex.exp (I * -(I * w) * (L : ℂ)) = Complex.exp (w * (L : ℂ)) := by
    intro L
    congr 1
    linear_combination (-(w * (L : ℂ))) * Complex.I_sq
  simp_rw [e] at h
  have hsq : (I * -(I * w)) ^ 2 = w ^ 2 := by
    linear_combination ((Complex.I ^ 2 - 1) * w ^ 2) * Complex.I_sq
  rw [hsq] at h
  have e1 : (∫ L : ℝ, φ L * Complex.exp (w * (L : ℂ)))
      = ∫ u : ℝ, Complex.exp (w * (u : ℂ)) * φ u :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only; ring)
  have e2 : (∫ L : ℝ, deriv (deriv φ) L * Complex.exp (w * (L : ℂ)))
      = ∫ u : ℝ, Complex.exp (w * (u : ℂ)) * deriv (deriv φ) u :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => by simp only; ring)
  rw [e1, e2] at h
  rw [← h]
  ring

theorem integrable_cexp_mul_deriv_deriv {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (w : ℂ) :
    Integrable (fun u : ℝ => Complex.exp (w * (u : ℂ)) * deriv (deriv φ) u) := by
  have hc : Continuous fun u : ℝ => Complex.exp (w * (u : ℂ)) * deriv (deriv φ) u :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
      φ.deriv_deriv_contDiff.continuous
  exact hc.integrable_of_hasCompactSupport
    (hasCompactSupport_mul_of_right φ.hasCompactSupport_deriv_deriv _)

/-- **Ray coefficient of the derivative test.** -/
theorem suzukiTestRayCoef_polarDerivativeTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (q : XiZeroCopy) :
    suzukiTestRayCoef φ.polarDerivativeTest q
      = -(xiSpectralPoint q ^ 2 + 1 / 4) * suzukiTestRayCoef φ q := by
  rw [suzukiTestRayCoef_eq_integral, suzukiTestRayCoef_eq_integral]
  simp_rw [SuzukiSmoothZeroMeanTest.polarDerivativeTest_apply]
  have hsplit : ∀ u : ℝ,
      Complex.exp ((-(I * xiSpectralPoint q)) * (u : ℂ)) * (deriv (deriv φ) u - (φ : ℝ → ℂ) u / 4)
        = Complex.exp ((-(I * xiSpectralPoint q)) * (u : ℂ)) * deriv (deriv φ) u
          - (1 / 4 : ℂ) * (Complex.exp ((-(I * xiSpectralPoint q)) * (u : ℂ)) * (φ : ℝ → ℂ) u) := by
    intro u; ring
  simp_rw [hsplit]
  rw [integral_sub (integrable_cexp_mul_deriv_deriv φ _)
    ((integrable_cexp_mul_test φ _).const_mul _), MeasureTheory.integral_const_mul,
    integral_cexp_mul_deriv_deriv φ.smooth φ.hasCompactSupport]
  have hw : (-(I * xiSpectralPoint q)) ^ 2 = -(xiSpectralPoint q ^ 2) := by
    linear_combination (xiSpectralPoint q ^ 2) * Complex.I_sq
  rw [hw]
  ring

/-- **Reflected ray coefficient of the derivative test.** -/
theorem suzukiTestRayCoefBar_polarDerivativeTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (q : XiZeroCopy) :
    suzukiTestRayCoefBar φ.polarDerivativeTest q
      = -(xiSpectralPoint q ^ 2 + 1 / 4) * suzukiTestRayCoefBar φ q := by
  rw [suzukiTestRayCoefBar_eq_integral, suzukiTestRayCoefBar_eq_integral]
  simp_rw [SuzukiSmoothZeroMeanTest.polarDerivativeTest_apply]
  have hdiff : Differentiable ℝ (φ : ℝ → ℂ) := φ.smooth.differentiable (by simp)
  have hdiff' : Differentiable ℝ (deriv φ) := φ.deriv_contDiff.differentiable (by simp)
  have hconj2 : ∀ t : ℝ, (starRingEnd ℂ) (deriv (deriv φ) t)
      = deriv (deriv fun y : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) y)) t := by
    intro t
    rw [deriv_conj_comp hdiff, deriv_conj_comp hdiff']
  have hsplit : ∀ t : ℝ,
      Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
          * (starRingEnd ℂ) (deriv (deriv φ) t - (φ : ℝ → ℂ) t / 4)
        = Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
            * deriv (deriv fun y : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) y)) t
          - (1 / 4 : ℂ) * (Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
              * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)) := by
    intro t
    rw [map_sub, map_div₀, map_ofNat, hconj2 t]
    ring
  simp_rw [hsplit]
  have hcs : HasCompactSupport (fun y : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) y)) :=
    φ.hasCompactSupport.comp_left (map_zero _)
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) y)) :=
    contDiff_conj_comp φ.smooth
  have hint1 : Integrable (fun t : ℝ => Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
      * deriv (deriv fun y : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) y)) t) := by
    have hc : Continuous fun t : ℝ => Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
        * deriv (deriv fun y : ℝ => (starRingEnd ℂ) ((φ : ℝ → ℂ) y)) t := by
      refine (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul ?_
      exact ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hsm).2).2).continuous
    exact hc.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hcs.deriv.deriv _)
  have hint2 : Integrable (fun t : ℝ => Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
      * (starRingEnd ℂ) ((φ : ℝ → ℂ) t)) := by
    have hc : Continuous fun t : ℝ => Complex.exp ((I * xiSpectralPoint q) * (t : ℂ))
        * (starRingEnd ℂ) ((φ : ℝ → ℂ) t) :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_conj.comp φ.continuous)
    exact hc.integrable_of_hasCompactSupport (hasCompactSupport_mul_of_right hcs _)
  rw [integral_sub hint1 (hint2.const_mul _), MeasureTheory.integral_const_mul,
    integral_cexp_mul_deriv_deriv hsm hcs]
  have hw : (I * xiSpectralPoint q) ^ 2 = -(xiSpectralPoint q ^ 2) := by
    linear_combination (xiSpectralPoint q ^ 2) * Complex.I_sq
  rw [hw]
  ring

/-- **The screw form of `Dφ` is the ray energy of `φ` weighted by `(z_q² + ¼)²`.** -/
theorem suzukiScrewSmoothForm_polarDerivativeTest {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) :
    suzukiScrewSmoothForm φ.polarDerivativeTest φ.polarDerivativeTest
      = ∑' q : XiZeroCopy, (xiSpectralPoint q ^ 2 + 1 / 4) ^ 2
          * (suzukiTestRayCoefBar φ q * suzukiTestRayCoef φ q / xiSpectralPoint q ^ 2) := by
  rw [suzukiScrewSmoothForm_eq_tsum]
  refine tsum_congr fun q => ?_
  rw [suzukiTestRayCoef_polarDerivativeTest, suzukiTestRayCoefBar_polarDerivativeTest]
  ring

/-! ## The pole-vanishing source and the ground-energy transfer -/

/-- The source `D Φ` with `Φ` the zero-mean primitive of `φ`, at an aperture containing the
support of `φ`. -/
def SuzukiSmoothZeroMeanTest.polarDerivativeSource {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (A : SuzukiPositiveAperture) (hA : a < A.1) : CCMComplexSmoothInteriorSource A :=
  (φ.zeroMeanPrimitiveSource A hA).polarMultiplier

theorem SuzukiSmoothZeroMeanTest.polarDerivativeSource_apply {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (A : SuzukiPositiveAperture) (hA : a < A.1) (x : ℝ) :
    (φ.polarDerivativeSource A hA : ℝ → ℂ) x = deriv φ x + (-(1 / 4 : ℂ)) * φ.zeroMeanPrimitive x := by
  show deriv (deriv φ.zeroMeanPrimitive) x + (-(1 / 4 : ℂ)) * φ.zeroMeanPrimitive x = _
  rw [φ.deriv_zeroMeanPrimitive]

theorem isPolarConstrained_polarDerivativeSource {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (A : SuzukiPositiveAperture) (hA : a < A.1) :
    IsPolarConstrained A (φ.polarDerivativeSource A hA).toCCMFormVector :=
  isPolarConstrained_polarMultiplier _

/-- The derivative test of the source `DΦ` is `Dφ`. -/
theorem deriv_polarDerivativeSource {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a)
    (A : SuzukiPositiveAperture) (hA : a < A.1) :
    ((φ.polarDerivativeSource A hA).toSuzukiSmoothCompactTest.toDerivativeZeroMean : ℝ → ℂ)
      = (φ.polarDerivativeTest : ℝ → ℂ) := by
  rw [SuzukiSmoothCompactTest.coe_toDerivativeZeroMean]
  funext x
  have hfun : ((φ.polarDerivativeSource A hA).toSuzukiSmoothCompactTest : ℝ → ℂ)
      = fun y => deriv φ y + (-(1 / 4 : ℂ)) * φ.zeroMeanPrimitive y := by
    funext y
    rw [CCMComplexSmoothInteriorSource.toSuzukiSmoothCompactTest_apply]
    exact φ.polarDerivativeSource_apply A hA y
  rw [hfun]
  have hd1 : HasDerivAt (deriv φ) (deriv (deriv φ) x) x :=
    (φ.deriv_contDiff.differentiable (by simp) x).hasDerivAt
  have hd2 : HasDerivAt (fun y => (-(1 / 4 : ℂ)) * φ.zeroMeanPrimitive y)
      ((-(1 / 4 : ℂ)) * (φ : ℝ → ℂ) x) x :=
    (φ.hasDerivAt_zeroMeanPrimitive x).const_mul _
  have hd : HasDerivAt (fun y => deriv φ y + (-(1 / 4 : ℂ)) * φ.zeroMeanPrimitive y)
      (deriv (deriv φ) x + (-(1 / 4 : ℂ)) * (φ : ℝ → ℂ) x) x := hd1.add hd2
  rw [hd.deriv, SuzukiSmoothZeroMeanTest.polarDerivativeTest_apply]
  ring

/-- **Ground-energy transfer.**  `μ₀(A) ‖DΦ‖² ≤ Re Q(Dφ)`. -/
theorem polarGroundEnergy_mul_le_re_smoothForm_polarDerivativeTest {a : ℝ}
    (φ : SuzukiSmoothZeroMeanTest a) (A : SuzukiPositiveAperture) (hA : a < A.1) :
    ccmRestrictedWeilPolarGroundEnergy A
        * ‖ccmArchimedeanFormToAperture A (φ.polarDerivativeSource A hA).toCCMFormVector‖ ^ 2
      ≤ (suzukiScrewSmoothForm φ.polarDerivativeTest φ.polarDerivativeTest).re := by
  have h := ccmRestrictedWeilPolarGroundEnergy_mul_le A _ (isPolarConstrained_polarDerivativeSource φ A hA)
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm,
    suzukiScrewSmoothForm_congr_coe _ φ.polarDerivativeTest (deriv_polarDerivativeSource φ A hA)]
    at h
  exact h

/-! ## The norm of the source -/

/-- The aperture norm of a smooth source is its `L²` norm. -/
theorem norm_sq_toAperture_eq_integral {A : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource A) :
    ‖ccmArchimedeanFormToAperture A u.toCCMFormVector‖ ^ 2 = ∫ x : ℝ, ‖(u : ℝ → ℂ) x‖ ^ 2 := by
  change ‖((ccmArchimedeanFormToAperture A u.toCCMFormVector : suzukiApertureHilbert A) : SoninL2)‖ ^ 2
    = _
  rw [norm_sq_eq_integral]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [u.toCCMFormVector_physical_coeFn] with x hx
  rw [hx]

theorem norm_zeroMeanPrimitive_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (ha : 0 ≤ a)
    (hφ : ∀ x, ‖(φ : ℝ → ℂ) x‖ ≤ 1) (x : ℝ) :
    ‖φ.zeroMeanPrimitive x‖ ≤ 2 * a + 1 := by
  rcases lt_or_ge x (-a) with hx | hx
  · rw [φ.zeroMeanPrimitive_eq_zero_of_lt hx, norm_zero]; linarith
  rcases lt_or_ge a x with hx' | hx'
  · rw [φ.zeroMeanPrimitive_eq_zero_of_gt hx', norm_zero]; linarith
  unfold SuzukiSmoothZeroMeanTest.zeroMeanPrimitive
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -a - 1) (b := x) (C := 1)
    (f := φ) fun t _ => hφ t
  refine h.trans ?_
  rw [one_mul, abs_of_nonneg (by linarith)]
  linarith

/-- Norm bound for the source `DΦ` built from a test bounded by `1` with derivative bounded by `B`. -/
theorem integral_norm_sq_polarDerivativeSource_le {a : ℝ} (φ : SuzukiSmoothZeroMeanTest a) (ha : 0 ≤ a)
    (A : SuzukiPositiveAperture) (hA : a < A.1)
    (hφ : ∀ x, ‖(φ : ℝ → ℂ) x‖ ≤ 1) {B : ℝ} (hφ' : ∀ x, ‖deriv φ x‖ ≤ B) :
    ∫ x : ℝ, ‖(φ.polarDerivativeSource A hA : ℝ → ℂ) x‖ ^ 2
      ≤ 2 * a * (B + (2 * a + 1) / 4) ^ 2 := by
  have hpt : ∀ x, ‖(φ.polarDerivativeSource A hA : ℝ → ℂ) x‖ ≤ B + (2 * a + 1) / 4 := by
    intro x
    rw [φ.polarDerivativeSource_apply A hA x]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
    have h1 := hφ' x
    have h2 := norm_zeroMeanPrimitive_le φ ha hφ x
    nlinarith
  have hzero : ∀ x ∉ Icc (-a) a, ‖(φ.polarDerivativeSource A hA : ℝ → ℂ) x‖ ^ 2 = 0 := by
    intro x hx
    rw [φ.polarDerivativeSource_apply A hA x]
    have h1 : deriv φ x = 0 := by
      by_contra h
      exact hx (φ.deriv_support_subset h)
    have h2 : φ.zeroMeanPrimitive x = 0 := by
      by_contra h
      exact hx (φ.support_zeroMeanPrimitive_subset h)
    rw [h1, h2]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have hcont : Continuous fun x : ℝ => ‖(φ.polarDerivativeSource A hA : ℝ → ℂ) x‖ ^ 2 :=
    ((φ.polarDerivativeSource A hA).smooth.continuous.norm).pow 2
  calc ∫ x in Icc (-a) a, ‖(φ.polarDerivativeSource A hA : ℝ → ℂ) x‖ ^ 2
      ≤ ∫ x in Icc (-a) a, (B + (2 * a + 1) / 4) ^ 2 := by
        refine setIntegral_mono_on hcont.integrableOn_Icc continuous_const.integrableOn_Icc
          measurableSet_Icc fun x _ => ?_
        exact pow_le_pow_left₀ (norm_nonneg _) (hpt x) 2
    _ = 2 * a * (B + (2 * a + 1) / 4) ^ 2 := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        ring

/-! ## Bounds for the twisted plateau test -/

theorem norm_twistedOddTest_plateau_le {a : ℝ} (ha0 : 0 ≤ a) (γ x : ℝ) :
    ‖(twistedOddTest (plateauProfile a ha0) γ : ℝ → ℂ) x‖ ≤ 1 := by
  rw [twistedOddTest_apply, Complex.norm_real, Real.norm_eq_abs, abs_mul, plateauProfile_apply]
  have h1 := Real.abs_cos_le_one (γ * x)
  have h2 := abs_plateauProfileFun_le_one a x
  exact mul_le_one₀ h1 (abs_nonneg _) h2

theorem hasDerivAt_twistedOddTest_plateau {a : ℝ} (ha0 : 0 ≤ a) (γ x : ℝ) :
    HasDerivAt (twistedOddTest (plateauProfile a ha0) γ : ℝ → ℂ)
      (((-Real.sin (γ * x) * γ * plateauProfileFun a x
          + Real.cos (γ * x) * plateauProfileDeriv a x : ℝ)) : ℂ) x := by
  have hlin : HasDerivAt (fun y : ℝ => γ * y) γ x := by
    simpa using (hasDerivAt_id x).const_mul γ
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (γ * y)) (-Real.sin (γ * x) * γ) x := hlin.cos
  have hprod := hcos.mul (hasDerivAt_plateauProfileFun a x)
  have h := hprod.ofReal_comp
  refine h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  rw [twistedOddTest_apply, plateauProfile_apply]
  rfl

theorem norm_deriv_twistedOddTest_plateau_le {a : ℝ} (ha0 : 0 ≤ a) (γ : ℝ) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℝ, |deriv plateauEdge s| ≤ K) (x : ℝ) :
    ‖deriv (twistedOddTest (plateauProfile a ha0) γ : ℝ → ℂ) x‖ ≤ |γ| + 4 * K := by
  rw [(hasDerivAt_twistedOddTest_plateau ha0 γ x).deriv, Complex.norm_real, Real.norm_eq_abs]
  have h1 := Real.abs_sin_le_one (γ * x)
  have h2 := Real.abs_cos_le_one (γ * x)
  have h3 := abs_plateauProfileFun_le_one a x
  have h4 := abs_plateauProfileDeriv_le hK0 hK a x
  calc |-Real.sin (γ * x) * γ * plateauProfileFun a x + Real.cos (γ * x) * plateauProfileDeriv a x|
      ≤ |-Real.sin (γ * x) * γ * plateauProfileFun a x|
          + |Real.cos (γ * x) * plateauProfileDeriv a x| := abs_add_le _ _
    _ = |Real.sin (γ * x)| * |γ| * |plateauProfileFun a x|
          + |Real.cos (γ * x)| * |plateauProfileDeriv a x| := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul]
    _ ≤ 1 * |γ| * 1 + 1 * (4 * K) := by
        gcongr
    _ = |γ| + 4 * K := by ring

/-- **Norm of the twisted plateau source.** -/
theorem norm_sq_twistedPlateau_polarDerivativeSource_le {a : ℝ} (ha0 : 0 ≤ a) (γ : ℝ)
    (A : SuzukiPositiveAperture) (hA : a < A.1) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ s : ℝ, |deriv plateauEdge s| ≤ K) :
    ‖ccmArchimedeanFormToAperture A
        ((twistedOddTest (plateauProfile a ha0) γ).polarDerivativeSource A hA).toCCMFormVector‖ ^ 2
      ≤ 2 * a * (|γ| + 4 * K + (2 * a + 1) / 4) ^ 2 := by
  rw [norm_sq_toAperture_eq_integral]
  exact integral_norm_sq_polarDerivativeSource_le _ ha0 A hA (norm_twistedOddTest_plateau_le ha0 γ)
    (norm_deriv_twistedOddTest_plateau_le ha0 γ hK0 hK)

end

end RHTower
