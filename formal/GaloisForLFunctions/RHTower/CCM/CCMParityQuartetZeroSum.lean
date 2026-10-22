import GaloisForLFunctions.RHTower.Suzuki.SuzukiPolarTranslateMultiplier
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewTestRayEnergy
import GaloisForLFunctions.HTGeometry.CompactTestTransform
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGroundParity
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRayleighInfimum
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.GaussHodgeWeilDeviationMoment
import GaloisForLFunctions.RHTower.CCM.CCMParityQuartetModel

/-!
# The restricted Weil form of a smooth source as a sum over Xi zeros, by transforms

For a strict-interior smooth source `u` at aperture `a`, with `û(w) = ∫ u(x) e^{iwx} dx`
(`testTransform`), the CCM source quadratic is

`Q_a(u) = Re Σ_q û(−z_q) · conj û(−z̄_q)`  (`sourceQuadratic_eq_re_tsum`),

where `z_q` runs over the spectral points of the Xi zero copies.  The sum converges absolutely
(`summable_zeroSumTerm`).  The proof integrates Suzuki's ray coefficients of the derivative test by
parts: each ray coefficient is `±i z` times a transform, and the two factors `iz`, `−iz` cancel
against `z²`.

Consequences used for the parity analysis:

* a real spectral point contributes `|û(−z)|² ≥ 0` (`re_zeroSumTerm_nonneg_of_im_eq_zero`);
* for an even or odd source the four points of a quartet `{σ, σ̄, −σ, −σ̄}` contribute the same
  real part `Re(û(σ) conj û(σ̄))` (`re_zeroSumTerm_quartet`);
* Cauchy–Schwarz bounds every transform by the physical norm (`norm_integral_mul_sq_le`).
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityQuartet

noncomputable section

/-! ## The zero-copy term -/

/-- The zero-copy term `f̂(−z) · conj f̂(−z̄)` of the Weil zero sum. -/
def zeroSumTerm (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  testTransform f (-z) * (starRingEnd ℂ) (testTransform f (-(starRingEnd ℂ) z))

/-- The transform of the conjugate function. -/
theorem testTransform_conj (f : ℝ → ℂ) (z : ℂ) :
    testTransform (fun x => (starRingEnd ℂ) (f x)) z =
      (starRingEnd ℂ) (testTransform f (-(starRingEnd ℂ) z)) := by
  unfold testTransform
  rw [← integral_conj]
  congr 1
  funext L
  rw [map_mul, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem contDiff_one_conj {g : ℝ → ℂ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun x => (starRingEnd ℂ) (g x)) :=
  Complex.conjCLE.contDiff.comp hg

theorem deriv_conj {g : ℝ → ℂ} (hg : Differentiable ℝ g) :
    deriv (fun x => (starRingEnd ℂ) (g x)) = fun x => (starRingEnd ℂ) (deriv g x) := by
  funext x
  exact ((hg x).hasDerivAt.star).deriv

/-- **Ray coefficients of the derivative test are transforms.** -/
theorem rayCoef_mul_div_sq_eq_zeroSumTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) :
    suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q *
        suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q /
          xiSpectralPoint q ^ (2 : ℕ) = zeroSumTerm u (xiSpectralPoint q) := by
  set γ : ℂ := xiSpectralPoint q with hγ
  have hγ0 : γ ≠ 0 := xiSpectralPoint_ne_zero q
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  have hus : HasCompactSupport (u : ℝ → ℂ) := u.hasCompactSupport
  set v : ℝ → ℂ := fun x => (starRingEnd ℂ) (u x) with hv
  have hv1 : ContDiff ℝ 1 v := contDiff_one_conj hu1
  have hvs : HasCompactSupport v := hus.comp_left (map_zero _)
  have hcoe : (u.toSuzukiSmoothCompactTest.toDerivativeZeroMean : ℝ → ℂ) =
      deriv (u : ℝ → ℂ) := rfl
  have hdv : deriv v = fun t => (starRingEnd ℂ) (deriv (u : ℝ → ℂ) t) :=
    deriv_conj (hu1.differentiable one_ne_zero)
  have hcoef : suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      testTransform (deriv (u : ℝ → ℂ)) (-γ) := by
    rw [suzukiTestRayCoef_eq_integral, hcoe]
    unfold testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_comm]
    congr 2
    ring
  have hbar : suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      testTransform (deriv v) γ := by
    rw [suzukiTestRayCoefBar_eq_integral, hcoe, hdv]
    unfold testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_comm]
  have hibp1 := testTransform_ibp hu1 hus (-γ)
  have hibp2 := testTransform_ibp hv1 hvs γ
  have hT1 : testTransform (deriv (u : ℝ → ℂ)) (-γ) =
      -(testTransform (u : ℝ → ℂ) (-γ) * (Complex.I * -γ)) := by
    rw [hibp1, neg_neg]
  have hT2 : testTransform (deriv v) γ = -(testTransform v γ * (Complex.I * γ)) := by
    rw [hibp2, neg_neg]
  rw [hbar, hcoef, hT1, hT2, hv, testTransform_conj]
  unfold zeroSumTerm
  field_simp
  linear_combination (-(testTransform (↑u) (-γ) *
    (starRingEnd ℂ) (testTransform (↑u) (-(starRingEnd ℂ) γ)))) * Complex.I_sq

/-- **The source quadratic as a zero sum.** -/
theorem sourceQuadratic_eq_re_tsum {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      (∑' q : XiZeroCopy, zeroSumTerm u (xiSpectralPoint q)).re := by
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm,
    suzukiScrewSmoothForm_eq_tsum]
  congr 1
  exact tsum_congr (rayCoef_mul_div_sq_eq_zeroSumTerm u)

theorem summable_zeroSumTerm {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    Summable fun q : XiZeroCopy => zeroSumTerm u (xiSpectralPoint q) := by
  set φ := u.toSuzukiSmoothCompactTest.toDerivativeZeroMean with hφ
  set C : ℝ := (Real.exp (|a.1| / 2) + 1) * ∫ x : ℝ, ‖(φ : ℝ → ℂ) x‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _)
  apply Summable.of_norm_bounded (xiSpectralPoint_inv_sq_summable.mul_left (C * C))
  intro q
  rw [← rayCoef_mul_div_sq_eq_zeroSumTerm u q, norm_div, norm_mul, norm_pow, mul_one_div]
  have h1 := norm_suzukiTestRayCoefBar_le φ q
  have h2 := norm_suzukiTestRayCoef_le φ q
  have hz : 0 ≤ ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul h1 h2 (norm_nonneg _) hC0) hz

/-! ## Sign and symmetry of the terms -/

theorem re_zeroSumTerm_nonneg_of_im_eq_zero (f : ℝ → ℂ) {z : ℂ} (hz : z.im = 0) :
    0 ≤ (zeroSumTerm f z).re := by
  have hconj : (starRingEnd ℂ) z = z := Complex.conj_eq_iff_im.mpr hz
  unfold zeroSumTerm
  rw [hconj, Complex.mul_conj]
  exact Complex.normSq_nonneg _

/-- Transforms of a source with a reflection sign `s`. -/
theorem testTransform_neg_of_reflect {f : ℝ → ℂ} {s : ℂ} (hf : ∀ x, f (-x) = s * f x) (w : ℂ) :
    testTransform f (-w) = s * testTransform f w := by
  unfold testTransform
  rw [← integral_neg_eq_self, ← integral_const_mul]
  congr 1
  funext x
  rw [hf]
  push_cast
  ring_nf

theorem re_zeroSumTerm_quartet {f : ℝ → ℂ} {s : ℂ} (hf : ∀ x, f (-x) = s * f x)
    (hs : s * (starRingEnd ℂ) s = 1) (σ : ℂ) {z : ℂ}
    (hz : z = σ ∨ z = (starRingEnd ℂ) σ ∨ z = -σ ∨ z = -(starRingEnd ℂ) σ) :
    (zeroSumTerm f z).re =
      (testTransform f σ * (starRingEnd ℂ) (testTransform f ((starRingEnd ℂ) σ))).re := by
  have hneg := testTransform_neg_of_reflect hf
  rcases hz with rfl | rfl | rfl | rfl
  · unfold zeroSumTerm
    rw [hneg, hneg, map_mul]
    have : s * testTransform f z * ((starRingEnd ℂ) s *
        (starRingEnd ℂ) (testTransform f ((starRingEnd ℂ) z))) =
        (s * (starRingEnd ℂ) s) *
          (testTransform f z * (starRingEnd ℂ) (testTransform f ((starRingEnd ℂ) z))) := by ring
    rw [this, hs, one_mul]
  · unfold zeroSumTerm
    rw [Complex.conj_conj, hneg, hneg, map_mul]
    have : s * testTransform f ((starRingEnd ℂ) σ) * ((starRingEnd ℂ) s *
        (starRingEnd ℂ) (testTransform f σ)) =
        (s * (starRingEnd ℂ) s) *
          (starRingEnd ℂ) (testTransform f σ * (starRingEnd ℂ)
            (testTransform f ((starRingEnd ℂ) σ))) := by
      rw [map_mul, Complex.conj_conj]
      ring
    rw [this, hs, one_mul, Complex.conj_re]
  · unfold zeroSumTerm
    rw [neg_neg, map_neg, neg_neg]
  · unfold zeroSumTerm
    rw [neg_neg, map_neg, Complex.conj_conj, neg_neg]
    rw [show testTransform f ((starRingEnd ℂ) σ) * (starRingEnd ℂ) (testTransform f σ) =
        (starRingEnd ℂ) (testTransform f σ * (starRingEnd ℂ)
          (testTransform f ((starRingEnd ℂ) σ))) by
      rw [map_mul, Complex.conj_conj]
      ring]
    rw [Complex.conj_re]

/-! ## Cauchy–Schwarz -/

/-- `‖∫ F H‖² ≤ (∫ ‖F‖²)(∫ ‖H‖²)` for square-integrable `F, H`. -/
theorem norm_integral_mul_sq_le {F H : ℝ → ℂ} (hF : MemLp F 2) (hH : MemLp H 2) :
    ‖∫ x, F x * H x‖ ^ 2 ≤ (∫ x, ‖F x‖ ^ 2) * ∫ x, ‖H x‖ ^ 2 := by
  have hF' : MemLp F (ENNReal.ofReal 2) := by simpa using hF
  have hH' : MemLp H (ENNReal.ofReal 2) := by simpa using hH
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hF' hH'
  have h1 : ‖∫ x, F x * H x‖ ≤ ∫ x, ‖F x‖ * ‖H x‖ := by
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    simp only [norm_mul]
  have hA : 0 ≤ ∫ x, ‖F x‖ ^ (2 : ℝ) := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ ∫ x, ‖H x‖ ^ (2 : ℝ) := integral_nonneg fun _ => by positivity
  have hrpow : ∀ g : ℝ → ℂ, (∫ x, ‖g x‖ ^ (2 : ℝ)) = ∫ x, ‖g x‖ ^ 2 := fun g => by
    congr 1
    funext x
    exact Real.rpow_two _
  have hsq : (∫ x, ‖F x‖ * ‖H x‖) ^ 2 ≤
      ((∫ x, ‖F x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∫ x, ‖H x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (integral_nonneg fun _ => by positivity) hcs 2
  rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA, Real.sq_sqrt hB,
    hrpow F, hrpow H] at hsq
  calc ‖∫ x, F x * H x‖ ^ 2 ≤ (∫ x, ‖F x‖ * ‖H x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := hsq

end

end RHTower.CCMParityQuartet
