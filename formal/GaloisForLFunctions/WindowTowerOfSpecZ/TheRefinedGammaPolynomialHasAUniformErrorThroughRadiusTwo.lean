import GaloisForLFunctions.WindowTowerOfSpecZ.NewtonRefinementControlsTheGammaKernelThroughRadiusTwo
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaComparisonRetainsItsChargesThroughRadiusTwo

/-!
# Uniform Gamma comparison through diameter two

The normalized sine reciprocal has constant coefficient one after every
Newton update. Factoring its quadratic vanishing removes the apparent
singularity at lag zero. The resulting polynomial lower form differs
from the Gamma energy by at most `6r/10¹⁷` times source mass.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory BiScaleUncertainty SpacingScaleHarmonicAnalysis

private def sinhLowerFactor (z : ℝ) : ℝ :=
  -1 / 6 + 7 * z ^ 2 / 360 - 31 * z ^ 4 / 15120 +
    127 * z ^ 6 / 604800 - 73 * z ^ 8 / 3421440 +
    1414477 * z ^ 10 / 653837184000 - 8191 * z ^ 12 / 37362124800

private def sinhUpperFactor (z : ℝ) : ℝ :=
  1 / 6 + z ^ 2 / 120 + z ^ 4 / 5040 + z ^ 6 / 362880 +
    z ^ 8 / 39916800 + z ^ 10 / 6227020800 + z ^ 12 / 1307674368000 +
    z ^ 14 / 355687428096000 + z ^ 16 / 100000000000000000

private def newtonFactor (z t p : ℝ) : ℝ :=
  -t - z ^ 2 * p ^ 2 - 2 * z ^ 2 * t * p - z ^ 4 * t * p ^ 2

private def sinhRefinedFactor (z : ℝ) : ℝ :=
  newtonFactor z (sinhUpperFactor z)
    (newtonFactor z (sinhUpperFactor z)
      (newtonFactor z (sinhUpperFactor z) (sinhLowerFactor z)))

private theorem reciprocal_newton_factor (z t p : ℝ) :
    gammaReciprocalNewton (1 + z ^ 2 * t) (1 + z ^ 2 * p) =
      1 + z ^ 2 * newtonFactor z t p := by
  dsimp only [gammaReciprocalNewton, newtonFactor]
  ring

private theorem sinh_newton3_factor (z : ℝ) :
    gammaSinhPolynomialNewton3 z = 1 + z ^ 2 * sinhRefinedFactor z := by
  have hT : gammaSinhDenominatorUpper z = 1 + z ^ 2 * sinhUpperFactor z := by
    dsimp only [gammaSinhDenominatorUpper, sinhUpperFactor]
    ring
  have hq : gammaSinhPolynomial14 z = 1 + z ^ 2 * sinhLowerFactor z := by
    dsimp only [gammaSinhPolynomial14, sinhLowerFactor]
    ring
  change gammaReciprocalNewton (gammaSinhDenominatorUpper z)
    (gammaReciprocalNewton (gammaSinhDenominatorUpper z)
      (gammaReciprocalNewton (gammaSinhDenominatorUpper z) (gammaSinhPolynomial14 z))) = _
  rw [hT, hq, reciprocal_newton_factor, reciprocal_newton_factor, reciprocal_newton_factor]
  rfl

private theorem continuous_newton {T q : ℝ → ℝ} (hT : Continuous T) (hq : Continuous q) :
    Continuous (fun z => gammaReciprocalNewton (T z) (q z)) :=
  hq.mul (continuous_const.sub (hT.mul hq))

private theorem continuous_cosh_newton3 : Continuous gammaCoshPolynomialNewton3 := by
  have hT : Continuous gammaCoshDenominatorUpper := by
    unfold gammaCoshDenominatorUpper
    fun_prop
  have hq : Continuous gammaCoshPolynomial14 := by
    unfold gammaCoshPolynomial14
    fun_prop
  exact continuous_newton hT (continuous_newton hT (continuous_newton hT hq))

/-- The refined higher-lag polynomial, with its removable singularity already canceled. -/
def gammaHigherLagPolynomialNewton3 (t : ℝ) : ℝ :=
  t / 4 * sinhRefinedFactor (t / 2) + (gammaCoshPolynomialNewton3 (t / 2) - 1) / 2 +
    t / 24 + t ^ 2 / 16

private theorem continuous_higher_lag_newton3 : Continuous gammaHigherLagPolynomialNewton3 := by
  have hp : Continuous sinhRefinedFactor := by
    dsimp only [sinhRefinedFactor, newtonFactor, sinhUpperFactor, sinhLowerFactor]
    fun_prop
  have hq := continuous_cosh_newton3.comp (continuous_id.div_const 2)
  dsimp only [gammaHigherLagPolynomialNewton3]
  exact (((continuous_id.div_const 4).mul (hp.comp (continuous_id.div_const 2))).add
    ((hq.sub continuous_const).div_const 2)).add (continuous_id.div_const 24) |>.add
      ((continuous_id.pow 2).div_const 16)

private theorem gamma_newton3_residual_identity {t : ℝ} (ht : t ≠ 0) :
    retainedGammaRemainderWeight t - gammaHigherLagPolynomialNewton3 t =
      archLevySinhWeight t -
        (gammaSinhPolynomialNewton3 (t / 2) / t + gammaCoshPolynomialNewton3 (t / 2) / 2) := by
  rw [sinh_newton3_factor]
  dsimp only [retainedGammaRemainderWeight, gammaHigherLagPolynomialNewton3]
  field_simp [ht]
  ring

private theorem refined_polynomial_lag_integrable {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) (r : ℝ) :
    IntegrableOn (fun t => gammaHigherLagPolynomialNewton3 t *
      (autocorr F 0 - autocorr F t)) (Ioc (0 : ℝ) r) :=
  (continuous_higher_lag_newton3.mul (continuous_const.sub
    (_root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs))).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self

/-- The integrated refined kernel error is bounded by `6r/10¹⁷` times mass. -/
theorem local_gamma_remainder_sub_newton3 {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ 2) :
    0 ≤ (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t)) -
      (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomialNewton3 t *
        (autocorr F 0 - autocorr F t)) ∧
    (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t)) -
      (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomialNewton3 t *
        (autocorr F 0 - autocorr F t)) ≤
      (6 * r / 100000000000000000) * ∫ x, F x ^ 2 := by
  let D := fun t => autocorr F 0 - autocorr F t
  have hd (t : ℝ) : 0 ≤ D t ∧ D t ≤ 2 * autocorr F 0 := by
    have h := abs_le.mp (abs_autocorr_le_zero hcs hF.continuous t)
    dsimp only [D]
    constructor <;> linarith only [h.1, h.2]
  have hiR : IntegrableOn (fun t => retainedGammaRemainderWeight t * D t)
      (Ioc (0 : ℝ) r) :=
    (local_gamma_terms_integrable_to_two hF hcs).2.mono_set
      (fun t ht => ⟨ht.1, ht.2.trans hr2⟩)
  have hiP := refined_polynomial_lag_integrable hF hcs r
  change IntegrableOn (fun t => gammaHigherLagPolynomialNewton3 t * D t)
    (Ioc (0 : ℝ) r) at hiP
  let E := fun t => retainedGammaRemainderWeight t * D t -
    gammaHigherLagPolynomialNewton3 t * D t
  have hiE : IntegrableOn E (Ioc (0 : ℝ) r) := hiR.sub hiP
  have hp (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) r) :
      0 ≤ E t ∧ E t ≤ 6 * autocorr F 0 / 100000000000000000 := by
    have h := archLevySinhWeight_newton3_error ht.1 (ht.2.trans hr2)
    rw [← gamma_newton3_residual_identity ht.1.ne'] at h
    have hnon := mul_nonneg h.1 (hd t).1
    have hu := mul_le_mul_of_nonneg_right h.2 (hd t).1
    have hD := mul_le_mul_of_nonneg_left (hd t).2
      (by norm_num : (0 : ℝ) ≤ 3 / 100000000000000000)
    dsimp only [E]
    constructor <;> nlinarith only [hnon, hu, hD]
  have heq : (∫ t in Ioc (0 : ℝ) r, E t) =
      (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t * D t) -
        (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomialNewton3 t * D t) :=
    integral_sub hiR hiP
  have hn : 0 ≤ ∫ t in Ioc (0 : ℝ) r, E t :=
    setIntegral_nonneg measurableSet_Ioc (fun t ht => (hp t ht).1)
  have hu := setIntegral_mono_on hiE
    (f := E) (g := fun _ : ℝ => 6 * autocorr F 0 / 100000000000000000)
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    measurableSet_Ioc (fun t ht => (hp t ht).2)
  have hc : (∫ _t in Ioc (0 : ℝ) r, 6 * autocorr F 0 / 100000000000000000) =
      (6 * r / 100000000000000000) * ∫ x, F x ^ 2 := by
    rw [setIntegral_const, autocorr_zero_eq]
    simp only [Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hr.le, smul_eq_mul]
    ring
  rw [heq] at hn hu
  rw [hc] at hu
  exact ⟨hn, hu⟩

/-- A polynomial Gamma lower form valid for all diameters up to two. -/
def gammaPolynomialLowerNewton3 (r : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ t in Ioc (0 : ℝ) r, (autocorr F 0 - autocorr F t) / t) +
    (EF.gammaBracket 0 + r / 2 - r ^ 2 / 48 - r ^ 3 / 48 + 2 * archLevyAntideriv r) *
      (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
    (∫ t in Ioc (0 : ℝ) r, t * autocorr F t) / 24 +
    (∫ t in Ioc (0 : ℝ) r, t ^ 2 * autocorr F t) / 16 +
    (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomialNewton3 t *
      (autocorr F 0 - autocorr F t))

/-- The full Gamma energy and the refined polynomial form have a uniform mass error. -/
theorem gammaPolynomialLowerNewton3_error {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hr2 : r ≤ 2) (hs : tsupport F ⊆ Icc (-(r / 2)) (r / 2)) :
    gammaPolynomialLowerNewton3 r F ≤ EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F ∧
      EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F -
        gammaPolynomialLowerNewton3 r F ≤ (6 * r / 100000000000000000) * ∫ x, F x ^ 2 := by
  have he := gamma_eq_logarithmic_lag_correlation_moments_and_remainder_to_two hF hcs hr hr2 hs
  obtain ⟨hn, hu⟩ := local_gamma_remainder_sub_newton3 hF hcs hr hr2
  dsimp only [gammaPolynomialLowerNewton3]
  constructor <;> linarith only [he, hn, hu]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_sub_newton3
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gammaPolynomialLowerNewton3_error
