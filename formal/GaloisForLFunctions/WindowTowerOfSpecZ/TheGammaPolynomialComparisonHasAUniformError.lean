import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaKernelHasAFourteenthOrderPolynomialLowerBound
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaComparisonRetainsItsChargesThroughRadiusTwo

/-!
# Gamma comparison with a controlled polynomial error

The higher correlation polynomial keeps the reciprocal hyperbolic terms
through degree fourteen. Its error in the Gamma energy is at most
`r/5000000` times the source mass for diameter `r≤11/10`.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology Zeta23
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open LatticeSectionTheory BiScaleUncertainty SpacingScaleHarmonicAnalysis

/-- Higher lag terms beyond the mean, linear and quadratic Gamma charges. -/
def gammaHigherLagPolynomial14 (t : ℝ) : ℝ :=
  7 * t ^ 3 / (360 * 2 ^ 4) + 5 * t ^ 4 / (24 * 2 ^ 5) -
    31 * t ^ 5 / (15120 * 2 ^ 6) - 61 * t ^ 6 / (720 * 2 ^ 7) +
    127 * t ^ 7 / (604800 * 2 ^ 8) + 1385 * t ^ 8 / (40320 * 2 ^ 9) -
    73 * t ^ 9 / (3421440 * 2 ^ 10) - 50521 * t ^ 10 / (3628800 * 2 ^ 11) +
    1414477 * t ^ 11 / (653837184000 * 2 ^ 12) +
    2702765 * t ^ 12 / (479001600 * 2 ^ 13) -
    8191 * t ^ 13 / (37362124800 * 2 ^ 14) -
    199360981 * t ^ 14 / (87178291200 * 2 ^ 15)

private theorem gamma_polynomial_residual_identity {t : ℝ} (ht : t ≠ 0) :
    retainedGammaRemainderWeight t - gammaHigherLagPolynomial14 t =
      archLevySinhWeight t -
        (gammaSinhPolynomial14 (t / 2) / t + gammaCoshPolynomial14 (t / 2) / 2) := by
  dsimp only [retainedGammaRemainderWeight, gammaHigherLagPolynomial14,
    gammaSinhPolynomial14, gammaCoshPolynomial14]
  field_simp [ht]
  ring

private theorem polynomial_lag_integrable {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) (r : ℝ) :
    IntegrableOn (fun t => gammaHigherLagPolynomial14 t *
      (autocorr F 0 - autocorr F t)) (Ioc (0 : ℝ) r) := by
  have hp : Continuous gammaHigherLagPolynomial14 := by
    unfold gammaHigherLagPolynomial14
    fun_prop
  exact (hp.mul (continuous_const.sub
    (_root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs))).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self

/-- Integrating the pointwise kernel error costs only a fixed multiple of the source mass. -/
theorem local_gamma_remainder_sub_polynomial14 {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 11 / 10) :
    0 ≤ (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t)) -
      (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomial14 t *
        (autocorr F 0 - autocorr F t)) ∧
    (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t)) -
      (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomial14 t *
        (autocorr F 0 - autocorr F t)) ≤
      (r / 5000000) * ∫ x, F x ^ 2 := by
  let D := fun t => autocorr F 0 - autocorr F t
  have hd (t : ℝ) : 0 ≤ D t ∧ D t ≤ 2 * autocorr F 0 := by
    have h := abs_le.mp (abs_autocorr_le_zero hcs hF.continuous t)
    dsimp only [D]
    constructor <;> linarith only [h.1, h.2]
  have hiR : IntegrableOn (fun t => retainedGammaRemainderWeight t * D t)
      (Ioc (0 : ℝ) r) :=
    (local_gamma_terms_integrable_to_two hF hcs).2.mono_set
      (fun t ht => ⟨ht.1, by linarith only [ht.2, hr1]⟩)
  have hiP := polynomial_lag_integrable hF hcs r
  change IntegrableOn (fun t => gammaHigherLagPolynomial14 t * D t)
    (Ioc (0 : ℝ) r) at hiP
  let E := fun t => retainedGammaRemainderWeight t * D t -
    gammaHigherLagPolynomial14 t * D t
  have hiE : IntegrableOn E (Ioc (0 : ℝ) r) := hiR.sub hiP
  have hp (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) r) :
      0 ≤ E t ∧ E t ≤ autocorr F 0 / 5000000 := by
    have h := archLevySinhWeight_polynomial14_error ht.1 (ht.2.trans hr1)
    rw [← gamma_polynomial_residual_identity ht.1.ne'] at h
    have hnon := mul_nonneg h.1 (hd t).1
    have hu := mul_le_mul_of_nonneg_right h.2 (hd t).1
    have hD := mul_le_mul_of_nonneg_left (hd t).2 (by norm_num : (0 : ℝ) ≤ 1 / 10000000)
    dsimp only [E]
    constructor <;> nlinarith only [hnon, hu, hD]
  have heq : (∫ t in Ioc (0 : ℝ) r, E t) =
      (∫ t in Ioc (0 : ℝ) r, retainedGammaRemainderWeight t * D t) -
        (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomial14 t * D t) :=
    integral_sub hiR hiP
  have hn : 0 ≤ ∫ t in Ioc (0 : ℝ) r, E t :=
    setIntegral_nonneg measurableSet_Ioc (fun t ht => (hp t ht).1)
  have hu := setIntegral_mono_on hiE
    (f := E) (g := fun _ : ℝ => autocorr F 0 / 5000000)
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    measurableSet_Ioc (fun t ht => (hp t ht).2)
  have hc : (∫ _t in Ioc (0 : ℝ) r, autocorr F 0 / 5000000) =
      (r / 5000000) * ∫ x, F x ^ 2 := by
    rw [setIntegral_const, autocorr_zero_eq]
    simp only [Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hr.le, smul_eq_mul]
    ring
  rw [heq] at hn hu
  rw [hc] at hu
  exact ⟨hn, hu⟩

/-- The retained finite Gamma form includes all correlation charges through degree fourteen. -/
def gammaPolynomialLower14 (r : ℝ) (F : ℝ → ℝ) : ℝ :=
  (∫ t in Ioc (0 : ℝ) r, (autocorr F 0 - autocorr F t) / t) +
    (EF.gammaBracket 0 + r / 2 - r ^ 2 / 48 - r ^ 3 / 48 + 2 * archLevyAntideriv r) *
      (∫ x, F x ^ 2) - (∫ x, F x) ^ 2 / 4 +
    (∫ t in Ioc (0 : ℝ) r, t * autocorr F t) / 24 +
    (∫ t in Ioc (0 : ℝ) r, t ^ 2 * autocorr F t) / 16 +
    (∫ t in Ioc (0 : ℝ) r, gammaHigherLagPolynomial14 t *
      (autocorr F 0 - autocorr F t))

/-- The Gamma energy and its finite correlation form differ by at most `r/5000000` times mass. -/
theorem gammaPolynomialLower14_error {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {r : ℝ} (hr : 0 < r)
    (hr1 : r ≤ 11 / 10) (hs : tsupport F ⊆ Icc (-(r / 2)) (r / 2)) :
    gammaPolynomialLower14 r F ≤ EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F ∧
      EF.gammaBracket 0 * (∫ x, F x ^ 2) + biScaleLevyEnergy F -
        gammaPolynomialLower14 r F ≤ (r / 5000000) * ∫ x, F x ^ 2 := by
  have he := gamma_eq_logarithmic_lag_correlation_moments_and_remainder_to_two
    hF hcs hr (by linarith only [hr1]) hs
  obtain ⟨hn, hu⟩ := local_gamma_remainder_sub_polynomial14 hF hcs hr hr1
  dsimp only [gammaPolynomialLower14]
  constructor <;> linarith only [he, hn, hu]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_sub_polynomial14
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.gammaPolynomialLower14_error
