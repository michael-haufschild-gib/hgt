import GaloisForLFunctions.RHTower.WeilPaperMixtureKernelEnergy
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity

/-!
# Pole-compensated energy controls the actual spectral logarithmic moment

Full energy is the sum of its signed pole term and its gamma term. The gamma
term is exactly an expectation under the native spectral probability. Its
logarithmic lower bound gives an unconditional coercive estimate with the pole
contribution retained explicitly.
-/

open MeasureTheory Filter Set Topology Zeta23
open scoped BigOperators
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The signed contribution of both poles, extended linearly to finite mixtures. -/
def paperMixturePole : (WeilTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun f => testPole f.1)

/-- The gamma contribution, extended linearly to finite mixtures. -/
def paperMixtureGamma : (WeilTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun f => testGamma f.1)

/-- The actual full energy retains exactly both the pole and gamma terms. -/
theorem energy_eq_paperMixturePole_add_gamma (c : WeilTestFn →₀ ℝ) :
    energy c = paperMixturePole c + paperMixtureGamma c := by
  simp only [energy, paperMixturePole, paperMixtureGamma, Finsupp.linearCombination_apply,
    Finsupp.sum, smul_eq_mul, weilArchRe_eq_testPole_add_testGamma, mul_add,
    Finset.sum_add_distrib]

/-- Gamma symbol in the exact frequency convention of the native probability. -/
def paperSpectralGammaWeight (ξ : ℝ) : ℝ := EF.gammaBracket (-(2 * Real.pi) * ξ)

/-- Coercive logarithmic weight in that same frequency convention. -/
def paperSpectralLogWeight (ξ : ℝ) : ℝ := Real.log (2 + |-(2 * Real.pi) * ξ|)

theorem paperSpectralLogWeight_nonneg (ξ : ℝ) : 0 ≤ paperSpectralLogWeight ξ :=
  Real.log_nonneg (by linarith [abs_nonneg (-(2 * Real.pi) * ξ)])

theorem continuous_paperSpectralLogWeight : Continuous paperSpectralLogWeight := by
  apply Continuous.log (continuous_const.add ((continuous_const.mul continuous_id).abs))
  intro ξ
  apply ne_of_gt
  change 0 < 2 + |-(2 * Real.pi) * ξ|
  linarith [abs_nonneg (-(2 * Real.pi) * ξ)]

/-- The logarithmic weight is bounded by the gamma symbol plus an explicit constant. -/
theorem paperSpectralLogWeight_le_gamma (ξ : ℝ) :
    paperSpectralLogWeight ξ ≤ paperSpectralGammaWeight ξ + (10 + Real.log 4) := by
  have h := joint_gamma_lower_log (-(2 * Real.pi) * ξ)
  change Real.log (2 + |-(2 * Real.pi) * ξ|) ≤
    EF.gammaBracket (-(2 * Real.pi) * ξ) + (10 + Real.log 4)
  linarith

/-- Real expectations, including unbounded integrable observables, use the literal density. -/
theorem integral_spectralProbability_real (c : NormalizedMixture) (F : ℝ → ℝ) :
    (∫ ξ, F ξ ∂(spectralProbability c : Measure ℝ)) =
      ∫ ξ, mixtureSpectralDensity c.1 ξ * F ξ := by
  change (∫ ξ, F ξ ∂volume.withDensity
    (fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuous_mixtureSpectralDensity c.1).measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    rw [ENNReal.toReal_ofReal (mixtureSpectralDensity_nonneg c.1 c.2.1 ξ), smul_eq_mul]

/-- Integrability against the native law is exactly density-weighted integrability. -/
theorem integrable_spectralProbability_real_iff (c : NormalizedMixture) (F : ℝ → ℝ) :
    Integrable F (spectralProbability c : Measure ℝ) ↔
      Integrable (fun ξ => mixtureSpectralDensity c.1 ξ * F ξ) := by
  have hweight (ξ : ℝ) : (ENNReal.ofReal (mixtureSpectralDensity c.1 ξ)).toReal =
      mixtureSpectralDensity c.1 ξ :=
    ENNReal.toReal_ofReal (mixtureSpectralDensity_nonneg c.1 c.2.1 ξ)
  change Integrable F (volume.withDensity
    (fun ξ => ENNReal.ofReal (mixtureSpectralDensity c.1 ξ))) ↔ _
  simpa only [hweight, mul_comm] using
    (integrable_withDensity_iff
      (continuous_mixtureSpectralDensity c.1).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) (g := F))

private theorem testSpectralDensity_rescale (f : WeilTestFn) (ξ : ℝ) :
    testSpectralDensity f ξ = ‖paperFT f.1 ((-(2 * Real.pi) * ξ : ℝ) : ℂ)‖ ^ 2 := by
  unfold testSpectralDensity
  have h : -(2 * Real.pi * (ξ : ℂ)) = ((-(2 * Real.pi) * ξ : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h]

private theorem integrable_test_gamma (f : WeilTestFn) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1 (ξ : ℂ)‖ ^ 2 * EF.gammaBracket ξ) := by
  have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    f.2.1 f.2.2 f.2.1 f.2.2
  refine h.re.congr (Filter.Eventually.of_forall fun ξ => ?_)
  change (paperFT (EF.weilTest f.1 f.1) (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal f.2.1.continuous f.2.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem integrable_testSpectralDensity_mul_gammaWeight (f : WeilTestFn) :
    Integrable (fun ξ => testSpectralDensity f ξ * paperSpectralGammaWeight ξ) := by
  simpa only [testSpectralDensity_rescale, paperSpectralGammaWeight] using
    (integrable_test_gamma f).comp_mul_left'
      (neg_ne_zero.mpr (mul_ne_zero two_ne_zero Real.pi_ne_zero))

/-- The Fourier change of variables retains the exact gamma normalization. -/
theorem integral_testSpectralDensity_mul_gammaWeight (f : WeilTestFn) :
    (∫ ξ, testSpectralDensity f ξ * paperSpectralGammaWeight ξ) = testGamma f.1 := by
  calc
    _ = ∫ ξ : ℝ, (fun t : ℝ => ‖paperFT f.1 (t : ℂ)‖ ^ 2 * EF.gammaBracket t)
        (-(2 * Real.pi) * ξ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        dsimp only
        rw [testSpectralDensity_rescale]
        rfl
    _ = |(-(2 * Real.pi))⁻¹| •
        ∫ t : ℝ, ‖paperFT f.1 (t : ℂ)‖ ^ 2 * EF.gammaBracket t :=
      Measure.integral_comp_mul_left
        (fun t : ℝ => ‖paperFT f.1 (t : ℂ)‖ ^ 2 * EF.gammaBracket t) (-(2 * Real.pi))
    _ = testGamma f.1 := by
      simp [testGamma, abs_mul, abs_of_pos Real.pi_pos, smul_eq_mul, one_div]

private theorem integrable_mixture_weight (c : WeilTestFn →₀ ℝ) (F : ℝ → ℝ)
    (hF : ∀ f, Integrable (fun ξ => testSpectralDensity f ξ * F ξ)) :
    Integrable (fun ξ => mixtureSpectralDensity c ξ * F ξ) := by
  have heq : (fun ξ => mixtureSpectralDensity c ξ * F ξ) =
      fun ξ => ∑ f ∈ c.support, c f * (testSpectralDensity f ξ * F ξ) := by
    funext ξ
    simp [mixtureSpectralDensity, Finsupp.sum, Finset.sum_mul, mul_assoc]
  rw [heq]
  exact integrable_finsetSum _ fun f _ => (hF f).const_mul _

theorem integrable_mixtureSpectralDensity_mul_gammaWeight (c : WeilTestFn →₀ ℝ) :
    Integrable (fun ξ => mixtureSpectralDensity c ξ * paperSpectralGammaWeight ξ) :=
  integrable_mixture_weight c _ integrable_testSpectralDensity_mul_gammaWeight

/-- The finite gamma functional is exactly the spectral-density expectation. -/
theorem paperMixtureGamma_eq_integral (c : WeilTestFn →₀ ℝ) :
    paperMixtureGamma c = ∫ ξ, mixtureSpectralDensity c ξ * paperSpectralGammaWeight ξ := by
  classical
  simp only [paperMixtureGamma, Finsupp.linearCombination_apply, Finsupp.sum, smul_eq_mul]
  calc
    _ = ∑ f ∈ c.support, ∫ ξ, c f * (testSpectralDensity f ξ * paperSpectralGammaWeight ξ) := by
      simp_rw [integral_const_mul, integral_testSpectralDensity_mul_gammaWeight]
    _ = ∫ ξ, ∑ f ∈ c.support, c f * (testSpectralDensity f ξ * paperSpectralGammaWeight ξ) :=
      (integral_finsetSum _ fun f _ => (integrable_testSpectralDensity_mul_gammaWeight f).const_mul _).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ξ => by
        simp [mixtureSpectralDensity, Finsupp.sum, Finset.sum_mul, mul_assoc]

theorem integrable_paperSpectralGammaWeight (c : NormalizedMixture) :
    Integrable paperSpectralGammaWeight (spectralProbability c : Measure ℝ) :=
  (integrable_spectralProbability_real_iff c _).mpr
    (integrable_mixtureSpectralDensity_mul_gammaWeight c.1)

/-- The gamma term is intrinsic to the actual probability law. -/
theorem integral_paperSpectralGammaWeight (c : NormalizedMixture) :
    (∫ ξ, paperSpectralGammaWeight ξ ∂(spectralProbability c : Measure ℝ)) =
      paperMixtureGamma c.1 := by
  rw [integral_spectralProbability_real, paperMixtureGamma_eq_integral]

/-- Every native spectral logarithmic moment is finite; this is proved, not assumed. -/
theorem integrable_paperSpectralLogWeight (c : NormalizedMixture) :
    Integrable paperSpectralLogWeight (spectralProbability c : Measure ℝ) := by
  apply ((integrable_paperSpectralGammaWeight c).add (integrable_const (10 + Real.log 4))).mono'
    continuous_paperSpectralLogWeight.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (paperSpectralLogWeight_nonneg ξ)]
    exact paperSpectralLogWeight_le_gamma ξ

/-- The actual logarithmic moment of a normalized native spectral law. -/
def paperSpectralLogMoment (c : NormalizedMixture) : ℝ :=
  ∫ ξ, paperSpectralLogWeight ξ ∂(spectralProbability c : Measure ℝ)

theorem paperSpectralLogMoment_nonneg (c : NormalizedMixture) : 0 ≤ paperSpectralLogMoment c :=
  integral_nonneg paperSpectralLogWeight_nonneg

/-- Full energy controls the spectral logarithmic moment after retaining the signed pole term. -/
theorem paperSpectralLogMoment_le_pole_compensated_energy (c : NormalizedMixture) :
    paperSpectralLogMoment c ≤ energy c.1 - paperMixturePole c.1 + (10 + Real.log 4) := by
  have h := integral_mono_ae (integrable_paperSpectralLogWeight c)
    ((integrable_paperSpectralGammaWeight c).add (integrable_const (10 + Real.log 4)))
    (Filter.Eventually.of_forall paperSpectralLogWeight_le_gamma)
  change (∫ ξ, paperSpectralLogWeight ξ ∂(spectralProbability c : Measure ℝ)) ≤
    ∫ ξ, paperSpectralGammaWeight ξ + (10 + Real.log 4) ∂(spectralProbability c : Measure ℝ) at h
  rw [integral_add (integrable_paperSpectralGammaWeight c) (integrable_const _),
    integral_paperSpectralGammaWeight, integral_const, probReal_univ, one_smul] at h
  rw [energy_eq_paperMixturePole_add_gamma]
  simpa only [paperSpectralLogMoment, add_sub_cancel_left] using h

end RHTower.WeilWorkPBAP
