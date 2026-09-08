import GaloisForLFunctions.HTGeometry.GaussianDisplacedSpectralPole
import GaloisForLFunctions.HTGeometry.GoldenRuleSelfEnergy

/-!
# Gaussian spectral broadening and both golden-rule limits

The Gaussian spectral law in equation (20) of arXiv:2608.26494 is applied
to the corpus energy-domain self-energy and time-domain transition kernel.
Their common limit is strictly positive at every real test energy.
All integrability, continuity, and positivity conditions are discharged.
-/

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry


/-- A strictly positive Gaussian spectral variance, parametrizing every positive variance. -/
def positiveGaussianSpectralVariance (a : ℝ) : ℝ≥0 := ⟨Real.exp a, (Real.exp_pos a).le⟩

theorem positiveGaussianSpectralVariance_ne_zero (a : ℝ) :
    positiveGaussianSpectralVariance a ≠ 0 := by
  intro h
  have he := congrArg (fun v : ℝ≥0 => (v : ℝ)) h
  exact (Real.exp_ne_zero a) he

/-- Density of the exact linear-displacement spectral measure in equation (20). -/
def displacedGaussianSpectralDensity (e a : ℝ) : ℝ → ℝ :=
  gaussianPDFReal e (positiveGaussianSpectralVariance a)

theorem integrable_displacedGaussianSpectralDensity (e a : ℝ) :
    Integrable (displacedGaussianSpectralDensity e a) :=
  integrable_gaussianPDFReal _ _

theorem continuous_displacedGaussianSpectralDensity (e a : ℝ) :
    Continuous (displacedGaussianSpectralDensity e a) := by
  unfold displacedGaussianSpectralDensity
  rw [gaussianPDFReal_def]
  fun_prop

theorem displacedGaussianSpectralDensity_pos (e a x : ℝ) :
    0 < displacedGaussianSpectralDensity e a x :=
  gaussianPDFReal_pos _ _ _ (positiveGaussianSpectralVariance_ne_zero a)

theorem integral_displacedGaussianSpectralDensity (e a : ℝ) :
    (∫ x, displacedGaussianSpectralDensity e a x) = 1 :=
  integral_gaussianPDFReal_eq_one _ (positiveGaussianSpectralVariance_ne_zero a)

/-- The broadened spectral law is exactly the Gaussian-displacement pushforward already constructed. -/
theorem displacedGaussianSpectralMeasure_eq_poleLaw (e a : ℝ) :
    gaussianPoleSpectralMeasure (positiveGaussianSpectralVariance a) e 1 0 =
      gaussianReal e (positiveGaussianSpectralVariance a) := by
  have hf : gaussianPolePosition e 1 0 = fun x : ℝ => e + x := by
    funext x
    simp [gaussianPolePosition]
  rw [gaussianPoleSpectralMeasure, hf, gaussianReal_map_const_add]
  simp

/-- On-shell rate for a Gaussian-broadened spectral density. -/
def displacedGaussianGoldenRuleRate (e a x : ℝ) : ℝ :=
  2 * Real.pi * displacedGaussianSpectralDensity e a x

theorem displacedGaussianGoldenRuleRate_pos (e a x : ℝ) :
    0 < displacedGaussianGoldenRuleRate e a x := by
  unfold displacedGaussianGoldenRuleRate
  exact mul_pos (mul_pos (by positivity) Real.pi_pos) (displacedGaussianSpectralDensity_pos e a x)

/-- The corpus's energy-domain golden-rule theorem now gives a strictly positive broadening
rate at every real test energy, with no analytic hypotheses left open. -/
theorem tendsto_displacedGaussian_selfEnergy_rate (e a x : ℝ) :
    Tendsto (fun eta : ℝ => -2 * (levelSelfEnergy (displacedGaussianSpectralDensity e a) x eta).im)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (𝓝 (displacedGaussianGoldenRuleRate e a x)) :=
  tendsto_levelSelfEnergy_rate (integrable_displacedGaussianSpectralDensity e a)
    (continuous_displacedGaussianSpectralDensity e a).continuousAt

/-- The same positive rate is the long-time slope of the exact golden-rule transition kernel. -/
theorem tendsto_displacedGaussian_transition_rate (e a x : ℝ) :
    Tendsto (fun t : ℝ =>
      (∫ E : ℝ, goldenRuleKernel t (E - x) * displacedGaussianSpectralDensity e a E) / t)
      atTop (𝓝 (displacedGaussianGoldenRuleRate e a x)) :=
  (goldenRule_rate_agreement (E₀ := x) (integrable_displacedGaussianSpectralDensity e a)
    (continuous_displacedGaussianSpectralDensity e a).continuousAt).1

end GaloisForLFunctions.HTGeometry
