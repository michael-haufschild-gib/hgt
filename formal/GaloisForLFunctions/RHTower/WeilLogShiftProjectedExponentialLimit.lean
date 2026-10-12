import GaloisForLFunctions.RHTower.WeilLogShiftProjectedMomentLimit
import GaloisForLFunctions.HTGeometry.WeakContinuousMomentTransfer

/-! Every real exponential moment of the actual projected index law converges
to its Gaussian value along every quadratic-index sequence. -/

open MeasureTheory ProbabilityTheory Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilProjectedGaussian_integrable_exponential (a b θ : ℝ) :
    Integrable (fun x : ℝ => Real.exp (θ * x)) (finiteWeilProjectedGaussian a b : Measure ℝ) := by
  simpa [finiteWeilProjectedGaussian] using
    (integrable_exp_mul_gaussianReal (μ := 0)
      (v := NNReal.mk ((a + b) ^ 2 / 4) (by positivity)) θ)

theorem finiteWeilProjectedGaussian_exponential_integral (a b θ : ℝ) :
    (∫ x : ℝ, Real.exp (θ * x) ∂(finiteWeilProjectedGaussian a b : Measure ℝ)) =
      Real.exp ((a + b) ^ 2 * θ ^ 2 / 8) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0)
    (v := NNReal.mk ((a + b) ^ 2 / 4) (by positivity))) θ
  change (∫ x : ℝ, Real.exp (θ * x) ∂(gaussianReal 0 _)) = _ at h
  change (∫ x : ℝ, Real.exp (θ * x) ∂(gaussianReal 0 _)) = _
  rw [h]
  congr 1
  change 0 * θ + ((a + b) ^ 2 / 4) * θ ^ 2 / 2 = _
  ring

theorem tendsto_finiteWeilCanonicalProjectedIndex_exponential (t : ℕ → ℕ) (θ : ℝ) :
    Tendsto (fun r => ∫ x : ℝ, Real.exp (θ * x)
      ∂(finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ))
      atTop (𝓝 (Real.exp (θ ^ 2 / 8))) := by
  have hsq (x : ℝ) : Real.exp (θ * x) ^ 2 = Real.exp ((2 * θ) * x) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hg : Integrable (fun x : ℝ => Real.exp (θ * x) ^ 2)
      (finiteWeilProjectedGaussian 1 0 : Measure ℝ) := by
    simpa only [hsq] using finiteWeilProjectedGaussian_integrable_exponential 1 0 (2 * θ)
  have h := tendsto_integral_continuous_of_uniform_square_bound
    (tendsto_finiteWeilCanonicalProjectedProbabilityLaw_gaussian t 1 0)
    (f := fun x : ℝ => Real.exp (θ * x)) (by fun_prop)
    (fun r => finiteWeilCanonicalProjectedProbabilityLaw_integrable _ _ _ _ _) hg
    (C := 4 * Real.exp (|2 * θ| + (2 * θ) ^ 2 / 8))
    (Eventually.of_forall fun r => by
      simpa only [hsq] using finiteWeilCanonicalProjectedIndex_exponential_bound r (t r) (2 * θ))
  rw [finiteWeilProjectedGaussian_exponential_integral] at h
  simpa only [add_zero, one_pow, one_mul] using h

end RHTower
