import GaloisForLFunctions.RHTower.WeilLogShiftProjectedMomentLimit
import GaloisForLFunctions.RHTower.WeilLogShiftJointQuantileLimit

/-! Exact moment transfer to the common uniform quantile probability space. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeil_quantile_pow_integrable (μ : ProbabilityMeasure ℝ) (p : ℕ)
    (hi : Integrable (fun x : ℝ => x ^ p) (μ : Measure ℝ)) :
    Integrable (fun u : ℝ => (quantile (μ : Measure ℝ) u) ^ p)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have hi' : Integrable (fun x : ℝ => x ^ p)
      (Measure.map (quantile (μ : Measure ℝ)) (volume.restrict (Ioo (0 : ℝ) 1))) := by
    simpa only [map_quantile_eq] using hi
  exact (integrable_map_measure (continuous_pow p).aestronglyMeasurable
    (measurable_quantile (μ : Measure ℝ)).aemeasurable).mp hi'

theorem finiteWeil_integral_quantile_pow (μ : ProbabilityMeasure ℝ) (p : ℕ) :
    (∫ u : ℝ, (quantile (μ : Measure ℝ) u) ^ p ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ x : ℝ, x ^ p ∂(μ : Measure ℝ) := by
  have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (measurable_quantile (μ : Measure ℝ)).aemeasurable
    (f := fun x : ℝ => x ^ p) (continuous_pow p).aestronglyMeasurable
  rw [map_quantile_eq] at h
  exact h.symm

theorem finiteWeilCanonicalProjectedIndex_quantile_pow_integrable (r k p : ℕ) :
    Integrable (fun u : ℝ =>
      (quantile (finiteWeilCanonicalProjectedProbabilityLaw r k 1 0 : Measure ℝ) u) ^ p)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  finiteWeil_quantile_pow_integrable _ p
    (finiteWeilCanonicalProjectedProbabilityLaw_integrable r k 1 0 _)

theorem finiteWeilProjectedGaussian_quantile_pow_integrable (a b : ℝ) (p : ℕ) :
    Integrable (fun u : ℝ => (quantile (finiteWeilProjectedGaussian a b : Measure ℝ) u) ^ p)
      (volume.restrict (Ioo (0 : ℝ) 1)) :=
  finiteWeil_quantile_pow_integrable _ p (finiteWeilProjectedGaussian_integrable_pow a b p)

theorem tendsto_finiteWeilCanonicalProjectedIndex_quantile_moment (t : ℕ → ℕ) (p : ℕ) :
    Tendsto (fun r => ∫ u : ℝ, (quantile
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u) ^ p
        ∂(volume.restrict (Ioo (0 : ℝ) 1))) atTop
      (𝓝 (∫ u : ℝ, (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u) ^ p
        ∂(volume.restrict (Ioo (0 : ℝ) 1)))) := by
  simp only [finiteWeil_integral_quantile_pow]
  exact tendsto_finiteWeilCanonicalProjectedIndex_moment t p

theorem ae_tendsto_finiteWeilCanonicalProjectedIndex_quantile (t : ℕ → ℕ) :
    ∀ᵐ u : ℝ ∂(volume.restrict (Ioo (0 : ℝ) 1)), Tendsto (fun r => quantile
      (finiteWeilCanonicalProjectedProbabilityLaw r (2 * (r + 1) ^ 2 + t r) 1 0 : Measure ℝ) u)
      atTop (𝓝 (quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ) u)) := by
  refine (ae_restrict_iff' measurableSet_Ioo).mpr ?_
  exact Eventually.of_forall fun u hu => tendsto_finiteWeilCanonicalProjectedIndex_quantile t ⟨u, hu⟩

end RHTower
