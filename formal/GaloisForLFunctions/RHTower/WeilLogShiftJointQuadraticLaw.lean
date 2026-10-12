import GaloisForLFunctions.RHTower.WeilLogShiftJointQuadraticEnvelope
import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticExponentialLimit

/-! Exact common-quantile and diagonal Gaussian formulas for every joint quadratic exponential. -/

open MeasureTheory ProbabilityTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem finiteWeilCanonicalJoint_quadratic_exponential_integrable (r k : ℕ) (a b d : ℝ) :
    Integrable (fun z => Real.exp (finiteWeilJointQuadratic a b d z))
      (finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) :=
  finiteWeilCanonicalObservableLaw_integrable r k _ _

theorem finiteWeilCanonicalJointQuantile_quadratic_exponential_integrable
    (r k : ℕ) (a b d : ℝ) :
    Integrable (fun u => Real.exp (finiteWeilJointQuadratic a b d
      (finiteWeilCanonicalJointQuantile r k u))) (volume.restrict (Ioo (0 : ℝ) 1)) := by
  have h := integrable_map_measure (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := finiteWeilCanonicalJointQuantile r k)
    (g := fun z => Real.exp (finiteWeilJointQuadratic a b d z))
    (Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d)).aestronglyMeasurable
    (finiteWeilCanonicalJointQuantile_measurable r k).aemeasurable
  rw [finiteWeilCanonicalJointQuantile_law] at h
  exact h.mp (finiteWeilCanonicalJoint_quadratic_exponential_integrable r k a b d)

theorem finiteWeilCanonicalJointQuantile_quadratic_exponential_integral
    (r k : ℕ) (a b d : ℝ) :
    (∫ u, Real.exp (finiteWeilJointQuadratic a b d (finiteWeilCanonicalJointQuantile r k u))
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) =
      ∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
        ∂(finiteWeilCanonicalJointProbabilityLaw r k : Measure (EuclideanSpace ℝ (Fin 2))) := by
  have h := integral_map (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (finiteWeilCanonicalJointQuantile_measurable r k).aemeasurable
    (Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d)).aestronglyMeasurable
  rw [finiteWeilCanonicalJointQuantile_law] at h
  exact h.symm

theorem finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integrable_iff (a b d : ℝ) :
    Integrable (fun u => Real.exp (finiteWeilJointQuadratic a b d
      (finiteWeilDiagonalGaussianQuantile u))) (volume.restrict (Ioo (0 : ℝ) 1)) ↔
      a + 2 * b + d < 2 := by
  simp only [finiteWeilDiagonalGaussianQuantile, finiteWeilJointQuadratic_diagonal]
  have h := integrable_map_measure (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (f := quantile (finiteWeilProjectedGaussian 1 0 : Measure ℝ))
    (g := fun x : ℝ => Real.exp ((a + 2 * b + d) * x ^ 2)) (by fun_prop)
    (measurable_quantile _).aemeasurable
  rw [map_quantile_eq] at h
  exact h.symm.trans (finiteWeilProjectedIndexGaussian_integrable_quadratic_exponential_iff _)

theorem finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integral (a b d : ℝ) :
    (∫ u, Real.exp (finiteWeilJointQuadratic a b d (finiteWeilDiagonalGaussianQuantile u))
      ∂(volume.restrict (Ioo (0 : ℝ) 1))) = Real.sqrt (2 / (2 - (a + 2 * b + d))) := by
  simp only [finiteWeilDiagonalGaussianQuantile, finiteWeilJointQuadratic_diagonal,
    finiteWeil_integral_quadratic_exponential_quantile,
    finiteWeilProjectedIndexGaussian_quadratic_exponential_integral]

theorem finiteWeilDiagonalGaussian_quadratic_exponential_integrable_iff (a b d : ℝ) :
    Integrable (fun z => Real.exp (finiteWeilJointQuadratic a b d z))
      (finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))) ↔
      a + 2 * b + d < 2 := by
  rw [← finiteWeilDiagonalGaussianQuantile_law]
  exact (integrable_map_measure
    (Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d)).aestronglyMeasurable
    finiteWeilDiagonalGaussianQuantile_measurable.aemeasurable).trans
      (finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integrable_iff a b d)

theorem finiteWeilDiagonalGaussian_quadratic_exponential_integral (a b d : ℝ) :
    (∫ z, Real.exp (finiteWeilJointQuadratic a b d z)
      ∂(finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2)))) =
        Real.sqrt (2 / (2 - (a + 2 * b + d))) := by
  rw [← finiteWeilDiagonalGaussianQuantile_law, integral_map
    (f := fun z => Real.exp (finiteWeilJointQuadratic a b d z))
    finiteWeilDiagonalGaussianQuantile_measurable.aemeasurable
    (Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d)).aestronglyMeasurable]
  exact finiteWeilDiagonalGaussianQuantile_quadratic_exponential_integral a b d

theorem ae_tendsto_finiteWeilCanonicalJointQuantile_quadratic_exponential
    (t : ℕ → ℕ) (a b d : ℝ) :
    ∀ᵐ u ∂(volume.restrict (Ioo (0 : ℝ) 1)), Tendsto (fun r => Real.exp
      (finiteWeilJointQuadratic a b d (finiteWeilCanonicalJointQuantile r (2 * (r + 1) ^ 2 + t r) u)))
        atTop (𝓝 (Real.exp (finiteWeilJointQuadratic a b d (finiteWeilDiagonalGaussianQuantile u)))) :=
  (ae_tendsto_finiteWeilCanonicalJointQuantile_gaussian t).mono fun _ hu =>
    (Real.continuous_exp.comp (continuous_finiteWeilJointQuadratic a b d)).continuousAt.tendsto.comp hu

end RHTower
