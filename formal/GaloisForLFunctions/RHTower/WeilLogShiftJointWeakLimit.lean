import GaloisForLFunctions.RHTower.WeilLogShiftDiagonalGaussian
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! Unconditional weak convergence of the canonical joint fluctuation law. -/

open MeasureTheory Filter
open scoped BigOperators Topology

noncomputable section
namespace RHTower

theorem tendsto_finiteWeilCanonicalJointProbabilityLaw_gaussian (t : ℕ → ℕ) :
    Tendsto (fun r => finiteWeilCanonicalJointProbabilityLaw r (2 * (r + 1) ^ 2 + t r))
      atTop (𝓝 finiteWeilDiagonalGaussian) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro v
  simp_rw [finiteWeilCanonicalJointProbabilityLaw_charFun, finiteWeilDiagonalGaussian_charFun]
  exact tendsto_finiteWeilCanonicalJointCharacteristic_gaussian t (v 0) (v 1)

theorem tendsto_finiteWeilCanonicalJointProbabilityLaw_observable (t : ℕ → ℕ)
    (f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin 2)) ℝ) :
    Tendsto (fun r => ∑ i, finiteWeilCanonicalEdgeMass r (2 * (r + 1) ^ 2 + t r) i *
      f (finiteWeilCanonicalFluctuationPoint r (2 * (r + 1) ^ 2 + t r) i))
      atTop (𝓝 (∫ x, f x ∂(finiteWeilDiagonalGaussian : Measure (EuclideanSpace ℝ (Fin 2))))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (tendsto_finiteWeilCanonicalJointProbabilityLaw_gaussian t) f
  simpa only [finiteWeilCanonicalJointProbabilityLaw,
    finiteWeilCanonicalObservableLaw_integral_real] using h

end RHTower
