import GaloisForLFunctions.HTGeometry.NevLeafFunction

/-!
# Integrals against a leaf are fiber sums

A weighted Dirac family integrates any integrable function to the weighted sum of its values, so an
integral against a leaf is a sum over the denominator fiber with the Christoffel weights.  This is the
form the Cauchy-transform analysis of the moment fiber consumes.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **Integration against a weighted Dirac family is the weighted sum of values.** -/
theorem integral_fiberMeasure (w : ℝ → ℝ) (F : Set ℝ) (f : ℝ → ℝ)
    (hf : Integrable f (fiberMeasure w F)) :
    ∫ x, f x ∂(fiberMeasure w F)
      = ∑' p : ↥F, (ENNReal.ofReal (w (p : ℝ))).toReal * f (p : ℝ) := by
  have hf' : Integrable f (Measure.sum fun p : ↥F =>
      ENNReal.ofReal (w (p : ℝ)) • Measure.dirac (p : ℝ)) := hf
  have hsum : ∫ x, f x ∂(fiberMeasure w F)
      = ∑' p : ↥F, ∫ x, f x ∂(ENNReal.ofReal (w (p : ℝ)) • Measure.dirac (p : ℝ)) := by
    rw [fiberMeasure]
    exact integral_sum_measure hf'
  rw [hsum]
  refine tsum_congr fun p => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]

/-- **An integral against a leaf is a Christoffel-weighted sum over its fiber.** -/
theorem integral_nevLeaf (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (tau : ℝ) (f : ℝ → ℝ)
    (hf : Integrable f (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)) :
    ∫ x, f x ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = ∑' p : ↥((nevMatrixDataInf h h0b).finiteDenominatorFiber tau),
          christoffelLimit s (p : ℝ) * f (p : ℝ) := by
  have hrw := nevLeaf_eq_fiberMeasure h h0b h0 tau
  have hf' : Integrable f
      (fiberMeasure (fun x => christoffelLimit s x)
        ((nevMatrixDataInf h h0b).finiteDenominatorFiber tau)) := by
    rwa [hrw] at hf
  rw [hrw, integral_fiberMeasure _ _ f hf']
  refine tsum_congr fun p => ?_
  rw [ENNReal.toReal_ofReal (christoffelLimit_nonneg h _)]

/-- Every bounded continuous function is integrable against a leaf, so its integral is the
Christoffel-weighted sum of its values on the fiber. -/
theorem integral_nevLeaf_of_boundedContinuous (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (tau : ℝ) (f : BoundedContinuousFunction ℝ ℝ) :
    ∫ x, f x ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = ∑' p : ↥((nevMatrixDataInf h h0b).finiteDenominatorFiber tau),
          christoffelLimit s (p : ℝ) * f (p : ℝ) := by
  haveI : IsProbabilityMeasure (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) := inferInstance
  exact integral_nevLeaf h h0b h0 tau f
    (BoundedContinuousFunction.integrable
      (nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ) f)

end HTGeometry
