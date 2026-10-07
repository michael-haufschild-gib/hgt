import GaloisForLFunctions.HTGeometry.SteinitzInverseCovariance
import GaloisForLFunctions.HilbertMetric.CrouzeixEvaluationEnergy

/-!
# Inverse stability of prescribed evaluation kernels

The inverse-branch remainder from the Steinitz application controls regularized
sample-kernel inversion. Its vanishing criterion agrees exactly with saturation
of the Crouzeix coupling inequality on the same evaluation packets.
-/

open Matrix
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

open HTGeometry

variable {d : ℕ} {X Y : Type*}

/-- The inverse remainder vanishes exactly when all prescribed sample-kernel entries agree. -/
theorem complexEvaluation_inverse_remainder_saturation
    (u : Fin d → X → ℂ) (p : Fin d → X) (v : Fin d → Y → ℂ) (q : Fin d → Y) :
    (synthesisInverseRemainder (complexEvaluationMatrix u p)
      (complexEvaluationMatrix v q)).trace.re = 0 ↔
      ∀ i j, (∑ k, u k (p i) * star (u k (p j))) = ∑ k, v k (q i) * star (v k (q j)) := by
  rw [synthesisInverseRemainder_trace_eq_zero_iff]
  constructor
  · intro h i j
    simpa only [complexEvaluationMatrix_mul_conjTranspose] using
      congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j) h
  · intro h
    ext i j
    simpa only [complexEvaluationMatrix_mul_conjTranspose] using h i j

/-- Regularized inverse reconstruction is controlled by an exact positive matrix remainder. -/
theorem complexEvaluation_inverse_remainder_distance_bound
    (u : Fin d → X → ℂ) (p : Fin d → X) (v : Fin d → Y → ℂ) (q : Fin d → Y) :
    finiteMatrixHilbertSchmidtSq
      (synthesisResolvent (complexEvaluationMatrix u p) -
        synthesisResolvent (complexEvaluationMatrix v q)) ≤
      (synthesisInverseRemainder (complexEvaluationMatrix u p)
        (complexEvaluationMatrix v q)).trace.re :=
  synthesisResolvent_distance_bound _ _

/-- Direct Gram coupling and inverse reconstruction detect exactly the same kernel agreement. -/
theorem complexEvaluation_crouzeix_iff_inverse_remainder_zero
    (u : Fin d → X → ℂ) (p : Fin d → X) (v : Fin d → Y → ℂ) (q : Fin d → Y) :
    (2 * finiteMatrixHilbertSchmidtSq
        ((complexEvaluationMatrix u p)ᴴ * complexEvaluationMatrix v q) =
      finiteMatrixHilbertSchmidtSq (complexEvaluationGram u p) +
        finiteMatrixHilbertSchmidtSq (complexEvaluationGram v q)) ↔
    (synthesisInverseRemainder (complexEvaluationMatrix u p)
      (complexEvaluationMatrix v q)).trace.re = 0 := by
  rw [complexEvaluation_energy_saturation, complexEvaluation_inverse_remainder_saturation]

end

end GaloisForLFunctions.HilbertMetric
