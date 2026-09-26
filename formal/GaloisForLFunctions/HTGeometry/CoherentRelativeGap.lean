import GaloisForLFunctions.HTGeometry.RelativeGapCurvature
import GaloisForLFunctions.HilbertMetric.GaussianCoherentFisherClock

/-!
# Relative-gap curvature in the Gaussian coherent-state model

Along any affine label trajectory, logarithmic mass curvature is exactly half
the squared sampling interval times quantum Fisher information. Fidelity to a
fixed anchor has the opposite curvature. The same state family therefore gives
opposite relative-gap directions for its mass and its normalized overlap.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HilbertMetric

/-- Three samples of a squared affine norm have constant discrete curvature. -/
theorem affineSquareNorm_logStepCurvature {d : ℕ}
    (x v : Fin d → ℝ) (t h : ℝ) :
    logStepCurvature (∑ i, (x i + t * v i) ^ (2 : ℕ))
      (∑ i, (x i + (t + h) * v i) ^ (2 : ℕ))
      (∑ i, (x i + (t + 2 * h) * v i) ^ (2 : ℕ)) =
        2 * h ^ (2 : ℕ) * ∑ i, v i ^ (2 : ℕ) := by
  unfold logStepCurvature
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The discrete signal amplitude is the existing coherent quantum Fisher metric. -/
theorem coherentClockMass_logStepCurvature {d : ℕ}
    (x v : Fin d → ℝ) (t h : ℝ) :
    logStepCurvature
      (Real.log (coherentClockMass (fun i => x i + t * v i)))
      (Real.log (coherentClockMass (fun i => x i + (t + h) * v i)))
      (Real.log (coherentClockMass (fun i => x i + (t + 2 * h) * v i))) =
        h ^ (2 : ℕ) / 2 * coherentClockInformation x v := by
  simp only [coherentClockMass, gaussianCoherentGram, coordinateDot, Real.log_exp,
    ← pow_two]
  rw [affineSquareNorm_logStepCurvature, coherentClockInformation_formula]
  ring

theorem coherentClockMass_relativeStep_le {d : ℕ}
    (x v : Fin d → ℝ) (t h : ℝ) :
    relativeStep (coherentClockMass (fun i => x i + t * v i))
      (coherentClockMass (fun i => x i + (t + h) * v i)) ≤
    relativeStep (coherentClockMass (fun i => x i + (t + h) * v i))
      (coherentClockMass (fun i => x i + (t + 2 * h) * v i)) := by
  have hr (s r : ℝ) :
      relativeStep (coherentClockMass (fun i => x i + s * v i))
        (coherentClockMass (fun i => x i + r * v i)) =
      logRelativeStep (Real.log (coherentClockMass (fun i => x i + s * v i)))
        (Real.log (coherentClockMass (fun i => x i + r * v i))) := by
    rw [← relativeStep_exp, Real.exp_log (coherentClockMass_pos _),
      Real.exp_log (coherentClockMass_pos _)]
  rw [hr, hr, logRelativeStep_le_iff, coherentClockMass_logStepCurvature,
    coherentClockInformation_formula]
  positivity

/-- The normalized overlap sees the negative of the mass curvature. -/
theorem coherentClockFidelity_logStepCurvature {d : ℕ}
    (anchor x v : Fin d → ℝ) (t h : ℝ) :
    logStepCurvature
      (Real.log (coherentClockFidelity anchor (fun i => x i + t * v i)))
      (Real.log (coherentClockFidelity anchor (fun i => x i + (t + h) * v i)))
      (Real.log (coherentClockFidelity anchor (fun i => x i + (t + 2 * h) * v i))) =
        -(h ^ (2 : ℕ) / 2 * coherentClockInformation x v) := by
  simp only [coherentClockFidelity_formula, Real.log_exp]
  rw [logStepCurvature_reciprocal]
  have he (s : ℝ) : (∑ i, (anchor i - (x i + s * v i)) ^ (2 : ℕ)) =
      ∑ i, ((anchor i - x i) + s * (-v i)) ^ (2 : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  simp_rw [he]
  rw [affineSquareNorm_logStepCurvature, coherentClockInformation_formula]
  simp only [neg_sq]
  ring

/-- Neutral mass curvature detects exactly a zero sampling interval or a stationary label. -/
theorem coherentClockMass_neutral_iff {d : ℕ}
    (x v : Fin d → ℝ) (t h : ℝ) :
    logStepCurvature
      (Real.log (coherentClockMass (fun i => x i + t * v i)))
      (Real.log (coherentClockMass (fun i => x i + (t + h) * v i)))
      (Real.log (coherentClockMass (fun i => x i + (t + 2 * h) * v i))) = 0 ↔
        h = 0 ∨ v = 0 := by
  rw [coherentClockMass_logStepCurvature, mul_eq_zero,
    coherentClockInformation_zero_iff]
  simp

end
end GaloisForLFunctions.HTGeometry
