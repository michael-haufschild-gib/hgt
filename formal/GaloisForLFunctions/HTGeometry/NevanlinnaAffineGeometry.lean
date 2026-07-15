import GaloisForLFunctions.HTGeometry.NevanlinnaStationaryBauer
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Affine geometry of the Nevanlinna boundary projector

The boundary barycenter, projective label law, and canonical carrier projector preserve genuine
probability mixtures.  This supplies the affine part of the Bauer-retract statement without
embedding probability measures into signed measures.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint ProbabilityTheory Set
open scoped BoundedContinuousFunction ENNReal OnePoint

noncomputable section

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Projective pushforward preserves probability mixtures. -/
theorem projectiveLaw_probabilityMixture
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (mu nu : ProbabilityMeasure ℝ) :
    F.projectiveLaw (probabilityMixture t ht mu nu) =
      probabilityMixture t ht (F.projectiveLaw mu) (F.projectiveLaw nu) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map F.matrix.projectiveLabel
      (t • (mu : Measure ℝ) + (1 - t) • (nu : Measure ℝ)) =
    t • Measure.map F.matrix.projectiveLabel (mu : Measure ℝ) +
      (1 - t) • Measure.map F.matrix.projectiveLabel (nu : Measure ℝ)
  rw [Measure.map_add _ _
      (F.matrix.continuous_projectiveLabel F.continuous_c F.continuous_d).measurable,
    Measure.map_smul, Measure.map_smul]

/-- The canonical carrier projector is affine for probability mixtures. -/
theorem carrierProjector_probabilityMixture
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (mu nu : ProbabilityMeasure ℝ) :
    F.carrierProjector (probabilityMixture t ht mu nu) =
      probabilityMixture t ht (F.carrierProjector mu) (F.carrierProjector nu) := by
  rw [carrierProjector, F.projectiveLaw_probabilityMixture,
    F.barycenter_probabilityMixture]
  rfl

/-- The measure-side action of the constraint kernel is affine on probability laws. -/
theorem constraintKernel_comp_probabilityMixture
    (t : ℝ≥0∞) (ht : t ≤ 1)
    (mu nu : ProbabilityMeasure ℝ) :
    F.constraintKernel ∘ₘ
        (probabilityMixture t ht mu nu : Measure ℝ) =
      (probabilityMixture t ht (F.carrierProjector mu)
        (F.carrierProjector nu) : Measure ℝ) := by
  rw [F.constraintKernel_comp_probability,
    F.carrierProjector_probabilityMixture]

/-- The bounded-continuous Markov operator is idempotent. -/
theorem constraintMarkovOperator_idempotent (f : ℝ →ᵇ ℝ) :
    F.constraintMarkovOperator (F.constraintMarkovOperator f) =
      F.constraintMarkovOperator f := by
  ext x
  simp only [constraintMarkovOperator_apply]
  calc
    ∫ y, ∫ z, f z ∂(F.constraintKernel y) ∂(F.constraintKernel x) =
        ∫ z, f z ∂((F.constraintKernel ∘ₖ F.constraintKernel) x) := by
      symm
      exact Kernel.integral_comp (f.integrable _)
    _ = ∫ z, f z ∂(F.constraintKernel x) := by
      rw [F.constraintKernel_comp_self]

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
