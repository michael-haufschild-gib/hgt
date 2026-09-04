import GaloisForLFunctions.HTGeometry.RandomMixedGraphCore
import GaloisForLFunctions.HTGeometry.BoundedConservationBlindness

open MeasureTheory InformationTheory

namespace GaloisForLFunctions.HTGeometry.RandomMixedGraph

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Paper's symmetrized KL convention is the corpus Jeffreys divergence, without a factor `1/2`. -/
def symmetrizedKLDivergence (P Q : Measure X) : ℝ := jeffreys P Q

theorem symmetrizedKLDivergence_eq (P Q : Measure X) :
    symmetrizedKLDivergence P Q =
      (klDiv P Q).toReal + (klDiv Q P).toReal := by
  rfl

theorem symmetrizedKLDivergence_symm (P Q : Measure X) :
    symmetrizedKLDivergence P Q = symmetrizedKLDivergence Q P :=
  jeffreys_symm P Q

theorem symmetrizedKLDivergence_nonneg (P Q : Measure X) :
    0 ≤ symmetrizedKLDivergence P Q :=
  jeffreys_nonneg P Q

/-- Averaged convention sometimes also called symmetric KL. -/
def averagedSymmetricKLDivergence (P Q : Measure X) : ℝ :=
  symmetrizedKLDivergence P Q / 2

theorem symmetrizedKLDivergence_eq_two_mul_averaged (P Q : Measure X) :
    symmetrizedKLDivergence P Q = 2 * averagedSymmetricKLDivergence P Q := by
  unfold averagedSymmetricKLDivergence
  ring

theorem averagedSymmetricKLDivergence_symm (P Q : Measure X) :
    averagedSymmetricKLDivergence P Q = averagedSymmetricKLDivergence Q P := by
  rw [averagedSymmetricKLDivergence, averagedSymmetricKLDivergence,
    symmetrizedKLDivergence_symm]

theorem averagedSymmetricKLDivergence_nonneg (P Q : Measure X) :
    0 ≤ averagedSymmetricKLDivergence P Q := by
  exact div_nonneg (symmetrizedKLDivergence_nonneg P Q) (by norm_num)

end

end GaloisForLFunctions.HTGeometry.RandomMixedGraph

