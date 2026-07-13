import GaloisForLFunctions.HTGeometry.CircleAtomlessProbabilityLaws
import GaloisForLFunctions.HTGeometry.SingularProbabilityLaws
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Residual singular-continuous probability laws on the circle

The atomless and Haar-singular constraints are each dense `G_delta` subsets of
the weak probability space on the circle.  Since that probability space is a
Baire space, their intersection--the singular-continuous laws--is again a dense
`G_delta`.
-/

open MeasureTheory Set Filter Metric Topology
open TopologicalSpace
open scoped ENNReal NNReal Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized Haar measure as a circle probability law. -/
def unitCircleHaarProbability : ProbabilityMeasure UnitAddCircle :=
  ⟨AddCircle.haarAddCircle, inferInstance⟩

@[simp] theorem unitCircleHaarProbability_toMeasure :
    (unitCircleHaarProbability : Measure UnitAddCircle) =
      AddCircle.haarAddCircle := rfl

local instance unitCircleHaarProbability_noAtoms :
    NoAtoms (unitCircleHaarProbability : Measure UnitAddCircle) :=
  unitAddCircleHaarNoAtoms

/-- Circle laws that are simultaneously atomless and singular to Haar. -/
def circleSingularContinuousProbabilityLaws :
    Set (ProbabilityMeasure UnitAddCircle) :=
  atomlessProbabilityLaws (X := UnitAddCircle) ∩
    singularProbabilityLaws unitCircleHaarProbability

theorem circle_singularProbabilityLaws_dense :
    Dense (singularProbabilityLaws unitCircleHaarProbability) :=
  singularProbabilityLaws_dense unitCircleHaarProbability

theorem circle_singularProbabilityLaws_isGdelta :
    IsGδ (singularProbabilityLaws unitCircleHaarProbability) :=
  singularProbabilityLaws_isGdelta unitCircleHaarProbability

theorem circleSingularContinuousProbabilityLaws_isGdelta :
    IsGδ circleSingularContinuousProbabilityLaws := by
  exact atomlessProbabilityLaws_isGdelta.inter
    circle_singularProbabilityLaws_isGdelta

theorem circleSingularContinuousProbabilityLaws_dense :
    Dense circleSingularContinuousProbabilityLaws := by
  exact Dense.inter_of_Gδ atomlessProbabilityLaws_isGdelta
    circle_singularProbabilityLaws_isGdelta
    circle_atomlessProbabilityLaws_dense
    circle_singularProbabilityLaws_dense

/-- Singular-continuous probability laws form a dense `G_delta` in the weak
probability space on the circle. -/
theorem circleSingularContinuousProbabilityLaws_dense_gdelta :
    Dense circleSingularContinuousProbabilityLaws ∧
      IsGδ circleSingularContinuousProbabilityLaws :=
  ⟨circleSingularContinuousProbabilityLaws_dense,
    circleSingularContinuousProbabilityLaws_isGdelta⟩

end


end GaloisForLFunctions.HTGeometry
