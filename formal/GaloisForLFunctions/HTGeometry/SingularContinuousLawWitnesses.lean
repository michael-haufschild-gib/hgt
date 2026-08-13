import GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual
import GaloisForLFunctions.HTGeometry.CircleSingularContinuousResidual

/-!
# The singular-continuous law classes are inhabited

Every theorem that runs on a singular-continuous projective law takes membership in
`projectiveSingularContinuousProbabilityLaws` as a hypothesis, and nothing exhibited a member: the
statements were correct but carried no guarantee of being about anything.

Density supplies the members for free.  Each of these classes is dense in a nonempty space of
probability laws, so it is nonempty — no explicit Cantor-type construction is needed, and the
witnesses are as unconditional as the density theorems that produce them.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

/-! ## On the circle -/

theorem circle_atomlessProbabilityLaws_nonempty :
    (atomlessProbabilityLaws (X := UnitAddCircle)).Nonempty :=
  circle_atomlessProbabilityLaws_dense.nonempty

theorem circle_singularProbabilityLaws_nonempty :
    (singularProbabilityLaws unitCircleHaarProbability).Nonempty :=
  circle_singularProbabilityLaws_dense.nonempty

theorem circleSingularContinuousProbabilityLaws_nonempty :
    circleSingularContinuousProbabilityLaws.Nonempty :=
  circleSingularContinuousProbabilityLaws_dense.nonempty

/-! ## On the projective line -/

theorem projective_atomlessProbabilityLaws_nonempty :
    (atomlessProbabilityLaws (X := OnePoint ℝ)).Nonempty :=
  projective_atomlessProbabilityLaws_dense.nonempty

theorem projective_singularProbabilityLaws_nonempty :
    (singularProbabilityLaws projectiveLebesgueProbability).Nonempty :=
  projective_singularProbabilityLaws_dense.nonempty

/-- **A singular-continuous projective law exists.**  Atomless laws singular to projective Lebesgue
probability form a dense subset of a nonempty space. -/
theorem projectiveSingularContinuousProbabilityLaws_nonempty :
    projectiveSingularContinuousProbabilityLaws.Nonempty :=
  projectiveSingularContinuousProbabilityLaws_dense.nonempty

/-- The membership hypothesis of the singular-continuous carrier theorems is satisfiable. -/
theorem exists_mem_projectiveSingularContinuousProbabilityLaws :
    ∃ eta : ProbabilityMeasure (OnePoint ℝ),
      eta ∈ projectiveSingularContinuousProbabilityLaws :=
  projectiveSingularContinuousProbabilityLaws_nonempty

/-- A singular-continuous projective probability law automatically has infinite topological
support, so downstream carrier theorems need no separate support hypothesis. -/
theorem projectiveSingularContinuousProbabilityLaw_support_infinite
    (eta : ProbabilityMeasure (OnePoint ℝ))
    (heta : eta ∈ projectiveSingularContinuousProbabilityLaws) :
    ((eta : ProbabilityMeasure (OnePoint ℝ)) : Measure (OnePoint ℝ)).support.Infinite := by
  letI : SecondCountableTopology (OnePoint ℝ) :=
    (onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)).secondCountableTopology
  letI : NullSingletonClass (eta : Measure (OnePoint ℝ)) := heta.1
  intro hfinite
  have hs : (eta : Measure (OnePoint ℝ)) (eta : Measure (OnePoint ℝ)).support = 0 :=
    hfinite.measure_zero _
  have hc : (eta : Measure (OnePoint ℝ))
      ((eta : Measure (OnePoint ℝ)).support)ᶜ = 0 :=
    Measure.measure_compl_support
  have hu : (eta : Measure (OnePoint ℝ)) Set.univ = 0 := by
    rw [← Set.union_compl_self (eta : Measure (OnePoint ℝ)).support]
    exact measure_union_null hs hc
  simp at hu

/-! ## In the Nevanlinna carrier simplex -/

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- The residual singular-continuous phase of the carrier simplex is inhabited. -/
theorem singularContinuousParameterCarrierPhase_nonempty :
    F.singularContinuousParameterCarrierPhase.Nonempty :=
  projectiveSingularContinuousProbabilityLaws_nonempty.image _

end NevanlinnaBoundaryFamily

end GaloisForLFunctions.HTGeometry
