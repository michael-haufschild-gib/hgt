import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw
import GaloisForLFunctions.HTGeometry.ObserverTemporalPhaseSupportLaw
import GaloisForLFunctions.HTGeometry.ObserverActionVisibilityConeLaw

/-!
# Universal recurrence constraint-conversion law

For every finite real spectrum, the characters fixed almost surely by its
completed-time phase law are exactly its balanced integer energy relations.
The same relations are exactly those found by the resolved replica
hierarchy, and each first appears at its positive character mass.

Thus completed recurrence, exact spectral arithmetic, operational temporal
dimension, and resolved replica detection are four descriptions of one
projective constraint object.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A projective character is fixed by the completed recurrence law exactly
when its balanced integer coefficient function is an exact spectral
relation. -/
theorem relationPhaseEnsemble_constraint_iff
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : ProjectiveCharacter I) :
    phaseLawConstraint (spectralRelationPhaseEnsemble energy) k ↔
      finiteCharacterOfProjective k ∈
        projectiveSpectralRelationLattice energy := by
  rw [phaseLawConstraint_iff_integral_eq_one,
    spectralRelationPhaseEnsemble_mFourier_integral]
  have hrelation :
      finiteCharacterOfProjective k ∈ spectralRelationLattice energy ↔
        finiteCharacterOfProjective k ∈
          projectiveSpectralRelationLattice energy := by
    rw [mem_spectralRelationLattice_iff,
      mem_projectiveSpectralRelationLattice_iff]
    constructor
    · intro hdetuning
      exact
        ⟨projectiveCharacter_spectralCharacterBalanced k,
          hdetuning⟩
    · rintro ⟨_, hdetuning⟩
      exact hdetuning
  rw [spectralRelationIndicator]
  by_cases h :
      finiteCharacterOfProjective k ∈ spectralRelationLattice energy
  · simp [h, hrelation.mp h]
  · simp [h, hrelation.not.mp h]

/-- Rational span of the balanced exact integer relations of a finite
spectrum. -/
def projectiveSpectralRelationRationalSpace
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    Submodule ℚ (ProjectiveRationalCharacter I) :=
  Submodule.span ℚ
    (projectiveCharacterToRational ''
      {k : ProjectiveCharacter I |
        finiteCharacterOfProjective k ∈
          projectiveSpectralRelationLattice energy})

/-- The almost-sure constraint space of the completed recurrence law is
exactly the rational span of the spectrum's balanced integer relations. -/
theorem relationPhaseEnsemble_constraintSpace_eq
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    phaseLawConstraintRationalSpace
        (spectralRelationPhaseEnsemble energy) =
      projectiveSpectralRelationRationalSpace energy := by
  unfold phaseLawConstraintRationalSpace
  unfold projectiveSpectralRelationRationalSpace
  congr 1
  ext q
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨k, (relationPhaseEnsemble_constraint_iff energy k).mp hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact
      ⟨k, (relationPhaseEnsemble_constraint_iff energy k).mpr hk, rfl⟩

/-- Every completed-recurrence constraint is detected at exactly its
minimum replica order. -/
theorem relationPhaseEnsemble_constraint_iff_detected
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (k : ProjectiveCharacter I) :
    phaseLawConstraint (spectralRelationPhaseEnsemble energy) k ↔
      ResolvedReplicaDetects energy
        (spectralCharacterPositiveMass
          (finiteCharacterOfProjective k))
        (finiteCharacterOfProjective k) := by
  rw [relationPhaseEnsemble_constraint_iff,
    relation_iff_detected_at_exact_replicaHeight]

/-- At replica order `n`, the resolved hierarchy sees exactly the
completed-recurrence constraints of minimum height at most `n`. -/
theorem relationPhaseEnsemble_resolvedReplica_iff
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (n : ℕ) (k : ProjectiveCharacter I) :
    ResolvedReplicaDetects energy n
        (finiteCharacterOfProjective k) ↔
      phaseLawConstraint (spectralRelationPhaseEnsemble energy) k ∧
        spectralCharacterPositiveMass
          (finiteCharacterOfProjective k) ≤ n := by
  rw [resolvedReplicaDetects_iff_relation_and_height_le,
    ← relationPhaseEnsemble_constraint_iff]

/-- **Constraint-conversion conservation law.** For every probability law
on finite projective phases, its operational temporal dimension plus the
rational rank of its almost-sure constraints equals the complete
projective character capacity. -/
theorem phaseLawTemporalDimension_add_constraintRank
    {I : Type*} [Fintype I]
    (μ : ProbabilityMeasure (UnitAddTorus I)) :
    phaseLawTemporalDimension μ +
        Module.finrank ℚ (phaseLawConstraintRationalSpace μ) =
      Module.finrank ℚ (ProjectiveRationalCharacter I) := by
  unfold phaseLawTemporalDimension
  have hle :
      Module.finrank ℚ (phaseLawConstraintRationalSpace μ) ≤
        Module.finrank ℚ (ProjectiveRationalCharacter I) :=
    Submodule.finrank_le _
  omega

/-- For the canonical completed recurrence law, temporal dimension and the
rank of exact balanced spectral relations exhaust the projective character
capacity. -/
theorem relationPhaseEnsemble_temporalDimension_add_relationRank
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    phaseLawTemporalDimension (spectralRelationPhaseEnsemble energy) +
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace energy) =
      Module.finrank ℚ (ProjectiveRationalCharacter I) := by
  rw [← relationPhaseEnsemble_constraintSpace_eq]
  exact phaseLawTemporalDimension_add_constraintRank _

end

end GaloisForLFunctions.HTGeometry
