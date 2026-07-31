import GaloisForLFunctions.HTGeometry.FiniteAndersonProjectiveGenericityLaw
import GaloisForLFunctions.HTGeometry.UniversalInteractionRecurrenceConversionLaw

/-!
# Local Anderson conversion of recurrence constraints into time

For every fixed finite Hermitian hopping graph, every reference onsite
potential, and every positive onsite-control budget, a nearby real onsite
potential has maximal projective spectral rank. The local perturbation
therefore converts the complete reference recurrence-relation rank into
temporal dimension, erases every post-perturbation balanced relation, and
attains every positive full-support replica collision floor.

This is a local-Hamiltonian realization of the universal constraint
conversion law. Hopping amplitudes and graph are held fixed; only diagonal
onsite controls change.
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Local Anderson recurrence-constraint conversion.** Around every
onsite potential of every fixed finite Hermitian hopping Hamiltonian lies a
potential that converts the complete initial recurrence-relation rank into
temporal dimension. Such converting potentials are in fact dense, residual,
and full measure by the imported genericity theorem. -/
theorem exists_finiteAnderson_onsite_fullConstraintConversion
    {d : ℕ}
    (T : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hT : T.IsHermitian)
    (onsite₀ : Fin (d + 1) → ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ onsite₁ : Fin (d + 1) → ℝ,
      dist onsite₁ onsite₀ < ε ∧
      MaximallyProjectiveEnergy
        (finiteAndersonHamiltonian_isHermitian
          T hT onsite₁).eigenvalues ∧
      phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues) -
          phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₀).eigenvalues) =
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (finiteAndersonHamiltonian_isHermitian
              T hT onsite₀).eigenvalues) ∧
      Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (finiteAndersonHamiltonian_isHermitian
              T hT onsite₁).eigenvalues) = 0 ∧
      (∀ (weight : Fin (d + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues r =
            fidelityReplicaPermutationFloor weight r) := by
  have hdense :=
    (finiteAndersonProjectiveMaximalSet_dense_residual_fullMeasure
      T hT).1
  have hopen : IsOpen (Metric.ball onsite₀ ε) :=
    Metric.isOpen_ball
  have hnonempty : (Metric.ball onsite₀ ε).Nonempty := by
    exact ⟨onsite₀, by simpa using hε⟩
  obtain ⟨onsite₁, hmax, hclose⟩ :=
    hdense.exists_mem_open hopen hnonempty
  have hconversion :=
    projectiveTemporalRank_gain_eq_relationRank_of_maximallyProjective
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₀).eigenvalues
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₁).eigenvalues
      hmax
  have hphase₀ :=
    relationPhaseEnsemble_temporalDimension_eq_projectiveRank
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₀).eigenvalues
  have hphase₁ :=
    relationPhaseEnsemble_temporalDimension_eq_projectiveRank
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₁).eigenvalues
  have hphaseConversion :
      phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues) -
          phaseLawTemporalDimension
            (spectralRelationPhaseEnsemble
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₀).eigenvalues) =
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (finiteAndersonHamiltonian_isHermitian
              T hT onsite₀).eigenvalues) := by
    rw [hphase₁, hphase₀]
    exact hconversion
  have hzero :=
    projectiveRelationRank_eq_zero_of_maximallyProjective
      (finiteAndersonHamiltonian_isHermitian
        T hT onsite₁).eigenvalues hmax
  have hcollision :
      ∀ (weight : Fin (d + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (finiteAndersonHamiltonian_isHermitian
                T hT onsite₁).eigenvalues r =
            fidelityReplicaPermutationFloor weight r := by
    intro weight hweight
    exact
      (all_fidelityReplicaCollisionMass_eq_floor_iff
        hweight
        (finiteAndersonHamiltonian_isHermitian
          T hT onsite₁).eigenvalues).2 hmax
  refine ⟨onsite₁, ?_, hmax, hphaseConversion, hzero, hcollision⟩
  simpa [Metric.mem_ball] using hclose

end

end GaloisForLFunctions.HTGeometry
