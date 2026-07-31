import GaloisForLFunctions.HTGeometry.UniversalRecurrenceConstraintConversionLaw
import GaloisForLFunctions.HTGeometry.TemporalDimensionInteractionMultiplicationLaw

/-!
# Universal projective recurrence capstone

For every finite real spectrum, one rational linear map from projective
characters to energy detunings has:

* kernel equal to the rational span of all exact balanced integer spectral
  relations;
* range equal to the rational span of all anchored energy gaps;
* rank equal to the operational temporal dimension of the completed-time
  phase law.

Rank-nullity therefore becomes the exact recurrence constraint-conversion
law. Together with resolved replica completeness, completed recurrence,
projective spectral arithmetic, temporal dimension, and minimum detector
height are invariants of one detuning map.
-/

open Set Filter MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational evaluation of a projective character against a finite energy
packet. -/
def projectiveEnergyDetuningLinearMap
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    ProjectiveRationalCharacter I →ₗ[ℚ] ℝ where
  toFun q := ∑ i, (q.1 i : ℝ) * energy i
  map_add' q r := by
    change
      (∑ i, ((q.1 i + r.1 i : ℚ) : ℝ) * energy i) =
        (∑ i, (q.1 i : ℝ) * energy i) +
          ∑ i, (r.1 i : ℝ) * energy i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring
  map_smul' a q := by
    change
      (∑ i, ((a * q.1 i : ℚ) : ℝ) * energy i) =
        a • ∑ i, (q.1 i : ℝ) * energy i
    simp only [Algebra.smul_def]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    norm_num
    ring

/-- Integral projective detuning agrees with rational evaluation after
scalar extension. -/
theorem projectiveEnergyDetuningLinearMap_toRational
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (k : ProjectiveCharacter I) :
    projectiveEnergyDetuningLinearMap energy
        (projectiveCharacterToRational k) =
      finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k) energy := by
  classical
  change
    (∑ i, ((((k.1 i : ℤ) : ℚ) : ℝ)) * energy i) =
      ∑ i, ((k.1 i : ℤ) : ℝ) * energy i
  apply Finset.sum_congr rfl
  intro i hi
  norm_num

/-- The rational kernel of projective detuning is exactly the rational span
of the exact balanced integer relation lattice. -/
theorem projectiveEnergyDetuning_ker_eq_relationSpace
    {I : Type*} [Fintype I]
    (energy : I → ℝ) :
    (projectiveEnergyDetuningLinearMap energy).ker =
      projectiveSpectralRelationRationalSpace energy := by
  apply le_antisymm
  · intro q hq
    obtain ⟨b, hb, k, hk⟩ :=
      exists_integer_projective_multiple q
    have hkdetuning :
        finiteTorusCharacterDetuning
            (finiteCharacterOfProjective k) energy = 0 := by
      rw [← projectiveEnergyDetuningLinearMap_toRational]
      rw [hk, map_zsmul, hq, smul_zero]
    have hkrelation :
        finiteCharacterOfProjective k ∈
          projectiveSpectralRelationLattice energy :=
      (mem_projectiveSpectralRelationLattice_iff energy _).2
        ⟨projectiveCharacter_spectralCharacterBalanced k,
          hkdetuning⟩
    have hgenerator :
        projectiveCharacterToRational k ∈
          projectiveSpectralRelationRationalSpace energy :=
      Submodule.subset_span ⟨k, hkrelation, rfl⟩
    have hbinv :
        (b : ℚ)⁻¹ • ((b : ℚ) • q) = q := by
      rw [← mul_smul]
      simp [hb]
    rw [hk] at hgenerator
    rw [← hbinv]
    exact Submodule.smul_mem _ _ hgenerator
  · apply Submodule.span_le.2
    rintro q ⟨k, hk, rfl⟩
    change
      projectiveEnergyDetuningLinearMap energy
          (projectiveCharacterToRational k) = 0
    rw [projectiveEnergyDetuningLinearMap_toRational]
    exact
      (mem_projectiveSpectralRelationLattice_iff energy _).1 hk |>.2

/-- Projective rational character selecting one anchored gap. -/
def projectiveGapRationalCharacter
    {d : ℕ} (i : Fin d) :
    ProjectiveRationalCharacter (Fin (d + 1)) := by
  let q : Fin (d + 1) → ℚ :=
    Fin.cases (-1 : ℚ)
      (fun j => if j = i then (1 : ℚ) else 0)
  refine ⟨q, ?_⟩
  change (∑ j : Fin (d + 1), q j) = (0 : ℚ)
  rw [Fin.sum_univ_succ]
  simp [q]

/-- Evaluation of the anchored-gap character is the corresponding energy
gap. -/
theorem projectiveEnergyDetuning_gapCharacter
    {d : ℕ} (energy : Fin (d + 1) → ℝ) (i : Fin d) :
    projectiveEnergyDetuningLinearMap energy
        (projectiveGapRationalCharacter i) =
      projectiveGapPacket energy i := by
  classical
  change
    (∑ j : Fin (d + 1),
      ((projectiveGapRationalCharacter i).1 j : ℝ) *
        energy j) =
      projectiveGapPacket energy i
  unfold projectiveGapRationalCharacter
  rw [Fin.sum_univ_succ]
  simp only [Fin.cases_zero, Fin.cases_succ]
  push_cast
  have hsum :
      (∑ j : Fin d,
        (((if j = i then (1 : ℚ) else 0) : ℚ) : ℝ) *
          energy j.succ) =
        energy i.succ := by
    rw [Finset.sum_eq_single i]
    · norm_num
    · intro j hj hji
      simp [hji]
    · simp
  rw [hsum]
  unfold projectiveGapPacket
  ring

/-- The image of projective detuning is exactly the rational anchored-gap
space. -/
theorem projectiveEnergyDetuning_range_eq_gapSubspace
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    (projectiveEnergyDetuningLinearMap energy).range =
      visibleGapSubspace (projectiveGapPacket energy) := by
  apply le_antisymm
  · rintro x ⟨q, rfl⟩
    have hcharge : ∑ i, q.1 i = 0 := q.2
    rw [Fin.sum_univ_succ] at hcharge
    have hzero :
        q.1 0 = -∑ i : Fin d, q.1 i.succ := by
      linarith
    have heq :
        projectiveEnergyDetuningLinearMap energy q =
          ∑ i : Fin d,
            q.1 i.succ • projectiveGapPacket energy i := by
      change
        (∑ j : Fin (d + 1), (q.1 j : ℝ) * energy j) =
          ∑ i : Fin d,
            (q.1 i.succ : ℝ) * projectiveGapPacket energy i
      rw [Fin.sum_univ_succ, hzero]
      push_cast
      simp_rw [projectiveGapPacket, mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [heq]
    apply Submodule.sum_mem
    intro (i : Fin d) hi
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    refine ⟨projectiveGapRationalCharacter i, ?_⟩
    exact projectiveEnergyDetuning_gapCharacter energy i

/-- **Projective recurrence rank conservation.** For every `d + 1` level
spectrum, anchored-gap temporal rank plus exact balanced-relation rank is
exactly `d`. -/
theorem projectiveTemporalRank_add_relationRank
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    projectiveTemporalRank energy +
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace energy) =
      d := by
  have h :=
    (projectiveEnergyDetuningLinearMap energy).finrank_range_add_finrank_ker
  rw [projectiveEnergyDetuning_range_eq_gapSubspace,
    projectiveEnergyDetuning_ker_eq_relationSpace] at h
  have hprojective :=
    finrank_projectiveRationalCharacter (Fin (d + 1))
  simp at hprojective
  unfold projectiveTemporalRank rationalCoordinateRank
  unfold visibleGapSubspace at h
  rw [hprojective] at h
  exact h

/-- Operational dimension of the completed recurrence phase law is exactly
the arithmetic rank of the anchored energy gaps. -/
theorem relationPhaseEnsemble_temporalDimension_eq_projectiveRank
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    phaseLawTemporalDimension
        (spectralRelationPhaseEnsemble energy) =
      projectiveTemporalRank energy := by
  have hphase :=
    relationPhaseEnsemble_temporalDimension_add_relationRank energy
  have hrank :=
    projectiveTemporalRank_add_relationRank energy
  have hprojective :=
    finrank_projectiveRationalCharacter (Fin (d + 1))
  simp at hprojective
  rw [hprojective] at hphase
  omega

/-- **Universal finite projective recurrence law.** Completed phase
constraints, exact balanced integer relations, temporal gap rank, and
resolved replica detection are the kernel, image rank, and height filtration
of one projective detuning map. -/
theorem finiteProjectiveRecurrence_universalLaw
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    phaseLawTemporalDimension
          (spectralRelationPhaseEnsemble energy) =
        projectiveTemporalRank energy ∧
      projectiveTemporalRank energy +
          Module.finrank ℚ
            (projectiveSpectralRelationRationalSpace energy) =
        d ∧
      (∀ k : ProjectiveCharacter (Fin (d + 1)),
        phaseLawConstraint
            (spectralRelationPhaseEnsemble energy) k ↔
          finiteCharacterOfProjective k ∈
            projectiveSpectralRelationLattice energy) ∧
      (∀ (n : ℕ) (k : ProjectiveCharacter (Fin (d + 1))),
        ResolvedReplicaDetects energy n
            (finiteCharacterOfProjective k) ↔
          phaseLawConstraint
              (spectralRelationPhaseEnsemble energy) k ∧
            spectralCharacterPositiveMass
              (finiteCharacterOfProjective k) ≤ n) := by
  exact
    ⟨relationPhaseEnsemble_temporalDimension_eq_projectiveRank energy,
      projectiveTemporalRank_add_relationRank energy,
      relationPhaseEnsemble_constraint_iff energy,
      relationPhaseEnsemble_resolvedReplica_iff energy⟩

end

end GaloisForLFunctions.HTGeometry
