import GaloisForLFunctions.HTGeometry.CountableRecurrenceWallRayLaw

/-!
# Generic protected relations along an affine coupling ray

For arbitrary spectral and interaction profiles, a projective character is
either shared by both profiles and therefore protected along the entire
coupling ray, or it can occur at only one coupling strength.  On a countable
carrier, all accidental crossings therefore lie in one countable set.  Away
from that set, the complete relation lattice of `energy + g * direction` is
exactly the intersection of the two input relation lattices.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Set

/-- One countable set containing every accidental projective-relation
crossing of an affine spectral coupling ray. -/
def projectiveAffineCrossingSet
    {I : Type*} (energy direction : I → ℝ) : Set ℝ :=
  Set.range fun k : ProjectiveCharacter I =>
    -projectiveCharacterDetuning k energy /
      projectiveCharacterDetuning k direction

/-- A countable spectral carrier has only countably many accidental
projective-relation strengths along any affine coupling direction. -/
theorem projectiveAffineCrossingSet_countable
    {I : Type*} [Countable I]
    (energy direction : I → ℝ) :
    (projectiveAffineCrossingSet energy direction).Countable := by
  exact Set.countable_range _

/-- Every nondegenerate coupling interval contains a strength outside the
accidental crossing set. -/
theorem exists_not_mem_projectiveAffineCrossingSet_in_interval
    {I : Type*} [Countable I]
    (energy direction : I → ℝ) {a b : ℝ} (hab : a < b) :
    ∃ g ∈ Set.Ioo a b,
      g ∉ projectiveAffineCrossingSet energy direction := by
  have hcount := projectiveAffineCrossingSet_countable energy direction
  by_contra hnone
  push Not at hnone
  have hIcount : (Set.Ioo a b).Countable :=
    hcount.mono (fun g hg => hnone g hg)
  have hle : b ≤ a :=
    (Cardinal.Real.Ioo_countable_iff (x := a) (y := b)).mp hIcount
  exact not_le.mpr hab hle

/-- **Generic protected-relation law.** Away from the countable crossing
set, a projective character is a relation of the coupled spectrum exactly
when it is simultaneously a relation of the bare spectrum and the
interaction direction. -/
theorem projectiveCharacter_affineRelation_iff_common_of_not_mem
    {I : Type*} (energy direction : I → ℝ) (g : ℝ)
    (hg : g ∉ projectiveAffineCrossingSet energy direction)
    (k : ProjectiveCharacter I) :
    projectiveCharacterDetuning k
        (fun i => energy i + g * direction i) = 0 ↔
      projectiveCharacterDetuning k energy = 0 ∧
        projectiveCharacterDetuning k direction = 0 := by
  constructor
  · intro hrelation
    by_cases hdirection :
        projectiveCharacterDetuning k direction = 0
    · rw [projectiveCharacterDetuning_affine, hdirection,
        mul_zero, add_zero] at hrelation
      exact ⟨hrelation, hdirection⟩
    · have hgCrossing :
          g = -projectiveCharacterDetuning k energy /
            projectiveCharacterDetuning k direction :=
        (projectiveCharacter_on_affineWall_iff
          k energy direction g hdirection).1 hrelation
      exfalso
      apply hg
      exact ⟨k, hgCrossing.symm⟩
  · rintro ⟨henergy, hdirection⟩
    rw [projectiveCharacterDetuning_affine, henergy, hdirection]
    ring

/-- Set-valued form of the generic protected-relation law: the complete
coupled relation set is the exact intersection of the two input relation
sets outside the countable crossing set. -/
theorem projectiveRelationSet_affine_eq_common_of_not_mem
    {I : Type*} (energy direction : I → ℝ) (g : ℝ)
    (hg : g ∉ projectiveAffineCrossingSet energy direction) :
    {k : ProjectiveCharacter I |
      projectiveCharacterDetuning k
        (fun i => energy i + g * direction i) = 0} =
      {k : ProjectiveCharacter I |
        projectiveCharacterDetuning k energy = 0 ∧
          projectiveCharacterDetuning k direction = 0} := by
  ext k
  exact projectiveCharacter_affineRelation_iff_common_of_not_mem
    energy direction g hg k

end

end GaloisForLFunctions.HTGeometry
