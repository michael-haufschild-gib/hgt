import GaloisForLFunctions.HTGeometry.CountableRecurrenceWallRayLaw
import GaloisForLFunctions.HTGeometry.ResolvedRecurrenceRelationCompletenessLaw

/-!
# Minimum-order resolved recurrence-wall spectroscopy

Every finite projective recurrence relation occurs in an actual
survival-fidelity replica polynomial at one exact minimum order: its positive
integer coefficient mass.  This file joins that detector-depth filtration to
the affine recurrence-wall law.

Below the minimum replica height, the resolved signal is identically zero.
At the minimum height it has strictly positive full-support coefficient, is
completed-time active exactly at the unique transverse wall crossing, and has
the exact coefficient-weighted sinc profile under inverse-time coupling
rescaling.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- On a finite carrier, the support-sum and full-coordinate definitions of
projective detuning agree. -/
theorem finiteProjectiveDetuning_eq_projectiveCharacterDetuning
    {I : Type*} [Fintype I]
    (k : ProjectiveCharacter I) (energy : I → ℝ) :
    finiteTorusCharacterDetuning
        (finiteCharacterOfProjective k) energy =
      projectiveCharacterDetuning k energy := by
  rw [finiteTorusCharacterDetuning_finiteCharacterOfProjective]
  unfold finiteProjectiveCharacterDetuning projectiveCharacterDetuning
  rw [Finsupp.sum_fintype]
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hnot
    have hzero : k.1 i = 0 := by
      simpa [Finsupp.mem_support_iff] using hnot
    simp [hzero]
  · intro i
    simp

/-- Resolved contribution of one projective character to an `n`-replica
survival-fidelity moment, averaged over a symmetric observation window. -/
def resolvedReplicaWallSignal
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (T g : ℝ) : ℂ :=
  (fidelityReplicaCharacterCoefficient weight n
      (finiteCharacterOfProjective k) : ℂ) *
    recurrenceWallReporter k energy direction T g

/-- Every resolved replica-wall contribution has an exact sinc line shape. -/
theorem resolvedReplicaWallSignal_eq_sinc
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (T g : ℝ) (hT : T ≠ 0) :
    resolvedReplicaWallSignal weight n k energy direction T g =
      (fidelityReplicaCharacterCoefficient weight n
          (finiteCharacterOfProjective k) : ℂ) *
        Real.sinc
          (T * (projectiveCharacterDetuning k energy +
            g * projectiveCharacterDetuning k direction)) := by
  rw [resolvedReplicaWallSignal,
    recurrenceWallReporter_eq_sinc _ _ _ _ _ hT]

/-- A projective recurrence wall is absent from every survival-fidelity
replica layer below its positive character mass. -/
theorem resolvedReplicaWallSignal_eq_zero_of_lt_height
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (n : ℕ) (k : ProjectiveCharacter I)
    (hlt : n < projectiveCharacterReplicaHeight k)
    (energy direction : I → ℝ) (T g : ℝ) :
    resolvedReplicaWallSignal weight n k energy direction T g = 0 := by
  have hnotpos :
      ¬ 0 < fidelityReplicaCharacterCoefficient weight n
        (finiteCharacterOfProjective k) := by
    intro hpos
    have hle :=
      (fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le
        hweight (projectiveCharacter_spectralCharacterBalanced k) n).mp hpos
    exact (not_le_of_gt hlt) hle
  have hnonneg :
      0 ≤ fidelityReplicaCharacterCoefficient weight n
        (finiteCharacterOfProjective k) :=
    fidelityReplicaCharacterCoefficient_nonneg hweight n _
  have hzero :
      fidelityReplicaCharacterCoefficient weight n
          (finiteCharacterOfProjective k) = 0 :=
    le_antisymm (le_of_not_gt hnotpos) hnonneg
  simp [resolvedReplicaWallSignal, hzero]

/-- The wall enters the actual full-support survival-fidelity expansion with
strictly positive weight at its first possible replica order. -/
theorem resolvedReplicaWallCoefficient_pos_at_height
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (k : ProjectiveCharacter I) :
    0 < fidelityReplicaCharacterCoefficient weight
      (projectiveCharacterReplicaHeight k)
      (finiteCharacterOfProjective k) := by
  exact
    (fidelityReplicaCharacterCoefficient_pos_iff_positiveMass_le
      hweight (projectiveCharacter_spectralCharacterBalanced k)
      (projectiveCharacterReplicaHeight k)).mpr le_rfl

/-- **Minimum-order recurrence-wall spectroscopy.** At the first replica
order capable of carrying a character, every transverse wall crossing has a
strictly positive resolved signal and all observation times collapse onto
one coefficient-weighted sinc profile after inverse-time rescaling. -/
theorem resolvedReplicaWallSignal_scaled_profile_at_height
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {weight : I → ℝ} (hweight : ∀ i, 0 < weight i)
    (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (T ξ : ℝ)
    (hT : T ≠ 0)
    (htransverse : projectiveCharacterDetuning k direction ≠ 0) :
    resolvedReplicaWallSignal weight
        (projectiveCharacterReplicaHeight k) k energy direction T
        (-projectiveCharacterDetuning k energy /
            projectiveCharacterDetuning k direction + ξ / T) =
      (fidelityReplicaCharacterCoefficient weight
          (projectiveCharacterReplicaHeight k)
          (finiteCharacterOfProjective k) : ℂ) *
        Real.sinc (ξ * projectiveCharacterDetuning k direction) ∧
      0 < fidelityReplicaCharacterCoefficient weight
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) := by
  constructor
  · rw [resolvedReplicaWallSignal,
      recurrenceWallReporter_scaled_profile _ _ _ _ _ hT htransverse]
  · exact resolvedReplicaWallCoefficient_pos_at_height hweight k

/-- Along a transverse affine ray, the minimum-order resolved detector is
completed-time active exactly at the unique wall crossing. -/
theorem resolvedReplicaDetects_at_height_iff_affineWall
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (k : ProjectiveCharacter I)
    (energy direction : I → ℝ) (g : ℝ)
    (htransverse : projectiveCharacterDetuning k direction ≠ 0) :
    ResolvedReplicaDetects
        (fun i => energy i + g * direction i)
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) ↔
      g = -projectiveCharacterDetuning k energy /
        projectiveCharacterDetuning k direction := by
  unfold ResolvedReplicaDetects
  have hrealizes :
      SpectralCharacterReplicaRealizes
        (projectiveCharacterReplicaHeight k)
        (finiteCharacterOfProjective k) := by
    exact spectralCharacterReplicaRealizes_positiveMass_of_balanced
      (projectiveCharacter_spectralCharacterBalanced k)
  rw [and_iff_right hrealizes,
    finiteProjectiveDetuning_eq_projectiveCharacterDetuning]
  exact projectiveCharacter_on_affineWall_iff
    k energy direction g htransverse

end

end GaloisForLFunctions.HTGeometry
