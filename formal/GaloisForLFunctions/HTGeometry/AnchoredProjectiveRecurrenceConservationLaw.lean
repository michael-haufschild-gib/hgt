import GaloisForLFunctions.HTGeometry.UniversalProjectiveRecurrenceCapstoneLaw

/-!
# Reference-independent projective recurrence conservation

For an arbitrary nonempty finite spectrum and any chosen reference level,
the image of the projective detuning map is exactly the rational span of
the anchored gaps. Rank-nullity therefore splits the complete projective
capacity into anchored temporal directions and exact balanced spectral
relations without first reindexing the spectrum by `Fin`.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Rational span of all energy gaps anchored at a chosen reference level. -/
def anchoredGapSubspace
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (reference : I) :
    Submodule ℚ ℝ :=
  Submodule.span ℚ
    (Set.range (fun i => energy i - energy reference))

/-- Rational dimension of a finite spectrum's anchored energy gaps. -/
def anchoredTemporalRank
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (reference : I) : ℕ :=
  Module.finrank ℚ (anchoredGapSubspace energy reference)

/-- Balanced rational character selecting one gap against the reference
level. -/
def anchoredGapRationalCharacter
    {I : Type*} [Fintype I] [DecidableEq I]
    (reference i : I) :
    ProjectiveRationalCharacter I := by
  let q : I → ℚ :=
    fun j =>
      (if j = i then 1 else 0) -
        if j = reference then 1 else 0
  refine ⟨q, ?_⟩
  change (∑ j, q j) = 0
  simp [q]

/-- Evaluation of the anchored character is the selected energy gap. -/
theorem projectiveEnergyDetuning_anchoredGapCharacter
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (reference i : I) :
    projectiveEnergyDetuningLinearMap energy
        (anchoredGapRationalCharacter reference i) =
      energy i - energy reference := by
  classical
  change
    (∑ j,
      (((if j = i then (1 : ℚ) else 0) -
        if j = reference then 1 else 0 : ℚ) : ℝ) *
        energy j) =
      energy i - energy reference
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hi :
      (∑ x,
        ((if x = i then (1 : ℚ) else 0 : ℚ) : ℝ) *
          energy x) = energy i := by
    rw [Finset.sum_eq_single i]
    · norm_num
    · intro j hj hji
      simp [hji]
    · simp
  have href :
      (∑ x,
        ((if x = reference then (1 : ℚ) else 0 : ℚ) : ℝ) *
          energy x) = energy reference := by
    rw [Finset.sum_eq_single reference]
    · norm_num
    · intro j hj hjr
      simp [hjr]
    · simp
  rw [hi, href]

/-- The range of projective energy detuning is exactly the gap space
anchored at any chosen reference level. -/
theorem projectiveEnergyDetuning_range_eq_anchoredGapSubspace
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (reference : I) :
    (projectiveEnergyDetuningLinearMap energy).range =
      anchoredGapSubspace energy reference := by
  apply le_antisymm
  · rintro x ⟨q, rfl⟩
    have hcharge : ∑ i, q.1 i = 0 := q.2
    have hchargeR : ∑ i, (q.1 i : ℝ) = 0 := by
      exact_mod_cast hcharge
    have heq :
        projectiveEnergyDetuningLinearMap energy q =
          ∑ i, q.1 i • (energy i - energy reference) := by
      change
        (∑ i, (q.1 i : ℝ) * energy i) =
          ∑ i, (q.1 i : ℝ) *
            (energy i - energy reference)
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hchargeR, zero_mul, sub_zero]
    rw [heq]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    refine ⟨anchoredGapRationalCharacter reference i, ?_⟩
    exact
      projectiveEnergyDetuning_anchoredGapCharacter
        energy reference i

/-- **Reference-independent recurrence conservation.** For every nonempty
finite spectrum, anchored temporal rank plus exact balanced-relation rank
equals number of levels minus global phase. -/
theorem anchoredTemporalRank_add_relationRank
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (energy : I → ℝ) (reference : I) :
    anchoredTemporalRank energy reference +
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace energy) =
      Fintype.card I - 1 := by
  have h :=
    (projectiveEnergyDetuningLinearMap energy).finrank_range_add_finrank_ker
  rw [projectiveEnergyDetuning_range_eq_anchoredGapSubspace,
    projectiveEnergyDetuning_ker_eq_relationSpace] at h
  have hprojective :=
    finrank_projectiveRationalCharacter I
  unfold anchoredTemporalRank at *
  rw [hprojective] at h
  exact h

end

end GaloisForLFunctions.HTGeometry
