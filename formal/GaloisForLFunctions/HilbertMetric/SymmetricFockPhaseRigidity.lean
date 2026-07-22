import GaloisForLFunctions.HilbertMetric.SymmetricFockPhase
import GaloisForLFunctions.HilbertMetric.SymmetricFockShadowRigidity

/-!
# Rigidity at the symmetric-Fock transverse phase bound

The rank-sensitive transverse Fano bound loses exactly two independent nonnegative defects: the
graded lowering-charge gap and the finite sum of transverse phase squares.  Equality therefore
forces two-sided lowering/creation closure at every positive level and the unique balancing phase
in every transverse channel.  Strictness is witnessed exactly by one level defect or one
off-balance channel.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- Left side of the rank-sensitive graded Fock transverse Fano bound. -/
def gradedFockTransverseRankBaseline
    (J : Type*) [Fintype J] (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n))) : ℝ :=
  (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) +
    ((Fintype.card I + 1 : ℕ) : ℝ) *
      (((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ) -
        (Fintype.card J : ℝ) * ((M : ℝ) * ((M : ℝ) - 4) / 4))

/-- Two-sided closure condition selected by equality in the lowering-shadow charge law. -/
def GradedFockLevelwiseCreatorClosed
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n))) : Prop :=
  ∀ n < M, 0 < n →
    symmetricFockLoweringShadow n (U (n + 1)) = U n ∧
      ∀ (i : I) (y : EuclideanSpace ℝ (Sym I n)), y ∈ U n →
        (symmetricFockAnnihilation n i).adjoint y ∈ U (n + 1)

/-- Every transverse channel lies at the unique square-completing phase. -/
def GradedFockTransversePhaseBalanced
    (M : ℕ) (p : J → ℝ) : Prop :=
  ∀ i, ((M : ℝ) - 1) * p i = ((M : ℝ) - 2) / 2

/-- **Symmetric-Fock phase-rigidity law.** Equality in the rank-sensitive Fano bound is equivalent
to simultaneous levelwise lowering/creation closure and channelwise phase balance. -/
theorem gradedFockTransverse_rank_bound_eq_iff_phase_rigidity
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ) :
    gradedFockTransverseRankBaseline J M U =
        ((Fintype.card I + 1 : ℕ) : ℝ) *
          gradedFockTransverseFanoMargin M U p ↔
      GradedFockLevelwiseCreatorClosed M U ∧
        GradedFockTransversePhaseBalanced M p := by
  classical
  let phaseSquare : J → ℝ := fun i =>
    (((M : ℝ) - 1) * p i - ((M : ℝ) - 2) / 2) ^ 2
  have hmargin :
      gradedFockTransverseFanoMargin M U p =
        gradedFockLoweringCharge M U +
          ((Module.finrank ℝ (U M) : ℝ) - (Fintype.card J : ℝ)) * (M : ℝ) -
          (Fintype.card J : ℝ) * ((M : ℝ) * ((M : ℝ) - 4) / 4) +
          ∑ i, phaseSquare i := by
    rw [gradedFockTransverseFanoMargin,
      transverseChannelFanoMargin_square_card]
  have hcharge := gradedFockLoweringCharge_lower_bound M U hshadow
  have hphaseNonneg : 0 ≤ ∑ i, phaseSquare i :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hcard : 0 < (((Fintype.card I + 1 : ℕ) : ℝ)) := by positivity
  constructor
  · intro heq
    rw [gradedFockTransverseRankBaseline, hmargin] at heq
    have hchargeEq :
        (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) =
          ((Fintype.card I + 1 : ℕ) : ℝ) * gradedFockLoweringCharge M U := by
      nlinarith
    have hphaseZero : ∑ i, phaseSquare i = 0 := by
      nlinarith
    refine ⟨?_, ?_⟩
    · exact (gradedFockLoweringCharge_eq_iff_levelwise_creator_closed
        M U hshadow).1 hchargeEq
    · intro i
      have hi : phaseSquare i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j (_hj : j ∈ Finset.univ) => sq_nonneg
            (((M : ℝ) - 1) * p j - ((M : ℝ) - 2) / 2))).1
          hphaseZero i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro ⟨hclosed, hbalanced⟩
    have hchargeEq :=
      (gradedFockLoweringCharge_eq_iff_levelwise_creator_closed
        M U hshadow).2 hclosed
    have hphaseZero : ∑ i, phaseSquare i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      dsimp only [phaseSquare]
      rw [hbalanced i]
      ring
    rw [gradedFockTransverseRankBaseline, hmargin, hphaseZero]
    nlinarith

/-- **Exact strict-defect classification.** The rank-sensitive Fano bound is strict precisely
when some positive adjacent level fails two-sided closure or some transverse channel leaves its
balancing phase. -/
theorem gradedFockTransverse_rank_bound_lt_iff_phase_defect
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n)
    (p : J → ℝ) :
    gradedFockTransverseRankBaseline J M U <
        ((Fintype.card I + 1 : ℕ) : ℝ) *
          gradedFockTransverseFanoMargin M U p ↔
      (∃ n < M, 0 < n ∧
        (symmetricFockLoweringShadow n (U (n + 1)) ≠ U n ∨
          ∃ (i : I) (y : EuclideanSpace ℝ (Sym I n)), y ∈ U n ∧
            (symmetricFockAnnihilation n i).adjoint y ∉ U (n + 1))) ∨
      ∃ i, ((M : ℝ) - 1) * p i ≠ ((M : ℝ) - 2) / 2 := by
  classical
  have hle : gradedFockTransverseRankBaseline J M U ≤
      ((Fintype.card I + 1 : ℕ) : ℝ) *
        gradedFockTransverseFanoMargin M U p := by
    simpa only [gradedFockTransverseRankBaseline] using
      gradedFockTransverseFanoMargin_rank_bound M U hshadow p
  have heq := gradedFockTransverse_rank_bound_eq_iff_phase_rigidity
    (J := J) M U hshadow p
  constructor
  · intro hlt
    by_cases hclosed : GradedFockLevelwiseCreatorClosed M U
    · right
      by_contra hbalanced
      push Not at hbalanced
      exact (ne_of_lt hlt) (heq.2 ⟨hclosed, hbalanced⟩)
    · left
      have hchargeNe :
          (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) ≠
            ((Fintype.card I + 1 : ℕ) : ℝ) * gradedFockLoweringCharge M U := by
        intro hchargeEq
        exact hclosed ((gradedFockLoweringCharge_eq_iff_levelwise_creator_closed
          M U hshadow).1 hchargeEq)
      have hchargeLt :
          (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) <
            ((Fintype.card I + 1 : ℕ) : ℝ) * gradedFockLoweringCharge M U :=
        lt_of_le_of_ne (gradedFockLoweringCharge_lower_bound M U hshadow) hchargeNe
      exact (gradedFockLoweringCharge_lt_iff_exists_level_defect
        M U hshadow).1 hchargeLt
  · intro hdefect
    apply lt_of_le_of_ne hle
    intro hequality
    have hrigid := heq.1 hequality
    rcases hdefect with hlevel | ⟨i, hi⟩
    · have hchargeLt :=
        (gradedFockLoweringCharge_lt_iff_exists_level_defect M U hshadow).2 hlevel
      have hchargeEq :=
        (gradedFockLoweringCharge_eq_iff_levelwise_creator_closed
          M U hshadow).2 hrigid.1
      exact (ne_of_lt hchargeLt) hchargeEq
    · exact hi (hrigid.2 i)

end

end GaloisForLFunctions.HilbertMetric
