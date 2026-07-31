import GaloisForLFunctions.HTGeometry.AnchoredProjectiveRecurrenceConservationLaw
import GaloisForLFunctions.HTGeometry.LBitReplicaInteractionFractureLaw

/-!
# Exact recurrence-constraint budget of localized l-bit spectra

For every finite binary l-bit Hamiltonian, the complete projective spectral
capacity splits exactly into rationally independent temporal directions and
balanced exact recurrence relations. A noninteracting localized spectrum
therefore carries exponentially many independent recurrence constraints,
whereas a full-rank interacting l-bit spectrum carries none, even though
both remain diagonal in the same localized configuration basis.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable local instance lbitRecurrenceConstraintFintypeForallBool
    {I : Type*} [Fintype I] :
    Fintype (I → Bool) :=
  Fintype.ofFinite _

/-- **Localized recurrence budget.** Temporal rank and exact balanced
relation rank exhaust the `2^N - 1` projective character directions of
every finite `N`-mode l-bit spectrum. -/
theorem lbitTemporalRank_add_relationRank
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitTemporalRank J +
        Module.finrank ℚ
          (projectiveSpectralRelationRationalSpace
            (lbitEnergy J)) =
      2 ^ Fintype.card I - 1 := by
  have h :=
    anchoredTemporalRank_add_relationRank
      (lbitEnergy J) (lbitZeroConfiguration : I → Bool)
  have hgap :
      anchoredGapSubspace
          (lbitEnergy J) (lbitZeroConfiguration : I → Bool) =
        lbitGapSubspace J := by
    rfl
  rw [show anchoredTemporalRank
      (lbitEnergy J) (lbitZeroConfiguration : I → Bool) =
        lbitTemporalRank J by
      unfold anchoredTemporalRank lbitTemporalRank
      rw [hgap]] at h
  have hcard :
      Fintype.card (I → Bool) = 2 ^ Fintype.card I := by
    rw [Fintype.card_eq_nat_card, Nat.card_fun]
    norm_num [Nat.card_eq_fintype_card]
  rw [hcard] at h
  exact h

/-- Every noninteracting `N`-mode localized spectrum carries at least
`2^N - 1 - N` rationally independent exact projective recurrence
constraints. -/
theorem lbitNoninteracting_relationRank_lower_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : ∀ S, 1 < S.card → J S = 0) :
    2 ^ Fintype.card I - 1 - Fintype.card I ≤
      Module.finrank ℚ
        (projectiveSpectralRelationRationalSpace
          (lbitEnergy J)) := by
  have hconservation :=
    lbitTemporalRank_add_relationRank J
  have hrank := lbitNoninteracting_temporalRank_le J hJ
  omega

/-- The packet of one-body l-bit coefficients. -/
def lbitSingletonCoefficientPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) : I → ℝ :=
  fun i => J {i}

/-- If every genuine interaction coefficient vanishes, the coefficient
subspace is exactly the rational span of the one-body coefficients. -/
theorem lbitCoefficientSubspace_eq_singletonSpan
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : ∀ S, 1 < S.card → J S = 0) :
    lbitCoefficientSubspace J =
      Submodule.span ℚ
        (Set.range (lbitSingletonCoefficientPacket J)) := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro z ⟨S, rfl⟩
    by_cases hcard : 1 < S.1.card
    · change J S.1 ∈ _
      rw [hJ S.1 hcard]
      exact Submodule.zero_mem _
    · have hcardone : S.1.card = 1 := by
        have hpos := S.2.card_pos
        omega
      obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcardone
      apply Submodule.subset_span
      refine ⟨i, ?_⟩
      simp [lbitSingletonCoefficientPacket, hi]
  · apply Submodule.span_le.2
    rintro z ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨{i}, by simp⟩, ?_⟩
    rfl

/-- A noninteracting localized spectrum with rationally independent one-body
energies has exactly one temporal direction per localized mode. -/
theorem lbitNoninteracting_temporalRank_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : ∀ S, 1 < S.card → J S = 0)
    (hIndependent :
      LinearIndependent ℚ
        (lbitSingletonCoefficientPacket J)) :
    lbitTemporalRank J = Fintype.card I := by
  rw [lbitTemporalRank_eq,
    lbitCoefficientSubspace_eq_singletonSpan J hJ]
  exact finrank_span_eq_card hIndependent

/-- Under the same independence hypothesis, the noninteracting localized
spectrum carries exactly `2^N - 1 - N` independent projective recurrence
constraints. -/
theorem lbitNoninteracting_relationRank_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hJ : ∀ S, 1 < S.card → J S = 0)
    (hIndependent :
      LinearIndependent ℚ
        (lbitSingletonCoefficientPacket J)) :
    Module.finrank ℚ
        (projectiveSpectralRelationRationalSpace
          (lbitEnergy J)) =
      2 ^ Fintype.card I - 1 - Fintype.card I := by
  have hconservation := lbitTemporalRank_add_relationRank J
  have hrank :=
    lbitNoninteracting_temporalRank_eq J hJ hIndependent
  rw [hrank] at hconservation
  exact Nat.eq_sub_of_add_eq (by
    simpa [Nat.add_comm] using hconservation)

/-- A full-temporal-rank localized l-bit spectrum has no nonzero rational
projective recurrence-relation direction. -/
theorem lbitFullTemporalRank_relationRank_eq_zero
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hfull :
      lbitTemporalRank J = 2 ^ Fintype.card I - 1) :
    Module.finrank ℚ
        (projectiveSpectralRelationRationalSpace
          (lbitEnergy J)) = 0 := by
  have hconservation :=
    lbitTemporalRank_add_relationRank J
  omega

/-- Equivalently, a full-temporal-rank localized spectrum's rational
projective recurrence-relation space is the bottom submodule. -/
theorem lbitFullTemporalRank_relationSpace_eq_bot
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (hfull :
      lbitTemporalRank J = 2 ^ Fintype.card I - 1) :
    projectiveSpectralRelationRationalSpace
        (lbitEnergy J) = ⊥ := by
  rw [← Submodule.finrank_eq_zero]
  exact lbitFullTemporalRank_relationRank_eq_zero J hfull

end

end GaloisForLFunctions.HTGeometry
