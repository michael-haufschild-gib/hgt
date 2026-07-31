import GaloisForLFunctions.HTGeometry.LBitTemporalDimensionLaw

/-!
# Symmetry obstruction to maximal l-bit recurrence rank

For a finite l-bit system, maximal temporal rank is attained exactly when all nonempty-support
coefficients are rationally linearly independent.  Consequently, any exact coefficient symmetry
that identifies two distinct nonempty supports forces strict rank loss.

The final statements apply this boundary to site permutations.  They make no claim that every
translation-invariant or permutation-invariant model has a particular smaller rank; only the
strict obstruction forced by one moved support is asserted.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal coefficient-count ceiling for a finite l-bit system. -/
theorem lbitTemporalRank_le_maximal
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitTemporalRank J ≤
      2 ^ Fintype.card I - 1 := by
  rw [lbitTemporalRank_eq]
  unfold lbitCoefficientSubspace
  calc
    Module.finrank ℚ
          (Submodule.span ℚ
            (Set.range
              (fun S : {S : Finset I // S.Nonempty} =>
                J S.1)))
        ≤ Fintype.card
            {S : Finset I // S.Nonempty} := by
          exact finrank_range_le_card
            (fun S : {S : Finset I // S.Nonempty} =>
              J S.1)
    _ = 2 ^ Fintype.card I - 1 :=
      card_nonemptyLBitSupports

/-- **Exact maximality criterion.**  A finite l-bit Hamiltonian has maximal temporal rank if and
only if its complete nonempty-support coefficient packet is rationally linearly independent. -/
theorem lbitTemporalRank_eq_maximal_iff_linearIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) :
    lbitTemporalRank J =
        2 ^ Fintype.card I - 1 ↔
      LinearIndependent ℚ
        (fun S : {S : Finset I // S.Nonempty} =>
          J S.1) := by
  constructor
  · intro hmax
    apply
      (linearIndependent_iff_card_eq_finrank_span :
        LinearIndependent ℚ
            (fun S : {S : Finset I // S.Nonempty} =>
              J S.1) ↔
          Fintype.card {S : Finset I // S.Nonempty} =
            Set.finrank ℚ
              (Set.range
                (fun S : {S : Finset I // S.Nonempty} =>
                  J S.1))).mpr
    calc
      Fintype.card {S : Finset I // S.Nonempty} =
          2 ^ Fintype.card I - 1 :=
        card_nonemptyLBitSupports
      _ = lbitTemporalRank J :=
        hmax.symm
      _ = Module.finrank ℚ
          (lbitCoefficientSubspace J) :=
        lbitTemporalRank_eq J
      _ = Set.finrank ℚ
          (Set.range
            (fun S : {S : Finset I // S.Nonempty} =>
              J S.1)) := by
        rfl
  · intro hIndependent
    exact lbitTemporalRank_eq_card J hIndependent

/-- Any exact collision between two distinct nonempty-support coefficients forces strict loss from
the maximal temporal rank. -/
theorem lbitTemporalRank_lt_maximal_of_coefficient_collision
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ)
    (S T : {S : Finset I // S.Nonempty})
    (hST : S ≠ T)
    (hcollision : J S.1 = J T.1) :
    lbitTemporalRank J <
      2 ^ Fintype.card I - 1 := by
  have hnotIndependent :
      ¬ LinearIndependent ℚ
        (fun A : {A : Finset I // A.Nonempty} =>
          J A.1) := by
    intro hIndependent
    exact hST (hIndependent.injective hcollision)
  have hne :
      lbitTemporalRank J ≠
        2 ^ Fintype.card I - 1 := by
    intro hmax
    exact hnotIndependent
      ((lbitTemporalRank_eq_maximal_iff_linearIndependent J).mp
        hmax)
  exact Nat.lt_of_le_of_ne
    (lbitTemporalRank_le_maximal J) hne

/-- A coefficient symmetry under a site permutation loses maximal rank as soon as one nonempty
support is genuinely moved. -/
theorem lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSupport
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (e : I ≃ I)
    (hsymmetry :
      ∀ S : Finset I,
        J (S.map e.toEmbedding) = J S)
    (S : Finset I) (hS : S.Nonempty)
    (hmoved : S.map e.toEmbedding ≠ S) :
    lbitTemporalRank J <
      2 ^ Fintype.card I - 1 := by
  let moved :
      {T : Finset I // T.Nonempty} :=
    ⟨S.map e.toEmbedding,
      Finset.map_nonempty.mpr hS⟩
  let original :
      {T : Finset I // T.Nonempty} :=
    ⟨S, hS⟩
  apply lbitTemporalRank_lt_maximal_of_coefficient_collision
    J moved original
  · intro heq
    apply hmoved
    exact congrArg Subtype.val heq
  · exact hsymmetry S

/-- Existential form: one moved nonempty support is enough to obstruct maximal rank. -/
theorem lbitTemporalRank_lt_maximal_of_permutation_symmetry
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (e : I ≃ I)
    (hsymmetry :
      ∀ S : Finset I,
        J (S.map e.toEmbedding) = J S)
    (hmoved :
      ∃ S : Finset I,
        S.Nonempty ∧ S.map e.toEmbedding ≠ S) :
    lbitTemporalRank J <
      2 ^ Fintype.card I - 1 := by
  obtain ⟨S, hSne, hSmoved⟩ := hmoved
  exact
    lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSupport
      J e hsymmetry S hSne hSmoved

/-- A nontrivial site permutation preserving all coefficients already creates a collision between
the two moved singleton supports, hence strict temporal-rank loss. -/
theorem lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSite
    {I : Type*} [Fintype I] [DecidableEq I]
    (J : Finset I → ℝ) (e : I ≃ I)
    (hsymmetry :
      ∀ S : Finset I,
        J (S.map e.toEmbedding) = J S)
    (i : I) (hi : e i ≠ i) :
    lbitTemporalRank J <
      2 ^ Fintype.card I - 1 := by
  apply
    lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSupport
      J e hsymmetry {i} (by simp)
  simp [hi]

end

end GaloisForLFunctions.HTGeometry
