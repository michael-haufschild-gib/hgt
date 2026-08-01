import GaloisForLFunctions.HTGeometry.UniversalInteractionRecurrenceConversionLaw
import GaloisForLFunctions.HTGeometry.RealPolynomialGenericity

/-!
# Generic projective independence from separable interactions
-/

open Set Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev SeparableInteractionParameterIndex (m n : ℕ) :=
  Fin (m + 1) ⊕ Fin (n + 1)

def finReindexedSeparableParameter
    {m n : ℕ}
    (q : Fin (Fintype.card (SeparableInteractionParameterIndex m n)) → ℝ) :
    SeparableInteractionParameterIndex m n → ℝ :=
  q ∘ Fintype.equivFin (SeparableInteractionParameterIndex m n)

def finReindexedSeparableRelationPolynomial
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (j : {k : Fin (m + 1) × Fin (n + 1) → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}) :
    MvPolynomial
      (Fin (Fintype.card (SeparableInteractionParameterIndex m n))) ℝ :=
  MvPolynomial.rename
      (Fintype.equivFin (SeparableInteractionParameterIndex m n))
    (separableSpectralRelationPolynomial left right j)

theorem eval_finReindexedSeparableRelationPolynomial
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (j : {k : Fin (m + 1) × Fin (n + 1) → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0})
    (q : Fin (Fintype.card (SeparableInteractionParameterIndex m n)) → ℝ) :
    MvPolynomial.eval q
        (finReindexedSeparableRelationPolynomial left right j) =
      separableSpectralRelation left right j
        (finReindexedSeparableParameter q) := by
  rw [finReindexedSeparableRelationPolynomial,
    MvPolynomial.eval_rename,
    eval_separableSpectralRelationPolynomial]
  rfl

def separableInteractionProjectiveGenericSet
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ) :
    Set
      (Fin (Fintype.card (SeparableInteractionParameterIndex m n)) → ℝ) :=
  {q | MaximallyProjectiveEnergy
    (separableInteractionEnergy left right
      (finReindexedSeparableParameter q))}

/-- Almost every separable rank-one diagonal interaction, in both the
Baire-category and Lebesgue senses, removes every nonzero balanced spectral
relation. -/
theorem separableInteractionProjectiveGenericSet_dense_residual_fullMeasure
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ) :
    Dense (separableInteractionProjectiveGenericSet left right) ∧
      separableInteractionProjectiveGenericSet left right ∈
        residual
          (Fin (Fintype.card
            (SeparableInteractionParameterIndex m n)) → ℝ) ∧
      volume (separableInteractionProjectiveGenericSet left right)ᶜ = 0 := by
  classical
  let J :=
    {k : Fin (m + 1) × Fin (n + 1) → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}
  letI : Countable J := by
    dsimp [J]
    infer_instance
  letI : Encodable J := Encodable.ofCountable J
  let P : ℕ → MvPolynomial
      (Fin (Fintype.card (SeparableInteractionParameterIndex m n))) ℝ :=
    fun a =>
      match (Encodable.decode a : Option J) with
      | none => 1
      | some j => finReindexedSeparableRelationPolynomial left right j
  obtain ⟨p₀, hmax, _hp₀⟩ :=
    exists_smallSeparableInteraction_maximallyProjective
      left right 1 zero_lt_one
  let q₀ : Fin (Fintype.card
      (SeparableInteractionParameterIndex m n)) → ℝ :=
    p₀ ∘ (Fintype.equivFin
      (SeparableInteractionParameterIndex m n)).symm
  have hreindex : finReindexedSeparableParameter q₀ = p₀ := by
    funext z
    simp [finReindexedSeparableParameter, q₀]
  have hP : ∀ a, P a ≠ 0 := by
    intro a
    unfold P
    split
    · simp
    · rename_i j hdecode
      have hrelation :
          separableSpectralRelation left right j p₀ ≠ 0 := by
        intro hzero
        apply j.property.2
        exact hmax j.1 j.property.1 (by
          simpa [separableSpectralRelation] using hzero)
      have heval :
          MvPolynomial.eval q₀
              (finReindexedSeparableRelationPolynomial left right j) ≠ 0 := by
        rw [eval_finReindexedSeparableRelationPolynomial, hreindex]
        exact hrelation
      intro hzero
      apply heval
      rw [hzero]
      simp
  have hset :
      separableInteractionProjectiveGenericSet left right =
        realPolynomialAvoidanceSet P := by
    ext q
    constructor
    · intro hq a
      unfold P
      split
      · simp
      · rename_i j hdecode
        rw [eval_finReindexedSeparableRelationPolynomial]
        intro hzero
        apply j.property.2
        exact hq j.1 j.property.1 (by
          simpa [separableSpectralRelation] using hzero)
    · intro hq k hbalanced hzero
      by_contra hk
      let j : J := ⟨k, hbalanced, hk⟩
      have hj := hq (Encodable.encode j)
      have heval :
          MvPolynomial.eval q
              (finReindexedSeparableRelationPolynomial left right j) = 0 := by
        rw [eval_finReindexedSeparableRelationPolynomial]
        simpa [separableSpectralRelation] using hzero
      apply hj
      simpa [P, Encodable.encodek, j] using heval
  rw [hset]
  exact realPolynomialAvoidanceSet_dense_residual_fullMeasure P hP

/-- The exceptional interactions remain null after restriction to any
parameter region, in particular every arbitrarily small norm ball. -/
theorem separableInteractionProjectiveGenericSet_local_fullMeasure
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (S : Set
      (Fin (Fintype.card (SeparableInteractionParameterIndex m n)) → ℝ)) :
    volume (S \ separableInteractionProjectiveGenericSet left right) = 0 := by
  apply measure_mono_null
    (Set.sdiff_subset_compl S
      (separableInteractionProjectiveGenericSet left right))
  exact
    (separableInteractionProjectiveGenericSet_dense_residual_fullMeasure
      left right).2.2

/-- Membership in the product-indexed generic set transfers to maximal
projective arithmetic after the canonical finite reindexing. -/
theorem mem_separableInteractionProjectiveGenericSet_maximallyProjective
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (q : Fin (Fintype.card
      (SeparableInteractionParameterIndex m n)) → ℝ)
    (hq : q ∈ separableInteractionProjectiveGenericSet left right) :
    MaximallyProjectiveEnergy
      (reindexedSeparableInteractionEnergy left right
        (finReindexedSeparableParameter q)) := by
  let e :
      Fin (m * n + m + n + 1) ≃
        Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans
      (@finProdFinEquiv (m + 1) (n + 1)).symm
  exact maximallyProjectiveEnergy_equiv e hq

/-- Every generic separable interaction realizes the complete
additive-to-multiplicative conversion: full temporal rank, at least `m*n`
new temporal directions, no residual balanced relation, and the universal
permutation collision floor at every replica order. -/
theorem mem_separableInteractionProjectiveGenericSet_fullConversion
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (q : Fin (Fintype.card
      (SeparableInteractionParameterIndex m n)) → ℝ)
    (hq : q ∈ separableInteractionProjectiveGenericSet left right) :
    projectiveTemporalRank
        (reindexedSeparableInteractionEnergy left right
          (finReindexedSeparableParameter q)) =
      m * n + m + n ∧
    m * n ≤
      projectiveTemporalRank
          (reindexedSeparableInteractionEnergy left right
            (finReindexedSeparableParameter q)) -
        projectiveTemporalRank
          (reindexedBipartiteProductEnergy left right) ∧
    Module.finrank ℚ
        (projectiveSpectralRelationRationalSpace
          (reindexedSeparableInteractionEnergy left right
            (finReindexedSeparableParameter q))) = 0 ∧
    ∀ (weight : Fin (m * n + m + n + 1) → ℝ),
      (∀ i, 0 < weight i) →
      ∀ r : ℕ,
        fidelityReplicaCollisionMass weight
            (reindexedSeparableInteractionEnergy left right
              (finReindexedSeparableParameter q)) r =
          fidelityReplicaPermutationFloor weight r := by
  have hmax :
      MaximallyProjectiveEnergy
        (reindexedSeparableInteractionEnergy left right
          (finReindexedSeparableParameter q)) := by
    exact mem_separableInteractionProjectiveGenericSet_maximallyProjective
      left right q hq
  have hrank :
      projectiveTemporalRank
          (reindexedSeparableInteractionEnergy left right
            (finReindexedSeparableParameter q)) =
        m * n + m + n :=
    projectiveTemporalRank_eq hmax
  have hbase :=
    bipartiteProduct_projectiveTemporalRank_le left right
  have hgain :
      m * n ≤
        projectiveTemporalRank
            (reindexedSeparableInteractionEnergy left right
              (finReindexedSeparableParameter q)) -
          projectiveTemporalRank
            (reindexedBipartiteProductEnergy left right) := by
    omega
  refine ⟨hrank, hgain,
    projectiveRelationRank_eq_zero_of_maximallyProjective _ hmax, ?_⟩
  intro weight hweight r
  exact
    ((all_fidelityReplicaCollisionMass_eq_floor_iff
      hweight
      (reindexedSeparableInteractionEnergy left right
        (finReindexedSeparableParameter q))).2 hmax) r

end

end GaloisForLFunctions.HTGeometry
