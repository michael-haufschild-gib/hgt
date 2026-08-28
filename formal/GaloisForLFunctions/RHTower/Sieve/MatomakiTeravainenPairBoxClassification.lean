import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFinitePieceClassification

/-!
# Complete classification of one pair box

The scalar source dichotomy is combined with exact box constructors.  Every admissible signed pair
box is therefore literally a Proposition 2.2 Type-I or Type-II piece.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Selected recursive scales times complementary recursive scales recover the full chain product. -/
theorem prod_selected_mul_blockChainRemainder
    {t : ℕ} (Q : Fin t → ℝ) (chain : List (Fin t))
    {I : Finset (Fin t)} (hI : I ⊆ chain.toFinset) :
    (∏ i ∈ I, Q i) *
        (∏ i ∈ (mtBlockChainRemainder chain I).toFinset, Q i) =
      ∏ i ∈ chain.toFinset, Q i := by
  rw [mtBlockChainRemainder_toFinset]
  have hsplit := Finset.prod_sdiff (f := Q) hI
  simpa only [mul_comm] using hsplit

/-- Every admissible minimal-geometric signed pair box has one exact Proposition 2.2 form. -/
theorem mtMinimalGeometricPairBox_isProposition22Piece
    {X Y z0Real epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hz : z = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta start 0)
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hQ1 : mtGeometricLevel delta start i1.1 ≤ X ^ (1 / 4 - 2 * epsilon))
    (hQ2 : mtGeometricLevel delta start i2.1 ≤ X ^ (1 / 4 - 2 * epsilon))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta start 0)
    (hchainCard : chain.toFinset.card ≤ Nat.floor (Real.log z / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hproduct : Y / 2 <
        mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
          mtUpperAdicScale delta kIndex ∧
      mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
          mtUpperAdicScale delta kIndex ≤ 4 * Y) :
    MTProposition22Piece X Y z0Real z delta epsilon
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex) := by
  let Q : Fin (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun i => mtGeometricLevel delta start i.1
  have hQone : ∀ i ∈ chain.toFinset, 1 ≤ Q i := by
    intro i hi
    exact hrootOne.trans (mtMinimalGeometricSchedule_scale_mem hdelta start i).1
  have hQcap : ∀ i ∈ chain.toFinset, Q i ≤ X ^ (2 / 11 : ℝ) := by
    intro i hi
    rw [← hz]
    exact (mtMinimalGeometricSchedule_scale_mem hdelta start i).2.le
  rcases matomakiTeravainen_pairTerm_typeI_or_typeII_finite
      (Q := Q) (S := chain.toFinset) hX hepsilon0 hepsilon
      (mtUpperAdicScale_pos hdelta eIndex).le
      (mtGeometricLevel_pos hdelta start i1.1).le
      (mtGeometricLevel_pos hdelta start i2.1).le
      hE hQ1 hQ2 hQone hQcap with htypeI | htypeII
  · have hM1le : mtMinimalGeometricPairBoxM1
        delta start i1 i2 chain eIndex ≤ X ^ (1 / 2 + epsilon) := by
      calc
        mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex =
            mtUpperAdicScale delta eIndex * Q i1 * Q i2 *
              ∏ i ∈ chain.toFinset, Q i := by
          rw [mtMinimalGeometricPairBoxM1]
          ring
        _ ≤ X ^ (1 / 2 + epsilon) := htypeI
    have hdilationI : (1 + delta) ^ (chain.length + 3) ≤ 2 :=
      hdilation _ (by omega)
    let data := mtMinimalGeometricPairBoxTypeIData
      z0 D start hdelta hz0 hroot i1 i2 chain hchain eIndex kIndex
      hdilationI hM1le hproduct
    rw [← mtMinimalGeometricPairBoxTypeIData_pieceAF_eq
      z0 D start hdelta hz0 hroot i1 i2 chain hchain eIndex kIndex
      hdilationI hM1le hproduct]
    exact MTProposition22Piece.typeI data
  · obtain ⟨I, hIS, hI, hIlower, hIupper⟩ := htypeII
    have hR : I.card ≤ Nat.floor (Real.log z / Real.log z0Real) :=
      (Finset.card_le_card hIS).trans hchainCard
    have hIMem : X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
        (∏ i ∈ I, Q i) ≤ z := by
      exact ⟨hIlower, by simpa [hz] using hIupper⟩
    have hproductEq :
        (∏ i ∈ I, Q i) *
            mtMinimalGeometricPairBoxTypeIIM2
              delta start i1 i2 chain I eIndex kIndex =
          mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
            mtUpperAdicScale delta kIndex := by
      rw [mtMinimalGeometricPairBoxTypeIIM2, mtMinimalGeometricPairBoxM1,
        mtMinimalGeometricPairBoxM1]
      have hsplit := prod_selected_mul_blockChainRemainder Q chain hIS
      dsimp [Q] at hsplit ⊢
      rw [← hsplit]
      ring
    have hproductII : Y / 2 <
          (∏ i ∈ I, Q i) *
            mtMinimalGeometricPairBoxTypeIIM2
              delta start i1 i2 chain I eIndex kIndex ∧
        (∏ i ∈ I, Q i) *
            mtMinimalGeometricPairBoxTypeIIM2
              delta start i1 i2 chain I eIndex kIndex ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hdilationII :
        (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 4) ≤ 2 :=
      hdilation _ (by
        have hlen := mtBlockChainRemainder_length_le chain I
        omega)
    let data := mtMinimalGeometricPairBoxTypeIIData
      z0 D start hdelta hz0 hroot i1 i2 chain hchain I hI eIndex kIndex
      hz0RealPos hz0RealLevel hR hIMem hproductII
    rw [← mtMinimalGeometricPairBoxTypeIIData_pieceAF_eq
      z0 D start hdelta hz0 hroot i1 i2 chain hchain I hIS hI eIndex kIndex
      hz0RealPos hz0RealLevel hR hdilationII hIMem hproductII]
    exact MTProposition22Piece.typeII data

end

end RHTower.Sieve
