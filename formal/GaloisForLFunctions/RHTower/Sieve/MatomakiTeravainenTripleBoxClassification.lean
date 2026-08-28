import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxClassification

/-!
# Complete classification of one triple box

The source scalar dichotomy and exact triple-box constructors show that every admissible signed
triple box is literally a Proposition 2.2 Type-I/II or Type-II piece.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Every admissible minimal-geometric signed triple box has one exact Proposition 2.2 form. -/
theorem mtMinimalGeometricTripleBox_isProposition22Piece
    {X Y z0Real epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hz : z = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta start 0)
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hQ1 : mtGeometricLevel delta start i1.1 ≤ X ^ (1 / 4 - 2 * epsilon))
    (hQ3Q2 : mtGeometricLevel delta start i3.1 ≤
      mtGeometricLevel delta start i2.1)
    (hgeometry : mtGeometricLevel delta start i1.1 *
        mtGeometricLevel delta start i2.1 ^ 4 ≤ X ^ (1 - 2 * epsilon))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta start 0)
    (hchainCard : chain.toFinset.card ≤ Nat.floor (Real.log z / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hproduct : Y / 2 <
        mtMinimalGeometricTripleBoxLongM1
            delta start i1 i2 i3 chain eIndex *
          mtUpperAdicScale delta kIndex ∧
      mtMinimalGeometricTripleBoxLongM1
            delta start i1 i2 i3 chain eIndex *
          mtUpperAdicScale delta kIndex ≤ 4 * Y) :
    MTProposition22Piece X Y z0Real z delta epsilon
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
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
  rcases matomakiTeravainen_tripleTerm_typeI_II_or_typeII_finite
      (Q := Q) (S := chain.toFinset) hX hepsilon0 hepsilon
      (mtUpperAdicScale_pos hdelta eIndex).le
      (mtGeometricLevel_pos hdelta start i1.1).le
      (mtGeometricLevel_pos hdelta start i2.1).le
      (mtGeometricLevel_pos hdelta start i3.1).le
      hE hQ1 hQ3Q2 hgeometry hQone hQcap with htypeI_II | htypeII
  · have hsquare : mtMinimalGeometricTripleBoxTypeI_II_M1
          delta start i2 i3 eIndex ^ 2 *
        mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain ≤
          X ^ (1 - epsilon) := by
      calc
        mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex ^ 2 *
            mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain =
          (mtUpperAdicScale delta eIndex * Q i2 * Q i3) ^ 2 *
            (Q i1 * ∏ i ∈ chain.toFinset, Q i) := by
              rw [mtMinimalGeometricTripleBoxTypeI_II_M1,
                mtMinimalGeometricTripleBoxTypeI_II_M2]
              ring
        _ ≤ X ^ (1 - epsilon) := htypeI_II.1
    have hM2le : mtMinimalGeometricTripleBoxTypeI_II_M2
        delta start i1 chain ≤ X ^ (1 / 4 - epsilon) := by
      simpa [mtMinimalGeometricTripleBoxTypeI_II_M2, Q] using htypeI_II.2
    have hproductEq :
        mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
            mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
              mtUpperAdicScale delta kIndex =
          mtMinimalGeometricTripleBoxLongM1
              delta start i1 i2 i3 chain eIndex *
            mtUpperAdicScale delta kIndex := by
      rw [mtMinimalGeometricTripleBoxTypeI_II_M1,
        mtMinimalGeometricTripleBoxTypeI_II_M2,
        mtMinimalGeometricTripleBoxLongM1]
      ring
    have hproductI_II : Y / 2 <
          mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
            mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
              mtUpperAdicScale delta kIndex ∧
        mtMinimalGeometricTripleBoxTypeI_II_M1 delta start i2 i3 eIndex *
            mtMinimalGeometricTripleBoxTypeI_II_M2 delta start i1 chain *
              mtUpperAdicScale delta kIndex ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hfirstDilation : (1 + delta) ^ 3 ≤ 2 := hdilation _ (by omega)
    have hsecondDilation : (1 + delta) ^ (chain.length + 1) ≤ 2 :=
      hdilation _ (by omega)
    let data := mtMinimalGeometricTripleBoxTypeI_II_Data
      z0 D start hdelta hz0 hroot i1 i2 i3 chain hchain eIndex kIndex
      hfirstDilation hsecondDilation hsquare hM2le hproductI_II
    rw [← mtMinimalGeometricTripleBoxTypeI_II_Data_pieceAF_eq
      z0 D start hdelta hz0 hroot i1 i2 i3 chain hchain eIndex kIndex
      hfirstDilation hsecondDilation hsquare hM2le hproductI_II]
    exact MTProposition22Piece.typeI_II data
  · obtain ⟨I, hIS, hI, hIlower, hIupper⟩ := htypeII
    have hR : I.card ≤ Nat.floor (Real.log z / Real.log z0Real) :=
      (Finset.card_le_card hIS).trans hchainCard
    have hIMem : X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
        (∏ i ∈ I, Q i) ≤ z :=
      ⟨hIlower, by simpa [hz] using hIupper⟩
    have hproductEq :
        (∏ i ∈ I, Q i) *
            mtMinimalGeometricTripleBoxTypeIIM2
              delta start i1 i2 i3 chain I eIndex kIndex =
          mtMinimalGeometricTripleBoxLongM1
              delta start i1 i2 i3 chain eIndex *
            mtUpperAdicScale delta kIndex := by
      rw [mtMinimalGeometricTripleBoxTypeIIM2,
        mtMinimalGeometricTripleBoxLongM1,
        mtMinimalGeometricTripleBoxLongM1]
      have hsplit := prod_selected_mul_blockChainRemainder Q chain hIS
      dsimp [Q] at hsplit ⊢
      rw [← hsplit]
      ring
    have hproductII : Y / 2 <
          (∏ i ∈ I, Q i) *
            mtMinimalGeometricTripleBoxTypeIIM2
              delta start i1 i2 i3 chain I eIndex kIndex ∧
        (∏ i ∈ I, Q i) *
            mtMinimalGeometricTripleBoxTypeIIM2
              delta start i1 i2 i3 chain I eIndex kIndex ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hdilationII :
        (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 5) ≤ 2 :=
      hdilation _ (by
        have hlen := mtBlockChainRemainder_length_le chain I
        omega)
    let data := mtMinimalGeometricTripleBoxTypeIIData
      z0 D start hdelta hz0 hroot i1 i2 i3 chain hchain I hI eIndex kIndex
      hz0RealPos hz0RealLevel hR hIMem hproductII
    rw [← mtMinimalGeometricTripleBoxTypeIIData_pieceAF_eq
      z0 D start hdelta hz0 hroot i1 i2 i3 chain hchain I hIS hI eIndex kIndex
      hz0RealPos hz0RealLevel hR hdilationII hIMem hproductII]
    exact MTProposition22Piece.typeII data

end

end RHTower.Sieve
