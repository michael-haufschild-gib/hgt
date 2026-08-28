import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenSeparatedBoxBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICardinality

/-!
# Pair-box classification for independent Harman and Buchstab schedules

Outer pair cells and recursive chains are kept separate.  This file supplies exact supported
factors and the resulting Proposition 2.2 Type-I/Type-II classification.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

def mtSeparatedPairBoxLongScale {u t : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (recStart : ℕ)
    (i1 i2 : Fin u) (chain : List (Fin t)) (eIndex : ℕ) : ℝ :=
  ((mtAdjacentBlockLowerScale endpoint i1.1 *
      mtAdjacentBlockLowerScale endpoint i2.1) *
      ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
    mtUpperAdicScale delta eIndex

theorem mtSeparatedPairBoxLongScale_pos
    {u t : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hdelta : 0 < delta)
    (recStart : ℕ) (i1 i2 : Fin u) (chain : List (Fin t)) (eIndex : ℕ) :
    0 < mtSeparatedPairBoxLongScale endpoint delta recStart i1 i2 chain eIndex := by
  unfold mtSeparatedPairBoxLongScale
  have hL1 : 0 < mtAdjacentBlockLowerScale endpoint i1.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i1.1; omega : 0 < endpoint i1.1 - 1)
  have hL2 : 0 < mtAdjacentBlockLowerScale endpoint i2.1 := by
    unfold mtAdjacentBlockLowerScale
    exact_mod_cast (by have := hendpoint i2.1; omega : 0 < endpoint i2.1 - 1)
  exact mul_pos
    (mul_pos (mul_pos hL1 hL2)
      (Finset.prod_pos fun j _ => mtGeometricLevel_pos hdelta recStart j.1))
    (mtUpperAdicScale_pos hdelta eIndex)

/-- Independent-schedule pair long factor is dyadically supported at its exact product scale. -/
theorem mtSeparatedPairLongAF_scaleSupported_dyadic
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 : Fin u)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup) (eIndex : ℕ)
    (hdilation : (1 + delta) ^ (chain.length + 3) ≤ 2) :
    MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex)
      (mtSeparatedPairBoxLongScale endpoint delta recStart i1 i2 chain eIndex)
      (2 * mtSeparatedPairBoxLongScale endpoint delta recStart
        i1 i2 chain eIndex) := by
  let Q : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) → ℝ :=
    fun i => mtGeometricLevel delta recStart i.1
  let L := mtAdjacentBlockLowerScale endpoint i1.1 *
    mtAdjacentBlockLowerScale endpoint i2.1
  let M := mtSeparatedPairBoxLongScale endpoint delta recStart i1 i2 chain eIndex
  have hrecBlock : ∀ i,
      MTRealScaleSupported (mtPrimeBlockAF (data.block i))
        (Q i) (Q i * (1 + delta)) := by
    intro i
    rw [hblocks]
    exact mtMinimalGeometricBlock_scaleSupported
      z0 D recStart hdelta hz0 hroot i
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hraw : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex)
      M
      (((mtAdjacentBlockUpperScale endpoint i1.1 *
          mtAdjacentBlockUpperScale endpoint i2.1) *
          ∏ j ∈ chain.toFinset, (Q j * (1 + delta))) *
        ((1 + delta) * mtUpperAdicScale delta eIndex)) := by
    intro n hn
    simpa only [M, mtSeparatedPairBoxLongScale, L, Q] using
      (mtBlockChainLongAF_scaleSupported
        (mtHarmanPairSourceCell_scaleSupported hendpoint P i1 i2)
        hrecBlock (fun i => (mtGeometricLevel_pos hdelta recStart i.1).le)
        hL hchain z0 D eIndex (mtUpperAdicScale_pos hdelta eIndex).le) hn
  have hnormalized : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex)
      M ((1 + delta) ^ (chain.length + 3) * M) := by
    intro n hn
    have hs := hraw hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans ?_⟩
    have hb : 0 ≤ 1 + delta := by linarith
    have hprod : (∏ j ∈ chain.toFinset, (Q j * (1 + delta))) =
        (1 + delta) ^ chain.length * ∏ j ∈ chain.toFinset, Q j :=
      prod_mul_constant_chain_toFinset Q (1 + delta) hchain
    rw [hprod]
    have hU2 : 0 ≤ mtAdjacentBlockUpperScale endpoint i2.1 := Nat.cast_nonneg _
    have hL1 : 0 ≤ mtAdjacentBlockLowerScale endpoint i1.1 := Nat.cast_nonneg _
    have hchainScale : 0 ≤ (1 + delta) ^ chain.length *
        ∏ j ∈ chain.toFinset, Q j := by
      exact mul_nonneg (pow_nonneg hb _)
        (Finset.prod_nonneg fun j _ => (mtGeometricLevel_pos hdelta recStart j.1).le)
    have heScale : 0 ≤ (1 + delta) * mtUpperAdicScale delta eIndex :=
      mul_nonneg hb (mtUpperAdicScale_pos hdelta eIndex).le
    have houter : mtAdjacentBlockUpperScale endpoint i1.1 *
          mtAdjacentBlockUpperScale endpoint i2.1 ≤
        ((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
          ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1) :=
      mul_le_mul (hband i1.1) (hband i2.1) hU2 (mul_nonneg hb hL1)
    calc
      (mtAdjacentBlockUpperScale endpoint i1.1 *
            mtAdjacentBlockUpperScale endpoint i2.1) *
          ((1 + delta) ^ chain.length * ∏ j ∈ chain.toFinset, Q j) *
          ((1 + delta) * mtUpperAdicScale delta eIndex) ≤
        (((1 + delta) * mtAdjacentBlockLowerScale endpoint i1.1) *
            ((1 + delta) * mtAdjacentBlockLowerScale endpoint i2.1)) *
          ((1 + delta) ^ chain.length * ∏ j ∈ chain.toFinset, Q j) *
          ((1 + delta) * mtUpperAdicScale delta eIndex) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right houter hchainScale) heScale
      _ = (1 + delta) ^ (chain.length + 3) * M := by
        rw [show chain.length + 3 = chain.length + 2 + 1 by omega,
          pow_succ, pow_add]
        dsimp [M, mtSeparatedPairBoxLongScale, Q]
        ring
  apply MTRealScaleSupported.dyadic_of_dilation hnormalized
  · exact (mtSeparatedPairBoxLongScale_pos hendpoint hdelta
      recStart i1 i2 chain eIndex).le
  · exact hdilation

theorem mtSeparatedPairLongAF_polynomialDivisorBounded
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i1 i2 : Fin u)
    {chain : List (Fin t)} (hchain : chain.Nodup)
    (z0 D : ℕ) (delta : ℝ) (eIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex n) := by
  exact mtBlockChainLongAF_polynomialDivisorBounded
    (mtHarmanPairCellCoefficient_polynomialDivisorBounded
      (mtHarmanSourceBlock endpoint P i1) (mtHarmanSourceBlock endpoint P i2))
    hchain z0 D delta eIndex

def mtSeparatedPairTypeIIBetaAF {u t : ℕ}
    (endpoint : ℕ → ℕ) (P : Finset ℕ) (data : MTFiniteIterationSourceData t)
    (i1 i2 : Fin u) (chain : List (Fin t)) (I : Finset (Fin t))
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    (mtBlockChainLongAF
      (mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P i1)
        (mtHarmanSourceBlock endpoint P i2))
      data.block (mtBlockChainRemainder chain I) z0 D delta eIndex *
      mtUpperAdicOneAF delta kIndex)

def mtSeparatedPairTypeIIM2 {u t : ℕ}
    (endpoint : ℕ → ℕ) (delta : ℝ) (recStart : ℕ)
    (i1 i2 : Fin u) (chain : List (Fin t)) (I : Finset (Fin t))
    (eIndex kIndex : ℕ) : ℝ :=
  mtSeparatedPairBoxProductScale endpoint delta recStart i1 i2
    (mtBlockChainRemainder chain I) eIndex kIndex

theorem mtSeparatedPairTypeIIM2_pos
    {u t : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i) (hdelta : 0 < delta)
    (recStart : ℕ) (i1 i2 : Fin u) (chain : List (Fin t)) (I : Finset (Fin t))
    (eIndex kIndex : ℕ) :
    0 < mtSeparatedPairTypeIIM2 endpoint delta recStart
      i1 i2 chain I eIndex kIndex := by
  unfold mtSeparatedPairTypeIIM2 mtSeparatedPairBoxProductScale
  exact mul_pos
    (mtSeparatedPairBoxLongScale_pos hendpoint hdelta recStart i1 i2
      (mtBlockChainRemainder chain I) eIndex)
    (mtUpperAdicScale_pos hdelta kIndex)

theorem mtSeparatedPairTypeIIBetaAF_scaleSupported
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 : Fin u)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 4) ≤ 2) :
    MTRealScaleSupported
      (mtSeparatedPairTypeIIBetaAF endpoint P data i1 i2 chain I
        z0 D delta eIndex kIndex)
      (mtSeparatedPairTypeIIM2 endpoint delta recStart
        i1 i2 chain I eIndex kIndex)
      (2 * mtSeparatedPairTypeIIM2 endpoint delta recStart
        i1 i2 chain I eIndex kIndex) := by
  let remainder := mtBlockChainRemainder chain I
  let U := mtBlockChainAdicBoxAF
    (mtHarmanPairCellCoefficient
      (mtHarmanSourceBlock endpoint P i1)
      (mtHarmanSourceBlock endpoint P i2))
    data.block remainder z0 D delta eIndex kIndex
  have hsigned : MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block remainder z0 D delta eIndex kIndex)
      (mtSeparatedPairTypeIIM2 endpoint delta recStart
        i1 i2 chain I eIndex kIndex)
      (2 * mtSeparatedPairTypeIIM2 endpoint delta recStart
        i1 i2 chain I eIndex kIndex) := by
    intro n hn
    have hs := (mtSignedSeparatedPairBox_scaleSupported_commonProductCollar
      (eta := 1) hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks i1 i2
      (mtBlockChainRemainder_nodup hchain I) remainder.length eIndex kIndex
      (le_refl _) (by
        convert hdilation using 1
        norm_num [remainder])) hn
    norm_num at hs
    simpa [mtSeparatedPairTypeIIM2, remainder] using hs
  have hunsigned : MTRealScaleSupported U
      (mtSeparatedPairTypeIIM2 endpoint delta recStart i1 i2 chain I eIndex kIndex)
      (2 * mtSeparatedPairTypeIIM2 endpoint delta recStart
        i1 i2 chain I eIndex kIndex) := by
    intro n hn
    apply hsigned
    change (((-1 : ℂ) ^ remainder.length) • U) n ≠ 0
    change ((-1 : ℂ) ^ remainder.length * U n) ≠ 0
    exact mul_ne_zero (by simp) hn
  intro n hn
  apply (MTRealScaleSupported.smul hunsigned ((-1 : ℂ) ^ chain.length))
  simpa only [mtSeparatedPairTypeIIBetaAF, U, mtBlockChainAdicBoxAF,
    mtBlockChainLongAF, mtBlockChainCoefficientAF, remainder] using hn

theorem mtSeparatedPairTypeIIBetaAF_polynomialDivisorBounded
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i1 i2 : Fin u)
    {chain : List (Fin t)} (hchain : chain.Nodup) (I : Finset (Fin t))
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtSeparatedPairTypeIIBetaAF endpoint P data i1 i2 chain I
        z0 D delta eIndex kIndex n) := by
  have hone : MTPolynomialDivisorBounded (fun _ : ℕ => (1 : ℂ)) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    simp
  have hlong := mtSeparatedPairLongAF_polynomialDivisorBounded
    endpoint P data i1 i2 (mtBlockChainRemainder_nodup hchain I)
    z0 D delta eIndex
  have hk : MTPolynomialDivisorBounded (fun n => mtUpperAdicOneAF delta kIndex n) :=
    mtRealIntervalAF_polynomialDivisorBounded hone _ _
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul
    (MTPolynomialDivisorBounded.arithmeticFunction_mul hlong hk)
    ((-1 : ℂ) ^ chain.length)

/-- Selected recursive blocks factor literally from an independent-schedule signed pair box. -/
theorem mtSignedSeparatedPairBox_eq_selected_mul_typeIIBeta
    {u t : ℕ} (endpoint : ℕ → ℕ) (P : Finset ℕ)
    (data : MTFiniteIterationSourceData t) (i1 i2 : Fin u)
    (chain : List (Fin t)) (I : Finset (Fin t)) (hI : I ⊆ chain.toFinset)
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex kIndex =
      mtPrimeBlockFamilyAF data.block I *
        mtSeparatedPairTypeIIBetaAF endpoint P data i1 i2 chain I
          z0 D delta eIndex kIndex := by
  rw [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtSeparatedPairTypeIIBetaAF, mtBlockChainLongAF,
    mtBlockChainCoefficientAF, mtPrimeBlockFamilyAF_split data.block hI,
    mtBlockChainRemainder_toFinset]
  rw [mul_smul_comm]
  congr 1
  ring

/-- Every admissible independent-schedule pair box is exactly Type I or Type II. -/
theorem mtSeparatedPairBox_isProposition22Piece
    {u : ℕ} {endpoint : ℕ → ℕ} {delta : ℝ}
    (hendpoint : ∀ i, 2 ≤ endpoint i)
    (hband : ∀ i, mtAdjacentBlockUpperScale endpoint i ≤
      (1 + delta) * mtAdjacentBlockLowerScale endpoint i)
    (P : Finset ℕ) {X Y z0Real epsilon : ℝ}
    (z0 D recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (i1 i2 : Fin u)
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hE : mtUpperAdicScale delta eIndex ≤ X ^ (epsilon / 4))
    (hQ1 : mtAdjacentBlockLowerScale endpoint i1.1 ≤
      X ^ (1 / 4 - 2 * epsilon))
    (hQ2 : mtAdjacentBlockLowerScale endpoint i2.1 ≤
      X ^ (1 / 4 - 2 * epsilon))
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainBound : 1 < z0Real ∨ chain.toFinset.card ≤
      Nat.floor (Real.log recRoot / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hproduct : Y / 2 <
        mtSeparatedPairBoxProductScale endpoint delta recStart
          i1 i2 chain eIndex kIndex ∧
      mtSeparatedPairBoxProductScale endpoint delta recStart
          i1 i2 chain eIndex kIndex ≤ 4 * Y) :
    MTProposition22Piece X Y z0Real recRoot delta epsilon
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (mtHarmanSourceBlock endpoint P i1)
          (mtHarmanSourceBlock endpoint P i2))
        data.block chain z0 D delta eIndex kIndex) := by
  let Q : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) → ℝ :=
    fun i => mtGeometricLevel delta recStart i.1
  have hQone : ∀ i ∈ chain.toFinset, 1 ≤ Q i := by
    intro i hi
    exact hrootOne.trans (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).1
  have hQcap : ∀ i ∈ chain.toFinset, Q i ≤ X ^ (2 / 11 : ℝ) := by
    intro i hi
    rw [← hrecRoot]
    exact (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).2.le
  rcases matomakiTeravainen_pairTerm_typeI_or_typeII_finite
      (Q := Q) (S := chain.toFinset) hX hepsilon0 hepsilon
      (mtUpperAdicScale_pos hdelta eIndex).le
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hE hQ1 hQ2 hQone hQcap with htypeI | htypeII
  · let M1 := mtSeparatedPairBoxLongScale endpoint delta recStart
      i1 i2 chain eIndex
    let M2 := mtUpperAdicScale delta kIndex
    let F0 := mtBlockChainLongAF
      (mtHarmanPairCellCoefficient
        (mtHarmanSourceBlock endpoint P i1)
        (mtHarmanSourceBlock endpoint P i2))
      data.block chain z0 D delta eIndex
    let F := ((-1 : ℂ) ^ chain.length) • F0
    have hM1le : M1 ≤ X ^ (1 / 2 + epsilon) := by
      calc
        M1 = mtUpperAdicScale delta eIndex *
            mtAdjacentBlockLowerScale endpoint i1.1 *
            mtAdjacentBlockLowerScale endpoint i2.1 *
            ∏ i ∈ chain.toFinset, Q i := by
          dsimp [M1, mtSeparatedPairBoxLongScale, Q]
          ring
        _ ≤ X ^ (1 / 2 + epsilon) := htypeI
    have hsupport0 : MTRealScaleSupported F0 M1 (2 * M1) := by
      exact mtSeparatedPairLongAF_scaleSupported_dyadic
        hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
        i1 i2 hchain eIndex (hdilation _ (by omega))
    have hsupport : MTRealScaleSupported F M1 (2 * M1) := by
      exact MTRealScaleSupported.smul hsupport0 ((-1 : ℂ) ^ chain.length)
    have hbounded0 : MTPolynomialDivisorBounded (fun n => F0 n) := by
      exact mtSeparatedPairLongAF_polynomialDivisorBounded
        endpoint P data i1 i2 hchain z0 D delta eIndex
    have hbounded : MTPolynomialDivisorBounded (fun n => F n) :=
      MTPolynomialDivisorBounded.arithmeticFunction_smul
        hbounded0 ((-1 : ℂ) ^ chain.length)
    have hproductI : Y / 2 < M1 * M2 ∧ M1 * M2 ≤ 4 * Y := by
      simpa [M1, M2, mtSeparatedPairBoxProductScale,
        mtSeparatedPairBoxLongScale] using hproduct
    let pieceData := mtTypeIPieceDataOfSupported (delta := delta) F
      (mtSeparatedPairBoxLongScale_pos hendpoint hdelta
        recStart i1 i2 chain eIndex)
      (mtUpperAdicScale_pos hdelta kIndex)
      hsupport hbounded hM1le hproductI
    have hpiece : pieceData.pieceAF =
        mtSignedBlockChainAdicBoxAF
          (mtHarmanPairCellCoefficient
            (mtHarmanSourceBlock endpoint P i1)
            (mtHarmanSourceBlock endpoint P i2))
          data.block chain z0 D delta eIndex kIndex := by
      dsimp only [pieceData]
      rw [mtTypeIPieceDataOfSupported_pieceAF_eq]
      dsimp [F, F0, M2]
      rw [smul_mul_assoc]
      rfl
    rw [← hpiece]
    exact MTProposition22Piece.typeI pieceData
  · obtain ⟨I, hIS, hI, hIlower, hIupper⟩ := htypeII
    have hR : I.card ≤ Nat.floor (Real.log recRoot / Real.log z0Real) := by
      rcases hchainBound with hz0RealOne | hchainCard
      · apply card_le_floor_log_div_log_of_one_lt_of_prod_le I Q hz0RealOne
        · intro i hi
          exact hz0RealLevel.trans
            (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).1
        · simpa [hrecRoot] using hIupper
      · exact (Finset.card_le_card hIS).trans hchainCard
    have hIMem : X ^ (epsilon / 2) ≤ ∏ i ∈ I, Q i ∧
        (∏ i ∈ I, Q i) ≤ recRoot :=
      ⟨hIlower, by simpa [hrecRoot] using hIupper⟩
    let M2 := mtSeparatedPairTypeIIM2 endpoint delta recStart
      i1 i2 chain I eIndex kIndex
    let betaAF := mtSeparatedPairTypeIIBetaAF endpoint P data i1 i2 chain I
      z0 D delta eIndex kIndex
    have hproductEq :
        (∏ i ∈ I, Q i) * M2 =
          mtSeparatedPairBoxProductScale endpoint delta recStart
            i1 i2 chain eIndex kIndex := by
      have hsplit := prod_selected_mul_blockChainRemainder Q chain hIS
      dsimp [M2, mtSeparatedPairTypeIIM2, mtSeparatedPairBoxProductScale,
        Q] at hsplit ⊢
      rw [← hsplit]
      ring
    have hproductII : Y / 2 < (∏ i ∈ I, Q i) * M2 ∧
        (∏ i ∈ I, Q i) * M2 ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hbetaSupport : MTRealScaleSupported betaAF M2 (2 * M2) := by
      exact mtSeparatedPairTypeIIBetaAF_scaleSupported
        hendpoint hband P z0 D recStart hdelta hz0 hroot data hblocks
        i1 i2 hchain I eIndex kIndex (hdilation _ (by
          have hlen := mtBlockChainRemainder_length_le chain I
          omega))
    have hbetaBounded : MTPolynomialDivisorBounded (fun n => betaAF n) := by
      exact mtSeparatedPairTypeIIBetaAF_polynomialDivisorBounded
        endpoint P data i1 i2 hchain I z0 D delta eIndex kIndex
    let pieceData := mtMinimalGeometricTypeIIData
      z0 D recStart hdelta hz0 hroot I hI hz0RealPos hz0RealLevel hR
      (fun n => betaAF n)
      (mtSeparatedPairTypeIIM2_pos hendpoint hdelta
        recStart i1 i2 chain I eIndex kIndex)
      hbetaBounded hIMem hproductII
    have hpiece : pieceData.pieceAF =
        mtSignedBlockChainAdicBoxAF
          (mtHarmanPairCellCoefficient
            (mtHarmanSourceBlock endpoint P i1)
            (mtHarmanSourceBlock endpoint P i2))
          data.block chain z0 D delta eIndex kIndex := by
      calc
        pieceData.pieceAF =
            mtPrimeBlockFamilyAF
                (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
                  z0 D recStart delta recRoot hdelta hz0 hroot).block I *
              mtRealIntervalAF (fun n => betaAF n) M2 (2 * M2) := by
          exact mtMinimalGeometricTypeIIData_pieceAF_eq
            z0 D recStart hdelta hz0 hroot I hI hz0RealPos hz0RealLevel hR
            (fun n => betaAF n)
            (mtSeparatedPairTypeIIM2_pos hendpoint hdelta
              recStart i1 i2 chain I eIndex kIndex)
            hbetaBounded hIMem hproductII
        _ = mtPrimeBlockFamilyAF data.block I * betaAF := by
          rw [← hblocks, mtRealIntervalAF_coe_eq_of_scaleSupported hbetaSupport]
        _ = mtSignedBlockChainAdicBoxAF
              (mtHarmanPairCellCoefficient
                (mtHarmanSourceBlock endpoint P i1)
                (mtHarmanSourceBlock endpoint P i2))
              data.block chain z0 D delta eIndex kIndex :=
          (mtSignedSeparatedPairBox_eq_selected_mul_typeIIBeta
            endpoint P data i1 i2 chain I hIS z0 D delta eIndex kIndex).symm
    rw [← hpiece]
    exact MTProposition22Piece.typeII pieceData

end

end RHTower.Sieve
