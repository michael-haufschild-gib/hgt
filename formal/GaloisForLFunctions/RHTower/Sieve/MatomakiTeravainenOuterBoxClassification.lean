import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAlignedBoxFamilyClassification
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIICardinality

/-!
# Classification with one narrow outer coefficient

Base and one-prime Harman terms have one narrow outer coefficient rather than pair/triple cells.
The recursive subset dichotomy still gives exact Type-I or Type-II pieces.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

def mtOuterBlockChainLongScale {t : ℕ} (L delta : ℝ) (recStart : ℕ)
    (chain : List (Fin t)) (eIndex : ℕ) : ℝ :=
  (L * ∏ j ∈ chain.toFinset, mtGeometricLevel delta recStart j.1) *
    mtUpperAdicScale delta eIndex

def mtOuterBlockChainProductScale {t : ℕ} (L delta : ℝ) (recStart : ℕ)
    (chain : List (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  mtOuterBlockChainLongScale L delta recStart chain eIndex *
    mtUpperAdicScale delta kIndex

theorem mtOuterBlockChainLongScale_pos
    {t : ℕ} {L delta : ℝ} (hL : 0 < L) (hdelta : 0 < delta)
    (recStart : ℕ) (chain : List (Fin t)) (eIndex : ℕ) :
    0 < mtOuterBlockChainLongScale L delta recStart chain eIndex := by
  unfold mtOuterBlockChainLongScale
  exact mul_pos
    (mul_pos hL (Finset.prod_pos fun j _ =>
      mtGeometricLevel_pos hdelta recStart j.1))
    (mtUpperAdicScale_pos hdelta eIndex)

/-- Exact common dilation of an outer coefficient, recursive chain, and `e` block. -/
theorem mtOuterBlockChainLongAF_scaleSupported_dilation
    {t : ℕ} {alpha : ℕ → ℂ} {L delta : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) L ((1 + delta) * L))
    (hL : 0 < L) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup) (eIndex : ℕ) :
    MTRealScaleSupported
      (mtBlockChainLongAF alpha data.block chain z0 D delta eIndex)
      (mtOuterBlockChainLongScale L delta recStart chain eIndex)
      ((1 + delta) ^ (chain.length + 2) *
        mtOuterBlockChainLongScale L delta recStart chain eIndex) := by
  let Q : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) → ℝ :=
    fun i => mtGeometricLevel delta recStart i.1
  have hrecBlock : ∀ i,
      MTRealScaleSupported (mtPrimeBlockAF (data.block i))
        (Q i) (Q i * (1 + delta)) := by
    intro i
    rw [hblocks]
    exact mtMinimalGeometricBlock_scaleSupported
      z0 D recStart hdelta hz0 hroot i
  have hraw : MTRealScaleSupported
      (mtBlockChainLongAF alpha data.block chain z0 D delta eIndex)
      ((L * ∏ j ∈ chain.toFinset, Q j) * mtUpperAdicScale delta eIndex)
      ((((1 + delta) * L) *
          ∏ j ∈ chain.toFinset, (Q j * (1 + delta))) *
        ((1 + delta) * mtUpperAdicScale delta eIndex)) := by
    exact mtBlockChainLongAF_scaleSupported halpha hrecBlock
      (fun i => (mtGeometricLevel_pos hdelta recStart i.1).le) hL.le
      hchain z0 D eIndex (mtUpperAdicScale_pos hdelta eIndex).le
  intro n hn
  have hs := hraw hn
  refine ⟨hs.1, by simpa [mtOuterBlockChainLongScale, Q] using hs.2.1, ?_⟩
  have hprod : (∏ j ∈ chain.toFinset, (Q j * (1 + delta))) =
      (1 + delta) ^ chain.length * ∏ j ∈ chain.toFinset, Q j :=
    prod_mul_constant_chain_toFinset Q (1 + delta) hchain
  calc
    (n : ℝ) ≤ (((1 + delta) * L) *
        ∏ j ∈ chain.toFinset, (Q j * (1 + delta))) *
        ((1 + delta) * mtUpperAdicScale delta eIndex) := hs.2.2
    _ = (1 + delta) ^ (chain.length + 2) *
        mtOuterBlockChainLongScale L delta recStart chain eIndex := by
      rw [hprod, show chain.length + 2 = chain.length + 1 + 1 by omega,
        pow_succ, pow_succ]
      dsimp [mtOuterBlockChainLongScale, Q]
      ring

theorem mtOuterBlockChainLongAF_scaleSupported_dyadic
    {t : ℕ} {alpha : ℕ → ℂ} {L delta : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) L ((1 + delta) * L))
    (hL : 0 < L) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup) (eIndex : ℕ)
    (hdilation : (1 + delta) ^ (chain.length + 2) ≤ 2) :
    MTRealScaleSupported
      (mtBlockChainLongAF alpha data.block chain z0 D delta eIndex)
      (mtOuterBlockChainLongScale L delta recStart chain eIndex)
      (2 * mtOuterBlockChainLongScale L delta recStart chain eIndex) := by
  exact MTRealScaleSupported.dyadic_of_dilation
    (mtOuterBlockChainLongAF_scaleSupported_dilation
      (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
      halpha hL z0 D recStart hdelta hz0 hroot data hblocks hchain eIndex)
    (mtOuterBlockChainLongScale_pos hL hdelta recStart chain eIndex).le hdilation

def mtOuterBlockChainTypeIIM2 {t : ℕ} (L delta : ℝ) (recStart : ℕ)
    (chain : List (Fin t)) (I : Finset (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  mtOuterBlockChainProductScale L delta recStart
    (mtBlockChainRemainder chain I) eIndex kIndex

def mtOuterBlockChainTypeIIBetaAF {t : ℕ} (alpha : ℕ → ℂ)
    (data : MTFiniteIterationSourceData t) (chain : List (Fin t))
    (I : Finset (Fin t)) (z0 D : ℕ) (delta : ℝ)
    (eIndex kIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    (mtBlockChainLongAF alpha data.block (mtBlockChainRemainder chain I)
      z0 D delta eIndex * mtUpperAdicOneAF delta kIndex)

theorem mtOuterBlockChainTypeIIM2_pos
    {t : ℕ} {L delta : ℝ} (hL : 0 < L) (hdelta : 0 < delta)
    (recStart : ℕ) (chain : List (Fin t)) (I : Finset (Fin t))
    (eIndex kIndex : ℕ) :
    0 < mtOuterBlockChainTypeIIM2 L delta recStart chain I eIndex kIndex :=
  mul_pos
    (mtOuterBlockChainLongScale_pos hL hdelta recStart
      (mtBlockChainRemainder chain I) eIndex)
    (mtUpperAdicScale_pos hdelta kIndex)

theorem mtOuterBlockChainTypeIIBetaAF_scaleSupported
    {t : ℕ} {alpha : ℕ → ℂ} {L delta : ℝ}
    (halpha : MTRealScaleSupported (mtCoefficientAF alpha) L ((1 + delta) * L))
    (hL : 0 < L) (z0 D recStart : ℕ) {recRoot : ℝ}
    (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    {chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 3) ≤ 2) :
    MTRealScaleSupported
      (mtOuterBlockChainTypeIIBetaAF alpha data chain I z0 D delta eIndex kIndex)
      (mtOuterBlockChainTypeIIM2 L delta recStart chain I eIndex kIndex)
      (2 * mtOuterBlockChainTypeIIM2 L delta recStart chain I eIndex kIndex) := by
  let remainder := mtBlockChainRemainder chain I
  let Mlong := mtOuterBlockChainLongScale L delta recStart remainder eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF alpha data.block remainder z0 D delta eIndex
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (remainder.length + 2) * Mlong) := by
    exact mtOuterBlockChainLongAF_scaleSupported_dilation
      (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
      halpha hL z0 D recStart hdelta hz0 hroot data hblocks
      (mtBlockChainRemainder_nodup hchain I) eIndex
  have hmul : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (remainder.length + 2) * Mlong) * ((1 + delta) * K)) := by
    exact MTRealScaleSupported.mul hlong (mtRealIntervalAF_scaleSupported _ _ _)
      (mtOuterBlockChainLongScale_pos hL hdelta recStart remainder eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hnormalized : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (remainder.length + 3) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show remainder.length + 3 = remainder.length + 2 + 1 by omega, pow_succ]
    ring
  have hdyadic : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) (2 * (Mlong * K)) :=
    MTRealScaleSupported.dyadic_of_dilation hnormalized
      (mul_nonneg
        (mtOuterBlockChainLongScale_pos hL hdelta recStart remainder eIndex).le
        (mtUpperAdicScale_pos hdelta kIndex).le) hdilation
  change MTRealScaleSupported
    (((-1 : ℂ) ^ chain.length) • (F * mtUpperAdicOneAF delta kIndex))
    (Mlong * K) (2 * (Mlong * K))
  intro n hn
  exact (MTRealScaleSupported.smul hdyadic ((-1 : ℂ) ^ chain.length)) hn

theorem mtOuterBlockChainTypeIIBetaAF_polynomialDivisorBounded
    {t : ℕ} {alpha : ℕ → ℂ}
    (halpha : MTPolynomialDivisorBounded alpha)
    (data : MTFiniteIterationSourceData t) {chain : List (Fin t)}
    (hchain : chain.Nodup) (I : Finset (Fin t))
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtOuterBlockChainTypeIIBetaAF alpha data chain I
        z0 D delta eIndex kIndex n) := by
  have hone : MTPolynomialDivisorBounded (fun _ : ℕ => (1 : ℂ)) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    simp
  have hlong : MTPolynomialDivisorBounded (fun n =>
      mtBlockChainLongAF alpha data.block (mtBlockChainRemainder chain I)
        z0 D delta eIndex n) := by
    exact mtBlockChainLongAF_polynomialDivisorBounded halpha
      (mtBlockChainRemainder_nodup hchain I) z0 D delta eIndex
  have hk : MTPolynomialDivisorBounded (fun n => mtUpperAdicOneAF delta kIndex n) :=
    mtRealIntervalAF_polynomialDivisorBounded hone _ _
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul
    (MTPolynomialDivisorBounded.arithmeticFunction_mul hlong hk)
    ((-1 : ℂ) ^ chain.length)

theorem mtSignedOuterBox_eq_selected_mul_typeIIBeta
    {t : ℕ} (alpha : ℕ → ℂ) (data : MTFiniteIterationSourceData t)
    (chain : List (Fin t)) (I : Finset (Fin t)) (hI : I ⊆ chain.toFinset)
    (z0 D : ℕ) (delta : ℝ) (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF alpha data.block chain z0 D delta eIndex kIndex =
      mtPrimeBlockFamilyAF data.block I *
        mtOuterBlockChainTypeIIBetaAF alpha data chain I
          z0 D delta eIndex kIndex := by
  rw [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtOuterBlockChainTypeIIBetaAF, mtBlockChainLongAF,
    mtBlockChainCoefficientAF, mtPrimeBlockFamilyAF_split data.block hI,
    mtBlockChainRemainder_toFinset]
  rw [mul_smul_comm]
  congr 1
  ring

/-- One narrow outer coefficient gives an exact Type-I/Type-II dichotomy. -/
theorem mtOuterBlockChainBox_isProposition22Piece
    {X Y z0Real epsilon L delta : ℝ} {alpha : ℕ → ℂ}
    (halphaSupport : MTRealScaleSupported
      (mtCoefficientAF alpha) L ((1 + delta) * L))
    (halphaBounded : MTPolynomialDivisorBounded alpha) (hL : 0 < L)
    (z0 D recStart : ℕ) {recRoot : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta recStart 0)
    (hroot : mtGeometricLevel delta recStart 0 < recRoot)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta recStart recRoot hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D recStart delta recRoot hdelta hz0 hroot).block)
    (chain : List (Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hX : 1 < X) (hepsilon0 : 0 < epsilon) (hepsilon : epsilon ≤ 2 / 11)
    (hrecRoot : recRoot = X ^ (2 / 11 : ℝ))
    (hrootOne : 1 ≤ mtGeometricLevel delta recStart 0)
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta recStart 0)
    (hchainBound : 1 < z0Real ∨ chain.toFinset.card ≤
      Nat.floor (Real.log recRoot / Real.log z0Real))
    (hdilation : ∀ R : ℕ, R ≤ chain.length + 5 → (1 + delta) ^ R ≤ 2)
    (hsmallCap : mtUpperAdicScale delta eIndex * L * X ^ (epsilon / 2) ≤
      X ^ (1 / 2 + epsilon))
    (hproduct : Y / 2 <
        mtOuterBlockChainProductScale L delta recStart chain eIndex kIndex ∧
      mtOuterBlockChainProductScale L delta recStart chain eIndex kIndex ≤ 4 * Y) :
    MTProposition22Piece X Y z0Real recRoot delta epsilon
      (mtSignedBlockChainAdicBoxAF alpha data.block chain
        z0 D delta eIndex kIndex) := by
  let Q : Fin (mtMinimalGeometricDepth delta recStart recRoot hdelta) → ℝ :=
    fun i => mtGeometricLevel delta recStart i.1
  have hQone : ∀ i ∈ chain.toFinset, 1 ≤ Q i := by
    intro i hi
    exact hrootOne.trans (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).1
  have hQcap : ∀ i ∈ chain.toFinset, Q i ≤ X ^ (2 / 11 : ℝ) := by
    intro i hi
    rw [← hrecRoot]
    exact (mtMinimalGeometricSchedule_scale_mem hdelta recStart i).2.le
  rcases matomakiTeravainen_primeBlockProduct_dichotomy_finite
      (Q := Q) (S := chain.toFinset) hX hepsilon0 hepsilon hQone hQcap with
    hsmall | htypeII
  · let M1 := mtOuterBlockChainLongScale L delta recStart chain eIndex
    let M2 := mtUpperAdicScale delta kIndex
    let F0 := mtBlockChainLongAF alpha data.block chain z0 D delta eIndex
    let F := ((-1 : ℂ) ^ chain.length) • F0
    have hprodNonneg : 0 ≤ ∏ i ∈ chain.toFinset, Q i :=
      Finset.prod_nonneg fun i hi => zero_le_one.trans (hQone i hi)
    have hM1le : M1 ≤ X ^ (1 / 2 + epsilon) := by
      calc
        M1 = mtUpperAdicScale delta eIndex * L * ∏ i ∈ chain.toFinset, Q i := by
          dsimp [M1, mtOuterBlockChainLongScale, Q]
          ring
        _ ≤ mtUpperAdicScale delta eIndex * L * X ^ (epsilon / 2) := by
          exact mul_le_mul_of_nonneg_left hsmall.le
            (mul_nonneg (mtUpperAdicScale_pos hdelta eIndex).le hL.le)
        _ ≤ X ^ (1 / 2 + epsilon) := hsmallCap
    have hsupport0 : MTRealScaleSupported F0 M1 (2 * M1) :=
      mtOuterBlockChainLongAF_scaleSupported_dyadic
        (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
        halphaSupport hL z0 D recStart hdelta hz0 hroot data hblocks
        hchain eIndex (hdilation _ (by omega))
    have hsupport : MTRealScaleSupported F M1 (2 * M1) :=
      MTRealScaleSupported.smul hsupport0 ((-1 : ℂ) ^ chain.length)
    have hbounded0 : MTPolynomialDivisorBounded (fun n => F0 n) :=
      mtBlockChainLongAF_polynomialDivisorBounded halphaBounded
        hchain z0 D delta eIndex
    have hbounded : MTPolynomialDivisorBounded (fun n => F n) :=
      MTPolynomialDivisorBounded.arithmeticFunction_smul
        hbounded0 ((-1 : ℂ) ^ chain.length)
    have hproductI : Y / 2 < M1 * M2 ∧ M1 * M2 ≤ 4 * Y := by
      simpa [M1, M2, mtOuterBlockChainProductScale] using hproduct
    let pieceData := mtTypeIPieceDataOfSupported (delta := delta) F
      (mtOuterBlockChainLongScale_pos hL hdelta recStart chain eIndex)
      (mtUpperAdicScale_pos hdelta kIndex)
      hsupport hbounded hM1le hproductI
    have hpiece : pieceData.pieceAF =
        mtSignedBlockChainAdicBoxAF alpha data.block chain
          z0 D delta eIndex kIndex := by
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
    let M2 := mtOuterBlockChainTypeIIM2 L delta recStart chain I eIndex kIndex
    let betaAF := mtOuterBlockChainTypeIIBetaAF alpha data chain I
      z0 D delta eIndex kIndex
    have hproductEq : (∏ i ∈ I, Q i) * M2 =
        mtOuterBlockChainProductScale L delta recStart chain eIndex kIndex := by
      have hsplit := prod_selected_mul_blockChainRemainder Q chain hIS
      dsimp [M2, mtOuterBlockChainTypeIIM2, mtOuterBlockChainProductScale,
        mtOuterBlockChainLongScale, Q] at hsplit ⊢
      rw [← hsplit]
      ring
    have hproductII : Y / 2 < (∏ i ∈ I, Q i) * M2 ∧
        (∏ i ∈ I, Q i) * M2 ≤ 4 * Y := by
      rw [hproductEq]
      exact hproduct
    have hbetaSupport : MTRealScaleSupported betaAF M2 (2 * M2) :=
      mtOuterBlockChainTypeIIBetaAF_scaleSupported
        (t := mtMinimalGeometricDepth delta recStart recRoot hdelta)
        halphaSupport hL z0 D recStart hdelta hz0 hroot data hblocks
        hchain I eIndex kIndex (hdilation _ (by
          have hlen := mtBlockChainRemainder_length_le chain I
          omega))
    have hbetaBounded : MTPolynomialDivisorBounded (fun n => betaAF n) :=
      mtOuterBlockChainTypeIIBetaAF_polynomialDivisorBounded
        halphaBounded data hchain I z0 D delta eIndex kIndex
    let pieceData := mtMinimalGeometricTypeIIData
      z0 D recStart hdelta hz0 hroot I hI hz0RealPos hz0RealLevel hR
      (fun n => betaAF n)
      (mtOuterBlockChainTypeIIM2_pos hL hdelta
        recStart chain I eIndex kIndex)
      hbetaBounded hIMem hproductII
    have hpiece : pieceData.pieceAF =
        mtSignedBlockChainAdicBoxAF alpha data.block chain
          z0 D delta eIndex kIndex := by
      calc
        pieceData.pieceAF =
            mtPrimeBlockFamilyAF
                (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
                  z0 D recStart delta recRoot hdelta hz0 hroot).block I *
              mtRealIntervalAF (fun n => betaAF n) M2 (2 * M2) := by
          exact mtMinimalGeometricTypeIIData_pieceAF_eq
            z0 D recStart hdelta hz0 hroot I hI hz0RealPos hz0RealLevel hR
            (fun n => betaAF n)
            (mtOuterBlockChainTypeIIM2_pos hL hdelta
              recStart chain I eIndex kIndex)
            hbetaBounded hIMem hproductII
        _ = mtPrimeBlockFamilyAF data.block I * betaAF := by
          rw [← hblocks, mtRealIntervalAF_coe_eq_of_scaleSupported hbetaSupport]
        _ = mtSignedBlockChainAdicBoxAF alpha data.block chain
              z0 D delta eIndex kIndex :=
          (mtSignedOuterBox_eq_selected_mul_typeIIBeta
            alpha data chain I hIS z0 D delta eIndex kIndex).symm
    rw [← hpiece]
    exact MTProposition22Piece.typeII pieceData

end

end RHTower.Sieve
