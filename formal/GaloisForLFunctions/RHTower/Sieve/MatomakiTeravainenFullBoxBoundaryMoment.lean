import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenFullBoxEnvelope
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricRooted
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxTypeI
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenProductScaleBoundaryMoment
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTripleBoxTypeII

/-!
# Product-scale boundary moments for complete Harman box families

Every factor in a complete pair or triple box uses the same literal geometric width.  A single
power-dilation certificate therefore puts the whole indexed family in a common product collar.
The joint `ζ⁵`/`ζ⁶` envelopes then price that collar without any box-count loss.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction
open scoped ArithmeticFunction.zeta

noncomputable section

abbrev MTPairFullBoxIndex (t : ℕ) :=
  (((Fin t × Fin t) × (ℕ × List (Fin t))) × ℕ) × ℕ

abbrev MTTripleFullBoxIndex (t : ℕ) :=
  ((((Fin t × Fin t) × Fin t) × (ℕ × List (Fin t))) × ℕ) × ℕ

local instance instDecidableEqMTTripleFullBoxIndex (t : ℕ) :
    DecidableEq (MTTripleFullBoxIndex t) := Classical.decEq _

/-- Finite source-prime family containing every block of one iteration datum. -/
def mtFiniteIterationSourcePrimeFamily {t : ℕ} (data : MTFiniteIterationSourceData t) :
    Finset ℕ :=
  Finset.univ.biUnion data.block

/-- Minimal geometric blocks are source-restricted Harman blocks for the union source family. -/
theorem ofMinimalGeometricSchedule_block_eq_harmanSourceBlock
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i : Fin (mtMinimalGeometricDepth delta start z hdelta)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).block i =
      mtHarmanSourceBlock (mtMinimalGeometricEndpoint delta start)
        (mtFiniteIterationSourcePrimeFamily
          (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot)) i := by
  let data := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  rw [MTFiniteIterationSourceData.ofMinimalGeometricSchedule_block]
  change mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i =
    mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i ∩
      mtFiniteIterationSourcePrimeFamily data
  rw [eq_comm, Finset.inter_eq_left]
  intro q hq
  rw [mtFiniteIterationSourcePrimeFamily, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  change q ∈ mtAdjacentPrimeBlock
    (mtRealBlockEndpoint (mtGeometricLevel delta start)) i at hq
  simpa [data] using hq

theorem ofMinimalGeometricRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
    (z0 D start z1 : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z1 : ℝ)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z0 D start z1 delta hdelta hz0 hroot).block =
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta (z1 : ℝ) hdelta hz0 hroot).block := by
  funext i
  rw [MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_block,
    MTFiniteIterationSourceData.ofMinimalGeometricSchedule_block]
  rfl

theorem ofMinimalGeometricRootedSchedule_block_eq_harmanSourceBlock
    (z0 D start z1 : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z1 : ℝ))
    (i : Fin (mtMinimalGeometricDepth delta start (z1 : ℝ) hdelta)) :
    (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z0 D start z1 delta hdelta hz0 hroot).block i =
      mtHarmanSourceBlock (mtMinimalGeometricEndpoint delta start)
        (mtFiniteIterationSourcePrimeFamily
          (MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
            z0 D start z1 delta hdelta hz0 hroot)) i := by
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    z0 D start z1 delta hdelta hz0 hroot
  rw [MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule_block]
  change mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i =
    mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i ∩
      mtFiniteIterationSourcePrimeFamily data
  rw [eq_comm, Finset.inter_eq_left]
  intro q hq
  rw [mtFiniteIterationSourcePrimeFamily, Finset.mem_biUnion]
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simpa [data] using hq

/-- Base product scale of one complete pair box. -/
def mtMinimalGeometricPairBoxProductScale
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 i2 : Fin t)
    (chain : List (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
    mtUpperAdicScale delta kIndex

/-- Base product scale of one complete triple box. -/
def mtMinimalGeometricTripleBoxProductScale
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 i2 i3 : Fin t)
    (chain : List (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  mtMinimalGeometricTripleBoxLongM1 delta start i1 i2 i3 chain eIndex *
    mtUpperAdicScale delta kIndex

def mtPairFullBoxIndexSet {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ) (j : Fin (t + 1))
    (eMax kMax : ℕ) : Finset (MTPairFullBoxIndex t) :=
  (((mtHarmanActiveGoodPairCells (t := t) endpoint E).product
      (mtAllActiveBlockChains data maxDepth j)).product
      (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))

def mtPairFullBoxAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (z D : ℕ) (delta : ℝ) (idx : MTPairFullBoxIndex t) : ArithmeticFunction ℂ :=
  mtSignedBlockChainAdicBoxAF
    (mtHarmanPairCellCoefficient
      (data.block idx.1.1.1.1) (data.block idx.1.1.1.2))
    data.block idx.1.1.2.2 z D delta idx.1.2 idx.2

def mtPairFullBoxScale {t : ℕ} (delta : ℝ) (start : ℕ)
    (idx : MTPairFullBoxIndex t) : ℝ :=
  mtMinimalGeometricPairBoxProductScale delta start
    idx.1.1.1.1 idx.1.1.1.2 idx.1.1.2.2 idx.1.2 idx.2

def mtTripleFullBoxIndexSet {t : ℕ} (endpoint : ℕ → ℕ) (E : ℝ)
    (data : MTFiniteIterationSourceData t) (maxDepth : ℕ) (j : Fin (t + 1))
    (eMax kMax : ℕ) : Finset (MTTripleFullBoxIndex t) :=
  (((mtHarmanActiveGoodTripleCells (t := t) endpoint E).product
      (mtAllActiveBlockChains data maxDepth j)).product
      (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))

def mtTripleFullBoxAF {t : ℕ} (data : MTFiniteIterationSourceData t)
    (z D : ℕ) (delta : ℝ) (idx : MTTripleFullBoxIndex t) : ArithmeticFunction ℂ :=
  mtSignedBlockChainAdicBoxAF
    (mtHarmanTripleCellCoefficient
      (data.block idx.1.1.1.1.1) (data.block idx.1.1.1.1.2)
      (data.block idx.1.1.1.2))
    data.block idx.1.1.2.2 z D delta idx.1.2 idx.2

def mtTripleFullBoxScale {t : ℕ} (delta : ℝ) (start : ℕ)
    (idx : MTTripleFullBoxIndex t) : ℝ :=
  mtMinimalGeometricTripleBoxProductScale delta start
    idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      idx.1.1.2.2 idx.1.2 idx.2

/-- One signed pair box fits the common family collar. -/
theorem mtSignedPairBox_scaleSupported_commonProductCollar
    (z0 D start : ℕ) {delta z eta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta start z hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup) (maxDepth eIndex kIndex : ℕ)
    (hlength : chain.length ≤ maxDepth)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (data.block i1) (data.block i2))
        data.block chain
        z0 D delta eIndex kIndex)
      (mtMinimalGeometricPairBoxProductScale
        delta start i1 i2 chain eIndex kIndex)
      ((1 + eta) * mtMinimalGeometricPairBoxProductScale
        delta start i1 i2 chain eIndex kIndex) := by
  let Mlong := mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF
    (mtHarmanPairCellCoefficient
      (data.block i1) (data.block i2))
    data.block chain z0 D delta eIndex
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (chain.length + 3) * Mlong) := by
    intro n hn
    have hs := mtMinimalGeometricPairLongAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 i2 hchain eIndex (n := n)
        (by simpa only [F, hblocks] using hn)
    simpa only [Mlong, mtMinimalGeometricPairBoxM1] using hs
  have hmul : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (chain.length + 3) * Mlong) * ((1 + delta) * K)) :=
    MTRealScaleSupported.mul hlong (mtRealIntervalAF_scaleSupported _ _ _)
      (mtMinimalGeometricPairBoxM1_pos
        hdelta start i1 i2 chain eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hexact : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (chain.length + 4) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show chain.length + 4 = chain.length + 3 + 1 by omega, pow_succ]
    ring
  have hpower : (1 + delta) ^ (chain.length + 4) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) (by omega)).trans hdilation
  have hcommon : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + eta) * (Mlong * K)) := by
    intro n hn
    have hs := hexact hn
    exact ⟨hs.1, hs.2.1, hs.2.2.trans
      (mul_le_mul_of_nonneg_right hpower
        (mul_nonneg
          (mtMinimalGeometricPairBoxM1_pos
            hdelta start i1 i2 chain eIndex).le
          (mtUpperAdicScale_pos hdelta kIndex).le))⟩
  change MTRealScaleSupported
    (((-1 : ℂ) ^ chain.length) • (F * mtUpperAdicOneAF delta kIndex))
    (Mlong * K) ((1 + eta) * (Mlong * K))
  exact MTRealScaleSupported.smul hcommon ((-1 : ℂ) ^ chain.length)

/-- One signed triple box fits the common family collar. -/
theorem mtSignedTripleBox_scaleSupported_commonProductCollar
    (z0 D start : ℕ) {delta z eta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (data : MTFiniteIterationSourceData
      (mtMinimalGeometricDepth delta start z hdelta))
    (hblocks : data.block =
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup) (maxDepth eIndex kIndex : ℕ)
    (hlength : chain.length ≤ maxDepth)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    MTRealScaleSupported
      (mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (data.block i1) (data.block i2) (data.block i3))
        data.block chain
        z0 D delta eIndex kIndex)
      (mtMinimalGeometricTripleBoxProductScale
        delta start i1 i2 i3 chain eIndex kIndex)
      ((1 + eta) * mtMinimalGeometricTripleBoxProductScale
        delta start i1 i2 i3 chain eIndex kIndex) := by
  let Mlong := mtMinimalGeometricTripleBoxLongM1
    delta start i1 i2 i3 chain eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF
    (mtHarmanTripleCellCoefficient
      (data.block i1) (data.block i2) (data.block i3))
    data.block chain z0 D delta eIndex
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (chain.length + 4) * Mlong) := by
    intro n hn
    have hs := mtMinimalGeometricTripleLongAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 i2 i3 hchain eIndex (n := n)
        (by simpa only [F, hblocks] using hn)
    simpa only [Mlong, mtMinimalGeometricTripleBoxLongM1] using hs
  have hmul : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (chain.length + 4) * Mlong) * ((1 + delta) * K)) :=
    MTRealScaleSupported.mul hlong (mtRealIntervalAF_scaleSupported _ _ _)
      (mtMinimalGeometricTripleBoxLongM1_pos
        hdelta start i1 i2 i3 chain eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hexact : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (chain.length + 5) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show chain.length + 5 = chain.length + 4 + 1 by omega, pow_succ]
    ring
  have hpower : (1 + delta) ^ (chain.length + 5) ≤ 1 + eta :=
    (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 1 + delta) (by omega)).trans hdilation
  have hcommon : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + eta) * (Mlong * K)) := by
    intro n hn
    have hs := hexact hn
    exact ⟨hs.1, hs.2.1, hs.2.2.trans
      (mul_le_mul_of_nonneg_right hpower
        (mul_nonneg
          (mtMinimalGeometricTripleBoxLongM1_pos
            hdelta start i1 i2 i3 chain eIndex).le
          (mtUpperAdicScale_pos hdelta kIndex).le))⟩
  change MTRealScaleSupported
    (((-1 : ℂ) ^ chain.length) • (F * mtUpperAdicOneAF delta kIndex))
    (Mlong * K) ((1 + eta) * (Mlong * K))
  exact MTRealScaleSupported.smul hcommon ((-1 : ℂ) ^ chain.length)

/-- Complete pair-family product boundary is controlled by the two local `ζ⁵` square moments. -/
theorem sum_normSq_mtSignedPairBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (E : ℝ) (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta start z hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    let data := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot
    let endpoint := mtMinimalGeometricEndpoint delta start
    let S := (((mtHarmanActiveGoodPairCells
      (t := mtMinimalGeometricDepth delta start z hdelta) endpoint E).product
        (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))
    let F : MTPairFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) →
        ArithmeticFunction ℂ := fun idx =>
      mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          (data.block idx.1.1.1.1) (data.block idx.1.1.1.2))
        data.block idx.1.1.2.2 z0 D delta idx.1.2 idx.2
    let M : MTPairFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
      fun idx => mtMinimalGeometricPairBoxProductScale
      delta start idx.1.1.1.1 idx.1.1.1.2 idx.1.1.2.2 idx.1.2 idx.2
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) n : ℝ) ^ 2) := by
  classical
  dsimp only
  let data := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  let endpoint := mtMinimalGeometricEndpoint delta start
  let P := mtFiniteIterationSourcePrimeFamily data
  let C := mtHarmanActiveGoodPairCells
    (t := mtMinimalGeometricDepth delta start z hdelta) endpoint E
  let H := mtAllActiveBlockChains data maxDepth j
  let S := ((C.product H).product (Finset.range (eMax + 1))).product
    (Finset.range (kMax + 1))
  let F : MTPairFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) →
      ArithmeticFunction ℂ := fun idx =>
    mtSignedBlockChainAdicBoxAF
      (mtHarmanPairCellCoefficient
        (data.block idx.1.1.1.1) (data.block idx.1.1.1.2))
      data.block idx.1.1.2.2 z0 D delta idx.1.2 idx.2
  let M : MTPairFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun idx => mtMinimalGeometricPairBoxProductScale
    delta start idx.1.1.1.1 idx.1.1.1.2 idx.1.1.2.2 idx.1.2 idx.2
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A S F M Y eta 5 hY heta
  · intro idx hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxCH := Finset.mem_product.mp hidxE.1
    have hdc := (mem_mtAllActiveBlockChains.mp hidxCH.2)
    have hchain := hdc.2
    have hlen := length_eq_of_mem_mtActiveBlockChains hchain
    apply mtSignedPairBox_scaleSupported_commonProductCollar
      z0 D start hdelta hz0 hroot data rfl idx.1.1.1.1 idx.1.1.1.2
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    simpa [S, F, C, H, endpoint, P, data] using
      sum_norm_mtSignedPairBoxFamily_le_zeta_pow_five
        (mtMinimalGeometricEndpoint_monotone hdelta start) P E data
        (fun i => ofMinimalGeometricSchedule_block_eq_harmanSourceBlock
          z0 D start hdelta hz0 hroot i)
        maxDepth j hdelta z0 D eMax kMax n

/-- Complete triple-family product boundary is controlled by the two local `ζ⁶` square moments. -/
theorem sum_normSq_mtSignedTripleBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (E : ℝ) (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta start z hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    let data := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot
    let endpoint := mtMinimalGeometricEndpoint delta start
    let S := (((mtHarmanActiveGoodTripleCells
      (t := mtMinimalGeometricDepth delta start z hdelta) endpoint E).product
        (mtAllActiveBlockChains data maxDepth j)).product
        (Finset.range (eMax + 1))).product (Finset.range (kMax + 1))
    let F : MTTripleFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) →
        ArithmeticFunction ℂ := fun idx =>
      mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          (data.block idx.1.1.1.1.1) (data.block idx.1.1.1.1.2)
          (data.block idx.1.1.1.2))
        data.block idx.1.1.2.2 z0 D delta idx.1.2 idx.2
    let M : MTTripleFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
      fun idx => mtMinimalGeometricTripleBoxProductScale
      delta start idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
        idx.1.1.2.2 idx.1.2 idx.2
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF S F M Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 6) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 6) n : ℝ) ^ 2) := by
  classical
  dsimp only
  let data := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  let endpoint := mtMinimalGeometricEndpoint delta start
  let P := mtFiniteIterationSourcePrimeFamily data
  let C := mtHarmanActiveGoodTripleCells
    (t := mtMinimalGeometricDepth delta start z hdelta) endpoint E
  let H := mtAllActiveBlockChains data maxDepth j
  let S := ((C.product H).product (Finset.range (eMax + 1))).product
    (Finset.range (kMax + 1))
  let F : MTTripleFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) →
      ArithmeticFunction ℂ := fun idx =>
    mtSignedBlockChainAdicBoxAF
      (mtHarmanTripleCellCoefficient
        (data.block idx.1.1.1.1.1) (data.block idx.1.1.1.1.2)
        (data.block idx.1.1.1.2))
      data.block idx.1.1.2.2 z0 D delta idx.1.2 idx.2
  let M : MTTripleFullBoxIndex (mtMinimalGeometricDepth delta start z hdelta) → ℝ :=
    fun idx => mtMinimalGeometricTripleBoxProductScale
    delta start idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      idx.1.1.2.2 idx.1.2 idx.2
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A S F M Y eta 6 hY heta
  · intro idx hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxCH := Finset.mem_product.mp hidxE.1
    have hdc := (mem_mtAllActiveBlockChains.mp hidxCH.2)
    have hchain := hdc.2
    have hlen := length_eq_of_mem_mtActiveBlockChains hchain
    apply mtSignedTripleBox_scaleSupported_commonProductCollar
      z0 D start hdelta hz0 hroot data rfl
        idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    simpa [S, F, C, H, endpoint, P, data] using
      sum_norm_mtSignedTripleBoxFamily_le_zeta_pow_six
        (mtMinimalGeometricEndpoint_monotone hdelta start) P E data
        (fun i => ofMinimalGeometricSchedule_block_eq_harmanSourceBlock
          z0 D start hdelta hz0 hroot i)
        maxDepth j hdelta z0 D eMax kMax n

/-- Canonical rooted pair family: exact product-collar square bound used by the repaired iteration. -/
theorem sum_normSq_mtRootedSignedPairBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z0 D start z1 : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z1 : ℝ))
    (E : ℝ) (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta start (z1 : ℝ) hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z0 D start z1 delta hdelta hz0 hroot
    let endpoint := mtMinimalGeometricEndpoint delta start
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtPairFullBoxIndexSet endpoint E data maxDepth j eMax kMax)
      (mtPairFullBoxAF data z0 D delta)
      (mtPairFullBoxScale delta start) Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 5) n : ℝ) ^ 2) := by
  classical
  dsimp only
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    z0 D start z1 delta hdelta hz0 hroot
  let endpoint := mtMinimalGeometricEndpoint delta start
  let P := mtFiniteIterationSourcePrimeFamily data
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtPairFullBoxIndexSet endpoint E data maxDepth j eMax kMax)
      (mtPairFullBoxAF data z0 D delta) (mtPairFullBoxScale delta start)
      Y eta 5 hY heta
  · intro idx hidx
    rw [mtPairFullBoxIndexSet] at hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxCH := Finset.mem_product.mp hidxE.1
    have hdc := mem_mtAllActiveBlockChains.mp hidxCH.2
    have hchain := hdc.2
    have hlen := length_eq_of_mem_mtActiveBlockChains hchain
    apply mtSignedPairBox_scaleSupported_commonProductCollar
      z0 D start hdelta hz0 hroot data
      (ofMinimalGeometricRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
        z0 D start z1 hdelta hz0 hroot)
      idx.1.1.1.1 idx.1.1.1.2 (activeBlockChain_nodup hchain)
      maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    simpa [mtPairFullBoxIndexSet, mtPairFullBoxAF, endpoint, P, data] using
      sum_norm_mtSignedPairBoxFamily_le_zeta_pow_five
        (mtMinimalGeometricEndpoint_monotone hdelta start) P E data
        (fun i => ofMinimalGeometricRootedSchedule_block_eq_harmanSourceBlock
          z0 D start z1 hdelta hz0 hroot i)
        maxDepth j hdelta z0 D eMax kMax n

/-- Canonical rooted triple family: exact product-collar square bound used by the repaired iteration. -/
theorem sum_normSq_mtRootedSignedTripleBoxFamily_productBoundary_le_collar_zeta_sq
    (A : Finset ℕ) (z0 D start z1 : ℕ) {delta : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < (z1 : ℝ))
    (E : ℝ) (maxDepth eMax kMax : ℕ)
    (j : Fin (mtMinimalGeometricDepth delta start (z1 : ℝ) hdelta + 1))
    (Y eta : ℝ) (hY : 0 < Y) (heta : 0 ≤ eta)
    (hdilation : (1 + delta) ^ (maxDepth + 5) ≤ 1 + eta) :
    let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
      z0 D start z1 delta hdelta hz0 hroot
    let endpoint := mtMinimalGeometricEndpoint delta start
    ∑ n ∈ A, ‖mtProductScaleBoundaryErrorAF
      (mtTripleFullBoxIndexSet endpoint E data maxDepth j eMax kMax)
      (mtTripleFullBoxAF data z0 D delta)
      (mtTripleFullBoxScale delta start) Y n‖ ^ 2 ≤
      (∑ n ∈ mtLowerProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 6) n : ℝ) ^ 2)) +
      ∑ n ∈ mtUpperProductScaleCollar Y eta,
        ((((ArithmeticFunction.zeta : ArithmeticFunction ℕ) ^ 6) n : ℝ) ^ 2) := by
  classical
  dsimp only
  let data := MTFiniteIterationSourceData.ofMinimalGeometricRootedSchedule
    z0 D start z1 delta hdelta hz0 hroot
  let endpoint := mtMinimalGeometricEndpoint delta start
  let P := mtFiniteIterationSourcePrimeFamily data
  apply sum_normSq_mtProductScaleBoundaryErrorAF_le_collar_zeta_sq
    A (mtTripleFullBoxIndexSet endpoint E data maxDepth j eMax kMax)
      (mtTripleFullBoxAF data z0 D delta) (mtTripleFullBoxScale delta start)
      Y eta 6 hY heta
  · intro idx hidx
    rw [mtTripleFullBoxIndexSet] at hidx
    have hidxK := Finset.mem_product.mp hidx
    have hidxE := Finset.mem_product.mp hidxK.1
    have hidxCH := Finset.mem_product.mp hidxE.1
    have hdc := mem_mtAllActiveBlockChains.mp hidxCH.2
    have hchain := hdc.2
    have hlen := length_eq_of_mem_mtActiveBlockChains hchain
    apply mtSignedTripleBox_scaleSupported_commonProductCollar
      z0 D start hdelta hz0 hroot data
      (ofMinimalGeometricRootedSchedule_block_eq_ofMinimalGeometricSchedule_block
        z0 D start z1 hdelta hz0 hroot)
      idx.1.1.1.1.1 idx.1.1.1.1.2 idx.1.1.1.2
      (activeBlockChain_nodup hchain) maxDepth idx.1.2 idx.2
    · rw [hlen]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hdc.1)
    · exact hdilation
  · intro n
    simpa [mtTripleFullBoxIndexSet, mtTripleFullBoxAF, endpoint, P, data] using
      sum_norm_mtSignedTripleBoxFamily_le_zeta_pow_six
        (mtMinimalGeometricEndpoint_monotone hdelta start) P E data
        (fun i => ofMinimalGeometricRootedSchedule_block_eq_harmanSourceBlock
          z0 D start z1 hdelta hz0 hroot i)
        maxDepth j hdelta z0 D eMax kMax n

end

end RHTower.Sieve
