import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTripleBoxTypeI_II

/-!
# Exact Type-II presentation of a selected triple box

A selected nonempty recursive-block subset is the literal equation-(2.11) factor.  Three outer
Harman primes, remaining recursive blocks, truncated-Moebius block, terminal cofactor, and chain
sign form the dyadically supported divisor-bounded second factor.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Base scale of a triple-box long factor. -/
def mtMinimalGeometricTripleBoxLongM1
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 i2 i3 : Fin t)
    (chain : List (Fin t)) (eIndex : ℕ) : ℝ :=
  (((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1) *
      mtGeometricLevel delta start i3.1) *
      ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
    mtUpperAdicScale delta eIndex

theorem mtMinimalGeometricTripleBoxLongM1_pos
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i1 i2 i3 : Fin t) (chain : List (Fin t)) (eIndex : ℕ) :
    0 < mtMinimalGeometricTripleBoxLongM1 delta start i1 i2 i3 chain eIndex := by
  exact mul_pos
    (mul_pos
      (mul_pos
        (mul_pos (mtGeometricLevel_pos hdelta start i1.1)
          (mtGeometricLevel_pos hdelta start i2.1))
        (mtGeometricLevel_pos hdelta start i3.1))
      (Finset.prod_pos fun j hj => mtGeometricLevel_pos hdelta start j.1))
    (mtUpperAdicScale_pos hdelta eIndex)

/-- Base scale of the dyadic Type-II second factor for a triple box. -/
def mtMinimalGeometricTripleBoxTypeIIM2
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 i2 i3 : Fin t)
    (chain : List (Fin t)) (I : Finset (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  mtMinimalGeometricTripleBoxLongM1 delta start i1 i2 i3
      (mtBlockChainRemainder chain I) eIndex *
    mtUpperAdicScale delta kIndex

theorem mtMinimalGeometricTripleBoxTypeIIM2_pos
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i1 i2 i3 : Fin t) (chain : List (Fin t)) (I : Finset (Fin t))
    (eIndex kIndex : ℕ) :
    0 < mtMinimalGeometricTripleBoxTypeIIM2
      delta start i1 i2 i3 chain I eIndex kIndex :=
  mul_pos
    (mtMinimalGeometricTripleBoxLongM1_pos hdelta start i1 i2 i3
      (mtBlockChainRemainder chain I) eIndex)
    (mtUpperAdicScale_pos hdelta kIndex)

/-- Signed dyadic remainder after extracting selected recursive blocks from a triple box. -/
def mtMinimalGeometricTripleTypeIIBetaAF
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    (mtBlockChainLongAF
      (mtHarmanTripleCellCoefficient
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i1)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i3))
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block
      (mtBlockChainRemainder chain I) z0 D delta eIndex *
      mtUpperAdicOneAF delta kIndex)

theorem mtMinimalGeometricTripleTypeIIBetaAF_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 5) ≤ 2) :
    MTRealScaleSupported
      (mtMinimalGeometricTripleTypeIIBetaAF z0 D start hdelta hz0 hroot
        i1 i2 i3 chain I eIndex kIndex)
      (mtMinimalGeometricTripleBoxTypeIIM2
        delta start i1 i2 i3 chain I eIndex kIndex)
      (2 * mtMinimalGeometricTripleBoxTypeIIM2
        delta start i1 i2 i3 chain I eIndex kIndex) := by
  let remainder := mtBlockChainRemainder chain I
  let Mlong := mtMinimalGeometricTripleBoxLongM1
    delta start i1 i2 i3 remainder eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF
    (mtHarmanTripleCellCoefficient
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i1)
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i2)
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i3))
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).block remainder z0 D delta eIndex
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (remainder.length + 4) * Mlong) := by
    intro n hn
    exact (mtMinimalGeometricTripleLongAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 i2 i3
      (mtBlockChainRemainder_nodup hchain I) eIndex) hn
  have hmul : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (remainder.length + 4) * Mlong) * ((1 + delta) * K)) :=
    MTRealScaleSupported.mul hlong (mtRealIntervalAF_scaleSupported _ _ _)
      (mtMinimalGeometricTripleBoxLongM1_pos
        hdelta start i1 i2 i3 remainder eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hnormalized : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (remainder.length + 5) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show remainder.length + 5 = remainder.length + 4 + 1 by omega, pow_succ]
    ring
  have hdyadic : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) (2 * (Mlong * K)) :=
    MTRealScaleSupported.dyadic_of_dilation hnormalized
      (mul_nonneg
        (mtMinimalGeometricTripleBoxLongM1_pos
          hdelta start i1 i2 i3 remainder eIndex).le
        (mtUpperAdicScale_pos hdelta kIndex).le) hdilation
  change MTRealScaleSupported
    (((-1 : ℂ) ^ chain.length) • (F * mtUpperAdicOneAF delta kIndex))
    (Mlong * K) (2 * (Mlong * K))
  intro n hn
  exact (MTRealScaleSupported.smul hdyadic ((-1 : ℂ) ^ chain.length)) hn

theorem mtMinimalGeometricTripleTypeIIBetaAF_polynomialDivisorBounded
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtMinimalGeometricTripleTypeIIBetaAF z0 D start hdelta hz0 hroot
        i1 i2 i3 chain I eIndex kIndex n) := by
  have hone : MTPolynomialDivisorBounded (fun _ : ℕ => (1 : ℂ)) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    simp
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  have hlong : MTPolynomialDivisorBounded (fun n =>
      mtBlockChainLongAF
        (mtHarmanTripleCellCoefficient
          (source.block i1) (source.block i2) (source.block i3))
        source.block (mtBlockChainRemainder chain I) z0 D delta eIndex n) :=
    mtBlockChainLongAF_polynomialDivisorBounded
      (block := source.block)
      (mtHarmanTripleCellCoefficient_polynomialDivisorBounded
        (source.block i1) (source.block i2) (source.block i3))
      (mtBlockChainRemainder_nodup hchain I) z0 D delta eIndex
  have hk : MTPolynomialDivisorBounded
      (fun n => mtUpperAdicOneAF delta kIndex n) :=
    mtRealIntervalAF_polynomialDivisorBounded hone _ _
  change MTPolynomialDivisorBounded (fun n =>
    (((( -1 : ℂ) ^ chain.length) •
      (mtBlockChainLongAF
        (mtHarmanTripleCellCoefficient
          (source.block i1) (source.block i2) (source.block i3))
        source.block (mtBlockChainRemainder chain I) z0 D delta eIndex *
          mtUpperAdicOneAF delta kIndex)) n))
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul
    (MTPolynomialDivisorBounded.arithmeticFunction_mul hlong hk)
    ((-1 : ℂ) ^ chain.length)

/-- Exact extraction of the selected block family from a signed triple box. -/
theorem mtSignedTripleBox_eq_selected_mul_typeIIBeta
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hI : I ⊆ chain.toFinset) (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex =
      mtPrimeBlockFamilyAF
          (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block I *
        mtMinimalGeometricTripleTypeIIBetaAF z0 D start hdelta hz0 hroot
          i1 i2 i3 chain I eIndex kIndex := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  let alpha := mtHarmanTripleCellCoefficient
    (source.block i1) (source.block i2) (source.block i3)
  let remainder := mtBlockChainRemainder chain I
  rw [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtMinimalGeometricTripleTypeIIBetaAF, mtBlockChainLongAF,
    mtBlockChainCoefficientAF, mtPrimeBlockFamilyAF_split source.block hI,
    mtBlockChainRemainder_toFinset]
  rw [mul_smul_comm]
  congr 1
  ring

/-- Complete Type-II datum for one triple box and selected nonempty block subset. -/
def mtMinimalGeometricTripleBoxTypeIIData
    {X Y z0Real epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hI : I.Nonempty) (eIndex kIndex : ℕ)
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta start 0)
    (hR : I.card ≤ Nat.floor (Real.log z / Real.log z0Real))
    (hM1 : X ^ (epsilon / 2) ≤
        ∏ i ∈ I, mtGeometricLevel delta start i.1 ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) ≤ z)
    (hproduct : Y / 2 <
        (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricTripleBoxTypeIIM2
            delta start i1 i2 i3 chain I eIndex kIndex ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricTripleBoxTypeIIM2
            delta start i1 i2 i3 chain I eIndex kIndex ≤ 4 * Y) :
    MTTypeIIPieceData X Y z0Real z delta epsilon := by
  let betaAF := mtMinimalGeometricTripleTypeIIBetaAF
    z0 D start hdelta hz0 hroot i1 i2 i3 chain I eIndex kIndex
  exact mtMinimalGeometricTypeIIData z0 D start hdelta hz0 hroot I hI
    hz0RealPos hz0RealLevel hR (fun n => betaAF n)
    (mtMinimalGeometricTripleBoxTypeIIM2_pos
      hdelta start i1 i2 i3 chain I eIndex kIndex)
    (mtMinimalGeometricTripleTypeIIBetaAF_polynomialDivisorBounded
      z0 D start hdelta hz0 hroot i1 i2 i3 hchain I eIndex kIndex)
    hM1 hproduct

/-- Constructed Type-II piece is exactly the original signed triple box. -/
theorem mtMinimalGeometricTripleBoxTypeIIData_pieceAF_eq
    {X Y z0Real epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 i3 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hIS : I ⊆ chain.toFinset) (hI : I.Nonempty) (eIndex kIndex : ℕ)
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta start 0)
    (hR : I.card ≤ Nat.floor (Real.log z / Real.log z0Real))
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 5) ≤ 2)
    (hM1 : X ^ (epsilon / 2) ≤
        ∏ i ∈ I, mtGeometricLevel delta start i.1 ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) ≤ z)
    (hproduct : Y / 2 <
        (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricTripleBoxTypeIIM2
            delta start i1 i2 i3 chain I eIndex kIndex ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricTripleBoxTypeIIM2
            delta start i1 i2 i3 chain I eIndex kIndex ≤ 4 * Y) :
    (mtMinimalGeometricTripleBoxTypeIIData z0 D start hdelta hz0 hroot
      i1 i2 i3 chain hchain I hI eIndex kIndex hz0RealPos hz0RealLevel hR
      hM1 hproduct).pieceAF =
      mtSignedBlockChainAdicBoxAF
        (mtHarmanTripleCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i3))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex := by
  let betaAF := mtMinimalGeometricTripleTypeIIBetaAF
    z0 D start hdelta hz0 hroot i1 i2 i3 chain I eIndex kIndex
  have hbetaSupport : MTRealScaleSupported betaAF
      (mtMinimalGeometricTripleBoxTypeIIM2
        delta start i1 i2 i3 chain I eIndex kIndex)
      (2 * mtMinimalGeometricTripleBoxTypeIIM2
        delta start i1 i2 i3 chain I eIndex kIndex) := by
    intro n hn
    exact (mtMinimalGeometricTripleTypeIIBetaAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 i2 i3 hchain I eIndex kIndex hdilation) hn
  rw [mtMinimalGeometricTripleBoxTypeIIData,
    mtMinimalGeometricTypeIIData_pieceAF_eq]
  rw [mtRealIntervalAF_coe_eq_of_scaleSupported hbetaSupport]
  exact (mtSignedTripleBox_eq_selected_mul_typeIIBeta
    z0 D start hdelta hz0 hroot i1 i2 i3 chain I hIS eIndex kIndex).symm

end

end RHTower.Sieve
