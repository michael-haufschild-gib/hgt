import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPairBoxTypeI

/-!
# Exact Type-II presentation of a selected pair box

A nonempty selected subset becomes the literal equation-(2.11) factor.  Outer Harman primes,
unselected recursive blocks, the truncated-Moebius block, the terminal cofactor, and the chain sign
form one dyadically supported divisor-bounded `beta` factor.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Ordered complement of a selected subset inside one active chain. -/
def mtBlockChainRemainder {t : ℕ}
    (chain : List (Fin t)) (I : Finset (Fin t)) : List (Fin t) :=
  chain.filter fun i => i ∉ I

theorem mtBlockChainRemainder_nodup {t : ℕ}
    {chain : List (Fin t)} (hchain : chain.Nodup) (I : Finset (Fin t)) :
    (mtBlockChainRemainder chain I).Nodup := by
  exact hchain.filter _

theorem mtBlockChainRemainder_toFinset {t : ℕ}
    (chain : List (Fin t)) (I : Finset (Fin t)) :
    (mtBlockChainRemainder chain I).toFinset = chain.toFinset \ I := by
  ext i
  simp [mtBlockChainRemainder]

theorem mtBlockChainRemainder_length_le {t : ℕ}
    (chain : List (Fin t)) (I : Finset (Fin t)) :
    (mtBlockChainRemainder chain I).length ≤ chain.length := by
  exact List.length_filter_le _ _

/-- Base scale of the dyadic Type-II `beta` factor for a pair box. -/
def mtMinimalGeometricPairBoxTypeIIM2
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 i2 : Fin t)
    (chain : List (Fin t)) (I : Finset (Fin t)) (eIndex kIndex : ℕ) : ℝ :=
  mtMinimalGeometricPairBoxM1 delta start i1 i2
      (mtBlockChainRemainder chain I) eIndex *
    mtUpperAdicScale delta kIndex

theorem mtMinimalGeometricPairBoxTypeIIM2_pos
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i1 i2 : Fin t) (chain : List (Fin t)) (I : Finset (Fin t))
    (eIndex kIndex : ℕ) :
    0 < mtMinimalGeometricPairBoxTypeIIM2 delta start i1 i2 chain I eIndex kIndex :=
  mul_pos
    (mtMinimalGeometricPairBoxM1_pos hdelta start i1 i2
      (mtBlockChainRemainder chain I) eIndex)
    (mtUpperAdicScale_pos hdelta kIndex)

/-- Signed dyadic remainder factor after extracting selected recursive blocks. -/
def mtMinimalGeometricPairTypeIIBetaAF
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    (mtBlockChainLongAF
      (mtHarmanPairCellCoefficient
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i1)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2))
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block
      (mtBlockChainRemainder chain I) z0 D delta eIndex *
      mtUpperAdicOneAF delta kIndex)

theorem mtMinimalGeometricPairTypeIIBetaAF_scaleSupported
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 4) ≤ 2) :
    MTRealScaleSupported
      (mtMinimalGeometricPairTypeIIBetaAF z0 D start hdelta hz0 hroot
        i1 i2 chain I eIndex kIndex)
      (mtMinimalGeometricPairBoxTypeIIM2 delta start i1 i2 chain I eIndex kIndex)
      (2 * mtMinimalGeometricPairBoxTypeIIM2
        delta start i1 i2 chain I eIndex kIndex) := by
  let remainder := mtBlockChainRemainder chain I
  let Mlong := mtMinimalGeometricPairBoxM1 delta start i1 i2 remainder eIndex
  let K := mtUpperAdicScale delta kIndex
  let F := mtBlockChainLongAF
    (mtHarmanPairCellCoefficient
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i1)
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i2))
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).block remainder z0 D delta eIndex
  have hlong : MTRealScaleSupported F Mlong
      ((1 + delta) ^ (remainder.length + 3) * Mlong) :=
    mtMinimalGeometricPairLongAF_scaleSupported z0 D start hdelta hz0 hroot
      i1 i2 (mtBlockChainRemainder_nodup hchain I) eIndex
  have hmul : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K)
      (((1 + delta) ^ (remainder.length + 3) * Mlong) * ((1 + delta) * K)) :=
    MTRealScaleSupported.mul hlong (mtRealIntervalAF_scaleSupported _ _ _)
      (mtMinimalGeometricPairBoxM1_pos hdelta start i1 i2 remainder eIndex).le
      (mtUpperAdicScale_pos hdelta kIndex).le
  have hnormalized : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) ((1 + delta) ^ (remainder.length + 4) * (Mlong * K)) := by
    intro n hn
    have hs := hmul hn
    refine ⟨hs.1, hs.2.1, hs.2.2.trans_eq ?_⟩
    rw [show remainder.length + 4 = remainder.length + 3 + 1 by omega, pow_succ]
    ring
  have hdyadic : MTRealScaleSupported (F * mtUpperAdicOneAF delta kIndex)
      (Mlong * K) (2 * (Mlong * K)) :=
    MTRealScaleSupported.dyadic_of_dilation hnormalized
      (mul_nonneg
        (mtMinimalGeometricPairBoxM1_pos hdelta start i1 i2 remainder eIndex).le
        (mtUpperAdicScale_pos hdelta kIndex).le) hdilation
  change MTRealScaleSupported
    (((-1 : ℂ) ^ chain.length) • (F * mtUpperAdicOneAF delta kIndex))
    (Mlong * K) (2 * (Mlong * K))
  exact MTRealScaleSupported.smul hdyadic ((-1 : ℂ) ^ chain.length)

theorem mtMinimalGeometricPairTypeIIBetaAF_polynomialDivisorBounded
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    {chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta))}
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex kIndex : ℕ) :
    MTPolynomialDivisorBounded (fun n =>
      mtMinimalGeometricPairTypeIIBetaAF z0 D start hdelta hz0 hroot
        i1 i2 chain I eIndex kIndex n) := by
  have hone : MTPolynomialDivisorBounded (fun _ : ℕ => (1 : ℂ)) := by
    refine ⟨1, by norm_num, 0, ?_⟩
    intro n hn
    simp
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  have hlong : MTPolynomialDivisorBounded (fun n =>
      mtBlockChainLongAF
        (mtHarmanPairCellCoefficient (source.block i1) (source.block i2))
        source.block (mtBlockChainRemainder chain I) z0 D delta eIndex n) :=
    mtBlockChainLongAF_polynomialDivisorBounded
      (block := source.block)
      (mtHarmanPairCellCoefficient_polynomialDivisorBounded
        (source.block i1) (source.block i2))
      (mtBlockChainRemainder_nodup hchain I) z0 D delta eIndex
  have hk : MTPolynomialDivisorBounded
      (fun n => mtUpperAdicOneAF delta kIndex n) :=
    mtRealIntervalAF_polynomialDivisorBounded hone _ _
  change MTPolynomialDivisorBounded (fun n =>
    (((( -1 : ℂ) ^ chain.length) •
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient (source.block i1) (source.block i2))
        source.block (mtBlockChainRemainder chain I) z0 D delta eIndex *
          mtUpperAdicOneAF delta kIndex)) n))
  exact MTPolynomialDivisorBounded.arithmeticFunction_smul
    (MTPolynomialDivisorBounded.arithmeticFunction_mul hlong hk)
    ((-1 : ℂ) ^ chain.length)

/-- Exact algebraic extraction of the selected block family from a signed pair box. -/
theorem mtSignedPairBox_eq_selected_mul_typeIIBeta
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hI : I ⊆ chain.toFinset) (eIndex kIndex : ℕ) :
    mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex =
      mtPrimeBlockFamilyAF
          (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block I *
        mtMinimalGeometricPairTypeIIBetaAF z0 D start hdelta hz0 hroot
          i1 i2 chain I eIndex kIndex := by
  let source := MTFiniteIterationSourceData.ofMinimalGeometricSchedule
    z0 D start delta z hdelta hz0 hroot
  let alpha := mtHarmanPairCellCoefficient (source.block i1) (source.block i2)
  let remainder := mtBlockChainRemainder chain I
  rw [mtSignedBlockChainAdicBoxAF, mtBlockChainAdicBoxAF,
    mtMinimalGeometricPairTypeIIBetaAF, mtBlockChainLongAF,
    mtBlockChainCoefficientAF, mtPrimeBlockFamilyAF_split source.block hI,
    mtBlockChainRemainder_toFinset]
  rw [mul_smul_comm]
  congr 1
  ring

/-- Complete Type-II datum for one pair box and one selected nonempty block subset. -/
def mtMinimalGeometricPairBoxTypeIIData
    {X Y z0Real epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
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
          mtMinimalGeometricPairBoxTypeIIM2
            delta start i1 i2 chain I eIndex kIndex ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricPairBoxTypeIIM2
            delta start i1 i2 chain I eIndex kIndex ≤ 4 * Y) :
    MTTypeIIPieceData X Y z0Real z delta epsilon := by
  let betaAF := mtMinimalGeometricPairTypeIIBetaAF
    z0 D start hdelta hz0 hroot i1 i2 chain I eIndex kIndex
  exact mtMinimalGeometricTypeIIData z0 D start hdelta hz0 hroot I hI
    hz0RealPos hz0RealLevel hR (fun n => betaAF n)
    (mtMinimalGeometricPairBoxTypeIIM2_pos
      hdelta start i1 i2 chain I eIndex kIndex)
    (mtMinimalGeometricPairTypeIIBetaAF_polynomialDivisorBounded
      z0 D start hdelta hz0 hroot i1 i2 hchain I eIndex kIndex)
    hM1 hproduct

/-- Constructed Type-II piece is exactly the original signed pair box. -/
theorem mtMinimalGeometricPairBoxTypeIIData_pieceAF_eq
    {X Y z0Real epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup)
    (I : Finset (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hIS : I ⊆ chain.toFinset) (hI : I.Nonempty) (eIndex kIndex : ℕ)
    (hz0RealPos : 0 < z0Real)
    (hz0RealLevel : z0Real ≤ mtGeometricLevel delta start 0)
    (hR : I.card ≤ Nat.floor (Real.log z / Real.log z0Real))
    (hdilation : (1 + delta) ^ ((mtBlockChainRemainder chain I).length + 4) ≤ 2)
    (hM1 : X ^ (epsilon / 2) ≤
        ∏ i ∈ I, mtGeometricLevel delta start i.1 ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) ≤ z)
    (hproduct : Y / 2 <
        (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricPairBoxTypeIIM2
            delta start i1 i2 chain I eIndex kIndex ∧
      (∏ i ∈ I, mtGeometricLevel delta start i.1) *
          mtMinimalGeometricPairBoxTypeIIM2
            delta start i1 i2 chain I eIndex kIndex ≤ 4 * Y) :
    (mtMinimalGeometricPairBoxTypeIIData z0 D start hdelta hz0 hroot
      i1 i2 chain hchain I hI eIndex kIndex hz0RealPos hz0RealLevel hR
      hM1 hproduct).pieceAF =
      mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex := by
  let betaAF := mtMinimalGeometricPairTypeIIBetaAF
    z0 D start hdelta hz0 hroot i1 i2 chain I eIndex kIndex
  have hbetaSupport : MTRealScaleSupported betaAF
      (mtMinimalGeometricPairBoxTypeIIM2 delta start i1 i2 chain I eIndex kIndex)
      (2 * mtMinimalGeometricPairBoxTypeIIM2
        delta start i1 i2 chain I eIndex kIndex) :=
    mtMinimalGeometricPairTypeIIBetaAF_scaleSupported
      z0 D start hdelta hz0 hroot i1 i2 hchain I eIndex kIndex hdilation
  rw [mtMinimalGeometricPairBoxTypeIIData,
    mtMinimalGeometricTypeIIData_pieceAF_eq]
  rw [mtRealIntervalAF_coe_eq_of_scaleSupported hbetaSupport]
  exact (mtSignedPairBox_eq_selected_mul_typeIIBeta
    z0 D start hdelta hz0 hroot i1 i2 chain I hIS eIndex kIndex).symm

end

end RHTower.Sieve
