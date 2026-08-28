import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGeometricBoxSupport

/-!
# Exact Type-I presentation of a small pair box

When the recursive block product lies in the small branch and total narrow dilation fits inside a
dyadic interval, one signed pair box is literally a Proposition 2.2 Type-I piece.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem MTRealScaleSupported.smul
    {F : ArithmeticFunction ℂ} {L U : ℝ}
    (hF : MTRealScaleSupported F L U) (c : ℂ) :
    MTRealScaleSupported (c • F) L U := by
  intro n hn
  apply hF
  intro hzero
  apply hn
  simp [hzero]

theorem MTPolynomialDivisorBounded.arithmeticFunction_smul
    {F : ArithmeticFunction ℂ}
    (hF : MTPolynomialDivisorBounded (fun n => F n)) (c : ℂ) :
    MTPolynomialDivisorBounded (fun n => (c • F) n) := by
  change MTPolynomialDivisorBounded (fun n => c * F n)
  exact hF.smul c

/-- Base scale of one pair long factor. -/
def mtMinimalGeometricPairBoxM1
    {t : ℕ} (delta : ℝ) (start : ℕ) (i1 i2 : Fin t)
    (chain : List (Fin t)) (eIndex : ℕ) : ℝ :=
  ((mtGeometricLevel delta start i1.1 * mtGeometricLevel delta start i2.1) *
      ∏ j ∈ chain.toFinset, mtGeometricLevel delta start j.1) *
    mtUpperAdicScale delta eIndex

theorem mtMinimalGeometricPairBoxM1_pos
    {t : ℕ} {delta : ℝ} (hdelta : 0 < delta) (start : ℕ)
    (i1 i2 : Fin t) (chain : List (Fin t)) (eIndex : ℕ) :
    0 < mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex := by
  rw [mtMinimalGeometricPairBoxM1]
  exact mul_pos
    (mul_pos
      (mul_pos (mtGeometricLevel_pos hdelta start i1.1)
        (mtGeometricLevel_pos hdelta start i2.1))
      (Finset.prod_pos fun j hj => mtGeometricLevel_pos hdelta start j.1))
    (mtUpperAdicScale_pos hdelta eIndex)

/-- Signed long coefficient of a pair box. -/
def mtMinimalGeometricSignedPairLongAF
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (eIndex : ℕ) : ArithmeticFunction ℂ :=
  ((-1 : ℂ) ^ chain.length) •
    mtBlockChainLongAF
      (mtHarmanPairCellCoefficient
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i1)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2))
      (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block chain z0 D delta eIndex

/-- Complete Type-I datum for one small signed pair box. -/
def mtMinimalGeometricPairBoxTypeIData
    {X Y epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ (chain.length + 3) ≤ 2)
    (hM1le : mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex ≤
      X ^ (1 / 2 + epsilon))
    (hproduct : Y / 2 <
        mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
          mtUpperAdicScale delta kIndex ∧
      mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
          mtUpperAdicScale delta kIndex ≤ 4 * Y) :
    MTTypeIPieceData X Y delta epsilon := by
  let F := mtMinimalGeometricSignedPairLongAF
    z0 D start hdelta hz0 hroot i1 i2 chain eIndex
  have hunsigned : MTRealScaleSupported
      (mtBlockChainLongAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain z0 D delta eIndex)
      (mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex)
      (2 * mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex) :=
    mtMinimalGeometricPairLongAF_scaleSupported_dyadic
      z0 D start hdelta hz0 hroot i1 i2 hchain eIndex hdilation
  have hFsupport : MTRealScaleSupported F
      (mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex)
      (2 * mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex) :=
    MTRealScaleSupported.smul hunsigned ((-1 : ℂ) ^ chain.length)
  have hFbounded : MTPolynomialDivisorBounded (fun n => F n) :=
    (mtBlockChainLongAF_polynomialDivisorBounded
      (mtHarmanPairCellCoefficient_polynomialDivisorBounded
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i1)
        ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block i2))
      hchain z0 D delta eIndex).arithmeticFunction_smul
        ((-1 : ℂ) ^ chain.length)
  exact mtTypeIPieceDataOfSupported F
    (mtMinimalGeometricPairBoxM1_pos hdelta start i1 i2 chain eIndex)
    (mtUpperAdicScale_pos hdelta kIndex) hFsupport hFbounded hM1le hproduct

/-- The constructed Type-I piece is exactly the original signed pair box. -/
theorem mtMinimalGeometricPairBoxTypeIData_pieceAF_eq
    {X Y epsilon : ℝ}
    (z0 D start : ℕ) {delta z : ℝ} (hdelta : 0 < delta)
    (hz0 : (z0 : ℝ) ≤ mtGeometricLevel delta start 0)
    (hroot : mtGeometricLevel delta start 0 < z)
    (i1 i2 : Fin (mtMinimalGeometricDepth delta start z hdelta))
    (chain : List (Fin (mtMinimalGeometricDepth delta start z hdelta)))
    (hchain : chain.Nodup) (eIndex kIndex : ℕ)
    (hdilation : (1 + delta) ^ (chain.length + 3) ≤ 2)
    (hM1le : mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex ≤
      X ^ (1 / 2 + epsilon))
    (hproduct : Y / 2 <
        mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
          mtUpperAdicScale delta kIndex ∧
      mtMinimalGeometricPairBoxM1 delta start i1 i2 chain eIndex *
          mtUpperAdicScale delta kIndex ≤ 4 * Y) :
    (mtMinimalGeometricPairBoxTypeIData z0 D start hdelta hz0 hroot
      i1 i2 chain hchain eIndex kIndex hdilation hM1le hproduct).pieceAF =
      mtSignedBlockChainAdicBoxAF
        (mtHarmanPairCellCoefficient
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i1)
          ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
            z0 D start delta z hdelta hz0 hroot).block i2))
        (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
          z0 D start delta z hdelta hz0 hroot).block chain
        z0 D delta eIndex kIndex := by
  let F := mtBlockChainLongAF
    (mtHarmanPairCellCoefficient
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i1)
      ((MTFiniteIterationSourceData.ofMinimalGeometricSchedule
        z0 D start delta z hdelta hz0 hroot).block i2))
    (MTFiniteIterationSourceData.ofMinimalGeometricSchedule
      z0 D start delta z hdelta hz0 hroot).block chain z0 D delta eIndex
  rw [mtMinimalGeometricPairBoxTypeIData,
    mtTypeIPieceDataOfSupported_pieceAF_eq]
  change (((-1 : ℂ) ^ chain.length) • F) * mtUpperAdicOneAF delta kIndex = _
  rw [smul_mul_assoc]
  rw [← mtBlockChainAdicBoxAF_eq_long_mul_upperAdicOne]
  rfl

end

end RHTower.Sieve
