import GaloisForLFunctions.RHTower.PrimeArchScaledHausdorffDivisorValueRelation
import GaloisForLFunctions.RHTower.PrimeArchFiniteKMSLocalMomentClosure
import GaloisForLFunctions.RHTower.CCM.CCMCumulativeNegativeMassSpectrum

/-!
# Endpoint Hausdorff source--temperature master law

The endpoint-calibrated Hausdorff array has three exact descriptions: a prime--Gamma moment
difference, a reciprocal-square Xi-divisor value, and a finite-KMS closure condition.  The
opposite-phase sector estimate proves the complete `14 × 44` southwest rectangle
unconditionally.  Consequently RH is carried entirely by the complementary cofinal tail.

This file packages the value relation, the unconditional estimate, and the remaining tail as one
master theorem.
-/

open scoped BigOperators Polynomial
open Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- The positive carrier left after the unconditional endpoint rectangle has been discharged. -/
def PrimeArchEndpointHausdorffTailNonnegative : Prop :=
  ∀ k r : ℕ, 13 < k ∨ 43 < r →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r

/-- The complementary tail is exactly the full endpoint-calibrated Hausdorff condition. -/
theorem primeArchEndpointHausdorffTailNonnegative_iff_full :
    PrimeArchEndpointHausdorffTailNonnegative ↔
      ScaledHausdorffMomentDifferencesNonnegative primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment :=
  scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_rectangleTailNonnegative.symm

/-- After the `14 × 44` rectangle is paid unconditionally, RH is precisely positivity of the
remaining cofinal tail. -/
theorem primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis :
    PrimeArchEndpointHausdorffTailNonnegative ↔ RiemannHypothesis :=
  primeArchEndpointHausdorffTailNonnegative_iff_full.trans
    scaledPrimeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis

/-- The same tail is precisely the finite-KMS local closure condition. -/
theorem primeArchEndpointHausdorffTailNonnegative_iff_finiteKMSLocalMomentClosure :
    PrimeArchEndpointHausdorffTailNonnegative ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure :=
  primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis.trans
    primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis.symm

/-- The same tail is precisely the critical cumulative growth law for the literal finite
prime--polar source. -/
theorem primeArchEndpointHausdorffTailNonnegative_iff_cumulativeNegativeMassCriticalGrowth
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    PrimeArchEndpointHausdorffTailNonnegative ↔
      NonnegativeDirichletSummatoryGrowthAt
        (rectangularPrimePolarSourceTailNegativePart L N) 1 :=
  primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis.trans
    (riemannHypothesis_iff_rectangularPrimePolarSource_cumulativeNegativeMassCriticalGrowth
      hL hN)

/-- The discharged southwest rectangle contains exactly 616 indexed inequalities. -/
theorem primeArchEndpointHausdorffRectangle_cardinality : 14 * 44 = 616 := by
  norm_num

/-- **Endpoint Hausdorff source--temperature master theorem.**

Every calibrated difference is an exact Xi-divisor polynomial value; the entire `14 × 44`
rectangle is nonnegative without RH; and the complementary tail is simultaneously the RH
condition, the critical source-abscissa endpoint, and finite KMS/Wightman local closure. -/
theorem primeArchEndpointHausdorffSourceTemperatureMaster
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    (∀ k r : ℕ,
      scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
          normalizedPrimeArchMoment k r =
        (∑' q : XiZeroCopy,
          xiZeroCopyReciprocalSquare q ^ (k + 1) *
            ((primeArchEndpointHausdorffRadius : ℂ) -
              xiZeroCopyReciprocalSquare q) ^ r).re) ∧
    (∀ k r : ℕ, k ≤ 13 → r ≤ 43 →
      0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
        normalizedPrimeArchMoment k r) ∧
    (PrimeArchEndpointHausdorffTailNonnegative ↔ RiemannHypothesis) ∧
    (LSeries.abscissaOfAbsConv
        (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤
          ((1 : ℝ) : EReal) ↔ PrimeArchEndpointHausdorffTailNonnegative) ∧
    (PrimeArchEndpointHausdorffTailNonnegative ↔
      NonnegativeDirichletSummatoryGrowthAt
        (rectangularPrimePolarSourceTailNegativePart L N) 1) ∧
    (PrimeArchEndpointHausdorffTailNonnegative ↔
      PrimeArchFiniteKMSWightmanLocalMomentClosure) := by
  exact ⟨fun k r => scaledHausdorffMomentDifference_eq_re_xiCentralSum
      primeArchEndpointHausdorffRadius k r,
    fun k r hk hr =>
      scaledPrimeArchEndpointHausdorffDifference_rectangle_nonnegative k r hk hr,
    primeArchEndpointHausdorffTailNonnegative_iff_riemannHypothesis,
    rectangularPrimePolarSource_negativeAbscissa_le_one_iff_rectangleHausdorffTailNonnegative
      hL hN,
    primeArchEndpointHausdorffTailNonnegative_iff_cumulativeNegativeMassCriticalGrowth hL hN,
    primeArchEndpointHausdorffTailNonnegative_iff_finiteKMSLocalMomentClosure⟩

end

end RHTower
