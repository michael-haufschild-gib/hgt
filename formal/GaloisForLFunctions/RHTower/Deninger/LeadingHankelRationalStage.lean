import GaloisForLFunctions.HTGeometry.Moments.FiniteStateLeadingMinors
import GaloisForLFunctions.RHTower.Deninger.DeningerKroneckerFieldStage

/-!
# Leading Hankel determinants detect rational Witt stages

The leading-minor theorem reduces Deninger's field-valued Hankel-rank condition
from all choices of rows and columns to the single chain of leading blocks.
The bound is unchanged: vanishing above size `n` is equivalent to a normalized
rational Witt presentation with numerator degree less than `n` and denominator
degree at most `n`.
-/

namespace RHTower

open HTGeometry.FiniteHankel

/-- For normalized Witt series, the leading determinant tail detects the full Hankel rank. -/
theorem deningerField_leadingTail_iff_hankelRankLT
    {K : Type*} [Field K] (n : ℕ) (w : DeningerBigWittAdditive K) :
    (∀ m, n < m → leadingDet (fun i => PowerSeries.coeff i (deningerBigWittSeries w)) m = 0) ↔
      DeningerBigWittHankelRankLT (n + 1) w := by
  let a : ℕ → K := fun i => PowerSeries.coeff i (deningerBigWittSeries w)
  constructor
  · intro h rows cols
    obtain ⟨d, hdn, hs⟩ := (leading_tail_zero_iff_stateSpace a n).mp h
    exact arbitrary_minor_zero_of_stateSpace hs (by omega) rows cols
  · intro h
    have ha0 : a 0 = 1 := by
      simpa [a, PowerSeries.constantCoeff] using deningerBigWittSeries_constantCoeff w
    let r := deningerFieldHankelRecurrence_of_rankLT a n ha0 (by
      intro rows cols
      exact h rows cols)
    exact (leading_tail_zero_iff_recurrence a n).mpr
      ⟨⟨r.order, r.coeff⟩, r.order_le, r.recurrence⟩

/-- Rational Witt stage membership can be tested using leading determinants alone. -/
theorem deningerField_leadingTail_iff_exists_rationalWittStage
    {K : Type*} [Field K] (n : ℕ) (w : DeningerBigWittAdditive K) :
    (∀ m, n < m → leadingDet (fun i => PowerSeries.coeff i (deningerBigWittSeries w)) m = 0) ↔
      ∃ x : DeningerCanonicalRationalWittRing K,
        DeningerCanonicalRationalWittStageLE n x ∧
          deningerCanonicalRationalWittBigWittCarrier x = w :=
  (deningerField_leadingTail_iff_hankelRankLT n w).trans
    (deningerField_hankelRankLT_iff_exists_rationalWittStage n w)

/-- Leading determinant bounds alone propagate through Witt multiplication with the
corrected resultant-degree bound. -/
theorem deningerField_leadingTail_mul_corrected
    {K : Type*} [Field K] {n m : ℕ} {u v : DeningerBigWittAdditive K}
    (hu : ∀ k, n < k → leadingDet (fun i => PowerSeries.coeff i (deningerBigWittSeries u)) k = 0)
    (hv : ∀ k, m < k → leadingDet (fun i => PowerSeries.coeff i (deningerBigWittSeries v)) k = 0) :
    ∀ k, deningerCorrectedWittMulStageBound n m < k →
      leadingDet (fun i => PowerSeries.coeff i
        (deningerBigWittSeries (deningerBigWittMul u v))) k = 0 :=
  (deningerField_leadingTail_iff_hankelRankLT _ _).mpr
    (deningerField_hankelRankLT_mul_corrected
      ((deningerField_leadingTail_iff_hankelRankLT n u).mp hu)
      ((deningerField_leadingTail_iff_hankelRankLT m v).mp hv))

#print axioms deningerField_leadingTail_iff_hankelRankLT
#print axioms deningerField_leadingTail_iff_exists_rationalWittStage
#print axioms deningerField_leadingTail_mul_corrected

end RHTower
