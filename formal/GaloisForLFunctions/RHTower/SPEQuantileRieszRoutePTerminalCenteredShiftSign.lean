import GaloisForLFunctions.RHTower.CCMActualHeadMatchedQuantilePolarParabolicCenteredBoundary

/-!
# Sign of Route-P's canonical terminal centering shift

The literal matched--quantile source boundary has strictly positive mass and
strictly positive first moment.  Its canonical barycentric parabolic shift is
therefore strictly negative.  This fixes the direction of the physical
terminal coefficient `sqrt M + shift`; proving its magnitude comparison at
the physical wall remains the separate Route-P obstacle.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

private theorem ccmParabolicMoment_one_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ ccmParabolicMoment a b 1 := by
  have hsquares : 0 ≤ b ^ 2 - a ^ 2 := by
    calc
      0 ≤ (b - a) * (b + a) := mul_nonneg (sub_nonneg.mpr hab) (by linarith)
      _ = b ^ 2 - a ^ 2 := by ring
  simp [ccmParabolicMoment]
  positivity

private theorem ccmParabolicMoment_one_pos
    {a b : ℝ} (ha : 0 ≤ a) (hgap : 0 < b - a) :
    0 < ccmParabolicMoment a b 1 := by
  have hsum : 0 < b + a := by linarith
  have hsquares : 0 < b ^ 2 - a ^ 2 := by
    calc
      0 < (b - a) * (b + a) := mul_pos hgap hsum
      _ = b ^ 2 - a ^ 2 := by ring
  simp [ccmParabolicMoment]
  linarith

private theorem ccmActualHeadMatchedParabolicMoment_one_nonneg (n : ℕ) :
    0 ≤ ccmActualHeadMatchedParabolicMoment n 1 := by
  apply ccmParabolicMoment_one_nonneg
  · unfold ccmActualHeadMatchedPolarLowerCoordinate
    positivity
  · apply sub_nonneg.mp
    rw [ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]
    exact criticalMellinAtomWeight_nonneg n

private theorem ccmActualHeadMatchedParabolicMoment_two_one_pos :
    0 < ccmActualHeadMatchedParabolicMoment 2 1 := by
  apply ccmParabolicMoment_one_pos
  · unfold ccmActualHeadMatchedPolarLowerCoordinate
    positivity
  · rw [ccmActualHeadMatchedPolarUpper_sub_lower_eq_atomWeight]
    exact criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow

private theorem ccmActualHeadQuantileParabolicMoment_one_nonneg (n : ℕ) :
    0 ≤ ccmActualHeadQuantileParabolicMoment n 1 := by
  let a := ccmActualHeadQuantilePolarCoordinate n
  let b := ccmActualHeadQuantilePolarCoordinate (n + 1)
  have ha : 0 ≤ a := by
    dsimp [a, ccmActualHeadQuantilePolarCoordinate]
    positivity
  have hb : 0 ≤ b := by
    dsimp [b, ccmActualHeadQuantilePolarCoordinate]
    positivity
  have hab : a ≤ b := by
    apply sub_nonneg.mp
    rw [show b - a = ccmActualHeadQuantilePolarCoordinate (n + 1) -
        ccmActualHeadQuantilePolarCoordinate n by rfl,
      ccmActualHeadQuantilePolarCoordinate_succ_sub_eq_atomWeight]
    exact criticalMellinAtomWeight_nonneg n
  exact ccmParabolicMoment_one_nonneg ha hab

/-- The literal finite source boundary has strictly positive first moment.
The prime-`2` matched cell supplies strictness; every remaining matched or
quantile cell has nonnegative first moment. -/
theorem ccmActualHeadMatchedQuantileParabolicSourceBoundary_one_pos (K : ℕ) :
    0 < ccmActualHeadMatchedQuantileParabolicSourceBoundary K 1 := by
  have hmatched : 0 < ccmActualHeadMatchedParabolicAggregate K 1 := by
    unfold ccmActualHeadMatchedParabolicAggregate
    simp only [Finset.sum_apply]
    have htwo : 0 < ccmActualHeadMatchedParabolicMoment 2 1 :=
      ccmActualHeadMatchedParabolicMoment_two_one_pos
    have hmem : 0 ∈ Finset.range (K + 1) := Finset.mem_range.mpr (by omega)
    have hle : ccmActualHeadMatchedParabolicMoment 2 1 ≤
        ∑ n ∈ Finset.range (K + 1), ccmActualHeadMatchedParabolicMoment (n + 2) 1 := by
      simpa using Finset.single_le_sum
        (s := Finset.range (K + 1))
        (f := fun n => ccmActualHeadMatchedParabolicMoment (n + 2) 1)
        (fun n _ => ccmActualHeadMatchedParabolicMoment_one_nonneg (n + 2)) hmem
    exact htwo.trans_le hle
  have hquantile : 0 ≤ ccmActualHeadQuantileParabolicAggregate K 1 := by
    unfold ccmActualHeadQuantileParabolicAggregate
    simp only [Finset.sum_apply]
    exact Finset.sum_nonneg fun n _ =>
      ccmActualHeadQuantileParabolicMoment_one_nonneg (n + 2)
  unfold ccmActualHeadMatchedQuantileParabolicSourceBoundary
  simp only [Pi.add_apply]
  linarith

/-- Canonical centering of the literal source boundary always shifts toward
the negative parabolic direction. -/
theorem ccmActualHeadMatchedQuantileParabolicCenteredShift_neg (K : ℕ) :
    ccmActualHeadMatchedQuantileParabolicCenteredShift K < 0 := by
  unfold ccmActualHeadMatchedQuantileParabolicCenteredShift
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (ccmActualHeadMatchedQuantileParabolicSourceBoundary_one_pos K))
    (ccmActualHeadMatchedQuantileParabolicSourceBoundary_zero_pos K)

end RHTower
