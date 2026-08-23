import GaloisForLFunctions.RHTower.PrimeArchOrderTwentyOneMixedHausdorffClaw
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyOneSourceBudgetClosure

/-!
# Order-twenty-one endpoint Hausdorff source band

The unconditional source-budget closure empties the centered order-21 residual
annulus.  Thus every twenty-first reciprocal-square power is right-facing.
Opposite phase of the endpoint-complement factor preserves nonnegativity through
all complement powers `r ≤ 57`.

This upgrades the unconditional endpoint rectangle from `20 × 58` to
`21 × 58`, removing the complete `k = 20` row from the RH-equivalent tail.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Every order-21 endpoint atom is nonnegative throughout the established complement band. -/
theorem re_xiCentral_scaledBasis_orderTwentyOneBand_nonneg
    (q : XiZeroCopy) (r : ℕ) (hr : r ≤ 57) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 21 *
      ((primeArchEndpointHausdorffRadius : ℂ) -
        xiZeroCopyReciprocalSquare q) ^ r).re := by
  let z := xiZeroCopyReciprocalSquare q
  let R := primeArchEndpointHausdorffRadius
  let w : ℂ := (R : ℂ) - z
  by_cases hon : (q.1 : ℂ).re = 1 / 2
  · have him : z.im = 0 := by
      dsimp only [z]
      rw [xiZeroCopyReciprocalSquare_im_formula, hon]
      norm_num
    have hzReal : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hwReal : w = ((R - z.re : ℝ) : ℂ) := by
      dsimp only [w]
      rw [hzReal]
      norm_num
    have hzre : 0 < z.re := by
      simpa only [z, xiThermalNode] using xiThermalNode_pos q
    have hzleR : z.re ≤ R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_le_primeArchEndpointHausdorffRadius q
    change 0 ≤ (z ^ 21 * w ^ r).re
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre.le 21)
      (pow_nonneg (sub_nonneg.mpr hzleR) r)
  · have hzre : 0 < z.re := by
      simpa only [z, xiThermalNode] using xiThermalNode_pos q
    have hzQuarter : z.re < (1 / 4 : ℝ) * R := by
      simpa only [z, R, xiThermalNode] using
        xiThermalNode_lt_one_fourth_endpointRadius_of_offLine q hon
    have hwre : 0 < w.re := by
      dsimp only [w]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith [primeArchEndpointHausdorffRadius_pos]
    have hzsector : (121 / 10 : ℝ) * |z.im| ≤ z.re := by
      simpa only [z] using twelvePointOne_mul_abs_im_xiZeroCopyReciprocalSquare_le_re q
    have hwsector : (363 / 10 : ℝ) * |w.im| ≤ w.re := by
      dsimp only [w]
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, abs_neg,
        Complex.sub_re, Complex.ofReal_re]
      nlinarith
    have hwim : w.im = -z.im := by dsimp only [w]; simp
    have hnot : ¬ XiCenteredOrderTwentyOneResidualAnnulus q := by
      intro hq
      exact xiCenteredOrderTwentyOneResidualAnnulusEmpty ⟨q, hq⟩
    have hzpow : 0 < (z ^ 21).re := by
      simpa only [z] using
        xiZeroCopyReciprocalSquare_pow_twentyOne_re_pos_of_not_mem_residualAnnulus q hnot
    exact re_twentyOne_pow_mul_pow_nonneg_of_opposite_phase_of_pow_pos
      z w r hzre hwre hwim hzsector hwsector hzpow hr

/-- The complete `k = 20`, `r ≤ 57` endpoint Hausdorff row is unconditional. -/
theorem scaledPrimeArchEndpointHausdorffDifference_orderTwentyOneBand_nonnegative
    (r : ℕ) (hr : r ≤ 57) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 20 r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 20 r)]
  apply tsum_nonneg
  intro q
  exact re_xiCentral_scaledBasis_orderTwentyOneBand_nonneg q r hr

/-- Remaining endpoint carrier after deleting the complete `21 × 58` rectangle. -/
def PrimeArchEndpointOrderTwentyOneHausdorffTailNonnegative : Prop :=
  ∀ k r : ℕ, 20 < k ∨ 57 < r →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r

/-- The former order-20 tail is exactly the order-21 tail after deleting the new row. -/
theorem primeArchEndpointOrderTwentyHausdorffTailNonnegative_iff_orderTwentyOneTailNonnegative :
    PrimeArchEndpointOrderTwentyHausdorffTailNonnegative ↔
      PrimeArchEndpointOrderTwentyOneHausdorffTailNonnegative := by
  constructor
  · intro hold k r htail
    exact hold k r (by omega)
  · intro hnew k r htail
    by_cases hr : r ≤ 57
    · by_cases hk : k ≤ 20
      · have hk20 : k = 20 := by omega
        subst k
        exact scaledPrimeArchEndpointHausdorffDifference_orderTwentyOneBand_nonnegative r hr
      · exact hnew k r (Or.inl (by omega))
    · exact hnew k r (Or.inr (by omega))

/-- The reduced order-21 endpoint tail remains exactly equivalent to RH. -/
theorem primeArchEndpointOrderTwentyOneHausdorffTailNonnegative_iff_riemannHypothesis :
    PrimeArchEndpointOrderTwentyOneHausdorffTailNonnegative ↔ RiemannHypothesis :=
  primeArchEndpointOrderTwentyHausdorffTailNonnegative_iff_orderTwentyOneTailNonnegative.symm.trans
    primeArchEndpointOrderTwentyHausdorffTailNonnegative_iff_riemannHypothesis

/-- The enlarged rectangle contains exactly 1218 indexed inequalities. -/
theorem primeArchEndpointOrderTwentyOneHausdorffRectangle_cardinality :
    21 * 58 = 1218 := by
  norm_num

end

end RHTower
