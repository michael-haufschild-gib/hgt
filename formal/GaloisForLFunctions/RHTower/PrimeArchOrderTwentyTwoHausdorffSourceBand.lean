import GaloisForLFunctions.RHTower.PrimeArchOppositePhasePurePowerPropagation
import GaloisForLFunctions.RHTower.PrimeArchOrderTwentyOneHausdorffSourceBand
import GaloisForLFunctions.RHTower.XiCenteredOrderTwentyTwoSourceBudgetClosure

/-!
# Order-twenty-two endpoint Hausdorff source band

Unconditional positivity of every reciprocal-square 22nd power, combined with
the generic opposite-phase propagation law, proves the complete endpoint row
`k = 21`, `r ≤ 57`.  The unconditional rectangle grows to `22 × 58`, and
its complement remains exactly equivalent to RH.
-/

open Complex Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

theorem re_xiCentral_scaledBasis_orderTwentyTwoBand_nonneg
    (q : XiZeroCopy) (r : ℕ) (hr : r ≤ 57) :
    0 ≤ (xiZeroCopyReciprocalSquare q ^ 22 *
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
    change 0 ≤ (z ^ 22 * w ^ r).re
    rw [hzReal, hwReal]
    norm_cast
    exact mul_nonneg (pow_nonneg hzre.le 22)
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
    have hzpow : 0 < (z ^ 22).re := by
      simpa only [z] using xiZeroCopyReciprocalSquare_pow_twentyTwo_re_pos q
    exact re_pow_mul_pow_nonneg_of_opposite_phase_of_pow_pos_bounded
      z w 22 r hzre hwre hwim hzsector hwsector hzpow (by norm_num) hr

theorem scaledPrimeArchEndpointHausdorffDifference_orderTwentyTwoBand_nonnegative
    (r : ℕ) (hr : r ≤ 57) :
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment 21 r := by
  rw [scaledHausdorffMomentDifference_eq_re_xiCentralSum,
    Complex.re_tsum (summable_xiCentralScaledHausdorffTerm
      primeArchEndpointHausdorffRadius 21 r)]
  apply tsum_nonneg
  intro q
  exact re_xiCentral_scaledBasis_orderTwentyTwoBand_nonneg q r hr

def PrimeArchEndpointOrderTwentyTwoHausdorffTailNonnegative : Prop :=
  ∀ k r : ℕ, 21 < k ∨ 57 < r →
    0 ≤ scaledHausdorffMomentDifference primeArchEndpointHausdorffRadius
      normalizedPrimeArchMoment k r

theorem primeArchEndpointOrderTwentyOneHausdorffTailNonnegative_iff_orderTwentyTwoTailNonnegative :
    PrimeArchEndpointOrderTwentyOneHausdorffTailNonnegative ↔
      PrimeArchEndpointOrderTwentyTwoHausdorffTailNonnegative := by
  constructor
  · intro hold k r htail
    exact hold k r (by omega)
  · intro hnew k r htail
    by_cases hr : r ≤ 57
    · by_cases hk : k ≤ 21
      · have hk21 : k = 21 := by omega
        subst k
        exact scaledPrimeArchEndpointHausdorffDifference_orderTwentyTwoBand_nonnegative r hr
      · exact hnew k r (Or.inl (by omega))
    · exact hnew k r (Or.inr (by omega))

theorem primeArchEndpointOrderTwentyTwoHausdorffTailNonnegative_iff_riemannHypothesis :
    PrimeArchEndpointOrderTwentyTwoHausdorffTailNonnegative ↔ RiemannHypothesis :=
  primeArchEndpointOrderTwentyOneHausdorffTailNonnegative_iff_orderTwentyTwoTailNonnegative.symm.trans
    primeArchEndpointOrderTwentyOneHausdorffTailNonnegative_iff_riemannHypothesis

theorem primeArchEndpointOrderTwentyTwoHausdorffRectangle_cardinality :
    22 * 58 = 1276 := by
  norm_num

end

end RHTower
