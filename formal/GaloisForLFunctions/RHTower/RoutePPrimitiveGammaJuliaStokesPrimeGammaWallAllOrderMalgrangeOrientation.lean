import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallSexticMalgrangePositiveOrientation
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# All-order orientation of the prime/Gamma wall Malgrange jets

Ordinary conjugation makes every reciprocal-square Xi atom occur in a distinct equal-norm pair.
The exact second source-moment budget therefore bounds twice each squared atom norm, improving the
uniform reciprocal-square radius from `231 / 9769` to `1 / 150`.  This radius is three times smaller
than the `1 / 50` ratio of successive forced first-jet scales.  One rational base comparison at
order two consequently propagates to every later order.

Thus every cold Malgrange target from order two onward has its exact alternating orientation,
without finite-order enumeration, an RH premise, zero selection, or numerical computation.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem secondMomentRadiusEnvelope_lt_firstJetFloor (k : ℕ) :
    (1 / 150 : ℝ) ^ k *
        ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) <
      (1 / 25 : ℝ) ^ (k + 2) / (2 : ℝ) ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hleft :
          (1 / 150 : ℝ) ^ k.succ *
              ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) =
            ((1 / 150 : ℝ) ^ k *
              ((42 / 41 : ℝ) * (17 / 200000 : ℝ))) / 150 := by
        rw [pow_succ]
        ring
      have hright :
          (1 / 25 : ℝ) ^ (k.succ + 2) / (2 : ℝ) ^ (k.succ + 1) =
            ((1 / 25 : ℝ) ^ (k + 2) / (2 : ℝ) ^ (k + 1)) / 50 := by
        rw [show k.succ + 2 = (k + 2) + 1 by omega,
          show k.succ + 1 = (k + 1) + 1 by omega, pow_succ, pow_succ]
        ring
      rw [hleft, hright]
      calc
        ((1 / 150 : ℝ) ^ k *
            ((42 / 41 : ℝ) * (17 / 200000 : ℝ))) / 150 <
            ((1 / 25 : ℝ) ^ (k + 2) / (2 : ℝ) ^ (k + 1)) / 150 :=
          div_lt_div_of_pos_right ih (by norm_num)
        _ < ((1 / 25 : ℝ) ^ (k + 2) / (2 : ℝ) ^ (k + 1)) / 50 := by
          have hpos : 0 <
              (1 / 25 : ℝ) ^ (k + 2) / (2 : ℝ) ^ (k + 1) := by
            positivity
          nlinarith

/-- Every positive-index cold residual lies below its forced first-jet scale. -/
theorem normalizedPrimeArchMoment_sub_firstJetScale_neg_of_one_le
    (n : ℕ) (hn : 1 ≤ n) :
    normalizedPrimeArchMoment n -
      normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n < 0 := by
  have habsRaw :=
    abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 1 (n - 1)
  have habs : |normalizedPrimeArchMoment n| ≤
      (1 / 150 : ℝ) ^ (n - 1) * xiShiftAbsoluteMass 1 := by
    simpa only [show 1 + (n - 1) = n by omega] using habsRaw
  have hmass := xiShiftAbsoluteMass_one_lt_secondMomentBudget
  have hradiusPowPos : 0 < (1 / 150 : ℝ) ^ (n - 1) := by positivity
  have hmUpper : normalizedPrimeArchMoment n <
      (1 / 150 : ℝ) ^ (n - 1) *
        ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) :=
    (le_abs_self (normalizedPrimeArchMoment n)).trans habs |>.trans_lt
      (mul_lt_mul_of_pos_left hmass hradiusPowPos)
  have hrat :
      (1 / 150 : ℝ) ^ (n - 1) *
          ((42 / 41 : ℝ) * (17 / 200000 : ℝ)) <
        (1 / 25 : ℝ) ^ (n + 1) / (2 : ℝ) ^ n := by
    simpa only [show n - 1 + 2 = n + 1 by omega,
      show n - 1 + 1 = n by omega] using
        secondMomentRadiusEnvelope_lt_firstJetFloor (n - 1)
  have hm0 := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
  have hm0pow : (1 / 25 : ℝ) ^ (n + 1) <
      normalizedPrimeArchMoment 0 ^ (n + 1) :=
    pow_lt_pow_left₀ hm0 (by norm_num) (Nat.succ_ne_zero n)
  have htarget : (1 / 25 : ℝ) ^ (n + 1) / (2 : ℝ) ^ n <
      normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n :=
    div_lt_div_of_pos_right hm0pow (pow_pos (by norm_num) n)
  linarith

/-- Every cold Malgrange target from order two onward has its exact alternating orientation. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallColdMalgrangeTarget_signed_pos_of_one_le
    (n : ℕ) (hn : 1 ≤ n) :
    0 < (-1 : ℝ) ^ (n + 1) *
      ((-1 : ℝ) ^ n * (n.factorial : ℝ) *
        (normalizedPrimeArchMoment n / 2 -
          (normalizedPrimeArchMoment 0 / 2) ^ (n + 1))) := by
  have hres := normalizedPrimeArchMoment_sub_firstJetScale_neg_of_one_le n hn
  have htwoPow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  have hscale :
      normalizedPrimeArchMoment n / 2 -
          (normalizedPrimeArchMoment 0 / 2) ^ (n + 1) =
        (normalizedPrimeArchMoment n -
          normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n) / 2 := by
    rw [div_pow, show (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 by rw [pow_succ]]
    field_simp [htwoPow]
  have hinner : normalizedPrimeArchMoment n / 2 -
      (normalizedPrimeArchMoment 0 / 2) ^ (n + 1) < 0 := by
    rw [hscale]
    nlinarith
  have hsign : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n = -1 := by
    rw [pow_succ]
    calc
      ((-1 : ℝ) ^ n * -1) * (-1 : ℝ) ^ n =
          -(((-1 : ℝ) ^ n) * (-1 : ℝ) ^ n) := by ring
      _ = -((-1 : ℝ) ^ (n + n)) := by rw [pow_add]
      _ = -((-1 : ℝ) ^ (2 * n)) := by rw [show n + n = 2 * n by omega]
      _ = -1 := by rw [pow_mul]; norm_num
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  calc
    (-1 : ℝ) ^ (n + 1) *
        ((-1 : ℝ) ^ n * (n.factorial : ℝ) *
          (normalizedPrimeArchMoment n / 2 -
            (normalizedPrimeArchMoment 0 / 2) ^ (n + 1))) =
      ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ n) *
        (n.factorial : ℝ) *
          (normalizedPrimeArchMoment n / 2 -
            (normalizedPrimeArchMoment 0 / 2) ^ (n + 1)) := by ring
    _ = -1 * (n.factorial : ℝ) *
          (normalizedPrimeArchMoment n / 2 -
            (normalizedPrimeArchMoment 0 / 2) ^ (n + 1)) := by rw [hsign]
    _ > 0 := by nlinarith

/-- Backward-compatible restriction of the all-positive-index residual theorem. -/
theorem normalizedPrimeArchMoment_sub_firstJetScale_neg_of_five_le
    (n : ℕ) (hn : 5 ≤ n) :
    normalizedPrimeArchMoment n -
      normalizedPrimeArchMoment 0 ^ (n + 1) / (2 : ℝ) ^ n < 0 :=
  normalizedPrimeArchMoment_sub_firstJetScale_neg_of_one_le n (by omega)

/-- Backward-compatible restriction of the all-positive-index orientation theorem. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallColdMalgrangeTarget_signed_pos_of_five_le
    (n : ℕ) (hn : 5 ≤ n) :
    0 < (-1 : ℝ) ^ (n + 1) *
      ((-1 : ℝ) ^ n * (n.factorial : ℝ) *
        (normalizedPrimeArchMoment n / 2 -
          (normalizedPrimeArchMoment 0 / 2) ^ (n + 1))) :=
  routePPrimitiveGammaJuliaStokesPrimeGammaWallColdMalgrangeTarget_signed_pos_of_one_le
    n (by omega)

end

end RHTower
