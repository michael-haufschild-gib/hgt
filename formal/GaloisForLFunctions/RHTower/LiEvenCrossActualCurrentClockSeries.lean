import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The entire reciprocal-moment clock series of the actual LI current

The factorial denominator controls the full moment tower at every real clock. The source sector
bound and the same factorial envelope give a positive margin throughout the clock interval
`0 ≤ w ≤ 25`, without a sign assumption on any later source moment.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The reciprocal-moment series with the exact adjacent-current clock normalization. -/
def liEvenCrossActualCurrentClockSeries (w : ℝ) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ j * (16 * w) ^ j * normalizedPrimeArchMoment j /
    ((2 * j + 1).factorial : ℝ)

/-- Absolute factorial envelope for the terms beyond the central source moment. -/
def liEvenCrossActualCurrentClockErrorEnvelope (w : ℝ) : ℝ :=
  ∑' j : ℕ, (16 * |w| / 150) ^ (j + 1) /
    ((2 * (j + 1) + 1).factorial : ℝ)

/-- The factorial clock envelope is summable at every nonnegative radius. -/
theorem summable_liEvenCrossActualCurrentClockFactorialEnvelope (r : ℝ) (hr : 0 ≤ r) :
    Summable (fun j : ℕ => r ^ j / ((2 * j + 1).factorial : ℝ)) := by
  apply (Real.summable_pow_div_factorial r).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply div_le_div_of_nonneg_left (by positivity)
  · positivity
  · exact_mod_cast Nat.factorial_le (show j ≤ 2 * j + 1 by omega)

/-- Every source coefficient is controlled by the complete absolute reciprocal mass. -/
theorem norm_liEvenCrossActualCurrentClockSeriesTerm_le (w : ℝ) (j : ℕ) :
    ‖(-1 : ℝ) ^ j * (16 * w) ^ j * normalizedPrimeArchMoment j /
      ((2 * j + 1).factorial : ℝ)‖ ≤
      xiShiftAbsoluteMass 0 *
        ((16 * |w| / 150) ^ j / ((2 * j + 1).factorial : ℝ)) := by
  have hm := abs_normalizedPrimeArchMoment_add_le_secondMomentRadius 0 j
  simp only [zero_add] at hm
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_pow, abs_pow]
  simp only [abs_neg, abs_one, one_pow, one_mul]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 16),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * j + 1).factorial : ℝ))]
  calc
    (16 * |w|) ^ j * |normalizedPrimeArchMoment j| /
        ((2 * j + 1).factorial : ℝ) ≤
        (16 * |w|) ^ j * ((1 / 150 : ℝ) ^ j * xiShiftAbsoluteMass 0) /
          ((2 * j + 1).factorial : ℝ) := by gcongr
    _ = xiShiftAbsoluteMass 0 *
        ((16 * |w| / 150) ^ j / ((2 * j + 1).factorial : ℝ)) := by
      rw [show 16 * |w| / 150 = (16 * |w|) * (1 / 150) by ring,
        mul_pow (16 * |w|) (1 / 150) j]
      ring

/-- The whole actual source series is summable at every real clock. -/
theorem summable_liEvenCrossActualCurrentClockSeries (w : ℝ) :
    Summable (fun j : ℕ => (-1 : ℝ) ^ j * (16 * w) ^ j *
      normalizedPrimeArchMoment j / ((2 * j + 1).factorial : ℝ)) := by
  exact ((summable_liEvenCrossActualCurrentClockFactorialEnvelope
    (16 * |w| / 150) (by positivity)).mul_left
    (xiShiftAbsoluteMass 0)).of_norm_bounded
      (norm_liEvenCrossActualCurrentClockSeriesTerm_le w)

/-- Absolute convergence holds without any restriction on the real clock. -/
theorem summable_norm_liEvenCrossActualCurrentClockSeries (w : ℝ) :
    Summable (fun j : ℕ => ‖(-1 : ℝ) ^ j * (16 * w) ^ j *
      normalizedPrimeArchMoment j / ((2 * j + 1).factorial : ℝ)‖) :=
  (summable_liEvenCrossActualCurrentClockSeries w).norm

theorem summable_liEvenCrossActualCurrentClockErrorEnvelope (w : ℝ) :
    Summable (fun j : ℕ => (16 * |w| / 150) ^ (j + 1) /
      ((2 * (j + 1) + 1).factorial : ℝ)) := by
  exact (summable_nat_add_iff 1).2
    (summable_liEvenCrossActualCurrentClockFactorialEnvelope
      (16 * |w| / 150) (by positivity))

/-- At zero clock the series retains exactly the central source moment. -/
theorem liEvenCrossActualCurrentClockSeries_zero :
    liEvenCrossActualCurrentClockSeries 0 = normalizedPrimeArchMoment 0 := by
  rw [liEvenCrossActualCurrentClockSeries, tsum_eq_single 0]
  · simp
  · intro j hj
    simp [zero_pow hj]

/-- The complete series error is bounded by its exact factorial envelope. -/
theorem abs_liEvenCrossActualCurrentClockSeries_sub_zero_le (w : ℝ) :
    |liEvenCrossActualCurrentClockSeries w - normalizedPrimeArchMoment 0| ≤
      xiShiftAbsoluteMass 0 * liEvenCrossActualCurrentClockErrorEnvelope w := by
  let f : ℕ → ℝ := fun j => (-1 : ℝ) ^ j * (16 * w) ^ j *
    normalizedPrimeArchMoment j / ((2 * j + 1).factorial : ℝ)
  have hf : Summable f := summable_liEvenCrossActualCurrentClockSeries w
  have ht : Summable (fun j => f (j + 1)) := (summable_nat_add_iff 1).2 hf
  have hzero : liEvenCrossActualCurrentClockSeries w - normalizedPrimeArchMoment 0 =
      ∑' j : ℕ, f (j + 1) := by
    change (∑' j, f j) - normalizedPrimeArchMoment 0 = _
    rw [hf.tsum_eq_zero_add]
    simp [f]
  have hg := (summable_liEvenCrossActualCurrentClockErrorEnvelope w).mul_left
    (xiShiftAbsoluteMass 0)
  rw [hzero, ← Real.norm_eq_abs]
  calc
    ‖∑' j : ℕ, f (j + 1)‖ ≤ ∑' j : ℕ, ‖f (j + 1)‖ :=
      norm_tsum_le_tsum_norm ht.norm
    _ ≤ ∑' j : ℕ, xiShiftAbsoluteMass 0 *
        ((16 * |w| / 150) ^ (j + 1) / ((2 * (j + 1) + 1).factorial : ℝ)) :=
      ht.norm.tsum_le_tsum
        (fun j => norm_liEvenCrossActualCurrentClockSeriesTerm_le w (j + 1)) hg
    _ = xiShiftAbsoluteMass 0 * liEvenCrossActualCurrentClockErrorEnvelope w := by
      rw [tsum_mul_left, liEvenCrossActualCurrentClockErrorEnvelope]

private theorem actualClock_factorial_geometric_lower (j : ℕ) :
    (6 : ℝ) * 20 ^ j ≤ ((2 * j + 3).factorial : ℝ) := by
  induction j with
  | zero => norm_num
  | succ j hj =>
    have hfac :
        ((2 * (j + 1) + 3).factorial : ℝ) =
          (2 * (j : ℝ) + 5) * (2 * (j : ℝ) + 4) *
            ((2 * j + 3).factorial : ℝ) := by
      rw [show 2 * (j + 1) + 3 = (2 * j + 3) + 1 + 1 by omega,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
    rw [hfac, pow_succ]
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have h20 : (20 : ℝ) ≤ (2 * (j : ℝ) + 5) * (2 * (j : ℝ) + 4) := by
      nlinarith
    calc
      6 * (20 ^ j * 20) = 20 * (6 * 20 ^ j) := by ring
      _ ≤ 20 * ((2 * j + 3).factorial : ℝ) := by gcongr
      _ ≤ (2 * (j : ℝ) + 5) * (2 * (j : ℝ) + 4) *
          ((2 * j + 3).factorial : ℝ) := by gcongr

private theorem actualClock_tail_term_le {r : ℝ}
    (hr : 0 ≤ r) (hr8 : r ≤ 8 / 3) (j : ℕ) :
    r ^ (j + 1) / ((2 * (j + 1) + 1).factorial : ℝ) ≤
      (4 / 9 : ℝ) * (2 / 15) ^ j := by
  rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
  calc
    r ^ (j + 1) / ((2 * j + 3).factorial : ℝ) ≤
        (8 / 3 : ℝ) ^ (j + 1) / (6 * 20 ^ j) :=
      div_le_div₀ (by positivity) (pow_le_pow_left₀ hr hr8 _)
        (by positivity) (actualClock_factorial_geometric_lower j)
    _ = (4 / 9 : ℝ) * (2 / 15) ^ j := by
      rw [pow_succ]
      conv_rhs =>
        rw [show (2 / 15 : ℝ) = (8 / 3) / 20 by norm_num, div_pow]
      ring

/-- The factorial tail costs at most `20/39` throughout the compact clock window. -/
theorem liEvenCrossActualCurrentClockErrorEnvelope_le_twenty_over_thirtyNine
    {w : ℝ} (hw : |w| ≤ 25) :
    liEvenCrossActualCurrentClockErrorEnvelope w ≤ 20 / 39 := by
  have hr8 : 16 * |w| / 150 ≤ (8 / 3 : ℝ) := by linarith
  have hg : Summable (fun j : ℕ => (4 / 9 : ℝ) * (2 / 15) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (2 / 15 : ℝ) < 1)).mul_left _
  calc
    liEvenCrossActualCurrentClockErrorEnvelope w ≤
        ∑' j : ℕ, (4 / 9 : ℝ) * (2 / 15) ^ j :=
      (summable_liEvenCrossActualCurrentClockErrorEnvelope w).tsum_le_tsum
        (fun j => actualClock_tail_term_le (by positivity) hr8 j) hg
    _ = 20 / 39 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num

/-- The actual source clock series has a strict source-dependent margin on `[0,25]`. -/
theorem liEvenCrossActualCurrentClockSeries_ge_positive_margin
    {w : ℝ} (hw0 : 0 ≤ w) (hw25 : w ≤ 25) :
    (1051 / 2184 : ℝ) * xiShiftAbsoluteMass 0 ≤
      liEvenCrossActualCurrentClockSeries w := by
  have he := abs_liEvenCrossActualCurrentClockSeries_sub_zero_le w
  have hen := liEvenCrossActualCurrentClockErrorEnvelope_le_twenty_over_thirtyNine
    (show |w| ≤ 25 by simpa [abs_of_nonneg hw0] using hw25)
  have hA := xiShiftAbsoluteMass_nonneg 0
  have hM := sectorFactor_mul_xiShiftAbsoluteMass_le_normalizedPrimeArchMoment 0
  norm_num at hM
  have hbound := mul_le_mul_of_nonneg_left hen hA
  have hlower := (abs_le.mp he).1
  linarith

theorem liEvenCrossActualCurrentClockSeries_pos
    {w : ℝ} (hw0 : 0 ≤ w) (hw25 : w ≤ 25) :
    0 < liEvenCrossActualCurrentClockSeries w := by
  exact (mul_pos (by norm_num : (0 : ℝ) < 1051 / 2184)
    (xiShiftAbsoluteMass_pos 0)).trans_le
      (liEvenCrossActualCurrentClockSeries_ge_positive_margin hw0 hw25)

end

end RHTower
