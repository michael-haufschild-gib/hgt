import GaloisForLFunctions.RHTower.ZetaSuperlinearCutoff

/-!
# Zeta truncation with a growing resonator weight

An arbitrary real power of height can be retained in the superlinear
Euler–Maclaurin estimate. The pole exponent and the remainder order give
the exact conditions; every intermediate derivative correction then decays.
-/

noncomputable section
open Complex Filter Topology Set
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

/-- A ceiling changes a power envelope only by a fixed factor. -/
theorem tendsto_real_weighted_superlinearCutoff {a b q : ℝ} (ha : 0 ≤ a)
    (hrate : q + a * b < 0) :
    Tendsto (fun T : ℝ => T ^ q * (superlinearCutoff a T : ℝ) ^ b)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => T ^ (q + a * b)) atTop (𝓝 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hrate)
  by_cases hb : b ≤ 0
  · refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := zero_lt_one.trans_le hT
      calc
        _ ≤ T ^ q * (T ^ a) ^ b := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 a)
            (Nat.le_ceil _) hb) (by positivity)
        _ = T ^ (q + a * b) := by
          rw [← Real.rpow_mul hT0.le, Real.rpow_add hT0]
  · have hb0 : 0 ≤ b := (lt_of_not_ge hb).le
    have hlim' : Tendsto (fun T : ℝ => (2 : ℝ) ^ b * T ^ (q + a * b))
        atTop (𝓝 0) := by simpa using hlim.const_mul ((2 : ℝ) ^ b)
    refine squeeze_zero' ?_ ?_ hlim'
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
      have hT0 : 0 < T := zero_lt_one.trans_le hT
      calc
        _ ≤ T ^ q * (2 * T ^ a) ^ b := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _)
            (superlinearCutoff_bounds ha hT).2.2 hb0) (by positivity)
        _ = (2 : ℝ) ^ b * T ^ (q + a * b) := by
          rw [Real.mul_rpow (by norm_num) (by positivity),
            ← Real.rpow_mul hT0.le, Real.rpow_add hT0]
          ring

/-- The full arbitrary-order zeta error decays after multiplication by `T^κ`. -/
theorem tendsto_weighted_zetaTruncationErrorScale {σ a κ : ℝ}
    (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 1 < a)
    (hpole : κ + a * (1 - σ) - 1 < 0) (hendpoint : κ < a * σ)
    (m : ℕ)
    (hrem : κ + (2 * m + 2 : ℕ) + a * (1 - σ - (2 * m + 2 : ℕ)) < 0) :
    Tendsto (fun T : ℝ => T ^ κ *
      zetaTruncationErrorScale σ m (superlinearCutoff a T) T) atTop (𝓝 0) := by
  have ha0 : 0 ≤ a := (zero_lt_one.trans ha).le
  have hp : Tendsto (fun T : ℝ =>
      T ^ κ * ((superlinearCutoff a T : ℝ) ^ (1 - σ) / T)) atTop (𝓝 0) := by
    have h := tendsto_real_weighted_superlinearCutoff (a := a) (b := 1 - σ)
      (q := κ - 1) ha0 (by linarith only [hpole])
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [Real.rpow_sub (zero_lt_one.trans_le hT), Real.rpow_one]
    ring
  have hh : Tendsto (fun T : ℝ =>
      T ^ κ * ((superlinearCutoff a T : ℝ) ^ (-σ) / 2)) atTop (𝓝 0) := by
    have h := (tendsto_real_weighted_superlinearCutoff (a := a) (b := -σ)
      (q := κ) ha0 (by linarith only [hendpoint])).div_const 2
    simpa only [zero_div, mul_div_assoc] using h
  have ht (r : ℕ) : Tendsto (fun T : ℝ => T ^ κ *
      (|((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
        ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
          (superlinearCutoff a T : ℝ) ^ (-σ - (2 * r + 1 : ℕ))))
      atTop (𝓝 0) := by
    have hj : (0 : ℝ) ≤ (2 * r + 1 : ℕ) := Nat.cast_nonneg _
    have hrate : κ + (2 * r + 1 : ℕ) + a * (-σ - (2 * r + 1 : ℕ)) < 0 := by
      nlinarith only [hendpoint, mul_nonneg (sub_nonneg.mpr ha.le) hj]
    have h := (tendsto_real_weighted_superlinearCutoff (a := a)
      (b := -σ - (2 * r + 1 : ℕ)) (q := κ + (2 * r + 1 : ℕ)) ha0 hrate).const_mul
      (|((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
        (σ + (2 * r + 1 : ℕ) + 2) ^ (2 * r + 1))
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [Real.rpow_add (zero_lt_one.trans_le hT), Real.rpow_natCast, mul_pow]
    ring
  have hs := tendsto_finsetSum (Finset.range (m + 1)) (fun r _ => ht r)
  have hr : Tendsto (fun T : ℝ => T ^ κ *
      (|((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((σ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) *
          ((superlinearCutoff a T : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) /
            (σ + (2 * m + 2 : ℕ) - 1)))) atTop (𝓝 0) := by
    have h := (tendsto_real_weighted_superlinearCutoff (a := a)
      (b := 1 - σ - (2 * m + 2 : ℕ)) (q := κ + (2 * m + 2 : ℕ)) ha0 hrem).const_mul
      (|((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        (σ + (2 * m + 2 : ℕ) + 2) ^ (2 * m + 2) /
          (σ + (2 * m + 2 : ℕ) - 1))
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    rw [Real.rpow_add (zero_lt_one.trans_le hT), Real.rpow_natCast, mul_pow]
    ring
  simpa only [zetaTruncationErrorScale, mul_add, Finset.mul_sum,
    Finset.sum_const_zero, add_zero] using ((hp.add hh).add hs).add hr

#print axioms tendsto_weighted_zetaTruncationErrorScale

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
