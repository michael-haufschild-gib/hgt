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

/-- Explicit parameters make the mean, coefficient tail, and pole errors decay
for every resonator support exponent strictly below `2σ-1`. -/
theorem exists_growing_resonator_exponents {σ κ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hκ0 : 0 ≤ κ) (hκ : κ < 2 * σ - 1) :
    ∃ a ε : ℝ, 1 < a ∧ 0 < ε ∧ ε < 2 * σ - 1 ∧
      κ * (1 + ε) + a * (2 + ε - 2 * σ) - 1 < 0 ∧
      κ * ε + a * (1 + ε - 2 * σ) / 2 < 0 ∧
      κ + a * (1 - σ) - 1 < 0 ∧ κ < a * σ := by
  let d := 2 * σ - 1 - κ
  let a := 1 + d / 8
  let ε := (d / 8) / (κ + a + 1)
  have hd : 0 < d := sub_pos.mpr hκ
  have hβ : 0 < 2 * σ - 1 := by linarith only [hσ]
  have hdb : d ≤ 2 * σ - 1 := by dsimp [d]; linarith only [hκ0]
  have ha : 1 < a := by dsimp [a]; linarith only [hd]
  have hden : 0 < κ + a + 1 := by linarith only [hκ0, ha]
  have hε : 0 < ε := div_pos (by positivity) hden
  have heq : ε * (κ + a + 1) = d / 8 := div_mul_cancel₀ _ hden.ne'
  have hp : 0 < ε * (κ + a) := mul_pos hε (by linarith only [hκ0, ha])
  have hεlt : ε < d / 8 := by nlinarith only [heq, hp]
  have hεβ : ε < 2 * σ - 1 := by linarith only [hεlt, hdb, hβ]
  have hsmall : ε * (κ + a) < d / 8 := by nlinarith only [heq, hε]
  have hds : d * (2 - 2 * σ) < d := by
    simpa only [mul_one] using mul_lt_mul_of_pos_left
      (by linarith only [hσ] : 2 - 2 * σ < 1) hd
  have hbase : κ + a * (2 - 2 * σ) - 1 < -7 * d / 8 := by
    calc
      _ = -d + d * (2 - 2 * σ) / 8 := by dsimp [a, d]; ring
      _ < _ := by linarith only [hds]
  refine ⟨a, ε, ha, hε, hεβ, ?_, ?_, ?_, ?_⟩
  · nlinarith only [hbase, hsmall, hd]
  · have hεa : 0 < ε * a := mul_pos hε (zero_lt_one.trans ha)
    have hsmall' : ε * (κ + a / 2) < d / 8 := by nlinarith only [hsmall, hεa]
    have hlarge : 0 ≤ (a - 1) * (2 * σ - 1) := mul_nonneg (sub_nonneg.mpr ha.le) hβ.le
    nlinarith only [hsmall', hlarge, hdb, hβ]
  · have hds' : d * (1 - σ) < d / 2 := by nlinarith only [hds]
    calc
      _ = σ - 1 - d + d * (1 - σ) / 8 := by dsimp [a, d]; ring
      _ < 0 := by linarith only [hds', hσ1, hd]
  · have hσ0 : 0 < σ := by linarith only [hσ]
    have hp' : 0 < (a - 1) * σ := mul_pos (sub_pos.mpr ha) hσ0
    nlinarith only [hκ, hσ1, hp']

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

/-- A single explicit exponent choice admits the growing weight, the sharp
polynomial mean error, and the diagonal coefficient tail simultaneously. -/
theorem exists_growing_resonator_truncation {σ κ : ℝ}
    (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hκ0 : 0 ≤ κ) (hκ : κ < 2 * σ - 1) :
    ∃ a ε : ℝ, ∃ m : ℕ, 1 < a ∧ 0 < ε ∧ ε < 2 * σ - 1 ∧
      Tendsto (fun T : ℝ => T ^ κ *
        zetaTruncationErrorScale σ m (superlinearCutoff a T) T) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => T ^ (κ * (1 + ε)) *
        (superlinearCutoff a T : ℝ) ^ (2 + ε - 2 * σ) / T) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => T ^ (κ * ε) *
        (superlinearCutoff a T : ℝ) ^ ((1 + ε - 2 * σ) / 2)) atTop (𝓝 0) := by
  obtain ⟨a, ε, ha, hε, hεσ, hmean, htail, hpole, hend⟩ :=
    exists_growing_resonator_exponents hσ hσ1 hκ0 hκ
  obtain ⟨m, hm⟩ := exists_nat_gt ((κ + a * (1 - σ)) / (a - 1))
  have hm' : κ + a * (1 - σ) < (m : ℝ) * (a - 1) :=
    (div_lt_iff₀ (sub_pos.mpr ha)).mp hm
  have hrem : κ + (2 * m + 2 : ℕ) + a * (1 - σ - (2 * m + 2 : ℕ)) < 0 := by
    have hp : 0 < ((m : ℝ) + 2) * (a - 1) :=
      mul_pos (by positivity) (sub_pos.mpr ha)
    push_cast
    nlinarith only [hm', hp]
  have ha0 : 0 ≤ a := (zero_lt_one.trans ha).le
  refine ⟨a, ε, m, ha, hε, hεσ,
    tendsto_weighted_zetaTruncationErrorScale (by linarith only [hσ])
      hσ1 ha hpole hend m hrem, ?_,
    tendsto_real_weighted_superlinearCutoff ha0 (by simpa only [mul_div_assoc] using htail)⟩
  have h := tendsto_real_weighted_superlinearCutoff (a := a)
    (b := 2 + ε - 2 * σ) (q := κ * (1 + ε) - 1) ha0
      (by linarith only [hmean])
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
  rw [Real.rpow_sub (zero_lt_one.trans_le hT), Real.rpow_one]
  ring

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
