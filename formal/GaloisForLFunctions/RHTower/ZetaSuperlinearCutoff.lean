import GaloisForLFunctions.RHTower.ZetaSuperlinearTruncation

/-!
# A superlinear cutoff with vanishing zeta truncation error

The choice `ceil(T^(σ+1/2))` balances the sharp finite mean-value error and
the arbitrary-order Euler–Maclaurin remainder for `1/2 < σ < 1`.
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower

def superlinearCutoff (a T : ℝ) : ℕ := ⌈T ^ a⌉₊

theorem superlinearCutoff_bounds {a T : ℝ} (ha : 0 ≤ a) (hT : 1 ≤ T) :
    1 ≤ superlinearCutoff a T ∧ T ^ a ≤ (superlinearCutoff a T : ℝ) ∧
      (superlinearCutoff a T : ℝ) ≤ 2 * T ^ a := by
  have hp : 1 ≤ T ^ a := Real.one_le_rpow hT ha
  refine ⟨Nat.one_le_ceil_iff.mpr (by linarith), Nat.le_ceil _, ?_⟩
  have hc := Nat.ceil_lt_add_one (show 0 ≤ T ^ a by positivity)
  dsimp [superlinearCutoff]
  linarith

theorem tendsto_superlinearCutoff {a : ℝ} (ha : 0 < a) :
    Tendsto (superlinearCutoff a) atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop ha).eventually (eventually_ge_atTop (b : ℝ)))
  refine ⟨T₀, fun T hT => ?_⟩
  have hb := (hT₀ T hT).trans (Nat.le_ceil (T ^ a))
  exact_mod_cast hb

theorem tendsto_superlinearCutoff_weighted_neg {a b : ℝ} (q : ℕ)
    (hb : b ≤ 0) (hrate : (q : ℝ) + a * b < 0) :
    Tendsto (fun T : ℝ => T ^ q * (superlinearCutoff a T : ℝ) ^ b)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => T ^ ((q : ℝ) + a * b)) atTop (𝓝 0) := by
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hrate))
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    calc
      T ^ q * (superlinearCutoff a T : ℝ) ^ b ≤ T ^ q * (T ^ a) ^ b :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT0 a)
            (Nat.le_ceil _) hb) (by positivity)
      _ = T ^ ((q : ℝ) + a * b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hT0.le, Real.rpow_add hT0]

theorem tendsto_superlinearCutoff_pow_div {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrate : a * b - 1 < 0) :
    Tendsto (fun T : ℝ => (superlinearCutoff a T : ℝ) ^ b / T) atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (2 : ℝ) ^ b * T ^ (a * b - 1))
      atTop (𝓝 0) := by
    simpa only [neg_neg, mul_zero] using
      (tendsto_rpow_neg_atTop (neg_pos.mpr hrate)).const_mul ((2 : ℝ) ^ b)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hT0 : 0 < T := by linarith
    calc
      (superlinearCutoff a T : ℝ) ^ b / T ≤ (2 * T ^ a) ^ b / T :=
        div_le_div_of_nonneg_right
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (superlinearCutoff_bounds ha hT).2.2 hb)
          hT0.le
      _ = (2 : ℝ) ^ b * T ^ (a * b - 1) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hT0.le,
          Real.rpow_sub hT0, Real.rpow_one]
        ring

theorem tendsto_zetaTruncationErrorScale {σ a : ℝ} (hσ : 0 < σ) (hσ1 : σ < 1)
    (ha : 1 < a) (hpole : a * (1 - σ) - 1 < 0) (m : ℕ)
    (hrem : (2 * m + 2 : ℕ) + a * (1 - σ - (2 * m + 2 : ℕ)) < 0) :
    Tendsto (fun T => zetaTruncationErrorScale σ m (superlinearCutoff a T) T)
      atTop (𝓝 0) := by
  have ha0 : 0 < a := by linarith
  have hp := tendsto_superlinearCutoff_pow_div ha0.le (by linarith : 0 ≤ 1 - σ) hpole
  have hh : Tendsto (fun T : ℝ => (superlinearCutoff a T : ℝ) ^ (-σ) / 2)
      atTop (𝓝 0) := by
    have h := (tendsto_superlinearCutoff_weighted_neg (a := a) (b := -σ) 0
      (by linarith) (by simp; nlinarith)).div_const 2
    simpa using h
  have ht (r : ℕ) : Tendsto (fun T : ℝ =>
      |((bernoulli (2 * r + 2) : ℚ) : ℝ)| / ((2 * r + 2).factorial : ℝ) *
        ((σ + (2 * r + 1 : ℕ) + 2) * T) ^ (2 * r + 1) *
          (superlinearCutoff a T : ℝ) ^ (-σ - (2 * r + 1 : ℕ))) atTop (𝓝 0) := by
    have hj : (0 : ℝ) ≤ (2 * r + 1 : ℕ) := Nat.cast_nonneg _
    have h := tendsto_superlinearCutoff_weighted_neg (a := a)
      (b := -σ - (2 * r + 1 : ℕ)) (2 * r + 1)
      (by linarith) (by nlinarith)
    convert h.const_mul (|((bernoulli (2 * r + 2) : ℚ) : ℝ)| /
      ((2 * r + 2).factorial : ℝ) * (σ + (2 * r + 1 : ℕ) + 2) ^ (2 * r + 1)) using 1
    · ext T
      simp only [mul_pow]
      ring
    · simp
  have hs := tendsto_finsetSum (Finset.range (m + 1)) (fun r _ => ht r)
  have hk : (2 : ℝ) ≤ (2 * m + 2 : ℕ) := by exact_mod_cast (by omega : 2 ≤ 2 * m + 2)
  have hr : Tendsto (fun T : ℝ =>
      |((bernoulli (2 * m + 2) : ℚ) : ℝ)| / ((2 * m + 2).factorial : ℝ) *
        ((σ + (2 * m + 2 : ℕ) + 2) * T) ^ (2 * m + 2) *
          ((superlinearCutoff a T : ℝ) ^ (1 - σ - (2 * m + 2 : ℕ)) /
            (σ + (2 * m + 2 : ℕ) - 1))) atTop (𝓝 0) := by
    have h := tendsto_superlinearCutoff_weighted_neg (a := a)
      (b := 1 - σ - (2 * m + 2 : ℕ)) (2 * m + 2) (by linarith) hrem
    convert h.const_mul (|((bernoulli (2 * m + 2) : ℚ) : ℝ)| /
      ((2 * m + 2).factorial : ℝ) * (σ + (2 * m + 2 : ℕ) + 2) ^ (2 * m + 2) /
        (σ + (2 * m + 2 : ℕ) - 1)) using 1
    · ext T
      simp only [mul_pow]
      ring
    · simp
  simpa only [zetaTruncationErrorScale, Finset.sum_const_zero, add_zero] using
    ((hp.add hh).add hs).add hr

theorem exists_zetaSuperlinearTruncation {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    ∃ m : ℕ,
      Tendsto (fun T => zetaTruncationErrorScale σ m (superlinearCutoff (σ + 1 / 2) T) T)
        atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => (superlinearCutoff (σ + 1 / 2) T : ℝ) ^ (2 - 2 * σ) / T)
        atTop (𝓝 0) := by
  let a := σ + 1 / 2
  have ha : 1 < a := by dsimp [a]; linarith
  have ha0 : 0 < a := by linarith
  have hσ0 : 0 < σ := by linarith
  have hpole : a * (1 - σ) - 1 < 0 := by dsimp [a]; nlinarith [sq_nonneg σ]
  have hmean : a * (2 - 2 * σ) - 1 < 0 := by dsimp [a]; nlinarith [sq_nonneg (σ - 1 / 2)]
  obtain ⟨m, hm⟩ := exists_nat_gt (a * (1 - σ) / (a - 1))
  have hm' : a * (1 - σ) < (m : ℝ) * (a - 1) :=
    (div_lt_iff₀ (by linarith : 0 < a - 1)).mp hm
  have hrem : (2 * m + 2 : ℕ) + a * (1 - σ - (2 * m + 2 : ℕ)) < 0 := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
  exact ⟨m, tendsto_zetaTruncationErrorScale hσ0 hσ1 ha hpole m hrem,
    tendsto_superlinearCutoff_pow_div ha0.le (by linarith) hmean⟩

end RHTower
