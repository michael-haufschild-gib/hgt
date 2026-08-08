import GaloisForLFunctions.RHTower.Sieve.CesaroDyadicMeanSquare

/-!
# The Cesàro chain as one explicit inequality

Summing the truncation error over the range and bounding the analytic side by the height-free dyadic
estimate leaves a single inequality with no residual sums:

`‖∑_{n ≤ N} f(n)log(x/n)‖ ≤ N·(C₁(1 + log(1 + T/σ)) + C₂(log log 2 − log log(1 + 1/T)))/T
    + x^σ(1 + log N)/(πTσ log 2) + (1/2π)(8x^σ√(5πe(1 + log N)) + 12x^σ√(5π))`

for every `|f| ≤ 1`, `1 ≤ σ ≤ 2`, `T ≥ 1`, `x ≥ N ≥ 1`.  The height enters only the first two terms,
which decay like `(log T)/T`, so `T` is free; what is left at `x = N` is `≍ N√(log N)`.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- **The logarithmic sum of a shifted power.** -/
theorem sum_Icc_rpow_div_le {N : ℕ} {σ x : ℝ} (hσ : 1 ≤ σ) (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 N, (x / n) ^ σ) ≤ x ^ σ * (1 + Real.log N) := by
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hstep : ∀ n ∈ Finset.Icc 1 N, (x / n) ^ σ ≤ x ^ σ * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hdiv : (x / n) ^ σ = x ^ σ / (n : ℝ) ^ σ := Real.div_rpow hx.le (by linarith) σ
    have hle : (n : ℝ) ≤ (n : ℝ) ^ σ := by
      have h := Real.rpow_le_rpow_of_exponent_le hnR hσ
      rwa [Real.rpow_one] at h
    rw [hdiv, mul_one_div]
    exact div_le_div_of_nonneg_left hxσ.le (by linarith) hle
  have hlog : ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) ≤ 1 + Real.log N :=
    sum_inv_comp_le_one_add_log (φ := id) (fun _ _ _ _ h => h) (fun a ha => ha)
  calc (∑ n ∈ Finset.Icc 1 N, (x / n) ^ σ)
      ≤ ∑ n ∈ Finset.Icc 1 N, x ^ σ * (1 / (n : ℝ)) := Finset.sum_le_sum hstep
    _ = x ^ σ * ∑ n ∈ Finset.Icc 1 N, 1 / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x ^ σ * (1 + Real.log N) := mul_le_mul_of_nonneg_left hlog hxσ.le

/-- **The truncation error summed over the range.** -/
theorem sum_Icc_cesaroError_le (N : ℕ) {σ T x : ℝ} (hσ : 1 ≤ σ) (hT : 1 ≤ T) (hx : 0 < x) :
    (∑ n ∈ Finset.Icc 1 N, cesaroError σ T (x / n))
      ≤ (N : ℝ) * ((4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T
            + (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T)))
            + 1 / (Real.pi * T))
        + x ^ σ * (1 + Real.log N) / (Real.pi * T * σ * Real.log 2) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hT0 : (0 : ℝ) < T := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set c : ℝ := (4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T
      + (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T)))
      + 1 / (Real.pi * T) with hc
  have hsplit : ∀ n ∈ Finset.Icc 1 N,
      cesaroError σ T (x / n) = c + (x / n) ^ σ / (Real.pi * T * σ * Real.log 2) := by
    intro n _
    rw [cesaroError, hc]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
    Nat.card_Icc, nsmul_eq_mul]
  have hcard : ((N + 1 - 1 : ℕ) : ℝ) = (N : ℝ) := by
    norm_num
  rw [hcard]
  have hdiv : ∑ n ∈ Finset.Icc 1 N, (x / n) ^ σ / (Real.pi * T * σ * Real.log 2)
      = (∑ n ∈ Finset.Icc 1 N, (x / n) ^ σ) / (Real.pi * T * σ * Real.log 2) := by
    rw [Finset.sum_div]
  rw [hdiv]
  have hnum := sum_Icc_rpow_div_le (N := N) hσ hx
  have hden : (0 : ℝ) < Real.pi * T * σ * Real.log 2 := by positivity
  have hstep : (∑ n ∈ Finset.Icc 1 N, (x / n) ^ σ) / (Real.pi * T * σ * Real.log 2)
      ≤ x ^ σ * (1 + Real.log N) / (Real.pi * T * σ * Real.log 2) :=
    div_le_div_of_nonneg_right hnum hden.le
  linarith

/-- **The Cesàro chain, explicitly.**  Every term is a closed expression in `N`, `σ`, `T` and `x`. -/
theorem norm_sum_Icc_mul_log_div_le_cesaro_explicit {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) {N : ℕ}
    (hN : 1 ≤ N) {σ T x : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ 2) (hT : 1 ≤ T) (hxN : (N : ℝ) ≤ x) :
    ‖∑ n ∈ Finset.Icc 1 N, truncSeq f N n * ((Real.log (x / n) : ℝ) : ℂ)‖
      ≤ (N : ℝ) * ((4 * (1 + Real.log (1 + T / σ)) / Real.pi + 1) / T
            + (4 / (Real.pi * T)) * (Real.log (Real.log 2) - Real.log (Real.log (1 + 1 / T)))
            + 1 / (Real.pi * T))
        + x ^ σ * (1 + Real.log N) / (Real.pi * T * σ * Real.log 2)
        + (1 / (2 * Real.pi))
          * (8 * x ^ σ * Real.sqrt (5 * Real.pi * Real.exp 1 * (1 + Real.log N))
            + 12 * x ^ σ * Real.sqrt (5 * Real.pi)) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hx : (0 : ℝ) < x := by linarith
  have hmain := norm_sum_Icc_mul_log_div_le_cesaro_dyadic hbdd hN hσ1 hσ2 hT hxN
  have herr := sum_Icc_cesaroError_le N hσ1 hT hx
  linarith

end RHTower.Sieve
end
