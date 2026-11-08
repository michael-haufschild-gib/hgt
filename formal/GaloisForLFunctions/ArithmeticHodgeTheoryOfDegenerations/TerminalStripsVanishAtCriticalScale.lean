import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.LogarithmicAnnuliHaveUniformRowMeans
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TopWindowConductorRowCancellation

/-!
# Terminal strips vanish at critical scale

An interior error of order `1/c + c/N` is negligible in square mean. A terminal
strip of logarithmic width `Tc/N` remains negligible even with an error bounded
by a fixed multiple of `c`, because `c³/N` tends to zero on every critical curve.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory

/-- Interior convergence and a linear-overlap terminal envelope imply square-mean convergence
on every fixed terminal fraction. -/
theorem tendsto_normalized_square_mean_of_terminal_strip
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {δ T C D K : ℝ} (hT : 0 ≤ T)
    {E : ℕ → ℕ → ℝ}
    (hbound : ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
      |E N n| ≤ K * c N)
    (hinterior : ∀ᶠ N : ℕ in atTop, ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (n : ℝ) * Real.exp (T * (c N / N)) ≤ N →
        |E N n| ≤ C / c N + D * (c N / N)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N, E N n ^ 2) / N)
      atTop (𝓝 0) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hcN : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have hc2N : Tendsto (fun N : ℕ => c N ^ 2 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 2 0
  have hc3N : Tendsto (fun N : ℕ => c N ^ 3 / N) atTop (𝓝 0) := by
    simpa only [pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 3 0
  have hsmall : Tendsto (fun N : ℕ => (C / c N + D * (c N / N)) ^ 2) atTop (𝓝 0) := by
    have hinv : Tendsto (fun N : ℕ => C / c N) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hcinf
    have hh := (hinv.add (hcN.const_mul D)).pow 2
    simpa only [mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)] using hh
  have hstrip : Tendsto (fun N : ℕ => (T * (c N / N) + 1 / N) * (K * c N) ^ 2)
      atTop (𝓝 0) := by
    have hh := (hc3N.const_mul (T * K ^ 2)).add (hc2N.const_mul (K ^ 2))
    simp only [mul_zero, add_zero] at hh
    exact hh.congr fun N => by ring
  have hlim := hsmall.add hstrip
  simp only [add_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1, hbound, hinterior] with N hN hb hi
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have he : ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N, E N n ^ 2 ≤ (K * c N) ^ 2 := by
    intro n hn
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hb n hn) 2
    simpa only [sq_abs] using hh
  have hei : ∀ n ∈ Finset.Ioc ⌊δ * (N : ℝ)⌋₊ N,
      (n : ℝ) * Real.exp (T * (c N / N)) ≤ N →
        E N n ^ 2 ≤ (C / c N + D * (c N / N)) ^ 2 := by
    intro n hn hni
    have hh := pow_le_pow_left₀ (abs_nonneg _) (hi n hn hni) 2
    simpa only [sq_abs] using hh
  exact normalized_sum_le_of_terminal_strip hN (by positivity) he hei

/-- Two errors vanishing in normalized square mean still vanish after addition. -/
theorem tendsto_normalized_square_mean_add {S : ℕ → Finset ℕ} {f g : ℕ → ℕ → ℝ}
    (hf : Tendsto (fun N : ℕ => (∑ n ∈ S N, f N n ^ 2) / N) atTop (𝓝 0))
    (hg : Tendsto (fun N : ℕ => (∑ n ∈ S N, g N n ^ 2) / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ n ∈ S N, (f N n + g N n) ^ 2) / N) atTop (𝓝 0) := by
  have hlim := (hf.const_mul 2).add (hg.const_mul 2)
  simp only [mul_zero, add_zero] at hlim
  refine squeeze_zero (fun N => by positivity) (fun N => ?_) hlim
  have hh : (∑ n ∈ S N, (f N n + g N n) ^ 2) ≤
      2 * (∑ n ∈ S N, f N n ^ 2) + 2 * (∑ n ∈ S N, g N n ^ 2) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_le_sum fun n _ => by nlinarith only [sq_nonneg (f N n - g N n)]
  exact (div_le_div_of_nonneg_right hh (Nat.cast_nonneg N)).trans_eq (by ring)

/-- A scalar tending to zero has vanishing square mean over any subset of a horizon. -/
theorem tendsto_normalized_square_mean_const {S : ℕ → Finset ℕ}
    (hS : ∀ N, (S N).card ≤ N) {f : ℕ → ℝ} (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (∑ _n ∈ S N, f N ^ 2) / N) atTop (𝓝 0) := by
  have hlim := hf.pow 2
  rw [zero_pow (by decide : 2 ≠ 0)] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [sum_const, nsmul_eq_mul, div_le_iff₀ hN0]
  have hh := mul_le_mul_of_nonneg_right (show ((S N).card : ℝ) ≤ N by exact_mod_cast hS N)
    (sq_nonneg (f N))
  simpa only [mul_comm] using hh

#print axioms tendsto_normalized_square_mean_add
#print axioms tendsto_normalized_square_mean_const

#print axioms tendsto_normalized_square_mean_of_terminal_strip
end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
