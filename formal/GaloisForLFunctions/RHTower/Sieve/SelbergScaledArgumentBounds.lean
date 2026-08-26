import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogPrincipalExact

open Finset

namespace RHTower.Sieve

theorem one_le_selbergScaledArgument
    {a c N d : ℕ} (ha : 0 < a) (hac : a ≤ c)
    (hd : d ∈ Finset.Icc 1 (N / c)) :
    (1 : ℝ) ≤ (N : ℝ) / ((a * d : ℕ) : ℝ) := by
  have hdc : d * c ≤ N := Nat.mul_le_of_le_div c d N (Finset.mem_Icc.mp hd).2
  have hadc : a * d ≤ d * c := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right d hac
  have hadN : a * d ≤ N := hadc.trans hdc
  have hden : (0 : ℝ) < ((a * d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos ha (Finset.mem_Icc.mp hd).1
  exact (one_le_div hden).mpr (by exact_mod_cast hadN)

theorem selbergScaledArgument_le_natCast
    {a N d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    (N : ℝ) / ((a * d : ℕ) : ℝ) ≤ (N : ℝ) := by
  have hden : (0 : ℝ) < ((a * d : ℕ) : ℝ) := by positivity
  have hdenOne : (1 : ℝ) ≤ ((a * d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos ha hd
  apply (div_le_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left hdenOne (Nat.cast_nonneg N)
  simpa using hmul

theorem inv_natCast_le_scaled_of_argument_lt
    {a c N d : ℕ} {K : ℝ} (hK : 0 < K) (hN : 0 < N) (ha : 0 < a)
    (hac : a ≤ c) (hd : 0 < d)
    (hlt : (N : ℝ) / ((a * d : ℕ) : ℝ) < K) :
    1 / (d : ℝ) ≤ K * (c : ℝ) / (N : ℝ) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hadR : (0 : ℝ) < ((a * d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos ha hd
  have hlt' : (N : ℝ) < K * (a : ℝ) * (d : ℝ) := by
    have hraw := (div_lt_iff₀ hadR).mp hlt
    push_cast at hraw
    nlinarith
  apply (le_div_iff₀ hNR).mpr
  rw [one_div, inv_mul_eq_div]
  apply (div_le_iff₀ hdR).mpr
  exact hlt'.le.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast hac) hK.le) hdR.le)

end RHTower.Sieve
