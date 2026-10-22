import GaloisForLFunctions.RHTower.Sieve.SelbergHigherLogPrincipalExact

/-!
# Elementary bounds for the Selberg scaled argument N/(a d)

Three elementary inequalities for the scaled argument `N/(a d)` that appears in Selberg sieve
main-term sums over `d ∈ [1, ⌊N/c⌋]`: it is at least `1` when `a ≤ c`, at most `N`, and if it is
below a threshold `K` then `1/d ≤ K c / N`.

## Main results

- `one_le_selbergScaledArgument`: if `0 < a ≤ c` and `1 ≤ d ≤ ⌊N/c⌋`, then `1 ≤ N/(a d)`.
- `selbergScaledArgument_le_natCast`: if `a, d > 0`, then `N/(a d) ≤ N`.
- `inv_natCast_le_scaled_of_argument_lt`: if `K > 0`, `N > 0`, `0 < a ≤ c`, `d > 0` and
  `N/(a d) < K`, then `1/d ≤ K c / N`.

## Hypotheses

Unconditional elementary inequalities; the positivity and range conditions are listed above.
-/

open Finset

namespace RHTower.Sieve

/-- If `0 < a ≤ c` and `d ∈ [1, ⌊N/c⌋]`, then `1 ≤ N/(a d)`. -/
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

/-- For positive `a` and `d`, the scaled argument satisfies `N/(a d) ≤ N`. -/
theorem selbergScaledArgument_le_natCast
    {a N d : ℕ} (ha : 0 < a) (hd : 0 < d) :
    (N : ℝ) / ((a * d : ℕ) : ℝ) ≤ (N : ℝ) := by
  have hden : (0 : ℝ) < ((a * d : ℕ) : ℝ) := by positivity
  have hdenOne : (1 : ℝ) ≤ ((a * d : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos ha hd
  apply (div_le_iff₀ hden).mpr
  have hmul := mul_le_mul_of_nonneg_left hdenOne (Nat.cast_nonneg N)
  simpa using hmul

/-- Assuming `K > 0`, `N > 0`, `0 < a ≤ c` and `d > 0`: if `N/(a d) < K` then `1/d ≤ K c / N`. -/
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
