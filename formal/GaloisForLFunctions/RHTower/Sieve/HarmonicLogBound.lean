import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The harmonic row sum in closed form

The Gram-row estimates of this folder produce partial harmonic sums indexed by `Finset.Icc 1 M`.
Identifying them with the harmonic numbers turns those estimates into closed-form logarithmic
bounds:

`∑_{1 ≤ k ≤ M} k^{-1} = H_M ≤ 1 + log M`.

The identification is an induction that matches `Finset.sum_Icc_succ_top` against `harmonic_succ`;
the logarithmic bound is then quoted.
-/

namespace RHTower.Sieve

open Finset

/-- The partial harmonic sum over `Icc 1 M` is the sum over `range M` of shifted reciprocals. -/
theorem sum_Icc_one_div_eq_sum_range (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) = ∑ i ∈ Finset.range M, 1 / ((i : ℝ) + 1) := by
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ← ih, Finset.sum_Icc_succ_top (by omega)]
      push_cast
      ring

/-- The partial harmonic sum is the harmonic number. -/
theorem sum_Icc_one_div_eq_harmonic (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) = (harmonic M : ℝ) := by
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, harmonic_succ]
      push_cast
      ring

/-- **Closed-form bound for the harmonic row sum.** -/
theorem sum_Icc_one_div_le_one_add_log (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ 1 + Real.log M := by
  rw [sum_Icc_one_div_eq_harmonic]
  exact harmonic_le_one_add_log M

end RHTower.Sieve
