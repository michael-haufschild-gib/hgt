import GaloisForLFunctions.RHTower.Sieve.LogSeparation

/-!
# The harmonic row sum at integer frequencies

`∑_{n < N, n ≠ m} |n - m|^{-1} ≤ 2(1 + log N)`.

This is `SeparatedRowSum.sum_inv_abs_dist_le` at the arithmetic progression `λ_i = i` with gap `1`,
combined with the closed-form harmonic bound.  It is the row sum that appears after
`LogSeparation.lean` has replaced the logarithmic separations of a Dirichlet polynomial by integer
ones.
-/

namespace RHTower.Sieve

open Finset

/-- **The harmonic row sum at integer frequencies.** -/
theorem sum_inv_abs_int_dist_le {N m : ℕ} (hm : m < N) :
    ∑ n ∈ (Finset.range N).erase m, 1 / |(n : ℝ) - (m : ℝ)| ≤ 2 * (1 + Real.log N) := by
  have hgap : ∀ i : ℕ, ((i : ℝ)) + 1 ≤ (((i + 1 : ℕ)) : ℝ) := by
    intro i
    push_cast
    linarith
  have h1 := sum_inv_abs_dist_le (lam := fun i : ℕ => (i : ℝ)) (δ := 1) one_pos hgap hm
  have h2 : ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
    rw [← sum_Icc_one_div_eq_sum_range]
    exact sum_Icc_one_div_le_one_add_log N
  have h3 : (2 : ℝ) / 1 = 2 := by norm_num
  rw [h3] at h1
  linarith

end RHTower.Sieve
