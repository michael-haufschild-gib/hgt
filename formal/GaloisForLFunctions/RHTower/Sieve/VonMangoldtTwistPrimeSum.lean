import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistSharpSum

/-!
# From the twisted Chebyshev sum to the twisted prime sum

The Perron argument produces `∑_{n ≤ K} Λ(n) n^{-iτ}`; a prime sum is
`∑_{p ≤ K} (log p) p^{-iτ}`.  The two differ exactly on the proper prime powers, and the twist has
modulus one, so the whole discrepancy is the *untwisted* von Mangoldt mass those powers carry —
Chebyshev's `ψ - θ`, of size `O(√K (log K)²)` and negligible against any prime sum.

This is the last elementary step before partial summation converts `∑_{p ≤ K}(log p)p^{-iτ}` into
`∑_{p ≤ K} p^{-iτ}`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- The twisted prime sum weighted by `log p`: the twisted Chebyshev `θ`. -/
noncomputable def vonMangoldtPrimeTwist (τ : ℝ) (n : ℕ) : ℂ :=
  if n.Prime then ((Real.log n : ℝ) : ℂ) * (n : ℂ) ^ (-((τ : ℂ) * Complex.I)) else 0

/-- The von Mangoldt mass carried by the proper prime powers up to `K`. -/
noncomputable def primePowerDefect (K : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (K + 1), ((vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0)

theorem primePowerDefect_nonneg (K : ℕ) : 0 ≤ primePowerDefect K := by
  refine Finset.sum_nonneg fun n _ => ?_
  by_cases hp : n.Prime
  · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
  · rw [if_neg hp, sub_zero]
    exact vonMangoldt_nonneg

/-- The twisted coefficients differ by the proper prime powers, with the twist factored out. -/
theorem vonMangoldtTwist_sub_prime (τ : ℝ) (n : ℕ) :
    vonMangoldtTwist τ n - vonMangoldtPrimeTwist τ n
      = (((vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0 : ℝ) : ℂ)
        * (n : ℂ) ^ (-((τ : ℂ) * Complex.I)) := by
  by_cases hp : n.Prime
  · rw [vonMangoldtPrimeTwist, if_pos hp, vonMangoldtTwist, vonMangoldt_apply_prime hp, if_pos hp]
    push_cast
    ring
  · rw [vonMangoldtPrimeTwist, if_neg hp, vonMangoldtTwist, if_neg hp]
    push_cast
    ring

/-- **Removing the proper prime powers from the twisted Chebyshev sum.**  The twist has modulus one,
so the whole discrepancy is the untwisted von Mangoldt mass of the proper prime powers. -/
theorem norm_partialSum_vonMangoldtTwist_sub_prime_le (τ : ℝ) (K : ℕ) :
    ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n
        - ∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖
      ≤ primePowerDefect K := by
  rw [← Finset.sum_sub_distrib]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun n _ => ?_
  rw [vonMangoldtTwist_sub_prime, norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; ring
    have h1 : ‖((n : ℕ) : ℂ) ^ (-((τ : ℂ) * Complex.I))‖ = 1 := by
      rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      simp
    have hnn : (0 : ℝ) ≤ (vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0 := by
      by_cases hp : n.Prime
      · rw [if_pos hp, vonMangoldt_apply_prime hp, sub_self]
      · rw [if_neg hp, sub_zero]
        exact vonMangoldt_nonneg
    rw [h1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]

/-- **The twisted prime sum, weighted by `log p`, from the twisted Chebyshev sum.** -/
theorem norm_partialSum_vonMangoldtPrimeTwist_le (τ : ℝ) (K : ℕ) {B : ℝ}
    (hB : ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖ ≤ B) :
    ‖∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖ ≤ B + primePowerDefect K := by
  have hsub := norm_partialSum_vonMangoldtTwist_sub_prime_le τ K
  have htri := norm_sub_norm_le (∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n)
    (∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n)
  rw [norm_sub_rev] at htri
  linarith

end RHTower.Sieve
