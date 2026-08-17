import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeSum

/-!
# The proper prime-power mass

The von Mangoldt mass carried by the proper prime powers below `K` is Chebyshev's `ψ − θ`, hence
at most `2√K log K`.  This is the exact cost of passing from a twisted Chebyshev sum to a twisted
prime sum.
-/

namespace RHTower.Sieve

open ArithmeticFunction

theorem primePowerDefect_eq (K : ℕ) :
    primePowerDefect K = Chebyshev.psi (K : ℝ) - Chebyshev.theta (K : ℝ) := by
  classical
  have hzero : ∀ n : ℕ,
      ((vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0)
        = if ¬ n.Prime then (vonMangoldt n : ℝ) else 0 := by
    intro n
    by_cases hp : n.Prime
    · rw [if_pos hp, if_neg (by simpa using hp), vonMangoldt_apply_prime hp, sub_self]
    · rw [if_neg hp, if_pos hp, sub_zero]
  have hsub : Finset.Ioc 0 K ⊆ Finset.range (K + 1) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]
    omega
  have hrange : (∑ n ∈ Finset.Ioc 0 K,
        ((vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0))
      = ∑ n ∈ Finset.range (K + 1),
        ((vonMangoldt n : ℝ) - if n.Prime then Real.log n else 0) := by
    refine Finset.sum_subset hsub fun n hn hn' => ?_
    rw [Finset.mem_range] at hn
    have hn0 : n = 0 := by
      by_contra hne
      exact hn' (Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero hne, by omega⟩)
    subst hn0
    simp
  rw [primePowerDefect, ← hrange, Chebyshev.psi_sub_theta_eq_sum_not_prime,
    Nat.floor_natCast, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => hzero n

/-- **The proper prime powers below `K` carry mass at most `2√K log K`.** -/
theorem primePowerDefect_le {K : ℕ} (hK : 1 ≤ K) :
    primePowerDefect K ≤ 2 * Real.sqrt (K : ℝ) * Real.log (K : ℝ) := by
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  rw [primePowerDefect_eq]
  exact Chebyshev.psi_sub_theta_le hK1

end RHTower.Sieve
