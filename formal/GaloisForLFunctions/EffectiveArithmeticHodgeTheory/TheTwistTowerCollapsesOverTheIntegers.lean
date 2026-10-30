import GaloisForLFunctions.ArithmeticOfSquareRootPrecision.TheBatteryOfTheCount

/-!
# The twist tower collapses over the integers

Over `𝔽_q` the one-sided count is completed by a **twist tower**: the quadratic twists of the
`2^j`-power base changes (AKL, `unitary_iff_twistTower_upper`). Each level reads the curve on the
places whose degree is divisible by `2^j`, with the sign `(−1)^{deg/2^j}`, and every level carries
information because places of every degree exist.

Over `ℤ` the twist is the Liouville character `(−1)^Ω`, the vertical shift of the degree `Ω` that
gives every prime degree one. Its base-change levels are the weights

  `w_j(n) = (−1)^{Ω(n)/2^j} Λ(n)` if `2^j ∣ Ω(n)`, and `0` otherwise (`twistLevel`).

Level `0` is the Liouville twin `λΛ` (`twistLevel_zero`). For `j ≥ 1` the level lives on prime powers
`p^k` with `2^j ∣ k`, never on a prime, so `|w_j| ≤ Λ − Λ·[prime]` and its partial sums are bounded
by `ψ(x) − θ(x) ≤ 2√x log x` (`abs_partialSum_twistLevel_le`): **every level above the first lies in
the square-root class `𝒬`** (`twistLevel_mem_sqrtClass`), invisible to the count.

So the tower collapses to its first level over `ℤ`. Whatever the twist tower supplies over `𝔽_q` is,
over `ℤ`, already in the parity form of the global law, and there one parity class suffices (AKL).
An object whose base changes produce a visible tower would need primes of every degree, which
`ℚ_{>0}` does not have.
-/

open Finset Filter Asymptotics
open ArithmeticFunction

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

open ArithmeticOfSquareRootPrecision

/-- The `j`-th level of the twist tower over `ℤ`: `(−1)^{Ω(n)/2^j} Λ(n)` when `2^j ∣ Ω(n)`. -/
def twistLevel (j : ℕ) (n : ℕ) : ℝ :=
  if 2 ^ j ∣ cardFactors n then (-1) ^ (cardFactors n / 2 ^ j) * vonMangoldt n else 0

/-- Level `0` is the Liouville twin `λΛ`. -/
theorem twistLevel_zero : twistLevel 0 = liouvilleWeight := by
  funext n
  simp [twistLevel, liouvilleWeight]

/-- Above the first level the twist tower lives on proper prime powers:
`|w_j(n)| ≤ Λ(n) − Λ(n)·[n prime]`. -/
theorem abs_twistLevel_le {j : ℕ} (hj : 1 ≤ j) (n : ℕ) :
    |twistLevel j n| ≤ vonMangoldt n - if n.Prime then Real.log n else 0 := by
  by_cases hn : n.Prime
  · have hdvd : ¬ 2 ^ j ∣ cardFactors n := by
      rw [cardFactors_apply_prime hn]
      intro h
      have := Nat.le_of_dvd one_pos h
      have : 2 ≤ 2 ^ j := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
      omega
    rw [twistLevel, if_neg hdvd, if_pos hn, vonMangoldt_apply_prime hn, abs_zero, sub_self]
  · rw [if_neg hn, sub_zero, twistLevel]
    split_ifs
    · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg vonMangoldt_nonneg]
    · rw [abs_zero]; exact vonMangoldt_nonneg

/-- **The levels above the first are bounded by the proper prime powers**:
`|Σ_{n≤x} w_j(n)| ≤ ψ(x) − θ(x)`. -/
theorem abs_partialSum_twistLevel_le {j : ℕ} (hj : 1 ≤ j) (x : ℝ) :
    |partialSum (twistLevel j) x| ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hψθ : Chebyshev.psi x - Chebyshev.theta x =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, (vonMangoldt n - if n.Prime then Real.log n else 0) := by
    rw [Chebyshev.psi, Chebyshev.theta, Finset.sum_sub_distrib, Finset.sum_ite,
      Finset.sum_const_zero, add_zero]
  rw [hψθ, partialSum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => abs_twistLevel_le hj n)

/-- **The twist tower collapses**: every level above the first lies in the square-root class. -/
theorem twistLevel_mem_sqrtClass {j : ℕ} (hj : 1 ≤ j) : twistLevel j ∈ sqrtClass := by
  show partialSum (twistLevel j) =O[atTop] sqrtScale
  refine IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp zero_le_one) hx
  have hlog : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hx
  have h1 := abs_partialSum_twistLevel_le hj x
  have h2 := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sqrtScale,
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg x) (sq_nonneg _))]
  have h3 : 2 * Real.sqrt x * Real.log x ≤ 2 * (Real.sqrt x * Real.log x ^ 2) := by
    have hl2 : Real.log x ≤ Real.log x ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hl2 (Real.sqrt_nonneg x)
    linarith
  linarith [le_abs_self (Chebyshev.psi x - Chebyshev.theta x)]

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
