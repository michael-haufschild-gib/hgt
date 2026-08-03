import GaloisForLFunctions.RHTower.Sieve.SmallestPart

/-!
# The upper tail of the distinct prime count in an interval

Splitting `ω n` at a cut `z` and treating the two halves by different devices gives an
unconditional bound on the number of integers of `Ioc a b` with many distinct prime factors.

The small-prime half uses the truncated factorial-moment inequality: its main term is the tilted
Euler product `∑_{i ≤ k'} (u-1)^i e_i(z)`, carrying the sharp Chernoff rate, and its error is one
unit per level divisor.  The large-prime half uses the geometric-mean extraction: many prime
factors above `z` force a squarefree divisor with exactly `J` of them whose `c`-th power is at most
`b`, so the divisor range is confined to a `c`-th root and the error is the single term `D`.

Every parameter is free: the cut `z`, the two tilts `u, v ≥ 1`, the level `k'`, the block size `J`,
the compression `c`, and the root bound `D`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Upper tail of the distinct prime count.** -/
theorem card_omega_ge_le (a b z k k' J c D : ℕ) (hab : a ≤ b) (hJ : 1 ≤ J) (hc : 1 ≤ c)
    (hD : b < (D + 1) ^ c) (hk : k' + c * J ≤ k + 1)
    {u : ℝ} (hu : 1 ≤ u) {v : ℝ} (hv : 1 ≤ v) :
    ((#{n ∈ Finset.Ioc a b | k ≤ n.primeFactors.card} : ℕ) : ℝ)
      ≤ (((b : ℝ) - a) * (∑ i ∈ Finset.range (k' + 1),
              (u - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
            + ∑ i ∈ Finset.range (k' + 1), (u - 1) ^ i * ((levelDivisors z i).card : ℝ)) / u ^ k'
        + (((b : ℝ) - a) * ((∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))) / v ^ J) + (D : ℝ)) := by
  classical
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have huk : (0 : ℝ) < u ^ k' := pow_pos hu0 k'
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hsplit : ((#{n ∈ Finset.Ioc a b | k ≤ n.primeFactors.card} : ℕ) : ℝ)
      ≤ ((#{n ∈ Finset.Ioc a b | k' ≤ omegaSmall z n} : ℕ) : ℝ)
        + ((#{n ∈ Finset.Ioc a b | c * J
              ≤ (n.primeFactors.filter (fun p => z < p)).card} : ℕ) : ℝ) := by
    exact_mod_cast card_omega_ge_le_add a b z k k' J c hk
  have hsmall : ((#{n ∈ Finset.Ioc a b | k' ≤ omegaSmall z n} : ℕ) : ℝ)
      ≤ (((b : ℝ) - a) * (∑ i ∈ Finset.range (k' + 1),
              (u - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
            + ∑ i ∈ Finset.range (k' + 1),
                (u - 1) ^ i * ((levelDivisors z i).card : ℝ)) / u ^ k' := by
    rw [le_div_iff₀ huk]
    exact card_omegaSmall_ge_mul_pow_le z a b k' hab hu
  have hbig : ((#{n ∈ Finset.Ioc a b | c * J
        ≤ (n.primeFactors.filter (fun p => z < p)).card} : ℕ) : ℝ)
      ≤ ((b : ℝ) - a) * ((∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))) / v ^ J) + (D : ℝ) := by
    refine le_trans (card_omegaBig_ge_le a b z J c D hab hJ hc hD) ?_
    have hweight := sum_bigDivisors_inv_le z b J c hv
    have := mul_le_mul_of_nonneg_left hweight hlen
    linarith
  linarith

end RHTower.Sieve
