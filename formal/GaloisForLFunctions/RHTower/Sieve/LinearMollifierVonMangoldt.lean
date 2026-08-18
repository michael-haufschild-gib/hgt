import GaloisForLFunctions.RHTower.Sieve.MollifierShortRange
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMoebius

/-!
# The linear mollifier produces the von Mangoldt weight

Levinson's mollifier carries the smoothing factor `P(log(X/m)/log X)`.  For the linear choice
`P(y) = y` the truncated coefficient at `k ≤ X` collapses, by the classical convolution identity
`μ * log = Λ`, to `Λ(k)/log X`.  This is the source of the boundedness of `∑_k |c_k|²`: the
Chebyshev weight has `∑_{k ≤ X} Λ(k)²/k ≍ (log X)²/2`, exactly cancelling the `(log X)²` in the
denominator, whereas the unsmoothed divisor bound would lose `log⁴`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- `∑_{d ∣ k} μ(d) log d = -Λ(k)` for `k > 1`. -/
theorem sum_moebius_mul_log_eq_neg_vonMangoldt {k : ℕ} (hk : 1 < k) :
    ∑ d ∈ k.divisors, ((μ d : ℤ) : ℝ) * Real.log (d : ℝ) = -vonMangoldt k := by
  have hk0 : 0 < k := lt_trans Nat.zero_lt_one hk
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hbase := vonMangoldt_eq_sum_moebius_mul_log k
  have hsplit : ∀ d ∈ k.divisors,
      ((μ d : ℤ) : ℝ) * Real.log ((k / d : ℕ) : ℝ)
        = ((μ d : ℤ) : ℝ) * Real.log (k : ℝ) - ((μ d : ℤ) : ℝ) * Real.log (d : ℝ) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    have hdvd : d ∣ k := Nat.dvd_of_mem_divisors hd
    have hquot : (((k / d : ℕ) : ℝ)) = (k : ℝ) / (d : ℝ) := by
      rw [Nat.cast_div hdvd (ne_of_gt hdR)]
    rw [hquot, Real.log_div (ne_of_gt hkR) (ne_of_gt hdR)]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_divisors_moebius_real k, if_neg (Nat.ne_of_gt hk), zero_mul, zero_sub] at hbase
  linarith

/-- **The linear mollifier at the short range is the von Mangoldt weight.**  For `1 < k ≤ X`,
`∑_{m ∣ k, m ≤ X} μ(m) log(X/m) = Λ(k)`. -/
theorem sum_moebius_filter_log_div_eq_vonMangoldt {k X : ℕ} (hk : 1 < k) (hkX : k ≤ X) :
    ∑ m ∈ k.divisors.filter (fun m => m ≤ X), ((μ m : ℤ) : ℝ) * Real.log ((X : ℝ) / (m : ℝ))
      = vonMangoldt k := by
  have hk0 : 0 < k := lt_trans Nat.zero_lt_one hk
  have hX0 : 0 < X := lt_of_lt_of_le hk0 hkX
  have hXR : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX0
  rw [filter_le_divisors_eq hk0 hkX]
  have hsplit : ∀ d ∈ k.divisors,
      ((μ d : ℤ) : ℝ) * Real.log ((X : ℝ) / (d : ℝ))
        = ((μ d : ℤ) : ℝ) * Real.log (X : ℝ) - ((μ d : ℤ) : ℝ) * Real.log (d : ℝ) := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    rw [Real.log_div (ne_of_gt hXR) (ne_of_gt hdR)]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_divisors_moebius_real k, if_neg (Nat.ne_of_gt hk), zero_mul, zero_sub,
    sum_moebius_mul_log_eq_neg_vonMangoldt hk]
  ring

end RHTower.Sieve
