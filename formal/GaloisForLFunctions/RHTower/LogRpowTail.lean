import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import GaloisForLFunctions.RHTower.RieszMellinPair

/-!
# The logarithmically weighted `p`-series tail over all integers

The Chebyshev tail `∑_{p > X}(log p)p^{-1-δ}` has an all-integer companion: a logarithm is absorbed
by half of the excess exponent, after which the tail is an ordinary `p`-series tail.  This is what
the prime-power part of an exterior atom tail needs, where the sum is over prime powers rather than
primes.
-/

namespace RHTower

open Finset

/-- **The all-integer logarithmic tail.**  For every `δ > 0` and every integer cutoff `L ≥ 1`,
`∑_{n > L}(log n)·n^{-1-δ} ≤ (4/δ²)·L^{-δ/2}`. -/
theorem sum_log_rpow_tail_le {δ : ℝ} (hδ : 0 < δ) {L : ℕ} (hL : 1 ≤ L) :
    ∑' j : ℕ, Real.log (((j + L + 1 : ℕ) : ℝ)) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ))
      ≤ (4 / δ ^ 2) * ((L : ℝ)) ^ (-(δ / 2)) := by
  have hσ : (1 : ℝ) < 1 + δ / 2 := by linarith
  have hL1 : (1 : ℝ) ≤ ((L : ℕ) : ℝ) := by exact_mod_cast hL
  have hterm : ∀ j : ℕ,
      Real.log (((j + L + 1 : ℕ) : ℝ)) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ))
        ≤ (2 / δ) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ / 2)) := by
    intro j
    have hn1 : (1 : ℝ) ≤ (((j + L + 1 : ℕ) : ℝ)) := by
      have : (1 : ℕ) ≤ j + L + 1 := by omega
      exact_mod_cast this
    have hn0 : (0 : ℝ) < (((j + L + 1 : ℕ) : ℝ)) := lt_of_lt_of_le one_pos hn1
    have hlog := GaloisForLFunctions.RHTower.log_le_rpow_div hδ hn1
    have hpow0 : (0 : ℝ) < (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ)) :=
      Real.rpow_pos_of_pos hn0 _
    have hmul := mul_le_mul_of_nonneg_right hlog hpow0.le
    refine hmul.trans (le_of_eq ?_)
    rw [mul_assoc, ← Real.rpow_add hn0]
    congr 2
    ring
  have hsummable_maj : Summable (fun j : ℕ =>
      (2 / δ) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ / 2))) := by
    have hbase : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(1 + δ / 2))) := by
      rw [Real.summable_nat_rpow]
      linarith
    have hshift := (summable_nat_add_iff (L + 1)).2 hbase
    refine (hshift.mul_left (2 / δ)).congr fun j => ?_
    congr 2
  have hsummable : Summable (fun j : ℕ =>
      Real.log (((j + L + 1 : ℕ) : ℝ)) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ))) := by
    refine Summable.of_nonneg_of_le (fun j => ?_) hterm hsummable_maj
    have hn1 : (1 : ℝ) ≤ (((j + L + 1 : ℕ) : ℝ)) := by
      have : (1 : ℕ) ≤ j + L + 1 := by omega
      exact_mod_cast this
    have : (0 : ℝ) ≤ Real.log (((j + L + 1 : ℕ) : ℝ)) := Real.log_nonneg hn1
    have hpow : (0 : ℝ) ≤ (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ)) :=
      Real.rpow_nonneg (by linarith) _
    positivity
  calc ∑' j : ℕ, Real.log (((j + L + 1 : ℕ) : ℝ)) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ))
      ≤ ∑' j : ℕ, (2 / δ) * (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ / 2)) :=
        Summable.tsum_le_tsum hterm hsummable hsummable_maj
    _ = (2 / δ) * ∑' j : ℕ, (((j + L + 1 : ℕ) : ℝ)) ^ (-(1 + δ / 2)) := tsum_mul_left
    _ ≤ (2 / δ) * (((L : ℝ)) ^ (1 - (1 + δ / 2)) / ((1 + δ / 2) - 1)) := by
        refine mul_le_mul_of_nonneg_left (Sieve.tsum_tail_rpow_neg_le hσ hL) (by positivity)
    _ = (4 / δ ^ 2) * ((L : ℝ)) ^ (-(δ / 2)) := by
        rw [show (1 : ℝ) - (1 + δ / 2) = -(δ / 2) by ring,
          show (1 : ℝ) + δ / 2 - 1 = δ / 2 by ring]
        field_simp
        ring

end RHTower
