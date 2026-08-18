import GaloisForLFunctions.RHTower.Sieve.RoughPairRemainderSum
import GaloisForLFunctions.RHTower.Sieve.RoughPairSieveBound

/-!
# The shifted rough pair count

Substituting the two halves of the sieve — the bounding sum from below and the remainder from above
— into Selberg's bound gives the estimate the short-interval argument needs: the number of `m ≤ Y`
with both `m` and `m + d` free of primes in `(P₁, h]` is at most

    Y · 2 · exp(mertensS h − mertensS P₁)^{-2} · C^{-1}  +  (remainder) ,

with `C` the shift correction.  The first factor is the `(log P₁/log h)²` saving; the remainder is
`y^{1+o(1)}`.  Both are uniform in the shift.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The distinct-prime-factor count is the cardinality of the prime-factor set. -/
theorem cardDistinctFactors_eq (n : ℕ) :
    ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

/-- **The shifted rough pair count.** -/
theorem card_roughPair_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ} (d k : ℕ) {z : ℝ}
    (hz : 1 ≤ z) (hY : 0 ≤ Y) (hh1 : 1 ≤ h) (hP₁h : P₁ ≤ h) (hlev : ((h : ℝ)) ^ (2 * k) ≤ z)
    (hk : Real.exp 1
        * (∑ p ∈ rangePrimes P₁ h, pairClassCount d p / ((p : ℝ) - pairClassCount d p))
        + Real.log 2 ≤ (k : ℝ)) :
    ((((Finset.Icc 1 ⌊Y⌋₊).filter
          (fun m => (∀ p ∈ rangePrimes P₁ h, ¬ p ∣ m)
            ∧ ∀ p ∈ rangePrimes P₁ h, ¬ p ∣ (m + d))).card : ℕ) : ℝ)
      ≤ Y / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ 2
            * ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ))))
        + ∑ e ∈ (rangePrimorial P₁ h).divisors,
            (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) := by
  classical
  set s : SelbergSieve := roughPairSieve Y hP₁ h d hz with hs
  set C : ℝ := ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ d), (((p : ℝ) - 1) / (p : ℝ)) with hC
  have hp3 : ∀ p ∈ rangePrimes P₁ h, (3 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    have : 3 ≤ p := by omega
    exact_mod_cast this
  have hC0 : (0 : ℝ) < C := by
    rw [hC]
    refine Finset.prod_pos fun p hp => ?_
    have h3 := hp3 p (Finset.mem_filter.1 hp).1
    have hnum : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    have hden : (0 : ℝ) < (p : ℝ) := by linarith
    positivity
  set L : ℝ := (1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ 2 * C) with hL
  have hL0 : (0 : ℝ) < L := by
    rw [hL]
    have : (0 : ℝ) < Real.exp (mertensS h - mertensS P₁) ^ 2 := by positivity
    positivity
  have hSge : L ≤ SelbergSieve.selbergBoundingSum s :=
    selbergBoundingSum_ge_mertens Y hP₁ d k hz hh1 hP₁h hlev hk
  have hSpos : 0 < SelbergSieve.selbergBoundingSum s := SelbergSieve.selbergBoundingSum_pos s
  have hbase := SelbergSieve.selberg_bound_simple s
  rw [siftedSum_roughPairSieve Y hP₁ h d hz] at hbase
  simp only [cardDistinctFactors_eq] at hbase
  refine hbase.trans (add_le_add ?_ ?_)
  · show Y / SelbergSieve.selbergBoundingSum s ≤ Y / L
    rw [div_le_div_iff₀ hSpos hL0]
    nlinarith [hSge, hY, hL0]
  · refine Finset.sum_le_sum fun e he => ?_
    rw [Nat.mem_divisors] at he
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | hpos
      · exact absurd (zero_dvd_iff.1 he.1) he.2
      · exact hpos
    have hsummand := selberg_summand_le Y hP₁ h d hz hY he1 he.1
    show (if ((e : ℕ) : ℝ) ≤ z then (3 : ℝ) ^ e.primeFactors.card
        * |BoundingSieve.rem (s := s.toBoundingSieve) e| else 0)
      ≤ (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0)
    split_ifs with hle
    · exact hsummand
    · exact le_rfl

end

end RHTower.Sieve
