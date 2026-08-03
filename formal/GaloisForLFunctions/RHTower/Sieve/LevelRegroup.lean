import GaloisForLFunctions.RHTower.Sieve.OmegaUpperTail

/-!
# Regrouping the level divisors into a Brun truncation

The divisors of `z#` with at most `r` prime factors are the disjoint union of the level sets with
exactly `i` prime factors, `i ≤ r`.  Consequently a sum weighted by a fixed power of the level is a
sum over the truncated divisor set:

`∑_{i ≤ r} w^i ∑_{d ∣ z#, ω d = i} 1/d = ∑_{d ∣ z#, ω d ≤ r} w^{ω d}/d`.

This converts the factorial-moment tail bounds into the Euler-product form already controlled by
`TruncationDefect.lean`: the untruncated weighted divisor sum is `∏_{p ≤ z}(1 + w/p)`, and the
truncation defect is `λ^{-r} ∏_{p ≤ z}(1 + λ/p)`.
-/

namespace RHTower.Sieve

open Finset Nat

theorem truncDivisors_biUnion (z r : ℕ) :
    truncDivisors (primorial z) r
      = (Finset.range (r + 1)).biUnion fun i => levelDivisors z i := by
  classical
  ext d
  simp only [truncDivisors, levelDivisors, Finset.mem_filter, Finset.mem_biUnion,
    Finset.mem_range]
  constructor
  · rintro ⟨hmem, hle⟩
    exact ⟨d.primeFactors.card, by omega, hmem, rfl⟩
  · rintro ⟨i, hi, hmem, rfl⟩
    exact ⟨hmem, by omega⟩

theorem sum_levelDivisors_regroup (z r : ℕ) {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ i ∈ Finset.range (r + 1), ∑ d ∈ levelDivisors z i, f d
      = ∑ d ∈ truncDivisors (primorial z) r, f d := by
  classical
  rw [truncDivisors_biUnion, Finset.sum_biUnion]
  intro i _ j _ hij
  refine Finset.disjoint_left.2 ?_
  intro d hi hj
  exact hij (((Finset.mem_filter.1 hi).2).symm.trans ((Finset.mem_filter.1 hj).2))

/-- The level-weighted reciprocal sum is the tilted divisor sum over a Brun truncation. -/
theorem sum_pow_mul_sum_levelDivisors_inv (z r : ℕ) (w : ℝ) :
    ∑ i ∈ Finset.range (r + 1), w ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d
      = ∑ d ∈ truncDivisors (primorial z) r, w ^ d.primeFactors.card / d := by
  classical
  rw [← sum_levelDivisors_regroup z r (fun d => w ^ d.primeFactors.card / d)]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro d hd
  rw [(Finset.mem_filter.1 hd).2]
  ring

/-- The level cardinalities sum to the size of the Brun truncation. -/
theorem sum_card_levelDivisors (z r : ℕ) :
    ∑ i ∈ Finset.range (r + 1), ((levelDivisors z i).card : ℝ)
      = ((truncDivisors (primorial z) r).card : ℝ) := by
  classical
  have h := sum_levelDivisors_regroup z r (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- **Upper tail in Euler form.**  For a tilt `u ∈ [1,2]` the small-prime main term is the Euler
product `∏_{p ≤ z}(1 + (u-1)/p)` and the small-prime error is the size of the Brun truncation. -/
theorem card_omega_ge_le_euler (a b z k k' J c D : ℕ) (hab : a ≤ b) (hJ : 1 ≤ J) (hc : 1 ≤ c)
    (hD : b < (D + 1) ^ c) (hk : k' + c * J ≤ k + 1)
    {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) {v : ℝ} (hv : 1 ≤ v) :
    ((#{n ∈ Finset.Ioc a b | k ≤ n.primeFactors.card} : ℕ) : ℝ)
      ≤ (((b : ℝ) - a) * (∏ p ∈ Nat.primesLE z, (1 + (u - 1) / (p : ℝ)))
            + ((truncDivisors (primorial z) k').card : ℝ)) / u ^ k'
        + (((b : ℝ) - a) * ((∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))) / v ^ J) + (D : ℝ)) := by
  classical
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu1
  have huk : (0 : ℝ) < u ^ k' := pow_pos hu0 k'
  have hw0 : (0 : ℝ) ≤ u - 1 := by linarith
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hbase := card_omega_ge_le a b z k k' J c D hab hJ hc hD hk hu1 hv
  have hmain : ∑ i ∈ Finset.range (k' + 1),
      (u - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d
      ≤ ∏ p ∈ Nat.primesLE z, (1 + (u - 1) / (p : ℝ)) := by
    rw [sum_pow_mul_sum_levelDivisors_inv z k' (u - 1)]
    have hfull := sum_divisors_pow_card_primeFactors_div_eq_prod
      (squarefree_primorial z) (u - 1)
    rw [primeFactors_primorial_eq] at hfull
    rw [← hfull]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.2 (mem_truncDivisors.1 hd).1
    · intro d hd _
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
      have : (0 : ℝ) < d := by exact_mod_cast hd0
      positivity
  have herr : ∑ i ∈ Finset.range (k' + 1), (u - 1) ^ i * ((levelDivisors z i).card : ℝ)
      ≤ ((truncDivisors (primorial z) k').card : ℝ) := by
    rw [← sum_card_levelDivisors z k']
    refine Finset.sum_le_sum ?_
    intro i _
    have hpow : (u - 1) ^ i ≤ 1 := pow_le_one₀ hw0 (by linarith)
    have hcard : (0 : ℝ) ≤ ((levelDivisors z i).card : ℝ) := by positivity
    nlinarith [hpow, hcard]
  have hmul : ((b : ℝ) - a) * (∑ i ∈ Finset.range (k' + 1),
      (u - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
      ≤ ((b : ℝ) - a) * ∏ p ∈ Nat.primesLE z, (1 + (u - 1) / (p : ℝ)) :=
    mul_le_mul_of_nonneg_left hmain hlen
  have hfirst : (((b : ℝ) - a) * (∑ i ∈ Finset.range (k' + 1),
            (u - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d)
          + ∑ i ∈ Finset.range (k' + 1), (u - 1) ^ i * ((levelDivisors z i).card : ℝ)) / u ^ k'
      ≤ (((b : ℝ) - a) * (∏ p ∈ Nat.primesLE z, (1 + (u - 1) / (p : ℝ)))
          + ((truncDivisors (primorial z) k').card : ℝ)) / u ^ k' := by
    rw [div_le_div_iff_of_pos_right huk]
    linarith
  linarith

/-- **Lower tail in Euler form.**  The Brun truncation defect separates the small-prime main term
into the Euler product `∏_{p ≤ z}(1 - (1-t)/p)` plus a tilted remainder. -/
theorem card_omega_le_le_euler (a b z k r : ℕ) (hab : a ≤ b) (hr : Even r) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) {lam : ℝ} (hlam : 1 ≤ lam) :
    ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ) * t ^ k
      ≤ ((b : ℝ) - a) * ((∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * (1 - t)))
            + (∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r)
        + ((truncDivisors (primorial z) r).card : ℝ) := by
  classical
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hsub : (#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k})
      ≤ (#{n ∈ Finset.Ioc a b | omegaSmall z n ≤ k}) := by
    refine Finset.card_le_card ?_
    intro n hn
    obtain ⟨hmem, hle⟩ := Finset.mem_filter.1 hn
    obtain ⟨han, -⟩ := Finset.mem_Ioc.1 hmem
    have hn0 : n ≠ 0 := by omega
    have hsplit := omegaSmall_add_card_filter (z := z) hn0
    exact Finset.mem_filter.2 ⟨hmem, by omega⟩
  have hcast : ((#{n ∈ Finset.Ioc a b | n.primeFactors.card ≤ k} : ℕ) : ℝ)
      ≤ ((#{n ∈ Finset.Ioc a b | omegaSmall z n ≤ k} : ℕ) : ℝ) := by exact_mod_cast hsub
  have htk : (0 : ℝ) < t ^ k := pow_pos ht0 k
  have hbase := card_omegaSmall_le_mul_pow_le z a b k r hab hr ht0 ht1
  have hstart := mul_le_mul_of_nonneg_right hcast htk.le
  have hdefect := abs_sum_truncDivisors_moebius_div_sub_prod_le
    (squarefree_primorial z) r hlam
  rw [primeFactors_primorial_eq] at hdefect
  have hsplit : ∑ d ∈ truncDivisors (primorial z) r, (t - 1) ^ d.primeFactors.card / d
      ≤ (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * (1 - t)))
        + (∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r := by
    have hfull : ∑ d ∈ (primorial z).divisors, (t - 1) ^ d.primeFactors.card / d
        = ∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * (1 - t)) := by
      have := sum_divisors_pow_card_primeFactors_div_eq_prod (squarefree_primorial z) (t - 1)
      rw [primeFactors_primorial_eq] at this
      rw [this]
      refine Finset.prod_congr rfl ?_
      intro p _
      ring
    have hsubset : truncDivisors (primorial z) r ⊆ (primorial z).divisors := by
      intro d hd
      exact Nat.mem_divisors.2 (mem_truncDivisors.1 hd).1
    have hdiff : ∑ d ∈ truncDivisors (primorial z) r, (t - 1) ^ d.primeFactors.card / d
        = (∑ d ∈ (primorial z).divisors, (t - 1) ^ d.primeFactors.card / d)
          - ∑ d ∈ (primorial z).divisors \ truncDivisors (primorial z) r,
              (t - 1) ^ d.primeFactors.card / d := by
      rw [← Finset.sum_sdiff hsubset]
      ring
    have htail : ∑ d ∈ (primorial z).divisors \ truncDivisors (primorial z) r,
        (t - 1) ^ d.primeFactors.card / d
        ≥ -((∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r) := by
      have hbound := sum_sdiff_truncDivisors_inv_le (squarefree_primorial z) r hlam
      rw [primeFactors_primorial_eq] at hbound
      have hterm : ∀ d ∈ (primorial z).divisors \ truncDivisors (primorial z) r,
          -((1 : ℝ) / d) ≤ (t - 1) ^ d.primeFactors.card / d := by
        intro d hd
        have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_sdiff.1 hd).1
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
        have hpow : -1 ≤ (t - 1) ^ d.primeFactors.card := by
          have habs : |(t - 1) ^ d.primeFactors.card| ≤ 1 := by
            rw [abs_pow]
            refine pow_le_one₀ (abs_nonneg _) ?_
            rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
            linarith
          have := (abs_le.1 habs).1
          linarith
        have heq : -((1 : ℝ) / d) = (-1 : ℝ) / d := by ring
        rw [heq, div_le_div_iff_of_pos_right hdR]
        exact hpow
      have hsum : -∑ d ∈ (primorial z).divisors \ truncDivisors (primorial z) r, (1 : ℝ) / d
          ≤ ∑ d ∈ (primorial z).divisors \ truncDivisors (primorial z) r,
              (t - 1) ^ d.primeFactors.card / d := by
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_le_sum hterm
      linarith
    rw [hdiff, hfull]
    linarith
  have hsum : ∑ i ∈ Finset.range (r + 1), (t - 1) ^ i * ∑ d ∈ levelDivisors z i, (1 : ℝ) / d
      ≤ (∏ p ∈ Nat.primesLE z, (1 - 1 / (p : ℝ) * (1 - t)))
        + (∏ p ∈ Nat.primesLE z, (1 + lam / (p : ℝ))) / lam ^ r := by
    rw [sum_pow_mul_sum_levelDivisors_inv z r (t - 1)]
    exact hsplit
  have hmul := mul_le_mul_of_nonneg_left hsum hlen
  have hcards := sum_card_levelDivisors z r
  linarith

end RHTower.Sieve
