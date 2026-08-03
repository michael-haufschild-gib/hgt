import GaloisForLFunctions.RHTower.Sieve.MainTerm

/-!
# The defect of a Brun truncation

Truncating inclusion–exclusion at `r` prime factors replaces the Euler product
`∏_{p ∣ m} (1 - 1/p)` by a finite sum.  The discarded divisors all carry more than `r` prime
factors, so for any scale `λ ≥ 1` they are penalised by a factor `λ^{-r}` inside the shifted
Euler product `∏_{p ∣ m} (1 + λ/p)`.

This exponential-tilt estimate replaces the elementary-symmetric-function inequality used in the
classical treatment: no factorial and no Maclaurin inequality is needed, and the resulting bound

`|truncated main term - ∏ (1 - 1/p)| ≤ λ^{-r} ∏ (1 + λ/p)`

has the same strength, since choosing `λ` of the order of `r / ∑_{p ∣ m} 1/p` makes it decay
geometrically in `r`.
-/

namespace RHTower.Sieve

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- **Tilted divisor sum.**  For squarefree `m` the generating sum of `λ^{ω d} / d` over the
divisors of `m` is the shifted Euler product. -/
theorem sum_divisors_pow_card_primeFactors_div_eq_prod {m : ℕ} (hm : Squarefree m) (lam : ℝ) :
    ∑ d ∈ m.divisors, lam ^ d.primeFactors.card / d
      = ∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ)) := by
  have hprod :
      ∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))
        = ∑ t ∈ m.primeFactors.powerset, ∏ p ∈ t, (lam / (p : ℝ)) := by
    have := Finset.prod_add (fun p : ℕ => lam / (p : ℝ)) (fun _ : ℕ => (1 : ℝ)) m.primeFactors
    simpa [add_comm] using this
  rw [hprod, sum_divisors_eq_sum_powerset hm]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hsub : t ⊆ m.primeFactors := Finset.mem_powerset.1 ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => (Nat.mem_primeFactors.1 (hsub hp)).1
  rw [Nat.primeFactors_prod hprime, Finset.prod_div_distrib, Finset.prod_const]
  push_cast
  ring

/-- Every divisor discarded by the truncation carries more than `r` prime factors, so a tilt by
`λ ≥ 1` gains a full factor `λ^r`. -/
theorem sum_sdiff_truncDivisors_inv_le {m : ℕ} (hm : Squarefree m) (r : ℕ) {lam : ℝ}
    (hlam : 1 ≤ lam) :
    ∑ d ∈ m.divisors \ truncDivisors m r, (1 : ℝ) / d
      ≤ (∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))) / lam ^ r := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hlamr : (0 : ℝ) < lam ^ r := pow_pos hlam0 r
  rw [le_div_iff₀ hlamr, Finset.sum_mul]
  have hstep : ∀ d ∈ m.divisors \ truncDivisors m r,
      (1 : ℝ) / d * lam ^ r ≤ lam ^ d.primeFactors.card / d := by
    intro d hd
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors (Finset.mem_sdiff.1 hd).1
    have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_sdiff.1 hd).1
    have hcard : r < d.primeFactors.card := by
      by_contra hcon
      exact (Finset.mem_sdiff.1 hd).2
        (mem_truncDivisors.2 ⟨⟨hdvd, hm.ne_zero⟩, by omega⟩)
    have hpow : lam ^ r ≤ lam ^ d.primeFactors.card :=
      pow_le_pow_right₀ hlam (by omega)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [div_mul_eq_mul_div, one_mul, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hpow (inv_nonneg.2 hdR.le)
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← sum_divisors_pow_card_primeFactors_div_eq_prod hm lam]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset) ?_
  intro d hd _
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  positivity

/-- **Truncation defect.**  The truncated inclusion–exclusion main term differs from the Euler
product by at most `λ^{-r}` times the shifted Euler product, for every tilt `λ ≥ 1`. -/
theorem abs_sum_truncDivisors_moebius_div_sub_prod_le {m : ℕ} (hm : Squarefree m) (r : ℕ)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    |(∑ d ∈ truncDivisors m r, (μ d : ℝ) / d) - ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))|
      ≤ (∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))) / lam ^ r := by
  have hsub : truncDivisors m r ⊆ m.divisors := by
    intro d hd
    exact Nat.mem_divisors.2 (mem_truncDivisors.1 hd).1
  have hsplit :
      (∑ d ∈ truncDivisors m r, (μ d : ℝ) / d) - ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
        = - ∑ d ∈ m.divisors \ truncDivisors m r, (μ d : ℝ) / d := by
    rw [← sum_divisors_moebius_div_eq_prod hm, ← Finset.sum_sdiff hsub]
    ring
  rw [hsplit, abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum ?_) (sum_sdiff_truncDivisors_inv_le hm r hlam)
  intro d hd
  have hdmem : d ∈ m.divisors := (Finset.mem_sdiff.1 hd).1
  have hdvd : d ∣ m := Nat.dvd_of_mem_divisors hdmem
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hdmem
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  have habs : |(μ d : ℝ)| = 1 :=
    abs_moebius_eq_one_of_mem_truncDivisors hm
      (mem_truncDivisors.2 ⟨⟨hdvd, hm.ne_zero⟩, le_refl _⟩)
  rw [abs_div, habs, abs_of_pos hdR]

/-- **Brun's pure sieve with an explicit Euler main term, upper bound.** -/
theorem card_coprime_Ioc_le_prod (m a b r : ℕ) (hm : Squarefree m) (hab : a ≤ b) (hr : Even r)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    (#{n ∈ Ioc a b | Nat.Coprime n m} : ℝ)
      ≤ ((b : ℝ) - a) * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
        + ((b : ℝ) - a) * ((∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))) / lam ^ r)
        + (truncDivisors m r).card := by
  have hbase := card_coprime_Ioc_le m a b r hm hab hr
  have hdef := abs_sum_truncDivisors_moebius_div_sub_prod_le hm r hlam
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hmul :
      ((b : ℝ) - a) * (∑ d ∈ truncDivisors m r, (μ d : ℝ) / d)
        ≤ ((b : ℝ) - a) * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
          + ((b : ℝ) - a) * ((∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))) / lam ^ r) := by
    have := (abs_le.1 hdef).2
    nlinarith [hlen]
  linarith

/-- **Brun's pure sieve with an explicit Euler main term, lower bound.** -/
theorem prod_sub_le_card_coprime_Ioc (m a b r : ℕ) (hm : Squarefree m) (hab : a ≤ b) (hr : Odd r)
    {lam : ℝ} (hlam : 1 ≤ lam) :
    ((b : ℝ) - a) * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
        - ((b : ℝ) - a) * ((∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))) / lam ^ r)
        - (truncDivisors m r).card
      ≤ (#{n ∈ Ioc a b | Nat.Coprime n m} : ℝ) := by
  have hbase := le_card_coprime_Ioc m a b r hm hab hr
  have hdef := abs_sum_truncDivisors_moebius_div_sub_prod_le hm r hlam
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hmul :
      ((b : ℝ) - a) * ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
          - ((b : ℝ) - a) * ((∏ p ∈ m.primeFactors, (1 + lam / (p : ℝ))) / lam ^ r)
        ≤ ((b : ℝ) - a) * (∑ d ∈ truncDivisors m r, (μ d : ℝ) / d) := by
    have := (abs_le.1 hdef).1
    nlinarith [hlen]
  linarith

end RHTower.Sieve
