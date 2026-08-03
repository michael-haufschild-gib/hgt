import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Truncated Möbius sums and the Bonferroni inequalities

Brun's pure sieve replaces the exact inclusion–exclusion indicator

`∑_{d ∣ m} μ d = [m = 1]`

by its truncation to divisors with at most `r` prime factors.  The truncation is not an identity,
but it is a one-sided inequality whose direction is the parity of `r`.  This file proves the exact
value of the truncated sum and the two Bonferroni inequalities.

The arithmetic core is the partial alternating binomial identity

`∑_{j ≤ r} (-1)^j C(k+1, j) = (-1)^r C(k, r)`,

which is Pascal's rule read as a telescoping sum.  Transported along the squarefree
divisor/powerset bijection it gives, for squarefree `m` with `k = #m.primeFactors ≥ 1`,

`∑_{d ∣ m, #d.primeFactors ≤ r} μ d = (-1)^r C(k-1, r)`,

whose sign is exactly `(-1)^r`.  Since the untruncated value is `[m = 1] = 0` for `m ≠ 1`, the
truncated sum overshoots for even `r` and undershoots for odd `r`.

Nothing here assumes primality of the modulus, an upper bound on `r`, or any analytic input.
-/

namespace RHTower.Sieve

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- **Partial alternating binomial sum.**  Truncating the binomial expansion of `(1-1)^(k+1)` at
level `r` leaves exactly `(-1)^r C(k, r)`. -/
theorem alternating_choose_partialSum (k r : ℕ) :
    ∑ j ∈ range (r + 1), (-1 : ℤ) ^ j * ((k + 1).choose j : ℤ) = (-1) ^ r * (k.choose r : ℤ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ k r]
      push_cast
      ring

/-- The Möbius value of a squarefree number in terms of its distinct prime factors. -/
theorem moebius_eq_neg_one_pow_card_primeFactors {d : ℕ} (hd : Squarefree d) :
    (μ d : ℤ) = (-1) ^ d.primeFactors.card := by
  rw [moebius_apply_of_squarefree hd]
  congr 1
  rw [cardFactors_apply]
  exact (List.toFinset_card_of_nodup hd.nodup_primeFactorsList).symm

/-- The squarefree divisor/powerset bijection, in the form needed for truncated sums:
divisors of a squarefree `m` with at most `r` prime factors correspond to subsets of
`m.primeFactors` of cardinality at most `r`. -/
theorem sum_divisors_filter_card_primeFactors_le {m : ℕ} (hm : Squarefree m) (r : ℕ)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ d ∈ {d ∈ m.divisors | d.primeFactors.card ≤ r}, f d
      = ∑ t ∈ {t ∈ m.primeFactors.powerset | t.card ≤ r}, f (∏ p ∈ t, p) := by
  refine (Finset.sum_nbij' (i := fun t => ∏ p ∈ t, p) (j := fun d => d.primeFactors)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    obtain ⟨hsub, hcard⟩ := ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => (Nat.mem_primeFactors.1 (hsub hp)).1
    have hdvd : (∏ p ∈ t, p) ∣ m := by
      refine dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub) ?_
      exact (Nat.prod_primeFactors_of_squarefree hm).dvd
    refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdvd, hm.ne_zero⟩, ?_⟩
    rwa [Nat.primeFactors_prod hprime]
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, hcard⟩ := hd
    exact Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Nat.primeFactors_mono hdvd hm.ne_zero), hcard⟩
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    exact Nat.primeFactors_prod fun p hp => (Nat.mem_primeFactors.1 (ht.1 hp)).1
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    exact Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hd.1.1)
  · intro t _
    rfl

/-- Splitting a bounded-cardinality powerset filter into the cardinality layers. -/
theorem sum_powerset_filter_card_le {α : Type*} [DecidableEq α] (s : Finset α) (r : ℕ)
    {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    ∑ t ∈ {t ∈ s.powerset | t.card ≤ r}, g t.card
      = ∑ j ∈ range (r + 1), (s.card.choose j) • g j := by
  have hsplit :
      {t ∈ s.powerset | t.card ≤ r} = (range (r + 1)).biUnion fun j => s.powersetCard j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_range,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hsub, hcard⟩
      exact ⟨t.card, by omega, hsub, rfl⟩
    · rintro ⟨j, hj, hsub, rfl⟩
      exact ⟨hsub, by omega⟩
  rw [hsplit, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro j _
    have : ∀ t ∈ s.powersetCard j, g t.card = g j := by
      intro t ht
      rw [(Finset.mem_powersetCard.1 ht).2]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_powersetCard]
  · intro i _ j _ hij
    refine Finset.disjoint_left.2 ?_
    intro t hi hj
    exact hij ((Finset.mem_powersetCard.1 hi).2.symm.trans (Finset.mem_powersetCard.1 hj).2)

/-- **Exact truncated Möbius sum.**  For squarefree `m` with at least one prime factor, the
inclusion–exclusion sum truncated at `r` prime factors equals `(-1)^r C(ω m - 1, r)`. -/
theorem sum_divisors_moebius_filter_card_le {m : ℕ} (hm : Squarefree m) (hm1 : m ≠ 1) (r : ℕ) :
    ∑ d ∈ {d ∈ m.divisors | d.primeFactors.card ≤ r}, (μ d : ℤ)
      = (-1) ^ r * ((m.primeFactors.card - 1).choose r : ℤ) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have h1m : 1 < m := by omega
  have hpos : 0 < m.primeFactors.card :=
    Finset.card_pos.2 (Nat.nonempty_primeFactors.2 h1m)
  obtain ⟨k, hk⟩ : ∃ k, m.primeFactors.card = k + 1 := ⟨m.primeFactors.card - 1, by omega⟩
  have hstep :
      ∑ d ∈ {d ∈ m.divisors | d.primeFactors.card ≤ r}, (μ d : ℤ)
        = ∑ t ∈ {t ∈ m.primeFactors.powerset | t.card ≤ r}, (-1 : ℤ) ^ t.card := by
    rw [sum_divisors_filter_card_primeFactors_le hm r (fun d => (μ d : ℤ))]
    refine Finset.sum_congr rfl ?_
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_powerset] at ht
    have hprime : ∀ p ∈ t, p.Prime := fun p hp => (Nat.mem_primeFactors.1 (ht.1 hp)).1
    have hsq : Squarefree (∏ p ∈ t, p) := by
      have hdvd : (∏ p ∈ t, p) ∣ m :=
        dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ ht.1)
          (Nat.prod_primeFactors_of_squarefree hm).dvd
      exact hm.squarefree_of_dvd hdvd
    rw [moebius_eq_neg_one_pow_card_primeFactors hsq, Nat.primeFactors_prod hprime]
  rw [hstep, sum_powerset_filter_card_le m.primeFactors r (fun j => (-1 : ℤ) ^ j), hk]
  simp only [nsmul_eq_mul, Nat.add_sub_cancel]
  rw [← alternating_choose_partialSum k r]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- **Even Bonferroni inequality.**  Truncating inclusion–exclusion at an even number of prime
factors gives an upper sieve. -/
theorem indicator_le_sum_divisors_moebius_filter_card_le
    {m : ℕ} (hm : Squarefree m) {r : ℕ} (hr : Even r) :
    (if m = 1 then (1 : ℤ) else 0)
      ≤ ∑ d ∈ {d ∈ m.divisors | d.primeFactors.card ≤ r}, (μ d : ℤ) := by
  by_cases hm1 : m = 1
  · subst hm1
    simp [Finset.filter_singleton, Nat.primeFactors_one]
  · rw [if_neg hm1, sum_divisors_moebius_filter_card_le hm hm1 r, hr.neg_one_pow, one_mul]
    positivity

/-- **Odd Bonferroni inequality.**  Truncating inclusion–exclusion at an odd number of prime
factors gives a lower sieve. -/
theorem sum_divisors_moebius_filter_card_le_le_indicator
    {m : ℕ} (hm : Squarefree m) {r : ℕ} (hr : Odd r) :
    ∑ d ∈ {d ∈ m.divisors | d.primeFactors.card ≤ r}, (μ d : ℤ)
      ≤ (if m = 1 then (1 : ℤ) else 0) := by
  by_cases hm1 : m = 1
  · subst hm1
    simp [Finset.filter_singleton, Nat.primeFactors_one]
  · rw [if_neg hm1, sum_divisors_moebius_filter_card_le hm hm1 r, hr.neg_one_pow]
    have : (0 : ℤ) ≤ ((m.primeFactors.card - 1).choose r : ℤ) := by positivity
    linarith

end RHTower.Sieve
