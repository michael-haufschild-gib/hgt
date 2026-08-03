import GaloisForLFunctions.RHTower.Sieve.BrunPure

/-!
# The sieve main term and the size of a Brun truncation

The truncated main term of Brun's pure sieve is compared here with the Euler product it
approximates.  For a squarefree modulus `m` with prime support `P = m.primeFactors`:

* the untruncated main term is exactly the Euler product `∏_{p ∈ P} (1 - 1/p)`;
* the divisors removed by a truncation at `r` prime factors are graded by the elementary
  symmetric layers of `(1/p)_{p ∈ P}`, so the truncation defect is bounded by the sum of those
  layers above level `r`;
* the number of divisors surviving the truncation is exactly `∑_{j ≤ r} C(#P, j)`.

All three statements are exact identities or explicit inequalities; nothing analytic enters.
-/

namespace RHTower.Sieve

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Every divisor of `m` has at most as many prime factors as `m`. -/
theorem card_primeFactors_le_of_dvd {d m : ℕ} (hd : d ∣ m) (hm : m ≠ 0) :
    d.primeFactors.card ≤ m.primeFactors.card :=
  Finset.card_le_card (Nat.primeFactors_mono hd hm)

/-- At the full truncation level the Brun divisor set is the whole divisor set. -/
theorem truncDivisors_card_primeFactors {m : ℕ} :
    truncDivisors m m.primeFactors.card = m.divisors := by
  ext d
  simp only [mem_truncDivisors, Nat.mem_divisors]
  constructor
  · rintro ⟨h, -⟩; exact h
  · rintro ⟨hdvd, hm0⟩
    exact ⟨⟨hdvd, hm0⟩, card_primeFactors_le_of_dvd hdvd hm0⟩

/-- **Squarefree divisor/powerset transfer.**  Summing any function over the divisors of a
squarefree number is summing over the subsets of its prime support. -/
theorem sum_divisors_eq_sum_powerset {m : ℕ} (hm : Squarefree m)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ d ∈ m.divisors, f d = ∑ t ∈ m.primeFactors.powerset, f (∏ p ∈ t, p) := by
  have hfull := sum_divisors_filter_card_primeFactors_le hm m.primeFactors.card f
  have hleft : {d ∈ m.divisors | d.primeFactors.card ≤ m.primeFactors.card} = m.divisors := by
    have := truncDivisors_card_primeFactors (m := m)
    simpa [truncDivisors] using this
  have hright :
      {t ∈ m.primeFactors.powerset | t.card ≤ m.primeFactors.card} = m.primeFactors.powerset := by
    refine Finset.filter_true_of_mem ?_
    intro t ht
    exact Finset.card_le_card (Finset.mem_powerset.1 ht)
  rwa [hleft, hright] at hfull

/-- **Euler product for the sieve main term.**  For squarefree `m` the full inclusion–exclusion
main term is the Euler product over the prime support. -/
theorem sum_divisors_moebius_div_eq_prod {m : ℕ} (hm : Squarefree m) :
    ∑ d ∈ m.divisors, (μ d : ℝ) / d = ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ)) := by
  have hprod :
      ∏ p ∈ m.primeFactors, (1 - 1 / (p : ℝ))
        = ∑ t ∈ m.primeFactors.powerset, ∏ p ∈ t, (-(1 / (p : ℝ))) := by
    have := Finset.prod_add (fun p : ℕ => -(1 / (p : ℝ))) (fun _ : ℕ => (1 : ℝ)) m.primeFactors
    simpa [sub_eq_add_neg, add_comm] using this
  rw [hprod, sum_divisors_eq_sum_powerset hm]
  refine Finset.sum_congr rfl ?_
  intro t ht
  have hsub : t ⊆ m.primeFactors := Finset.mem_powerset.1 ht
  have hprime : ∀ p ∈ t, p.Prime := fun p hp => (Nat.mem_primeFactors.1 (hsub hp)).1
  have hsq : Squarefree (∏ p ∈ t, p) := by
    have hdvd : (∏ p ∈ t, p) ∣ m :=
      dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
        (Nat.prod_primeFactors_of_squarefree hm).dvd
    exact hm.squarefree_of_dvd hdvd
  have hmu : (μ (∏ p ∈ t, p) : ℝ) = (-1) ^ t.card := by
    have h1 : (μ (∏ p ∈ t, p) : ℤ) = (-1) ^ (∏ p ∈ t, p).primeFactors.card :=
      moebius_eq_neg_one_pow_card_primeFactors hsq
    rw [Nat.primeFactors_prod hprime] at h1
    exact_mod_cast h1
  rw [hmu, Finset.prod_neg, Finset.prod_div_distrib, Finset.prod_const_one]
  push_cast
  ring

/-- The divisors dropped by a Brun truncation, graded by their number of prime factors. -/
theorem sum_divisors_sdiff_truncDivisors {m : ℕ} (hm : Squarefree m) (r : ℕ)
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ d ∈ m.divisors \ truncDivisors m r, f d
      = ∑ j ∈ Ico (r + 1) (m.primeFactors.card + 1),
          ∑ t ∈ m.primeFactors.powersetCard j, f (∏ p ∈ t, p) := by
  classical
  have hsdiff : m.divisors \ truncDivisors m r = {d ∈ m.divisors | ¬ d.primeFactors.card ≤ r} := by
    ext d
    simp only [Finset.mem_sdiff, mem_truncDivisors, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdvd, hm0⟩, hnot⟩
      exact ⟨⟨hdvd, hm0⟩, fun hle => hnot ⟨⟨hdvd, hm0⟩, hle⟩⟩
    · rintro ⟨⟨hdvd, hm0⟩, hnot⟩
      exact ⟨⟨hdvd, hm0⟩, fun h => hnot h.2⟩
  rw [hsdiff]
  have hbij :
      ∑ d ∈ {d ∈ m.divisors | ¬ d.primeFactors.card ≤ r}, f d
        = ∑ t ∈ {t ∈ m.primeFactors.powerset | ¬ t.card ≤ r}, f (∏ p ∈ t, p) := by
    refine (Finset.sum_nbij' (i := fun t => ∏ p ∈ t, p) (j := fun d => d.primeFactors)
      ?_ ?_ ?_ ?_ ?_).symm
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_powerset] at ht
      obtain ⟨hsub, hcard⟩ := ht
      have hprime : ∀ p ∈ t, p.Prime := fun p hp => (Nat.mem_primeFactors.1 (hsub hp)).1
      have hdvd : (∏ p ∈ t, p) ∣ m :=
        dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
          (Nat.prod_primeFactors_of_squarefree hm).dvd
      refine Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdvd, hm.ne_zero⟩, ?_⟩
      rwa [Nat.primeFactors_prod hprime]
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdvd, -⟩, hcard⟩ := hd
      exact Finset.mem_filter.2
        ⟨Finset.mem_powerset.2 (Nat.primeFactors_mono hdvd hm.ne_zero), hcard⟩
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_powerset] at ht
      exact Nat.primeFactors_prod fun p hp => (Nat.mem_primeFactors.1 (ht.1 hp)).1
    · intro d hd
      simp only [Finset.mem_filter, Nat.mem_divisors] at hd
      exact Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hd.1.1)
    · intro t _
      rfl
  rw [hbij]
  have hsplit :
      {t ∈ m.primeFactors.powerset | ¬ t.card ≤ r}
        = (Ico (r + 1) (m.primeFactors.card + 1)).biUnion
            fun j => m.primeFactors.powersetCard j := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_biUnion, Finset.mem_Ico,
      Finset.mem_powersetCard, not_le]
    constructor
    · rintro ⟨hsub, hcard⟩
      have hle : t.card ≤ m.primeFactors.card := Finset.card_le_card hsub
      exact ⟨t.card, ⟨hcard, by omega⟩, hsub, rfl⟩
    · rintro ⟨j, ⟨hj1, -⟩, hsub, rfl⟩
      exact ⟨hsub, by omega⟩
  rw [hsplit, Finset.sum_biUnion]
  intro i _ j _ hij
  refine Finset.disjoint_left.2 ?_
  intro t hi hj
  exact hij ((Finset.mem_powersetCard.1 hi).2.symm.trans (Finset.mem_powersetCard.1 hj).2)

/-- **Exact size of a Brun truncation.**  The truncated divisor set has cardinality
`∑_{j ≤ r} C(ω m, j)`. -/
theorem card_truncDivisors {m : ℕ} (hm : Squarefree m) (r : ℕ) :
    (truncDivisors m r).card = ∑ j ∈ range (r + 1), (m.primeFactors.card).choose j := by
  have h1 : (truncDivisors m r).card = ∑ _d ∈ truncDivisors m r, 1 := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  have h2 :
      ∑ _d ∈ truncDivisors m r, (1 : ℕ)
        = ∑ t ∈ {t ∈ m.primeFactors.powerset | t.card ≤ r}, (1 : ℕ) := by
    simpa [truncDivisors] using
      sum_divisors_filter_card_primeFactors_le hm r (fun _ => (1 : ℕ))
  have h3 :
      ∑ t ∈ {t ∈ m.primeFactors.powerset | t.card ≤ r}, (1 : ℕ)
        = ∑ j ∈ range (r + 1), (m.primeFactors.card).choose j := by
    have := sum_powerset_filter_card_le m.primeFactors r (fun _ => (1 : ℕ))
    simpa using this
  rw [h1, h2, h3]

end RHTower.Sieve
