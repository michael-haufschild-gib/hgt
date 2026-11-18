import GaloisForLFunctions.ExceptionalLayerTheory.PrimeDivisorsAtTheFirstDyadicSquareCrossing
import GaloisForLFunctions.ExceptionalLayerTheory.TheDirichletSeriesOfDyadicBinomialPrimeCounts

/-!
# Distinct ordinary primes in dyadic binomial gcds

Every ordinary-prime carry supplies a prime divisor. Any additional factor
comes from a prime having at least two possible levels below the cutoff.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- Ordinary primes in the last quotient class, each counted once. -/
def lastClassPrimes (q X : ℕ) : Finset ℕ :=
  (Nat.primesLE X).filter (fun p => q ∣ X/p+1)

private theorem carry_one_dvd_gcd {j N p : ℕ} (hp : p.Prime)
    (hc : dyadicQuotientCarry j N p=1) : p ∈ (dyadicBinomialGcd j N).primeFactors := by
  let K := p.log (2^(j+1)*N)+2
  have hK : 2≤K := Nat.le_add_left ..
  have he := (dyadicBinomialGcd_carry_bounds j N hp hK
    (show p.log (2^(j+1)*N)<K by dsimp only [K]; omega)).1
  have h₁ : dyadicQuotientCarry j N p ≤ ∑ r ∈ Ico 1 K, dyadicQuotientCarry j N (p^r) := by
    simpa only [pow_one] using single_le_sum (f := fun r => dyadicQuotientCarry j N (p^r))
      (fun _ _ => Nat.zero_le _) (mem_Ico.mpr ⟨le_rfl,by omega : 1<K⟩)
  rw [hc] at h₁
  rw [← Nat.support_factorization,Finsupp.mem_support_iff]
  exact Nat.ne_of_gt (h₁.trans he)

/-- The set omitted by using only the prime level is confined to the square-root cutoff. -/
theorem dyadicBinomialGcd_distinct_prime_factors (j N : ℕ) :
    let q := 2^(j+1)
    lastClassPrimes q (q*N) ⊆ (dyadicBinomialGcd j N).primeFactors ∧
      (dyadicBinomialGcd j N).primeFactors ⊆ lastClassPrimes q (q*N) ∪ Nat.primesLE (q*N).sqrt := by
  let q := 2^(j+1)
  have hq : 2≤q := by dsimp only [q]; have := Nat.lt_two_pow_self (n := j+1); omega
  constructor
  · intro p hp
    obtain ⟨hpr,hd⟩ := mem_filter.mp hp
    exact carry_one_dvd_gcd (Nat.prime_of_mem_primesLE hpr) (if_pos hd)
  · intro p hp
    have hpr := (Nat.mem_primeFactors.mp hp).1
    by_cases hs : p≤(q*N).sqrt
    · exact mem_union_right _ (Nat.mem_primesLE.mpr ⟨hs,hpr⟩)
    · apply mem_union_left
      have hsq : q*N<p^2 := lt_of_not_ge (fun h => hs (Nat.le_sqrt.mpr (by simpa only [sq] using h)))
      have he := factorization_dyadicBinomialGcd_of_lt_sq (j := j) (N := N) hpr hsq
      rw [← Nat.support_factorization,Finsupp.mem_support_iff,he] at hp
      have hd : q ∣ q*N/p+1 := by
        by_contra hh
        exact hp (if_neg hh)
      have hx : p≤q*N := by
        by_contra! h
        rw [Nat.div_eq_of_lt h,zero_add] at hd
        have := Nat.le_of_dvd one_pos hd
        omega
      exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hx,hpr⟩,hd⟩

/-- Uniform count discrepancy, with the ordinary prime-counting function as
the exact available small-prime allowance. -/
theorem dyadicBinomialGcd_distinct_prime_count_error (j N : ℕ) :
    let X := 2^(j+1)*N
    0 ≤ ((dyadicBinomialGcd j N).primeFactors.card : ℝ)-(lastClassPrimes (2^(j+1)) X).card ∧
      ((dyadicBinomialGcd j N).primeFactors.card : ℝ)-(lastClassPrimes (2^(j+1)) X).card ≤
        Nat.primeCounting X.sqrt := by
  obtain ⟨hl,hu⟩ := dyadicBinomialGcd_distinct_prime_factors j N
  exact ⟨sub_nonneg.mpr (by exact_mod_cast card_le_card hl),sub_le_iff_le_add'.mpr (by
    have h := (card_le_card hu).trans (card_union_le ..)
    rw [Nat.primesLE_card_eq_primeCounting] at h
    exact_mod_cast h)⟩

#print axioms dyadicBinomialGcd_distinct_prime_factors
#print axioms dyadicBinomialGcd_distinct_prime_count_error

end GaloisForLFunctions.ExceptionalLayerTheory
