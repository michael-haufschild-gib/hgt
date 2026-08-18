import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# The `ω_P`-weighted Möbius polynomial factors exactly

Weighting an integer by the *number* of its designated prime factors — rather than by Ramaré's
reciprocal of that number — turns a Dirichlet polynomial into a bilinear form with **no error term
at all**: double counting replaces the weight by a sum over the designated primes, and Möbius
multiplicativity splits each summand, the indices whose cofactor is still divisible by the prime
contributing zero because they are not squarefree.

This is the factorisation the short-interval argument uses before Turán--Kubilius removes the
weight.  The price of the weight is paid once, arithmetically, in the variance of `ω_P`; the
spectral side sees an exact product.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The Möbius polynomial with each index weighted by its number of designated prime factors. -/
def omegaWeightedMoebiusPoly (P S : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ n ∈ S, ((primeFactorsIn P n).card : ℂ) * moebiusPhase w n

/-- **Double counting the weight.**  The weight is the number of designated primes dividing the
index, so the weighted sum is the sum over designated primes of the sum over their multiples. -/
theorem omegaWeightedMoebiusPoly_eq_sum (P S : Finset ℕ) (w : ℝ) :
    omegaWeightedMoebiusPoly P S w = ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, moebiusPhase w n := by
  classical
  have hswap : ∀ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n}, moebiusPhase w n
      = ∑ n ∈ S, (if p ∣ n then moebiusPhase w n else 0) := fun p _ => Finset.sum_filter _ _
  simp only [omegaWeightedMoebiusPoly]
  rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_filter]
  have hfilter : {p ∈ P | p ∣ n} = primeFactorsIn P n := rfl
  rw [hfilter, Finset.sum_const, nsmul_eq_mul]

/-- A Möbius phase at a non-squarefree index vanishes: if a prime divides the cofactor, the product
carries its square. -/
theorem moebiusPhase_eq_zero_of_dvd {p m : ℕ} (hp : p.Prime) (hpm : p ∣ m) (w : ℝ) :
    moebiusPhase w (p * m) = 0 := by
  have hsq : ¬ Squarefree (p * m) := by
    intro hsf
    obtain ⟨k, rfl⟩ := hpm
    have hdvd : p * p ∣ p * (p * k) := ⟨k, by ring⟩
    have hone : p = 1 := Nat.isUnit_iff.1 (hsf p hdvd)
    exact absurd hone (Nat.Prime.ne_one hp)
  rw [moebiusPhase, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  simp

/-- **The `ω_P`-weighted Möbius polynomial is an exact bilinear form.**  Every designated prime
contributes its own phase times the Möbius polynomial over its cofactors coprime to it. -/
theorem omegaWeightedMoebiusPoly_eq_bilinear {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime)
    (S : Finset ℕ) (w : ℝ) :
    omegaWeightedMoebiusPoly P S w
      = ∑ p ∈ P, moebiusPhase w p
          * ∑ m ∈ {m ∈ ramareCofactorSet S p | ¬ p ∣ m}, moebiusPhase w m := by
  classical
  rw [omegaWeightedMoebiusPoly_eq_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := hPprime p hp
  have hreindex : ∑ n ∈ {n ∈ S | p ∣ n}, moebiusPhase w n
      = ∑ m ∈ ramareCofactorSet S p, moebiusPhase w (p * m) :=
    (sum_div_image_complex p {n ∈ S | p ∣ n} (fun n hn => (Finset.mem_filter.1 hn).2)
      (fun n => moebiusPhase w n)).symm
  rw [hreindex]
  have hsplit : ∑ m ∈ ramareCofactorSet S p, moebiusPhase w (p * m)
      = (∑ m ∈ {m ∈ ramareCofactorSet S p | ¬ p ∣ m}, moebiusPhase w (p * m))
        + ∑ m ∈ {m ∈ ramareCofactorSet S p | p ∣ m}, moebiusPhase w (p * m) := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (ramareCofactorSet S p) (fun m => p ∣ m) _).symm
  have hzero : ∑ m ∈ {m ∈ ramareCofactorSet S p | p ∣ m}, moebiusPhase w (p * m) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    exact moebiusPhase_eq_zero_of_dvd hprime (Finset.mem_filter.1 hm).2 w
  rw [hsplit, hzero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  exact map_mul_prime_of_not_dvd_complex (moebiusPhase_mul_of_coprime w) hprime
    (Finset.mem_filter.1 hm).2

/-! ## The factorisation over a partition of the designated primes -/

/-- **The weighted polynomial over a partition of the designated primes.**  Splitting `P` into
blocks splits the bilinear form into one summand per block. -/
theorem omegaWeightedMoebiusPoly_eq_blocks {P : Finset ℕ} (hPprime : ∀ p ∈ P, p.Prime)
    (S : Finset ℕ) (w : ℝ) {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    omegaWeightedMoebiusPoly P S w
      = ∑ i ∈ I, ∑ p ∈ B i, moebiusPhase w p
          * ∑ m ∈ {m ∈ ramareCofactorSet S p | ¬ p ∣ m}, moebiusPhase w m := by
  classical
  rw [omegaWeightedMoebiusPoly_eq_bilinear hPprime S w, ← hcover]
  exact Finset.sum_biUnion hdisj

end

end RHTower.Sieve
