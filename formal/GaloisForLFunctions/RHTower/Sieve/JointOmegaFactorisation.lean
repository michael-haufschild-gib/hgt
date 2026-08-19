import GaloisForLFunctions.RHTower.Sieve.JointOmegaSpectral

/-!
# The two-variable factorisation of the jointly weighted Möbius polynomial

Exposé §4 writes the `ω_P·ω_Q`-weighted Möbius polynomial as a sum over the short designated primes
of a phase times a cofactor polynomial which still carries the long weight `ω_Q`.  The identity is
exact — no error term — because a designated prime dividing its own cofactor makes the index
non-squarefree, and because the two designated ranges are disjoint sets of primes, so removing a
`p ∈ P` does not change `ω_Q`.

The cofactor is literally the corpus's single-weight `omegaWeightedMoebiusPoly Q ·`, so the second
factorisation (over `Q`) is `Sieve/OmegaWeightedFactorisation.omegaWeightedMoebiusPoly_eq_bilinear`
applied again.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Removing a prime outside `Q` does not change the `Q`-count. -/
theorem primeFactorsIn_mul_prime_not_mem {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {p : ℕ}
    (hp : p.Prime) (hpQ : p ∉ Q) (m : ℕ) :
    primeFactorsIn Q (p * m) = primeFactorsIn Q m := by
  classical
  ext q
  rw [mem_primeFactorsIn, mem_primeFactorsIn]
  constructor
  · rintro ⟨hqQ, hqdvd⟩
    refine ⟨hqQ, ?_⟩
    rcases (Nat.Prime.dvd_mul (hQ q hqQ)).1 hqdvd with hq | hq
    · exact absurd (by rwa [(Nat.prime_dvd_prime_iff_eq (hQ q hqQ) hp).1 hq] at hqQ) hpQ
    · exact hq
  · rintro ⟨hqQ, hqdvd⟩
    exact ⟨hqQ, hqdvd.mul_left p⟩

/-- **The jointly weighted polynomial, factorised over the short designated primes.**  Exact, with
no error term; the cofactor is the single-`Q`-weighted Möbius polynomial. -/
theorem jointOmegaPoly_eq_bilinear {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) (S : Finset ℕ) (w : ℝ) :
    jointOmegaPoly P Q S w
      = ∑ p ∈ P, moebiusPhase w p
          * omegaWeightedMoebiusPoly Q {m ∈ ramareCofactorSet S p | ¬ p ∣ m} w := by
  classical
  -- double counting the short weight
  have hsum : jointOmegaPoly P Q S w
      = ∑ p ∈ P, ∑ n ∈ {n ∈ S | p ∣ n},
          ((primeFactorsIn Q n).card : ℂ) * moebiusPhase w n := by
    have hswap : ∀ p ∈ P, (∑ n ∈ {n ∈ S | p ∣ n},
          ((primeFactorsIn Q n).card : ℂ) * moebiusPhase w n)
        = ∑ n ∈ S, (if p ∣ n then ((primeFactorsIn Q n).card : ℂ) * moebiusPhase w n else 0) :=
      fun p _ => Finset.sum_filter _ _
    rw [jointOmegaPoly, Finset.sum_congr rfl hswap, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_filter]
    have hfilter : {p ∈ P | p ∣ n} = primeFactorsIn P n := rfl
    rw [hfilter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hsum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hprime := hP p hp
  have hpQ : p ∉ Q := Finset.disjoint_left.1 hPQ hp
  have hreindex : (∑ n ∈ {n ∈ S | p ∣ n}, ((primeFactorsIn Q n).card : ℂ) * moebiusPhase w n)
      = ∑ m ∈ ramareCofactorSet S p,
          ((primeFactorsIn Q (p * m)).card : ℂ) * moebiusPhase w (p * m) :=
    (sum_div_image_complex p {n ∈ S | p ∣ n} (fun n hn => (Finset.mem_filter.1 hn).2)
      (fun n => ((primeFactorsIn Q n).card : ℂ) * moebiusPhase w n)).symm
  rw [hreindex]
  have hsplit : (∑ m ∈ ramareCofactorSet S p,
        ((primeFactorsIn Q (p * m)).card : ℂ) * moebiusPhase w (p * m))
      = (∑ m ∈ {m ∈ ramareCofactorSet S p | ¬ p ∣ m},
          ((primeFactorsIn Q (p * m)).card : ℂ) * moebiusPhase w (p * m))
        + ∑ m ∈ {m ∈ ramareCofactorSet S p | p ∣ m},
            ((primeFactorsIn Q (p * m)).card : ℂ) * moebiusPhase w (p * m) := by
    rw [add_comm]
    exact (Finset.sum_filter_add_sum_filter_not (ramareCofactorSet S p) (fun m => p ∣ m) _).symm
  have hzero : (∑ m ∈ {m ∈ ramareCofactorSet S p | p ∣ m},
      ((primeFactorsIn Q (p * m)).card : ℂ) * moebiusPhase w (p * m)) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [moebiusPhase_eq_zero_of_dvd hprime (Finset.mem_filter.1 hm).2 w, mul_zero]
  rw [hsplit, hzero, add_zero, omegaWeightedMoebiusPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hnd : ¬ p ∣ m := (Finset.mem_filter.1 hm).2
  rw [primeFactorsIn_mul_prime_not_mem hQ hprime hpQ m,
    map_mul_prime_of_not_dvd_complex (moebiusPhase_mul_of_coprime w) hprime hnd]
  ring

/-- **The factorisation over a partition of the short designated primes.** -/
theorem jointOmegaPoly_eq_blocks {P Q : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) (S : Finset ℕ) (w : ℝ)
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (B : ι → Finset ℕ)
    (hdisj : (I : Set ι).PairwiseDisjoint B) (hcover : I.biUnion B = P) :
    jointOmegaPoly P Q S w
      = ∑ i ∈ I, ∑ p ∈ B i, moebiusPhase w p
          * omegaWeightedMoebiusPoly Q {m ∈ ramareCofactorSet S p | ¬ p ∣ m} w := by
  classical
  rw [jointOmegaPoly_eq_bilinear hP hQ hPQ S w, ← hcover]
  exact Finset.sum_biUnion hdisj

end

end RHTower.Sieve
