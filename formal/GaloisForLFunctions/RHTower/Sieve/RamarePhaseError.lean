import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear

/-!
# The error of the Ramaré phase factorisation

The bilinear form loses two things: the cofactors still divisible by the designated prime, and the
integers carrying no designated prime factor at all.  The first is a square-multiple count and is
therefore genuinely negligible,

```text
#{ m ∈ cofactors(s, p) : p ∣ m }  ≤  #{ n ∈ s : p² ∣ n } ,
```

which for `s = [1, M]` is exactly `⌊M/p²⌋`.  Summed over a set of designated primes it is at most
`M·∑_{p ∈ P} p^{-2}`, so over a dyadic range `P ⊂ [Q, 2Q]` the total is `O(M/(Q log Q))`: the
factorisation is exact up to a saving of a full power of the prime scale.

The second error — the rough integers — is a sieve quantity, and is the reason a single prime range
never suffices.
-/

noncomputable section

namespace RHTower.Sieve

open Finset
open scoped ArithmeticFunction.Moebius

/-- A cofactor divisible by the designated prime comes from a multiple of its square. -/
theorem card_ramareCofactorSet_filter_dvd_le (s : Finset ℕ) {p : ℕ} (hp : 0 < p) :
    ({m ∈ ramareCofactorSet s p | p ∣ m}).card ≤ ({n ∈ s | p * p ∣ n}).card := by
  classical
  refine Finset.card_le_card_of_surjOn (fun n => n / p) ?_
  intro m hm
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hm
  obtain ⟨hmem, hpm⟩ := hm
  rw [ramareCofactorSet, Finset.mem_image] at hmem
  obtain ⟨n, hn, rfl⟩ := hmem
  rw [Finset.mem_filter] at hn
  obtain ⟨hns, hpn⟩ := hn
  obtain ⟨k, hk⟩ := hpn
  subst hk
  have hdiv : p * k / p = k := Nat.mul_div_cancel_left k hp
  rw [hdiv] at hpm
  obtain ⟨j, hj⟩ := hpm
  refine ⟨p * k, ?_, rfl⟩
  simp only [Finset.coe_filter, Set.mem_setOf_eq]
  exact ⟨hns, ⟨j, by rw [hj]; ring⟩⟩

/-- The multiples of `d` in `[1, M]` are counted exactly. -/
theorem card_Icc_filter_dvd (M d : ℕ) :
    ({n ∈ Finset.Icc 1 M | d ∣ n}).card = M / d := by
  classical
  have hset : Finset.Icc 1 M = Finset.Ioc 0 M := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hset]
  exact Nat.Ioc_filter_dvd_card_eq_div M d

/-- **The cofactor error of the Ramaré phase factorisation on `[1, M]`.** -/
theorem card_ramareCofactorSet_Icc_le (M : ℕ) {p : ℕ} (hp : 0 < p) :
    (({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m}).card : ℝ)
      ≤ (M : ℝ) / ((p : ℝ) * (p : ℝ)) := by
  have hle := card_ramareCofactorSet_filter_dvd_le (Finset.Icc 1 M) hp
  rw [card_Icc_filter_dvd M (p * p)] at hle
  have hcast : ((M / (p * p) : ℕ) : ℝ) ≤ (M : ℝ) / ((p * p : ℕ) : ℝ) := Nat.cast_div_le
  have hle' : (({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m}).card : ℝ)
      ≤ ((M / (p * p) : ℕ) : ℝ) := by exact_mod_cast hle
  have hpp : ((p * p : ℕ) : ℝ) = (p : ℝ) * (p : ℝ) := by push_cast; ring
  rw [hpp] at hcast
  linarith

/-- **The total cofactor error over a set of designated primes.** -/
theorem sum_ramare_phase_error_le (M : ℕ) {P : Finset ℕ} (hP : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, (({m ∈ ramareCofactorSet (Finset.Icc 1 M) p | p ∣ m}).card : ℝ)
      ≤ ∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)) :=
  Finset.sum_le_sum fun p hp => card_ramareCofactorSet_Icc_le M (hP p hp)

/-- **The Möbius Dirichlet polynomial on `[1, M]` is a bilinear form up to `M·∑ p^{-2}` and the
rough count.**  The square-multiple error is negligible for a prime range going to infinity; only
the rough integers — those with no designated prime factor — remain. -/
theorem norm_logPoly_moebius_Icc_sub_ramare_bilinear_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (M : ℕ) (w : ℝ) :
    ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w
        - ∑ p ∈ P, moebiusPhase w p
            * logPoly (ramareCofactorCoeff P)
                {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} w‖
      ≤ (∑ p ∈ P, (M : ℝ) / ((p : ℝ) * (p : ℝ)))
        + (({n ∈ Finset.Icc 1 M | primeFactorsIn P n = ∅}).card : ℝ) := by
  refine le_trans (norm_logPoly_moebius_sub_ramare_bilinear_le hPprime (Finset.Icc 1 M) w) ?_
  refine add_le_add ?_ le_rfl
  exact sum_ramare_phase_error_le M fun p hp => (hPprime p hp).pos

end RHTower.Sieve

end
