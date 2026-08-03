import GaloisForLFunctions.RHTower.Sieve.SmoothTilt

/-!
# Counting smooth integers with few prime factors

A `z`-smooth integer `s ≤ Y` with at most `k` distinct prime factors is determined by the set of
its maximal prime powers, a subset of size at most `k` of the prime powers `p ^ e ≤ Y` with
`p ≤ z`.  Since `2 ^ e ≤ p ^ e ≤ Y` forces `e ≤ log₂ Y`, there are at most
`π(z) · log₂ Y` such prime powers, whence

`#{s ≤ Y : s is z-smooth, ω s ≤ k} ≤ ∑_{j ≤ k} C(π(z) · log₂ Y, j)`.

This is the bound that lets the per-divisor sieve errors be summed: with `log z` of order
`log X / log log X` and `k` of order `log log X`, the right-hand side is `X^{o(1)}`, far below the
length of the interval being sieved.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The prime powers `p ^ e` with `p ≤ z` prime and `1 ≤ e ≤ log₂ Y`. -/
def primePowerSet (z Y : ℕ) : Finset ℕ :=
  (Nat.primesLE z ×ˢ Finset.Icc 1 (Nat.log 2 Y)).image fun x => x.1 ^ x.2

theorem card_primePowerSet_le (z Y : ℕ) :
    (primePowerSet z Y).card ≤ (Nat.primesLE z).card * Nat.log 2 Y := by
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]

/-- The maximal prime powers of a smooth number lie in the prime power set. -/
theorem maxPrimePow_mem_primePowerSet {z Y s : ℕ}
    (hs : s ∈ smoothUpTo (Nat.primesLE z) Y) {p : ℕ} (hp : p ∈ s.primeFactors) :
    p ^ s.factorization p ∈ primePowerSet z Y := by
  obtain ⟨⟨hs1, hsY⟩, hsub⟩ := mem_smoothUpTo.1 hs
  have hs0 : s ≠ 0 := by omega
  have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hvpos : 0 < s.factorization p :=
    Nat.Prime.factorization_pos_of_dvd hprime hs0 (Nat.dvd_of_mem_primeFactors hp)
  have hdvd : p ^ s.factorization p ∣ s := Nat.ordProj_dvd s p
  have hle : p ^ s.factorization p ≤ s := Nat.le_of_dvd (by omega) hdvd
  have htwo : (2 : ℕ) ^ s.factorization p ≤ p ^ s.factorization p :=
    Nat.pow_le_pow_left hprime.two_le _
  have hpow : (2 : ℕ) ^ s.factorization p ≤ Y := le_trans htwo (le_trans hle hsY)
  have hlog : s.factorization p ≤ Nat.log 2 Y := Nat.le_log_of_pow_le (by norm_num) hpow
  refine Finset.mem_image.2 ⟨(p, s.factorization p), ?_, rfl⟩
  exact Finset.mem_product.2 ⟨hsub hp, Finset.mem_Icc.2 ⟨hvpos, hlog⟩⟩

/-- **Counting bound.**  Smooth integers with few prime factors inject into small subsets of the
prime power set. -/
theorem card_smoothUpTo_card_primeFactors_le (z Y k : ℕ) :
    (#{s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k})
      ≤ ∑ j ∈ Finset.range (k + 1), ((Nat.primesLE z).card * Nat.log 2 Y).choose j := by
  classical
  set Φ : ℕ → Finset ℕ := fun s => s.primeFactors.image fun p => p ^ s.factorization p with hΦ
  have hmap : ∀ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k},
      Φ s ∈ {T ∈ (primePowerSet z Y).powerset | T.card ≤ k} := by
    intro s hs
    obtain ⟨hsmem, hcard⟩ := Finset.mem_filter.1 hs
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 ?_, ?_⟩
    · intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
      exact maxPrimePow_mem_primePowerSet hsmem hp
    · exact le_trans (Finset.card_image_le) hcard
  have hprodrec : ∀ s ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k},
      ∏ q ∈ Φ s, q = s := by
    intro s hs
    obtain ⟨hsmem, -⟩ := Finset.mem_filter.1 hs
    obtain ⟨⟨hs1, -⟩, -⟩ := mem_smoothUpTo.1 hsmem
    have hs0 : s ≠ 0 := by omega
    have hinj : ∀ p ∈ s.primeFactors, ∀ q ∈ s.primeFactors,
        p ^ s.factorization p = q ^ s.factorization q → p = q := by
      intro p hp q hq hpq
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hvp : 0 < s.factorization p :=
        Nat.Prime.factorization_pos_of_dvd hpprime hs0 (Nat.dvd_of_mem_primeFactors hp)
      have hdvd : p ∣ q ^ s.factorization q := by
        rw [← hpq]
        exact dvd_pow_self p hvp.ne'
      exact (Nat.prime_dvd_prime_iff_eq hpprime hqprime).1 (hpprime.dvd_of_dvd_pow hdvd)
    rw [hΦ, Finset.prod_image hinj]
    have h := Nat.prod_factorization_pow_eq_self hs0
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact h
  have hinjOn : ∀ x ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k},
      ∀ y ∈ {s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k}, Φ x = Φ y → x = y := by
    intro x hx y hy hxy
    have h1 := hprodrec x hx
    have h2 := hprodrec y hy
    rw [hxy] at h1
    exact h1.symm.trans h2
  have hcardle : (#{s ∈ smoothUpTo (Nat.primesLE z) Y | s.primeFactors.card ≤ k})
      ≤ (#{T ∈ (primePowerSet z Y).powerset | T.card ≤ k}) :=
    Finset.card_le_card_of_injOn Φ hmap hinjOn
  have hcount : (#{T ∈ (primePowerSet z Y).powerset | T.card ≤ k})
      = ∑ j ∈ Finset.range (k + 1), ((primePowerSet z Y).card).choose j := by
    have h1 : (#{T ∈ (primePowerSet z Y).powerset | T.card ≤ k})
        = ∑ _T ∈ {T ∈ (primePowerSet z Y).powerset | T.card ≤ k}, 1 := by
      rw [Finset.sum_const, smul_eq_mul, mul_one]
    have h2 := sum_powerset_filter_card_le (primePowerSet z Y) k (fun _ => (1 : ℕ))
    rw [h1]
    simpa using h2
  rw [hcount] at hcardle
  refine le_trans hcardle ?_
  refine Finset.sum_le_sum ?_
  intro j _
  exact Nat.choose_le_choose j (card_primePowerSet_le z Y)

end RHTower.Sieve
