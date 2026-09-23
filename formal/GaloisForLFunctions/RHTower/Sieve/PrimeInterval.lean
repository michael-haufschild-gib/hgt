import GaloisForLFunctions.RHTower.Sieve.HardyRamanujanStep

/-!
# Primes and prime powers in an interval

The base level of the Hardy–Ramanujan recursion is `ω n = 1`, that is the prime powers of the
interval.  Two elementary observations reduce it to the Selberg sieve:

* a prime exceeding `z` is coprime to the primorial `z#`, and the primes at most `z` number at most
  `z`, so the explicit Brun–Titchmarsh bound counts the primes of the interval;
* a prime power `p^e ≤ b` with `e ≥ 2` has `p ≤ √b` and `e ≤ log₂ b`, so there are at most
  `√b · log₂ b` of them in total.

The result is a completely explicit bound on `#{n ∈ (a,b] : ω n = 1}` whose main term is
`2(b-a)/log Y` with `Y` free up to `z`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- **Primes in an interval.**  Brun–Titchmarsh with all constants named. -/
theorem card_prime_Ioc_le (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    ((#{n ∈ Finset.Ioc a b | n.Prime} : ℕ) : ℝ)
      ≤ 2 * ((b : ℝ) - a) / Real.log Y + selbergFibreError z Y + (z : ℝ) := by
  classical
  have hsub : {n ∈ Finset.Ioc a b | n.Prime}
      ⊆ {n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} ∪ Finset.Icc 1 z := by
    intro n hn
    obtain ⟨hmem, hprime⟩ := Finset.mem_filter.1 hn
    rw [Finset.mem_union]
    rcases Nat.lt_or_ge z n with hnz | hnz
    · refine Or.inl (Finset.mem_filter.2 ⟨hmem, ?_⟩)
      have hnotdvd : ¬ n ∣ primorial z := by
        intro hdvd
        have hmemf : n ∈ (primorial z).primeFactors :=
          Nat.mem_primeFactors.2 ⟨hprime, hdvd, (primorial_pos z).ne'⟩
        rw [primeFactors_primorial_eq] at hmemf
        have := (Nat.mem_primesLE.1 hmemf).1
        omega
      exact ((hprime.coprime_iff_not_dvd).2 hnotdvd).symm
    · exact Or.inr (Finset.mem_Icc.2 ⟨hprime.pos, hnz⟩)
  have hcard : (#{n ∈ Finset.Ioc a b | n.Prime})
      ≤ (#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n}) + z := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_union_le _ _) ?_
    have : (Finset.Icc 1 z).card = z := by rw [Nat.card_Icc]; omega
    omega
  have hstart : ((#{n ∈ Finset.Ioc a b | n.Prime} : ℕ) : ℝ)
      ≤ ((#{n ∈ Finset.Ioc a b | Nat.Coprime (primorial z) n} : ℕ) : ℝ) + (z : ℝ) := by
    exact_mod_cast hcard
  have hbase := card_coprime_Ioc_le_explicit a b z Y hab hY hYz hz hlog
  unfold selbergFibreError
  linarith

/-- Prime powers of exponent at least two are square-root sparse. -/
theorem card_omegaLevel_one_notPrime_le (a b : ℕ) :
    (#{n ∈ Finset.Ioc a b | n.primeFactors.card = 1 ∧ ¬ n.Prime})
      ≤ Nat.sqrt b * Nat.log 2 b := by
  classical
  set S : Finset ℕ := {n ∈ Finset.Ioc a b | n.primeFactors.card = 1 ∧ ¬ n.Prime} with hS
  set T : Finset (ℕ × ℕ) := Finset.Icc 2 (Nat.sqrt b) ×ˢ Finset.Icc 2 (Nat.log 2 b) with hT
  have key : ∀ n ∈ S, n.minFac ^ n.factorization n.minFac = n ∧ 2 ≤ n.minFac
      ∧ 2 ≤ n.factorization n.minFac ∧ n.minFac ≤ Nat.sqrt b
      ∧ n.factorization n.minFac ≤ Nat.log 2 b := by
    intro n hn
    obtain ⟨hmem, hcard, hnp⟩ := Finset.mem_filter.1 hn
    obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hmem
    have hn0 : n ≠ 0 := by omega
    have hn1 : n ≠ 1 := by
      intro h
      rw [h] at hcard
      simp at hcard
    have hprime : (n.minFac).Prime := Nat.minFac_prime hn1
    have hmemf : n.minFac ∈ n.primeFactors :=
      Nat.mem_primeFactors.2 ⟨hprime, Nat.minFac_dvd n, hn0⟩
    have hsingle : n.primeFactors = {n.minFac} := by
      obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hcard
      rw [hp] at hmemf ⊢
      rw [Finset.mem_singleton.1 hmemf]
    have hrecon : n.minFac ^ n.factorization n.minFac = n := by
      have h := Nat.prod_factorization_pow_eq_self hn0
      rw [Finsupp.prod, Nat.support_factorization, hsingle, Finset.prod_singleton] at h
      exact h
    have he1 : 0 < n.factorization n.minFac :=
      Nat.Prime.factorization_pos_of_dvd hprime hn0 (Nat.minFac_dvd n)
    have he2 : 2 ≤ n.factorization n.minFac := by
      rcases Nat.lt_or_ge (n.factorization n.minFac) 2 with h | h
      · exfalso
        have : n.factorization n.minFac = 1 := by omega
        rw [this, pow_one] at hrecon
        exact hnp (hrecon ▸ hprime)
      · exact h
    have hsq : n.minFac ≤ Nat.sqrt b := by
      refine Nat.le_sqrt.2 ?_
      have hpow : n.minFac * n.minFac ≤ n.minFac ^ n.factorization n.minFac := by
        calc n.minFac * n.minFac = n.minFac ^ (2 : ℕ) := by ring
          _ ≤ n.minFac ^ n.factorization n.minFac := Nat.pow_le_pow_right hprime.pos he2
      omega
    have hlg : n.factorization n.minFac ≤ Nat.log 2 b := by
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      have : (2 : ℕ) ^ n.factorization n.minFac ≤ n.minFac ^ n.factorization n.minFac :=
        Nat.pow_le_pow_left hprime.two_le _
      omega
    exact ⟨hrecon, hprime.two_le, he2, hsq, hlg⟩
  have hmaps : ∀ n ∈ S, (n.minFac, n.factorization n.minFac) ∈ T := by
    intro n hn
    obtain ⟨-, h2, h3, h4, h5⟩ := key n hn
    exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨h2, h4⟩, Finset.mem_Icc.2 ⟨h3, h5⟩⟩
  have hinj : ∀ x ∈ S, ∀ y ∈ S,
      (x.minFac, x.factorization x.minFac) = (y.minFac, y.factorization y.minFac) → x = y := by
    intro x hx y hy hxy
    obtain ⟨hrx, -, -, -, -⟩ := key x hx
    obtain ⟨hry, -, -, -, -⟩ := key y hy
    have h1 : x.minFac = y.minFac := congrArg Prod.fst hxy
    have h2 : x.factorization x.minFac = y.factorization y.minFac := congrArg Prod.snd hxy
    rw [← hrx, ← hry, h2, h1]
  refine le_trans (Finset.card_le_card_of_injOn _ hmaps hinj) ?_
  rw [hT, Finset.card_product, Nat.card_Icc, Nat.card_Icc]
  exact Nat.mul_le_mul (by omega) (by omega)

/-- **Level one of the recursion.**  The integers of `Ioc a b` with a single distinct prime factor,
counted by the Selberg sieve plus a square-root error. -/
theorem card_omegaLevel_one_le (a b z Y : ℕ) (hab : a ≤ b) (hY : 1 ≤ Y) (hYz : Y ≤ z) (hz : 2 ≤ z)
    (hlog : 0 < Real.log Y) :
    ((omegaLevel a b 1).card : ℝ)
      ≤ 2 * ((b : ℝ) - a) / Real.log Y + selbergFibreError z Y + (z : ℝ)
        + ((Nat.sqrt b * Nat.log 2 b : ℕ) : ℝ) := by
  classical
  have hsplit : (omegaLevel a b 1).card
      ≤ (#{n ∈ Finset.Ioc a b | n.Prime})
        + (#{n ∈ Finset.Ioc a b | n.primeFactors.card = 1 ∧ ¬ n.Prime}) := by
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro n hn
    obtain ⟨hmem, hcard⟩ := Finset.mem_filter.1 hn
    rw [Finset.mem_union]
    by_cases hp : n.Prime
    · exact Or.inl (Finset.mem_filter.2 ⟨hmem, hp⟩)
    · exact Or.inr (Finset.mem_filter.2 ⟨hmem, hcard, hp⟩)
  have hstart : ((omegaLevel a b 1).card : ℝ)
      ≤ ((#{n ∈ Finset.Ioc a b | n.Prime} : ℕ) : ℝ)
        + ((#{n ∈ Finset.Ioc a b | n.primeFactors.card = 1 ∧ ¬ n.Prime} : ℕ) : ℝ) := by
    exact_mod_cast hsplit
  have h1 := card_prime_Ioc_le a b z Y hab hY hYz hz hlog
  have h2 : ((#{n ∈ Finset.Ioc a b | n.primeFactors.card = 1 ∧ ¬ n.Prime} : ℕ) : ℝ)
      ≤ ((Nat.sqrt b * Nat.log 2 b : ℕ) : ℝ) := by
    exact_mod_cast card_omegaLevel_one_notPrime_le a b
  linarith

end RHTower.Sieve
