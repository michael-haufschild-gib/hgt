import GaloisForLFunctions.RHTower.Sieve.RoughCount

/-!
# The smooth–rough splitting of an integer

Every nonzero `n` factors uniquely as `n = smoothPart z n * roughPart z n`, where the first factor
collects the prime powers with `p ≤ z` and the second those with `p > z`.  The rough factor is what
the sieve sees, and the two factors have disjoint prime supports, so

`ω n = ω (smoothPart z n) + ω (roughPart z n)`.

The rough factor also obeys the size constraint that drives Shiu-type bounds: since each of its
`ω (roughPart z n)` distinct prime factors exceeds `z`, one has `z ^ ω (roughPart z n) ≤ n`.  With
`z = X^{1/L}` this caps the rough prime count by `L`, so any fixed multiplicative weight of the
rough part is bounded by a constant depending only on `L`.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The `z`-smooth part of `n`. -/
def smoothPart (z n : ℕ) : ℕ := ∏ p ∈ {p ∈ n.primeFactors | p ≤ z}, p ^ n.factorization p

/-- The `z`-rough part of `n`. -/
def roughPart (z n : ℕ) : ℕ := ∏ p ∈ {p ∈ n.primeFactors | ¬ p ≤ z}, p ^ n.factorization p

theorem smoothPart_mul_roughPart {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    smoothPart z n * roughPart z n = n := by
  classical
  have h := Nat.prod_factorization_pow_eq_self hn
  rw [Finsupp.prod, Nat.support_factorization] at h
  rw [smoothPart, roughPart, Finset.prod_filter_mul_prod_filter_not]
  exact h

theorem roughPart_dvd (z n : ℕ) : roughPart z n ∣ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Dvd.intro_left _ (smoothPart_mul_roughPart hn.ne' z)

theorem smoothPart_dvd (z n : ℕ) : smoothPart z n ∣ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Dvd.intro _ (smoothPart_mul_roughPart hn.ne' z)

theorem roughPart_pos (z n : ℕ) : 0 < roughPart z n := by
  refine Finset.prod_pos ?_
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos _

theorem smoothPart_pos (z n : ℕ) : 0 < smoothPart z n := by
  refine Finset.prod_pos ?_
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).pos _

/-- The rough part has exactly the prime factors of `n` exceeding `z`. -/
theorem primeFactors_roughPart {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    (roughPart z n).primeFactors = {p ∈ n.primeFactors | ¬ p ≤ z} := by
  classical
  ext q
  constructor
  · intro hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ roughPart z n := Nat.dvd_of_mem_primeFactors hq
    have hmem : ∃ p ∈ {p ∈ n.primeFactors | ¬ p ≤ z}, q ∣ p ^ n.factorization p := by
      simpa using (Nat.Prime.prime hqprime).dvd_finsetProd_iff _ |>.1 hqdvd
    obtain ⟨p, hp, hqp⟩ := hmem
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
    have : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).1
      (hqprime.dvd_of_dvd_pow hqp)
    rwa [this]
  · intro hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1
    have hfac : q ^ n.factorization q ∣ roughPart z n :=
      Finset.dvd_prod_of_mem (fun p => p ^ n.factorization p) hq
    have hpos : 0 < n.factorization q :=
      (Nat.Prime.factorization_pos_of_dvd hqprime hn
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hq).1))
    have hqdvd : q ∣ roughPart z n :=
      dvd_trans (dvd_pow_self q hpos.ne') hfac
    exact Nat.mem_primeFactors.2 ⟨hqprime, hqdvd, (roughPart_pos z n).ne'⟩

/-- No prime up to `z` divides the rough part. -/
theorem not_dvd_roughPart {n : ℕ} (hn : n ≠ 0) {z p : ℕ} (hp : p ∈ Nat.primesLE z) :
    ¬ p ∣ roughPart z n := by
  intro hdvd
  have hprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hmem : p ∈ (roughPart z n).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hprime, hdvd, (roughPart_pos z n).ne'⟩
  rw [primeFactors_roughPart hn z] at hmem
  exact (Finset.mem_filter.1 hmem).2 (Nat.mem_primesLE.1 hp).1

/-- The smooth part has exactly the prime factors of `n` up to `z`. -/
theorem primeFactors_smoothPart {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    (smoothPart z n).primeFactors = {p ∈ n.primeFactors | p ≤ z} := by
  classical
  ext q
  constructor
  · intro hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ smoothPart z n := Nat.dvd_of_mem_primeFactors hq
    have hmem : ∃ p ∈ {p ∈ n.primeFactors | p ≤ z}, q ∣ p ^ n.factorization p := by
      simpa using (Nat.Prime.prime hqprime).dvd_finsetProd_iff _ |>.1 hqdvd
    obtain ⟨p, hp, hqp⟩ := hmem
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1
    have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).1
      (hqprime.dvd_of_dvd_pow hqp)
    rwa [hqp']
  · intro hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hq).1
    have hfac : q ^ n.factorization q ∣ smoothPart z n :=
      Finset.dvd_prod_of_mem (fun p => p ^ n.factorization p) hq
    have hpos : 0 < n.factorization q :=
      (Nat.Prime.factorization_pos_of_dvd hqprime hn
        (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.1 hq).1))
    exact Nat.mem_primeFactors.2
      ⟨hqprime, dvd_trans (dvd_pow_self q hpos.ne') hfac, (smoothPart_pos z n).ne'⟩

/-- The distinct prime count splits along the smooth–rough factorization. -/
theorem card_primeFactors_roughPart_add {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    (smoothPart z n).primeFactors.card + (roughPart z n).primeFactors.card
      = n.primeFactors.card := by
  classical
  rw [primeFactors_smoothPart hn z, primeFactors_roughPart hn z]
  exact Finset.card_filter_add_card_filter_not (p := fun p => p ≤ z)

/-- **Size constraint on the rough prime count.**  Each of the `ω (roughPart z n)` distinct prime
factors of the rough part exceeds `z`, so their product — a divisor of `n` — is at least
`z ^ ω (roughPart z n)`. -/
theorem pow_card_primeFactors_roughPart_le {n : ℕ} (hn : n ≠ 0) (z : ℕ) :
    z ^ (roughPart z n).primeFactors.card ≤ n := by
  classical
  set s := (roughPart z n).primeFactors with hs
  have hsub : s ⊆ n.primeFactors := by
    rw [hs, primeFactors_roughPart hn z]
    exact Finset.filter_subset _ _
  have hprod_dvd : (∏ p ∈ s, p) ∣ n := by
    refine dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub) ?_
    exact Nat.prod_primeFactors_dvd n
  have hle : z ^ s.card ≤ ∏ p ∈ s, p := by
    have hterm : ∀ p ∈ s, z ≤ p := by
      intro p hp
      have hp' : p ∈ {p ∈ n.primeFactors | ¬ p ≤ z} := by
        rwa [hs, primeFactors_roughPart hn z] at hp
      exact le_of_lt (not_le.1 (Finset.mem_filter.1 hp').2)
    calc z ^ s.card = ∏ _p ∈ s, z := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ s, p := Finset.prod_le_prod' hterm
  exact le_trans hle (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hprod_dvd)

end RHTower.Sieve
