import GaloisForLFunctions.RHTower.Sieve.RamareWeight

/-!
# The Turán–Kubilius inequality on an interval

Writing `ω_z(n)` for the number of primes `p ≤ z` dividing `n`, the centred quantity is a sum of
independent-looking indicators:

`ω_z(n) - ∑_{p ≤ z} 1/p = ∑_{p ≤ z} (1_{p ∣ n} - 1/p)`.

Squaring and exchanging the sums turns the variance into a sum over *pairs* of primes.  Every
off-diagonal pair contributes only a bounded amount — the main terms cancel identically, because
`1_{p ∣ n} 1_{q ∣ n} = 1_{pq ∣ n}` for distinct primes and the archimedean prediction for `pq` is the
product of the two predictions — while the diagonal contributes `(b-a)(1/p - 1/p²)`.  Hence

`∑_{n ∈ (a,b]} (ω_z(n) - ∑_{p ≤ z} 1/p)² ≤ (b-a) ∑_{p ≤ z} 1/p + π(z) + 2π(z)²`,

uniformly in the interval.  Only the interval multiple count enters; no distribution theorem, and no
elementary symmetric function bookkeeping.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The indicator of divisibility, as a real number. -/
noncomputable def indDvd (p n : ℕ) : ℝ := if p ∣ n then 1 else 0

/-- The centred indicator attached to a prime. -/
noncomputable def centredInd (p n : ℕ) : ℝ := indDvd p n - 1 / (p : ℝ)

/-- The number of primes at most `z` dividing `n`. -/
def omegaCount (z n : ℕ) : ℕ := #{p ∈ Nat.primesLE z | p ∣ n}

theorem sum_indDvd_eq (z n : ℕ) :
    ∑ p ∈ Nat.primesLE z, indDvd p n = (omegaCount z n : ℝ) := by
  classical
  simp only [indDvd, omegaCount]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The centred prime count is the sum of the centred indicators. -/
theorem sum_centredInd_eq (z n : ℕ) :
    ∑ p ∈ Nat.primesLE z, centredInd p n = (omegaCount z n : ℝ) - mertensS z := by
  classical
  unfold centredInd
  rw [Finset.sum_sub_distrib, sum_indDvd_eq]
  rfl

/-- The interval sum of a divisibility indicator is the multiple count. -/
theorem sum_indDvd_Ioc (p a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, indDvd p n = ((#{n ∈ Finset.Ioc a b | p ∣ n} : ℕ) : ℝ) := by
  classical
  simp only [indDvd]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- The interval sum of a product of two divisibility indicators is the count of common
multiples. -/
theorem sum_indDvd_mul_Ioc (p q a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, indDvd p n * indDvd q n
      = ((#{n ∈ Finset.Ioc a b | p ∣ n ∧ q ∣ n} : ℕ) : ℝ) := by
  classical
  have hterm : ∀ n ∈ Finset.Ioc a b,
      indDvd p n * indDvd q n = (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
    intro n _
    unfold indDvd
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Off-diagonal pairs cancel.**  For distinct primes the main terms cancel identically, leaving a
bounded remainder. -/
theorem abs_sum_centredInd_mul_le {z p q a b : ℕ} (hab : a ≤ b)
    (hp : p ∈ Nat.primesLE z) (hq : q ∈ Nat.primesLE z) (hpq : p ≠ q) :
    |∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n| ≤ 2 := by
  classical
  have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hqprime : q.Prime := Nat.prime_of_mem_primesLE hq
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqprime.two_le
  have hppos : 0 < p := hpprime.pos
  have hqpos : 0 < q := hqprime.pos
  have hpqpos : 0 < p * q := Nat.mul_pos hppos hqpos
  have hsets : {n ∈ Finset.Ioc a b | p ∣ n ∧ q ∣ n} = {n ∈ Finset.Ioc a b | p * q ∣ n} := by
    refine Finset.filter_congr ?_
    intro n _
    constructor
    · rintro ⟨h1, h2⟩
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hpprime hqprime).2 hpq) h1 h2
    · intro h
      exact ⟨dvd_trans (Dvd.intro q rfl) h, dvd_trans (Dvd.intro_left p rfl) h⟩
  have hexpand : ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n
      = (∑ n ∈ Finset.Ioc a b, indDvd p n * indDvd q n)
        - (1 / (q : ℝ)) * (∑ n ∈ Finset.Ioc a b, indDvd p n)
        - (1 / (p : ℝ)) * (∑ n ∈ Finset.Ioc a b, indDvd q n)
        + ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
    have hcard : ∑ _n ∈ Finset.Ioc a b, ((1 : ℝ) / (p : ℝ)) * (1 / (q : ℝ))
        = ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      have hc : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
        push_cast [Nat.cast_sub hab]
        ring
      rw [hc]
      ring
    have hkey : ∀ n ∈ Finset.Ioc a b,
        centredInd p n * centredInd q n
          = indDvd p n * indDvd q n - (1 / (q : ℝ)) * indDvd p n - (1 / (p : ℝ)) * indDvd q n
            + ((1 : ℝ) / (p : ℝ)) * (1 / (q : ℝ)) := by
      intro n _
      unfold centredInd
      ring
    rw [Finset.sum_congr rfl hkey, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcard]
  rw [hexpand, sum_indDvd_mul_Ioc, hsets, sum_indDvd_Ioc, sum_indDvd_Ioc]
  have h0 := abs_card_filter_dvd_Ioc_sub_lt (p * q) a b hpqpos hab
  have h1 := abs_card_filter_dvd_Ioc_sub_lt p a b hppos hab
  have h2 := abs_card_filter_dvd_Ioc_sub_lt q a b hqpos hab
  have hcast : (((p * q : ℕ)) : ℝ) = (p : ℝ) * (q : ℝ) := by push_cast; ring
  rw [hcast] at h0
  rw [abs_lt] at h0 h1 h2
  rw [abs_le]
  have hpinv : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have hqinv : (0 : ℝ) < 1 / (q : ℝ) := by positivity
  have hple : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hqle : 1 / (q : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hprod : ((b : ℝ) - a) / ((p : ℝ) * (q : ℝ))
      = ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by
    field_simp
  have hp' : ((b : ℝ) - a) / (p : ℝ) * (1 / (q : ℝ))
      = ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by ring
  have hq' : ((b : ℝ) - a) / (q : ℝ) * (1 / (p : ℝ))
      = ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (q : ℝ)) := by ring
  constructor
  · nlinarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, hpinv, hqinv, hple, hqle]
  · nlinarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, hpinv, hqinv, hple, hqle]

/-- **Diagonal pairs.**  A single prime contributes at most `(b-a)/p + 1`. -/
theorem sum_centredInd_sq_le {z p a b : ℕ} (hab : a ≤ b) (hp : p ∈ Nat.primesLE z) :
    ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd p n ≤ ((b : ℝ) - a) / (p : ℝ) + 1 := by
  classical
  have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
  have hppos : 0 < p := hpprime.pos
  have hsets : {n ∈ Finset.Ioc a b | p ∣ n ∧ p ∣ n} = {n ∈ Finset.Ioc a b | p ∣ n} := by
    refine Finset.filter_congr ?_
    intro n _
    tauto
  have hexpand : ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd p n
      = (∑ n ∈ Finset.Ioc a b, indDvd p n * indDvd p n)
        - 2 * (1 / (p : ℝ)) * (∑ n ∈ Finset.Ioc a b, indDvd p n)
        + ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
    have hcard : ∑ _n ∈ Finset.Ioc a b, ((1 : ℝ) / (p : ℝ)) * (1 / (p : ℝ))
        = ((b : ℝ) - a) * (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Ioc]
      have hc : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
        push_cast [Nat.cast_sub hab]
        ring
      rw [hc]
      ring
    have hkey : ∀ n ∈ Finset.Ioc a b,
        centredInd p n * centredInd p n
          = indDvd p n * indDvd p n - (2 * (1 / (p : ℝ))) * indDvd p n
            + ((1 : ℝ) / (p : ℝ)) * (1 / (p : ℝ)) := by
      intro n _
      unfold centredInd
      ring
    rw [Finset.sum_congr rfl hkey, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hcard]
  rw [hexpand, sum_indDvd_mul_Ioc, hsets, sum_indDvd_Ioc]
  have h1 := abs_card_filter_dvd_Ioc_sub_lt p a b hppos hab
  rw [abs_lt] at h1
  have hpinv : (0 : ℝ) < 1 / (p : ℝ) := by positivity
  have hple : 1 / (p : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hlen : (0 : ℝ) ≤ (b : ℝ) - a := by
    have : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith
  have hdiv : ((b : ℝ) - a) / (p : ℝ) = ((b : ℝ) - a) * (1 / (p : ℝ)) := by ring
  rw [hdiv] at h1 ⊢
  nlinarith [h1.1, h1.2, hpinv, hple, hlen]

/-- **Turán–Kubilius on an interval.**  The variance of the small-prime count is at most the
interval length times the prime reciprocal sum, plus a prime-counting error. -/
theorem sum_omegaCount_variance_le (z a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc a b, ((omegaCount z n : ℝ) - mertensS z) ^ 2
      ≤ ((b : ℝ) - a) * mertensS z + ((Nat.primesLE z).card : ℝ)
        + 2 * ((Nat.primesLE z).card : ℝ) ^ 2 := by
  classical
  set P : Finset ℕ := Nat.primesLE z with hP
  have hsq : ∀ n ∈ Finset.Ioc a b,
      ((omegaCount z n : ℝ) - mertensS z) ^ 2
        = ∑ p ∈ P, ∑ q ∈ P, centredInd p n * centredInd q n := by
    intro n _
    rw [← sum_centredInd_eq z n, sq, hP]
    exact Finset.sum_mul_sum (Nat.primesLE z) (Nat.primesLE z)
      (fun p => centredInd p n) (fun q => centredInd q n)
  rw [Finset.sum_congr rfl hsq, Finset.sum_comm]
  have hswap : ∀ p ∈ P, ∑ n ∈ Finset.Ioc a b, ∑ q ∈ P, centredInd p n * centredInd q n
      = ∑ q ∈ P, ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n :=
    fun p _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hswap]
  have hinner : ∀ p ∈ P,
      ∑ q ∈ P, ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n
        ≤ ((b : ℝ) - a) / (p : ℝ) + 1 + 2 * ((P.card : ℝ)) := by
    intro p hp
    have hsplit : ∑ q ∈ P, ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n
        = (∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd p n)
          + ∑ q ∈ P.erase p, ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n :=
      (Finset.add_sum_erase P _ hp).symm
    rw [hsplit]
    have hdiag := sum_centredInd_sq_le (z := z) hab (hP ▸ hp)
    have hoff : ∑ q ∈ P.erase p, ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n
        ≤ 2 * ((P.card : ℝ)) := by
      have hstep : ∑ q ∈ P.erase p, ∑ n ∈ Finset.Ioc a b, centredInd p n * centredInd q n
          ≤ ∑ _q ∈ P.erase p, (2 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro q hq
        obtain ⟨hqp, hqP⟩ := Finset.mem_erase.1 hq
        exact (abs_le.1 (abs_sum_centredInd_mul_le hab (hP ▸ hp) (hP ▸ hqP)
          (fun hcon => hqp hcon.symm))).2
      refine le_trans hstep ?_
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : ((P.erase p).card : ℝ) ≤ (P.card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset p P)
      nlinarith [hcard, Nat.cast_nonneg (α := ℝ) P.card]
    linarith
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_const, nsmul_eq_mul]
  have hmert : ∑ p ∈ P, ((b : ℝ) - a) / (p : ℝ) = ((b : ℝ) - a) * mertensS z := by
    rw [mertensS, hP, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hmert]
  have hcard : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  nlinarith [hcard]

end RHTower.Sieve
