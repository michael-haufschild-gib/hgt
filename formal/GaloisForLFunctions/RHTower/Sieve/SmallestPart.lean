import GaloisForLFunctions.RHTower.Sieve.GeometricMeanDivisor
import Mathlib.Data.Finset.Sort

/-!
# Extracting a small divisor from many large prime factors

The `J` smallest elements of a finite set of naturals are obtained by truncating its sorted
enumeration.  Combined with the integral geometric-mean inequality this yields the extraction
device behind the large-prime half of a distinct-prime-count tail estimate:

if `n` has at least `c · J` prime factors exceeding `z`, then the product of the `J` smallest of
them is a squarefree divisor `d ∣ n` with `ω d = J`, all prime factors above `z`, and `d ^ c ≤ n`.

The last property is what matters: it confines `d` to a range of size `n ^ (1/c)`, so the
one-unit-per-divisor error of a divisor-counting argument stays far below the length of the
interval being counted.
-/

namespace RHTower.Sieve

open Finset Nat

/-- The `J` smallest elements of a finite set of naturals. -/
def smallestPart (S : Finset ℕ) (J : ℕ) : Finset ℕ :=
  ((S.sort (· ≤ ·)).take J).toFinset

theorem smallestPart_subset (S : Finset ℕ) (J : ℕ) : smallestPart S J ⊆ S := by
  intro p hp
  rw [smallestPart, List.mem_toFinset] at hp
  exact (Finset.mem_sort (· ≤ ·)).1 (List.mem_of_mem_take hp)

theorem card_smallestPart (S : Finset ℕ) (J : ℕ) :
    (smallestPart S J).card = min J S.card := by
  rw [smallestPart, List.toFinset_card_of_nodup (Finset.sort_nodup S (· ≤ ·)).take,
    List.length_take, Finset.length_sort]

theorem smallestPart_le (S : Finset ℕ) (J : ℕ) :
    ∀ p ∈ smallestPart S J, ∀ q ∈ S \ smallestPart S J, p ≤ q := by
  intro p hp q hq
  obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.1 hq
  rw [smallestPart, List.mem_toFinset] at hp hqT
  have hqsort : q ∈ S.sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).2 hqS
  have hqdrop : q ∈ (S.sort (· ≤ ·)).drop J := by
    have hsplit := List.take_append_drop J (S.sort (· ≤ ·))
    rw [← hsplit, List.mem_append] at hqsort
    tauto
  have hpw : List.Pairwise (· ≤ ·)
      ((S.sort (· ≤ ·)).take J ++ (S.sort (· ≤ ·)).drop J) := by
    rw [List.take_append_drop]
    exact Finset.pairwise_sort _ _
  exact (List.pairwise_append.1 hpw).2.2 p hp q hqdrop

/-- **Small-divisor extraction.**  Many prime factors above `z` force a small squarefree divisor
with exactly `J` of them. -/
theorem exists_small_divisor {z n J c : ℕ} (hn : n ≠ 0) (hJ : 1 ≤ J) (hc : 1 ≤ c)
    (hbig : c * J ≤ (n.primeFactors.filter (fun p => z < p)).card) :
    ∃ d : ℕ, d ∣ n ∧ Squarefree d ∧ d.primeFactors.card = J
      ∧ (∀ p ∈ d.primeFactors, z < p) ∧ d ^ c ≤ n := by
  classical
  set S : Finset ℕ := n.primeFactors.filter (fun p => z < p) with hS
  set T : Finset ℕ := smallestPart S J with hT
  have hTS : T ⊆ S := smallestPart_subset S J
  have hSn : S ⊆ n.primeFactors := Finset.filter_subset _ _
  have hprimeS : ∀ p ∈ S, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (hSn hp)
  have hSJ : J ≤ S.card := le_trans (Nat.le_mul_of_pos_left J (by omega)) hbig
  have hTcard : T.card = J := by
    rw [hT, card_smallestPart]
    omega
  have hprimeT : ∀ p ∈ T, p.Prime := fun p hp => hprimeS p (hTS hp)
  refine ⟨∏ p ∈ T, p, ?_, ?_, ?_, ?_, ?_⟩
  · exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ (hTS.trans hSn))
      (Nat.prod_primeFactors_dvd n)
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
      fun p hp => (hprimeT p hp).squarefree
    simp only [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hprimeT p hp) (hprimeT q hq)).mpr hpq
  · rw [Nat.primeFactors_prod hprimeT]
    exact hTcard
  · rw [Nat.primeFactors_prod hprimeT]
    intro p hp
    exact (Finset.mem_filter.1 (hTS hp)).2
  · refine pow_prod_le_of_card_mul_le hTS (smallestPart_le S J)
      (fun p hp => (hprimeS p hp).pos) ?_ ?_ ?_
    · exact Finset.card_pos.1 (by rw [hTcard]; omega)
    · rw [hTcard]
      exact hbig
    · refine Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ?_
      exact dvd_trans (Finset.prod_dvd_prod_of_subset _ _ _ hSn)
        (Nat.prod_primeFactors_dvd n)

/-- The squarefree divisors with exactly `J` prime factors, all above `z`, whose `c`-th power is
still at most `b`. -/
def bigDivisors (z b J c : ℕ) : Finset ℕ :=
  {d ∈ Finset.Icc 1 b | d ^ c ≤ b ∧ Squarefree d ∧ d.primeFactors.card = J
    ∧ ∀ p ∈ d.primeFactors, z < p}

/-- Members of `bigDivisors` are confined to a `c`-th root range. -/
theorem bigDivisors_subset_Icc {z b J c D : ℕ} (hc : 1 ≤ c) (hb : b < (D + 1) ^ c) :
    bigDivisors z b J c ⊆ Finset.Icc 1 D := by
  intro d hd
  obtain ⟨hdmem, hdpow, -⟩ := Finset.mem_filter.1 hd
  obtain ⟨hd1, -⟩ := Finset.mem_Icc.1 hdmem
  refine Finset.mem_Icc.2 ⟨hd1, ?_⟩
  have hlt : d ^ c < (D + 1) ^ c := lt_of_le_of_lt hdpow hb
  have := (Nat.pow_lt_pow_iff_left (by omega : c ≠ 0)).1 hlt
  omega

/-- **Large-prime tail by small divisors.**  Integers with many prime factors above `z` are covered
by the multiples of the small divisors produced by `exists_small_divisor`. -/
theorem card_omegaBig_ge_le_sum (a b z J c : ℕ) (hJ : 1 ≤ J) (hc : 1 ≤ c) :
    (#{n ∈ Finset.Ioc a b | c * J ≤ (n.primeFactors.filter (fun p => z < p)).card})
      ≤ ∑ d ∈ bigDivisors z b J c, (#{n ∈ Finset.Ioc a b | d ∣ n}) := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_biUnion_le)
  intro n hn
  obtain ⟨hmem, hbig⟩ := Finset.mem_filter.1 hn
  obtain ⟨han, hnb⟩ := Finset.mem_Ioc.1 hmem
  have hn0 : n ≠ 0 := by omega
  obtain ⟨d, hdvd, hsq, hcard, hprimes, hpow⟩ := exists_small_divisor hn0 hJ hc hbig
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hdb : d ≤ b := le_trans (Nat.le_of_dvd (by omega) hdvd) hnb
  refine Finset.mem_biUnion.2 ⟨d, ?_, ?_⟩
  · refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, hdb⟩, ?_, hsq, hcard, hprimes⟩
    exact le_trans hpow hnb
  · exact Finset.mem_filter.2 ⟨hmem, hdvd⟩

/-- **Large-prime tail, quantitative form.**  The count of integers with many prime factors above
`z` is the interval length times the reciprocal weight of the small divisors, plus one unit per
divisor — and the divisors are confined to a `c`-th root range. -/
theorem card_omegaBig_ge_le (a b z J c D : ℕ) (hab : a ≤ b) (hJ : 1 ≤ J) (hc : 1 ≤ c)
    (hD : b < (D + 1) ^ c) :
    ((#{n ∈ Finset.Ioc a b | c * J ≤ (n.primeFactors.filter (fun p => z < p)).card} : ℕ) : ℝ)
      ≤ ((b : ℝ) - a) * (∑ d ∈ bigDivisors z b J c, (1 : ℝ) / d) + (D : ℝ) := by
  classical
  have hcover := card_omegaBig_ge_le_sum a b z J c hJ hc
  have hcast : ((#{n ∈ Finset.Ioc a b | c * J
        ≤ (n.primeFactors.filter (fun p => z < p)).card} : ℕ) : ℝ)
      ≤ ∑ d ∈ bigDivisors z b J c, ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) := by
    exact_mod_cast hcover
  have hdpos : ∀ d ∈ bigDivisors z b J c, 0 < d := by
    intro d hd
    obtain ⟨hdmem, -⟩ := Finset.mem_filter.1 hd
    exact (Finset.mem_Icc.1 hdmem).1
  have hstep : ∀ d ∈ bigDivisors z b J c,
      ((#{n ∈ Finset.Ioc a b | d ∣ n} : ℕ) : ℝ) ≤ ((b : ℝ) - a) * (1 / d) + 1 := by
    intro d hd
    have hrem := abs_card_filter_dvd_Ioc_sub_lt d a b (hdpos d hd) hab
    have := (abs_lt.1 hrem).2
    have hrw : ((b : ℝ) - a) / d = ((b : ℝ) - a) * (1 / d) := by ring
    rw [hrw] at this
    linarith
  refine le_trans hcast (le_trans (Finset.sum_le_sum hstep) ?_)
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
  have hcard : ((bigDivisors z b J c).card : ℝ) ≤ (D : ℝ) := by
    have hsub : (bigDivisors z b J c).card ≤ (Finset.Icc 1 D).card :=
      Finset.card_le_card (bigDivisors_subset_Icc hc hD)
    rw [Nat.card_Icc] at hsub
    have : (bigDivisors z b J c).card ≤ D := by omega
    exact_mod_cast this
  linarith

/-- The primes in `(z, b]`. -/
def bigPrimeSet (z b : ℕ) : Finset ℕ := {p ∈ Finset.Icc (z + 1) b | p.Prime}

theorem prime_of_mem_bigPrimeSet {z b p : ℕ} (hp : p ∈ bigPrimeSet z b) : p.Prime :=
  (Finset.mem_filter.1 hp).2

/-- The squarefree modulus carrying all primes in `(z, b]`. -/
def bigModulus (z b : ℕ) : ℕ := ∏ p ∈ bigPrimeSet z b, p

theorem squarefree_bigModulus (z b : ℕ) : Squarefree (bigModulus z b) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_)
    fun _p hp => (prime_of_mem_bigPrimeSet hp).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (prime_of_mem_bigPrimeSet hp) (prime_of_mem_bigPrimeSet hq)).mpr hpq

theorem primeFactors_bigModulus (z b : ℕ) :
    (bigModulus z b).primeFactors = bigPrimeSet z b :=
  Nat.primeFactors_prod fun _p hp => prime_of_mem_bigPrimeSet hp

/-- Every small divisor produced by the extraction divides the big modulus. -/
theorem bigDivisors_subset (z b J c : ℕ) :
    bigDivisors z b J c ⊆ {d ∈ (bigModulus z b).divisors | d.primeFactors.card = J} := by
  intro d hd
  obtain ⟨hdmem, -, hsq, hcard, hprimes⟩ := Finset.mem_filter.1 hd
  obtain ⟨hd1, hdb⟩ := Finset.mem_Icc.1 hdmem
  have hd0 : d ≠ 0 := by omega
  have hsub : d.primeFactors ⊆ bigPrimeSet z b := by
    intro p hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hple : p ≤ d := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, le_trans hple hdb⟩, hprime⟩
    have := hprimes p hp
    omega
  have hdvd : d ∣ bigModulus z b := by
    have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
    rw [← hprod, bigModulus]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  exact Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hdvd, (squarefree_bigModulus z b).ne_zero⟩, hcard⟩

/-- **Reciprocal weight of the small divisors.**  A tilt by `v ≥ 1` turns the fixed prime count `J`
into a factor `v^{-J}` against the Euler product over the primes in `(z,b]`. -/
theorem sum_bigDivisors_inv_le (z b J c : ℕ) {v : ℝ} (hv : 1 ≤ v) :
    ∑ d ∈ bigDivisors z b J c, (1 : ℝ) / d
      ≤ (∏ p ∈ bigPrimeSet z b, (1 + v / (p : ℝ))) / v ^ J := by
  classical
  have hv0 : (0 : ℝ) < v := lt_of_lt_of_le zero_lt_one hv
  have hvJ : (0 : ℝ) < v ^ J := pow_pos hv0 J
  rw [le_div_iff₀ hvJ, Finset.sum_mul]
  have hstep : ∀ d ∈ bigDivisors z b J c,
      (1 : ℝ) / d * v ^ J = v ^ d.primeFactors.card / d := by
    intro d hd
    obtain ⟨-, -, -, hcard, -⟩ := Finset.mem_filter.1 hd
    rw [hcard]
    ring
  rw [Finset.sum_congr rfl hstep]
  have hsubset := bigDivisors_subset z b J c
  have hnonneg : ∀ d ∈ (bigModulus z b).divisors, (0 : ℝ) ≤ v ^ d.primeFactors.card / d := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have : (0 : ℝ) < d := by exact_mod_cast hd0
    positivity
  have hstep2 : ∑ d ∈ bigDivisors z b J c, v ^ d.primeFactors.card / d
      ≤ ∑ d ∈ (bigModulus z b).divisors, v ^ d.primeFactors.card / d := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (le_trans hsubset (Finset.filter_subset _ _)) ?_
    intro d hd _
    exact hnonneg d hd
  refine le_trans hstep2 (le_of_eq ?_)
  rw [sum_divisors_pow_card_primeFactors_div_eq_prod (squarefree_bigModulus z b) v,
    primeFactors_bigModulus]

/-- The prime factors of `gcd n z#` are exactly the prime factors of `n` up to `z`. -/
theorem primeFactors_gcd_primorial {z n : ℕ} (hn : n ≠ 0) :
    (Nat.gcd n (primorial z)).primeFactors = n.primeFactors.filter (fun p => p ≤ z) := by
  have hm0 : primorial z ≠ 0 := (squarefree_primorial z).ne_zero
  have hg0 : Nat.gcd n (primorial z) ≠ 0 := Nat.gcd_ne_zero_right hm0
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_filter, Nat.dvd_gcd_iff, hg0, hn, ne_eq,
    not_false_eq_true, and_true]
  constructor
  · rintro ⟨hprime, hpn, hpm⟩
    refine ⟨⟨hprime, hpn⟩, ?_⟩
    have hmem : p ∈ (primorial z).primeFactors := Nat.mem_primeFactors.2 ⟨hprime, hpm, hm0⟩
    rw [primeFactors_primorial_eq] at hmem
    exact (Nat.mem_primesLE.1 hmem).1
  · rintro ⟨⟨hprime, hpn⟩, hpz⟩
    refine ⟨hprime, hpn, ?_⟩
    have hmem : p ∈ Nat.primesLE z := Nat.mem_primesLE.2 ⟨hpz, hprime⟩
    rw [← primeFactors_primorial_eq] at hmem
    exact Nat.dvd_of_mem_primeFactors hmem

/-- The distinct prime count splits at the cut `z`. -/
theorem omegaSmall_add_card_filter {z n : ℕ} (hn : n ≠ 0) :
    omegaSmall z n + (n.primeFactors.filter (fun p => z < p)).card = n.primeFactors.card := by
  classical
  have hcong : n.primeFactors.filter (fun p => ¬ p ≤ z)
      = n.primeFactors.filter (fun p => z < p) := by
    refine Finset.filter_congr ?_
    intro p _
    simp [not_le]
  rw [omegaSmall, primeFactors_gcd_primorial hn, ← hcong]
  exact Finset.card_filter_add_card_filter_not (p := fun p => p ≤ z)

/-- **Upper tail split.**  Many distinct prime factors force either many small ones or many large
ones. -/
theorem card_omega_ge_le_add (a b z k k' J c : ℕ) (hk : k' + c * J ≤ k + 1) :
    (#{n ∈ Finset.Ioc a b | k ≤ n.primeFactors.card})
      ≤ (#{n ∈ Finset.Ioc a b | k' ≤ omegaSmall z n})
        + (#{n ∈ Finset.Ioc a b | c * J
              ≤ (n.primeFactors.filter (fun p => z < p)).card}) := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  obtain ⟨hmem, hbig⟩ := Finset.mem_filter.1 hn
  obtain ⟨han, -⟩ := Finset.mem_Ioc.1 hmem
  have hn0 : n ≠ 0 := by omega
  have hsplit := omegaSmall_add_card_filter (z := z) hn0
  rw [Finset.mem_union]
  by_cases hcase : c * J ≤ (n.primeFactors.filter (fun p => z < p)).card
  · exact Or.inr (Finset.mem_filter.2 ⟨hmem, hcase⟩)
  · refine Or.inl (Finset.mem_filter.2 ⟨hmem, ?_⟩)
    omega

end RHTower.Sieve
