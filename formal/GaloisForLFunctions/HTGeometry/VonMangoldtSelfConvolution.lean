import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# The self-convolution of the von Mangoldt function

`Λ * Λ` is the Dirichlet self-convolution of the von Mangoldt function.  It is supported on the
integers with at most two distinct prime divisors, and there it is explicit:

```text
(Λ * Λ)(p^a)     = (a - 1) (log p)^2,
(Λ * Λ)(p^a q^b) = 2 log p log q       (p ≠ q).
```
-/

open Finset
open scoped ArithmeticFunction BigOperators

namespace GaloisForLFunctions.HTGeometry

/-! ## Prime-power decomposition helpers -/

/-- A positive natural number is the product of its prime powers, indexed by its prime factors. -/
theorem prod_primeFactors_pow_factorization {n : ℕ} (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- A number with a single prime factor is the corresponding prime power. -/
theorem eq_pow_factorization_of_primeFactors_singleton {n p : ℕ} (hn : n ≠ 0)
    (h : n.primeFactors = {p}) : n = p ^ n.factorization p := by
  have hprod := prod_primeFactors_pow_factorization hn
  rw [h, Finset.prod_singleton] at hprod
  exact hprod.symm

/-- The von Mangoldt value of a number with a single prime factor. -/
theorem vonMangoldt_of_primeFactors_singleton {n p : ℕ} (h : n.primeFactors = {p}) :
    Λ n = Real.log p := by
  have hpp : IsPrimePow n := isPrimePow_iff_card_primeFactors_eq_one.mpr (by rw [h]; simp)
  have h2 : 2 ≤ n := hpp.two_le
  have hmem : n.minFac ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
  rw [h, Finset.mem_singleton] at hmem
  rw [ArithmeticFunction.vonMangoldt_apply, if_pos hpp, hmem]

/-! ## The support of the self-convolution -/

/-- A nonvanishing term of the self-convolution forces at most two distinct primes. -/
theorem card_primeFactors_mul_le_two {d e : ℕ} (hd : Λ d ≠ 0) (he : Λ e ≠ 0) :
    (d * e).primeFactors.card ≤ 2 := by
  classical
  have hdp : IsPrimePow d := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hd
  have hep : IsPrimePow e := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp he
  have hd0 : d ≠ 0 := by have := hdp.two_le; omega
  have he0 : e ≠ 0 := by have := hep.two_le; omega
  rw [Nat.primeFactors_mul hd0 he0]
  calc (d.primeFactors ∪ e.primeFactors).card
      ≤ d.primeFactors.card + e.primeFactors.card := Finset.card_union_le _ _
    _ = 2 := by
        rw [isPrimePow_iff_card_primeFactors_eq_one.mp hdp,
          isPrimePow_iff_card_primeFactors_eq_one.mp hep]

/-- **The self-convolution vanishes beyond two distinct primes.** -/
theorem vonMangoldt_mul_self_eq_zero_of_three_le {n : ℕ} (hn : 3 ≤ n.primeFactors.card) :
    (Λ * Λ) n = 0 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun x hx => ?_
  rcases eq_or_ne (Λ x.1) 0 with h | h
  · rw [h, zero_mul]
  rcases eq_or_ne (Λ x.2) 0 with h' | h'
  · rw [h', mul_zero]
  exfalso
  have hxn : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hle := card_primeFactors_mul_le_two h h'
  rw [hxn] at hle
  omega

/-! ## The two explicit layers -/

/-- **The one-prime layer.**  `(Λ * Λ)(p^a) = (a - 1)(log p)^2`. -/
theorem vonMangoldt_mul_self_prime_pow {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (Λ * Λ) (p ^ a) = ((a : ℝ) - 1) * Real.log p ^ 2 := by
  classical
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => Λ i * Λ j),
    Nat.sum_divisors_prime_pow hp]
  have hstep : ∀ x ∈ Finset.range (a + 1),
      Λ (p ^ x) * Λ (p ^ a / p ^ x) = if x ∈ Finset.Ioo 0 a then Real.log p ^ 2 else 0 := by
    intro x hx
    have hxa : x ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    rw [Nat.pow_div hxa hp.pos]
    by_cases h0 : x = 0
    · subst h0
      simp
    by_cases hxa' : x = a
    · subst hxa'
      simp
    · have hmem : x ∈ Finset.Ioo 0 a := Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
      rw [if_pos hmem, ArithmeticFunction.vonMangoldt_apply_pow h0,
        ArithmeticFunction.vonMangoldt_apply_pow (by omega : a - x ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      ring
  have hsub : Finset.Ioo 0 a ⊆ Finset.range (a + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (by have := Finset.mem_Ioo.mp hx; omega)
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub,
    Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul]
  rw [Nat.sub_zero, Nat.cast_sub ha]
  norm_num

/-- The block extraction step: a single-prime block of a factorization is the full prime power. -/
theorem block_eq_pow_factorization {n d e p : ℕ} (hde : d * e = n) (hd0 : d ≠ 0) (he0 : e ≠ 0)
    (hdpf : d.primeFactors = {p}) (hpe : p ∉ e.primeFactors) : d = p ^ n.factorization p := by
  have hfd := eq_pow_factorization_of_primeFactors_singleton hd0 hdpf
  have hfe : e.factorization p = 0 := by
    rw [← Nat.support_factorization] at hpe
    exact Finsupp.notMem_support_iff.mp hpe
  have hn : n.factorization p = d.factorization p := by
    rw [← hde, Nat.factorization_mul hd0 he0]
    simp [hfe]
  rw [hn]
  exact hfd

/-- **The two-prime layer.**  On an integer with exactly two distinct prime divisors the
self-convolution is twice the product of the two prime logarithms. -/
theorem vonMangoldt_mul_self_of_card_eq_two {n : ℕ} (hn : n.primeFactors.card = 2) :
    (Λ * Λ) n = 2 * ∏ p ∈ n.primeFactors, Real.log p := by
  classical
  obtain ⟨p, q, hpq, hfac⟩ := Finset.card_eq_two.mp hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hfac
    exact absurd hfac.symm (by simp)
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hfac]; simp)
  have hq : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hfac]; simp)
  have hpmem : p ∈ n.primeFactors := by rw [hfac]; simp
  have hqmem : q ∈ n.primeFactors := by rw [hfac]; simp
  have hane : n.factorization p ≠ 0 := by
    rw [← Nat.support_factorization] at hpmem
    exact fun h => (Finsupp.notMem_support_iff.mpr h) hpmem
  have hbne : n.factorization q ≠ 0 := by
    rw [← Nat.support_factorization] at hqmem
    exact fun h => (Finsupp.notMem_support_iff.mpr h) hqmem
  set a := n.factorization p with ha_def
  set b := n.factorization q with hb_def
  have hprod : p ^ a * q ^ b = n := by
    have h := prod_primeFactors_pow_factorization hn0
    rwa [hfac, Finset.prod_pair hpq] at h
  have hpa : (p ^ a).primeFactors = {p} := Nat.primeFactors_prime_pow hane hp
  have hqb : (q ^ b).primeFactors = {q} := Nat.primeFactors_prime_pow hbne hq
  have hblockne : p ^ a ≠ q ^ b := by
    intro h
    rw [h, hqb] at hpa
    exact hpq (Finset.singleton_injective hpa.symm)
  have hpa0 : p ^ a ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hqb0 : q ^ b ≠ 0 := pow_ne_zero _ hq.pos.ne'
  have hsub : ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) ⊆ n.divisorsAntidiagonal := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn0⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨by rw [mul_comm]; exact hprod, hn0⟩
  have hzero : ∀ x ∈ n.divisorsAntidiagonal,
      x ∉ ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) → Λ x.1 * Λ x.2 = 0 := by
    intro x hx hxn
    by_contra hne
    have h1 : Λ x.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : Λ x.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hxde : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hdp : IsPrimePow x.1 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1
    have hep : IsPrimePow x.2 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2
    have hd0 : x.1 ≠ 0 := by have := hdp.two_le; omega
    have he0 : x.2 ≠ 0 := by have := hep.two_le; omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp (isPrimePow_iff_card_primeFactors_eq_one.mp hdp)
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp (isPrimePow_iff_card_primeFactors_eq_one.mp hep)
    have hunion : ({u} : Finset ℕ) ∪ {v} = ({p, q} : Finset ℕ) := by
      rw [← hu, ← hv, ← Nat.primeFactors_mul hd0 he0, hxde, hfac]
    have huv : u ≠ v := by
      intro h
      subst h
      rw [Finset.union_self] at hunion
      have : ({u} : Finset ℕ).card = ({p, q} : Finset ℕ).card := by rw [hunion]
      rw [Finset.card_singleton, Finset.card_insert_of_notMem (by simpa using hpq),
        Finset.card_singleton] at this
      omega
    have humem : u ∈ ({p, q} : Finset ℕ) := by rw [← hunion]; simp
    have hvmem : v ∈ ({p, q} : Finset ℕ) := by rw [← hunion]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at humem hvmem
    have hcase : (u = p ∧ v = q) ∨ (u = q ∧ v = p) := by
      rcases humem with rfl | rfl
      · rcases hvmem with h | h
        · exact absurd h.symm huv
        · exact Or.inl ⟨rfl, h⟩
      · rcases hvmem with h | h
        · exact Or.inr ⟨rfl, h⟩
        · exact absurd h.symm huv
    apply hxn
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hcase with ⟨hup, hvq⟩ | ⟨huq, hvp⟩
    · rw [hup] at hu
      rw [hvq] at hv
      left
      have hd : x.1 = p ^ a := by
        refine block_eq_pow_factorization hxde hd0 he0 hu ?_
        rw [hv]
        simpa using hpq
      have he : x.2 = q ^ b := by
        have h' : p ^ a * x.2 = p ^ a * q ^ b := by
          rw [hd] at hxde
          rw [hxde, ← hprod]
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpa0) h'
      exact Prod.ext hd he
    · rw [huq] at hu
      rw [hvp] at hv
      right
      have hd : x.1 = q ^ b := by
        refine block_eq_pow_factorization hxde hd0 he0 hu ?_
        rw [hv]
        simpa using hpq.symm
      have he : x.2 = p ^ a := by
        have h' : q ^ b * x.2 = q ^ b * p ^ a := by
          rw [hd] at hxde
          rw [hxde, ← hprod]
          ring
        exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hqb0) h'
      exact Prod.ext hd he
  rw [ArithmeticFunction.mul_apply, ← Finset.sum_subset hsub hzero,
    Finset.sum_pair (by simp [Prod.ext_iff, hblockne]), hfac, Finset.prod_pair hpq]
  rw [vonMangoldt_of_primeFactors_singleton hpa, vonMangoldt_of_primeFactors_singleton hqb]
  ring

end GaloisForLFunctions.HTGeometry
