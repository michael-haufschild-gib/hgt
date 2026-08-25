import GaloisForLFunctions.RHTower.Sieve.VonMangoldtSelfConvLogBound

noncomputable section

open Finset ArithmeticFunction
open scoped ArithmeticFunction BigOperators

namespace RHTower.Sieve

/-- Pointwise square of the von Mangoldt arithmetic function. -/
def vonMangoldtSquare : ArithmeticFunction ℝ :=
  ⟨fun n => Λ n ^ 2, by simp⟩

@[simp] theorem vonMangoldtSquare_apply (n : ℕ) :
    vonMangoldtSquare n = Λ n ^ 2 := rfl

theorem vonMangoldtSquare_ne_zero_iff (n : ℕ) :
    vonMangoldtSquare n ≠ 0 ↔ Λ n ≠ 0 := by
  simp [vonMangoldtSquare]

theorem vonMangoldtSquare_mul_self_eq_zero_of_three_le
    {n : ℕ} (hn : 3 ≤ n.primeFactors.card) :
    (vonMangoldtSquare * vonMangoldtSquare) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases h1 : vonMangoldtSquare x.1 = 0
  · rw [h1, zero_mul]
  by_cases h2 : vonMangoldtSquare x.2 = 0
  · rw [h2, mul_zero]
  exfalso
  have hxn : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
  have hle := GaloisForLFunctions.HTGeometry.card_primeFactors_mul_le_two
    ((vonMangoldtSquare_ne_zero_iff x.1).mp h1)
    ((vonMangoldtSquare_ne_zero_iff x.2).mp h2)
  rw [hxn] at hle
  omega

theorem vonMangoldtSquare_mul_self_prime_pow
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (vonMangoldtSquare * vonMangoldtSquare) (p ^ a) =
      ((a : ℝ) - 1) * Real.log p ^ 4 := by
  classical
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun i j => vonMangoldtSquare i * vonMangoldtSquare j),
    Nat.sum_divisors_prime_pow hp]
  have hstep : ∀ x ∈ Finset.range (a + 1),
      vonMangoldtSquare (p ^ x) * vonMangoldtSquare (p ^ a / p ^ x) =
        if x ∈ Finset.Ioo 0 a then Real.log p ^ 4 else 0 := by
    intro x hx
    have hxa : x ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
    rw [Nat.pow_div hxa hp.pos]
    by_cases h0 : x = 0
    · subst h0
      simp [vonMangoldtSquare]
    by_cases hxa' : x = a
    · subst hxa'
      simp [vonMangoldtSquare]
    · have hmem : x ∈ Finset.Ioo 0 a := Finset.mem_Ioo.mpr ⟨by omega, by omega⟩
      rw [if_pos hmem, vonMangoldtSquare_apply, vonMangoldtSquare_apply,
        ArithmeticFunction.vonMangoldt_apply_pow h0,
        ArithmeticFunction.vonMangoldt_apply_pow (by omega : a - x ≠ 0),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
      ring
  have hsub : Finset.Ioo 0 a ⊆ Finset.range (a + 1) := by
    intro x hx
    exact Finset.mem_range.mpr (by have := Finset.mem_Ioo.mp hx; omega)
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem,
    Finset.inter_eq_right.mpr hsub, Finset.sum_const, Nat.card_Ioo, nsmul_eq_mul]
  rw [Nat.sub_zero, Nat.cast_sub ha]
  norm_num

/-- On the two-prime layer, the square-weight convolution has the expected two ordered blocks. -/
theorem vonMangoldtSquare_mul_self_of_card_eq_two
    {n : ℕ} (hn : n.primeFactors.card = 2) :
    (vonMangoldtSquare * vonMangoldtSquare) n =
      2 * ∏ p ∈ n.primeFactors, Real.log p ^ 2 := by
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
  set a := n.factorization p
  set b := n.factorization q
  have hprod : p ^ a * q ^ b = n := by
    have h := GaloisForLFunctions.HTGeometry.prod_primeFactors_pow_factorization hn0
    rwa [hfac, Finset.prod_pair hpq] at h
  have hpa : (p ^ a).primeFactors = {p} := Nat.primeFactors_prime_pow hane hp
  have hqb : (q ^ b).primeFactors = {q} := Nat.primeFactors_prime_pow hbne hq
  have hblockne : p ^ a ≠ q ^ b := by
    intro h
    rw [h, hqb] at hpa
    exact hpq (Finset.singleton_injective hpa.symm)
  have hpa0 : p ^ a ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hqb0 : q ^ b ≠ 0 := pow_ne_zero _ hq.pos.ne'
  have hsub : ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) ⊆
      n.divisorsAntidiagonal := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hn0⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨by rw [mul_comm]; exact hprod, hn0⟩
  have hzero : ∀ x ∈ n.divisorsAntidiagonal,
      x ∉ ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) →
        vonMangoldtSquare x.1 * vonMangoldtSquare x.2 = 0 := by
    intro x hx hxn
    by_contra hne
    have h1 : vonMangoldtSquare x.1 ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : vonMangoldtSquare x.2 ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hxde : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hdp : IsPrimePow x.1 := vonMangoldt_ne_zero_iff.mp
      ((vonMangoldtSquare_ne_zero_iff x.1).mp h1)
    have hep : IsPrimePow x.2 := vonMangoldt_ne_zero_iff.mp
      ((vonMangoldtSquare_ne_zero_iff x.2).mp h2)
    have hd0 : x.1 ≠ 0 := by have := hdp.two_le; omega
    have he0 : x.2 ≠ 0 := by have := hep.two_le; omega
    obtain ⟨u, hu⟩ := Finset.card_eq_one.mp
      (isPrimePow_iff_card_primeFactors_eq_one.mp hdp)
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp
      (isPrimePow_iff_card_primeFactors_eq_one.mp hep)
    have hunion : ({u} : Finset ℕ) ∪ {v} = ({p, q} : Finset ℕ) := by
      rw [← hu, ← hv, ← Nat.primeFactors_mul hd0 he0, hxde, hfac]
    have huv : u ≠ v := by
      intro h
      subst h
      rw [Finset.union_self] at hunion
      have hcard : ({u} : Finset ℕ).card = ({p, q} : Finset ℕ).card := by rw [hunion]
      rw [Finset.card_singleton, Finset.card_insert_of_notMem (by simpa using hpq),
        Finset.card_singleton] at hcard
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
        refine GaloisForLFunctions.HTGeometry.block_eq_pow_factorization
          hxde hd0 he0 hu ?_
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
        refine GaloisForLFunctions.HTGeometry.block_eq_pow_factorization
          hxde hd0 he0 hu ?_
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
  rw [vonMangoldtSquare_apply, vonMangoldtSquare_apply,
    GaloisForLFunctions.HTGeometry.vonMangoldt_of_primeFactors_singleton hpa,
    GaloisForLFunctions.HTGeometry.vonMangoldt_of_primeFactors_singleton hqb]
  ring

theorem vonMangoldtSelfConv_sq_eq_two_mul_squareConv_of_card_eq_two
    {n : ℕ} (hn : n.primeFactors.card = 2) :
    ((Λ * Λ) n) ^ 2 = 2 * (vonMangoldtSquare * vonMangoldtSquare) n := by
  obtain ⟨p, q, hpq, hfac⟩ := Finset.card_eq_two.mp hn
  rw [GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_of_card_eq_two hn,
    vonMangoldtSquare_mul_self_of_card_eq_two hn, hfac, Finset.prod_pair hpq,
    Finset.prod_pair hpq]
  ring

/-- Away from prime powers, the squared self-convolution is exactly twice the convolution of the
pointwise von Mangoldt square. -/
theorem vonMangoldtSelfConv_sq_eq_two_mul_squareConv_of_not_isPrimePow
    (n : ℕ) (hn : 1 ≤ n) (hpp : ¬ IsPrimePow n) :
    ((Λ * Λ) n) ^ 2 = 2 * (vonMangoldtSquare * vonMangoldtSquare) n := by
  by_cases hcard0 : n.primeFactors.card = 0
  · have hempty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
    have hn01 := Nat.primeFactors_eq_empty.mp hempty
    have hn1 : n = 1 := by omega
    subst hn1
    norm_num [vonMangoldtSquare, ArithmeticFunction.mul_apply]
  by_cases hcard1 : n.primeFactors.card = 1
  · exact absurd (isPrimePow_iff_card_primeFactors_eq_one.mpr hcard1) hpp
  by_cases hcard2 : n.primeFactors.card = 2
  · exact vonMangoldtSelfConv_sq_eq_two_mul_squareConv_of_card_eq_two hcard2
  · have hcard3 : 3 ≤ n.primeFactors.card := by omega
    rw [GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_eq_zero_of_three_le hcard3,
      vonMangoldtSquare_mul_self_eq_zero_of_three_le hcard3]
    norm_num

/-- Prime powers are the entire correction to the square-convolution main term, and their
pointwise correction is bounded by the fourth logarithmic power. -/
theorem abs_vonMangoldtSelfConv_sq_sub_two_mul_squareConv_le_of_isPrimePow
    {n : ℕ} (hn : IsPrimePow n) :
    |((Λ * Λ) n) ^ 2 - 2 * (vonMangoldtSquare * vonMangoldtSquare) n| ≤
      Real.log n ^ 4 := by
  obtain ⟨p, a, hp, ha, hpa⟩ := (isPrimePow_nat_iff n).mp hn
  rw [← hpa, GaloisForLFunctions.HTGeometry.vonMangoldt_mul_self_prime_pow hp ha,
    vonMangoldtSquare_mul_self_prime_pow hp ha, Nat.cast_pow, Real.log_pow]
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hlog4 : 0 ≤ Real.log (p : ℝ) ^ 4 := by positivity
  have habs : |((a : ℝ) - 1) ^ 2 - 2 * ((a : ℝ) - 1)| ≤ (a : ℝ) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((a : ℝ) - 1)]
  calc
    |(((a : ℝ) - 1) * Real.log (p : ℝ) ^ 2) ^ 2 -
        2 * (((a : ℝ) - 1) * Real.log (p : ℝ) ^ 4)| =
        |(((a : ℝ) - 1) ^ 2 - 2 * ((a : ℝ) - 1)) *
          Real.log (p : ℝ) ^ 4| := by
      congr 1
      ring
    _ = |((a : ℝ) - 1) ^ 2 - 2 * ((a : ℝ) - 1)| *
          Real.log (p : ℝ) ^ 4 := by
      rw [abs_mul, abs_of_nonneg hlog4]
    _ ≤ (a : ℝ) ^ 2 * Real.log (p : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_right habs hlog4
    _ ≤ ((a : ℝ) * Real.log (p : ℝ)) ^ 4 := by
      have ha0 : 0 ≤ (a : ℝ) := le_trans zero_le_one haR
      have ha2 : (a : ℝ) ^ 2 ≤ (a : ℝ) ^ 4 := by
        nlinarith [sq_nonneg ((a : ℝ) ^ 2 - 1)]
      calc
        (a : ℝ) ^ 2 * Real.log (p : ℝ) ^ 4 ≤
            (a : ℝ) ^ 4 * Real.log (p : ℝ) ^ 4 :=
          mul_le_mul_of_nonneg_right ha2 hlog4
        _ = ((a : ℝ) * Real.log (p : ℝ)) ^ 4 := by ring

end RHTower.Sieve
