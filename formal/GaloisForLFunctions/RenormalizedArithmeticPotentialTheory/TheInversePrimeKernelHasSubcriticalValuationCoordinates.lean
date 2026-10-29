import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSievePrimeKernelIsABoundedOperator

/-!
# Inverse-prime incidence in valuation coordinates

Replacing the square-root prime multiplier by its full inverse changes
the geometric parameter on each valuation ladder from `1 / sqrt p` to
`1 / p`. The same unique prime-power quotient determines every entry.
-/

noncomputable section
open Finset
open scoped Classical

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open ArithmeticFunction ArithmeticIntersectionTheory ArithmeticEffectivityTheory HTGeometry

/-- The symmetric prime-power kernel with inverse multiplier. -/
def inversePrimeKernel (m n : ℕ) : ℝ :=
  if m ∣ n ∧ m ≠ n then vonMangoldt (n / m) / (n / m : ℕ) else
  if n ∣ m ∧ n ≠ m then vonMangoldt (m / n) / (m / n : ℕ) else 0

theorem inversePrimeKernel_self (n : ℕ) : inversePrimeKernel n n = 0 := by
  simp only [inversePrimeKernel, ne_eq, not_true_eq_false, and_false, if_false]

theorem inversePrimeKernel_eq_directed (m n : ℕ) :
    inversePrimeKernel m n =
      (if m ∣ n ∧ m ≠ n then vonMangoldt (n / m) / (n / m : ℕ) else 0) +
      (if n ∣ m ∧ n ≠ m then vonMangoldt (m / n) / (m / n : ℕ) else 0) := by
  unfold inversePrimeKernel
  by_cases h : m ∣ n ∧ m ≠ n
  · have h' : ¬ (n ∣ m ∧ n ≠ m) := fun h' => h.2 (Nat.dvd_antisymm h.1 h'.1)
    simp only [if_pos h, if_neg h', add_zero]
  · simp only [if_neg h, zero_add]

theorem inversePrimeKernel_symm (m n : ℕ) : inversePrimeKernel m n = inversePrimeKernel n m := by
  rw [inversePrimeKernel_eq_directed, inversePrimeKernel_eq_directed, add_comm]

/-- The inverse multiplier is the geometric parameter on a prime ladder. -/
theorem inversePrimeKernel_ladder {p c : ℕ} (hp : p.Prime) (hc : 0 < c) (i j : ℕ) :
    inversePrimeKernel (c * p ^ i) (c * p ^ j) =
      if i = j then 0 else Real.log p * kmsEntry (1 / (p : ℝ)) i j := by
  have hpos : ∀ a, 0 < c * p ^ a := fun a => Nat.mul_pos hc (pow_pos hp.pos a)
  have hinj : ∀ a b, c * p ^ a = c * p ^ b ↔ a = b := fun a b => by
    rw [Nat.mul_left_cancel_iff hc]
    exact (Nat.pow_right_injective hp.two_le).eq_iff
  have hent (d : ℕ) (hd : 0 < d) :
      vonMangoldt (p ^ d) / ((p ^ d : ℕ) : ℝ) = Real.log p * (1 / (p : ℝ)) ^ d := by
    rw [vonMangoldt_apply_pow hd.ne', vonMangoldt_apply_prime hp,
      Nat.cast_pow, one_div_pow, div_eq_mul_inv, one_div]
  rcases lt_trichotomy i j with hij | rfl | hij
  · have hdvd : c * p ^ i ∣ c * p ^ j := Nat.mul_dvd_mul_left c (pow_dvd_pow p hij.le)
    have hdiv : c * p ^ j / (c * p ^ i) = p ^ (j - i) := by
      rw [Nat.mul_div_mul_left _ _ hc, Nat.pow_div hij.le hp.pos]
    rw [inversePrimeKernel, if_pos ⟨hdvd, (hinj i j).not.mpr hij.ne⟩, hdiv,
      hent _ (by omega), if_neg hij.ne, kmsEntry, max_eq_right hij.le, min_eq_left hij.le]
  · rw [if_pos rfl, inversePrimeKernel_self]
  · have hdvd : c * p ^ j ∣ c * p ^ i := Nat.mul_dvd_mul_left c (pow_dvd_pow p hij.le)
    have hndvd : ¬ (c * p ^ i ∣ c * p ^ j ∧ c * p ^ i ≠ c * p ^ j) := by
      rintro ⟨h, _⟩
      have h₁ := Nat.le_of_dvd (hpos j) h
      have h₂ := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right hp.one_lt hij) hc
      omega
    have hdiv : c * p ^ i / (c * p ^ j) = p ^ (i - j) := by
      rw [Nat.mul_div_mul_left _ _ hc, Nat.pow_div hij.le hp.pos]
    rw [inversePrimeKernel, if_neg hndvd,
      if_pos ⟨hdvd, (hinj j i).not.mpr hij.ne⟩, hdiv,
      hent _ (by omega), if_neg hij.ne', kmsEntry, max_eq_left hij.le, min_eq_right hij.le]

/-- One transverse ladder of the inverse-multiplier kernel. -/
def inversePrimeLadderKernel (p m n : ℕ) : ℝ :=
  if m ≠ n ∧ ordCompl[p] m = ordCompl[p] n then
    Real.log p * kmsEntry (1 / (p : ℝ)) (m.factorization p) (n.factorization p)
  else 0

theorem inversePrimeLadderKernel_eq {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (h : ordCompl[p] m = ordCompl[p] n) :
    inversePrimeLadderKernel p m n = inversePrimeKernel m n := by
  have hP := inversePrimeKernel_ladder hp (Nat.ordCompl_pos p hm)
    (m.factorization p) (n.factorization p)
  rw [← eq_ordCompl_mul_pow, h, ← eq_ordCompl_mul_pow] at hP
  by_cases hmn : m = n
  · subst n
    rw [inversePrimeKernel_self]
    simp only [inversePrimeLadderKernel, ne_eq, not_true_eq_false, false_and, if_false]
  · have hv : m.factorization p ≠ n.factorization p :=
      fun hv => hmn (eq_of_sameLadder_of_factorization_eq h hv)
    rw [inversePrimeLadderKernel, if_pos ⟨hmn, h⟩, hP, if_neg hv]

private theorem criticalKernel_ne_zero_of_inverse_ne_zero {m n : ℕ}
    (h : inversePrimeKernel m n ≠ 0) : weilPrimeKernel m n ≠ 0 := by
  unfold inversePrimeKernel at h
  unfold weilPrimeKernel
  split_ifs at h ⊢ with h₁ h₂
  · have hn : vonMangoldt (n / m) ≠ 0 := fun hz => h (by rw [hz, zero_div])
    have hd : n / m ≠ 0 := by
      intro hz
      exact hn (by rw [hz, vonMangoldt_apply_zero])
    exact div_ne_zero hn (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))).ne'
  · have hn : vonMangoldt (m / n) ≠ 0 := fun hz => h (by rw [hz, zero_div])
    have hd : m / n ≠ 0 := by
      intro hz
      exact hn (by rw [hz, vonMangoldt_apply_zero])
    exact div_ne_zero hn (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hd))).ne'
  · exact (h rfl).elim

/-- A nonzero inverse-prime entry changes one and only one prime coordinate. -/
theorem inversePrimeKernel_eq_sum_ladders {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    inversePrimeKernel m n = ∑ p ∈ (m * n).primeFactors, inversePrimeLadderKernel p m n := by
  by_cases hex : ∃ p ∈ (m * n).primeFactors, m ≠ n ∧ ordCompl[p] m = ordCompl[p] n
  · obtain ⟨p, hp, hmn, he⟩ := hex
    rw [sum_eq_single p,
      inversePrimeLadderKernel_eq (Nat.prime_of_mem_primeFactors hp) hm he]
    · intro p' _ hp'
      rw [inversePrimeLadderKernel, if_neg]
      rintro ⟨_, he'⟩
      exact hmn (eq_of_sameLadder_of_sameLadder hp'.symm hm hn he he')
    · exact fun h => (h hp).elim
  · have hz : ∀ p ∈ (m * n).primeFactors, inversePrimeLadderKernel p m n = 0 := by
      intro p hp
      rw [inversePrimeLadderKernel, if_neg (fun h => hex ⟨p, hp, h⟩)]
    rw [sum_eq_zero hz]
    by_contra h
    obtain ⟨p, hp, he⟩ := exists_sameLadder_of_weilPrimeKernel_ne_zero hm hn
      (criticalKernel_ne_zero_of_inverse_ne_zero h)
    exact hex ⟨p, hp, he⟩

theorem inversePrimeLadderKernel_zero_of_notMem {p m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hp : p ∉ (m * n).primeFactors) : inversePrimeLadderKernel p m n = 0 := by
  rw [inversePrimeLadderKernel, if_neg]
  rintro ⟨hmn, he⟩
  have hv (k l : ℕ) (hk : k ≠ 0) (hl : l ≠ 0)
      (hp' : p ∉ (k * l).primeFactors) : k.factorization p = 0 := by
    by_contra h
    exact hp' (Nat.primeFactors_mul hk hl ▸ mem_union_left _
      (Nat.support_factorization k ▸ Finsupp.mem_support_iff.mpr h))
  exact hmn (eq_of_sameLadder_of_factorization_eq he
    ((hv m n hm hn hp).trans (hv n m hn hm (by simpa only [mul_comm] using hp)).symm))

theorem inversePrimeKernel_sieve_sum {Q : Finset Nat.Primes} {m n : ℕ}
    (hm : SieveSupported Q m) (hn : SieveSupported Q n) :
    inversePrimeKernel m n = ∑ p ∈ Q, inversePrimeLadderKernel (p : ℕ) m n := by
  have hsub : (m * n).primeFactors ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    exact mem_image.mpr ⟨⟨p, hp'.1⟩, (hm.mul hn).prime_dvd_mem hp'.2.1, rfl⟩
  rw [inversePrimeKernel_eq_sum_ladders hm.pos.ne' hn.pos.ne']
  calc
    _ = ∑ p ∈ Q.image (fun p : Nat.Primes => (p : ℕ)), inversePrimeLadderKernel p m n :=
      sum_subset hsub fun p _ hp => inversePrimeLadderKernel_zero_of_notMem hm.pos.ne' hn.pos.ne' hp
    _ = _ := sum_image (fun a _ b _ h => Subtype.ext h)

/-- The literal inverse-prime ladder is the `1/p` KMS fibre with its diagonal removed. -/
theorem inversePrimeLadderKernel_tensor {p m n : ℕ} (hp : p.Prime) (hm : m ≠ 0) (hn : n ≠ 0) :
    inversePrimeLadderKernel p m n =
      if ∀ l, l ≠ p → m.factorization l = n.factorization l then
        Real.log p * (kmsEntry (1 / (p : ℝ)) (m.factorization p) (n.factorization p) -
          if m.factorization p = n.factorization p then 1 else 0)
      else 0 := by
  have hiff : ordCompl[p] m = ordCompl[p] n ↔
      ∀ l, l ≠ p → m.factorization l = n.factorization l := by
    constructor
    · intro h l hl
      have he := congrArg (fun k => k.factorization l) h
      simpa only [Nat.factorization_ordCompl, Finsupp.erase_ne hl] using he
    · intro h
      apply Nat.eq_of_factorization_eq (Nat.ordCompl_pos p hm).ne' (Nat.ordCompl_pos p hn).ne'
      intro l
      rw [Nat.factorization_ordCompl, Nat.factorization_ordCompl]
      by_cases hl : l = p
      · subst l
        simp only [Finsupp.erase_same]
      · rw [Finsupp.erase_ne hl, Finsupp.erase_ne hl]
        exact h l hl
  by_cases hl : ordCompl[p] m = ordCompl[p] n
  · rw [if_pos (hiff.mp hl)]
    by_cases hv : m.factorization p = n.factorization p
    · have he := eq_of_sameLadder_of_factorization_eq hl hv
      subst n
      simp only [inversePrimeLadderKernel, ne_eq, not_true_eq_false, false_and,
        if_false, kmsEntry_self, if_true, sub_self, mul_zero]
    · have hmn : m ≠ n := fun h => hv (h ▸ rfl)
      rw [inversePrimeLadderKernel, if_pos ⟨hmn, hl⟩, if_neg hv, sub_zero]
  · rw [if_neg (fun h => hl (hiff.mpr h)), inversePrimeLadderKernel,
      if_neg (fun h => hl h.2)]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
