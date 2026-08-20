import GaloisForLFunctions.RHTower.Sieve.RamareWeight

/-!
# Ramaré's identity applied to two disjoint prime ranges at once

For an integer carrying a prime factor in `P` **and** one in `Q`,

```text
   1 = ∑_{p ∈ P, p ∣ n} ∑_{q ∈ Q, q ∣ n} 1/(ω_P(n)·ω_Q(n))
```

exactly, so any sum over a finite set of integers becomes a sum over triples `(p, q, n)` plus the
part carried by integers missing one of the two ranges.  Unlike the joint Turán–Kubilius weight
`ω_P·ω_Q` this costs no variance and no prime-counting error, which is what lets the second range
be placed far above the first: the two discarded classes are controlled by their densities alone.
-/

namespace RHTower.Sieve

open Finset

/-- **The double Ramaré weight sums to one.** -/
theorem sum_sum_inv_card_double {P Q : Finset ℕ} {n : ℕ}
    (hP : (primeFactorsIn P n).Nonempty) (hQ : (primeFactorsIn Q n).Nonempty) :
    ∑ _p ∈ primeFactorsIn P n, ∑ _q ∈ primeFactorsIn Q n,
        (1 : ℂ) / ((primeFactorsIn P n).card : ℂ) / ((primeFactorsIn Q n).card : ℂ) = 1 := by
  have hPc : 0 < (primeFactorsIn P n).card := Finset.card_pos.2 hP
  have hQc : 0 < (primeFactorsIn Q n).card := Finset.card_pos.2 hQ
  have hPC : (((primeFactorsIn P n).card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hPc.ne'
  have hQC : (((primeFactorsIn Q n).card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQc.ne'
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- The integers of `S` carrying a designated prime factor from **each** range. -/
def doubleCore (P Q S : Finset ℕ) : Finset ℕ :=
  {n ∈ S | (primeFactorsIn P n).Nonempty ∧ (primeFactorsIn Q n).Nonempty}

/-- The integers of `S` missing one of the two ranges. -/
def doubleRough (P Q S : Finset ℕ) : Finset ℕ :=
  {n ∈ S | primeFactorsIn P n = ∅ ∨ primeFactorsIn Q n = ∅}

theorem doubleCore_subset (P Q S : Finset ℕ) : doubleCore P Q S ⊆ S :=
  Finset.filter_subset _ _

theorem doubleRough_subset (P Q S : Finset ℕ) : doubleRough P Q S ⊆ S :=
  Finset.filter_subset _ _

theorem sum_doubleCore_add_doubleRough (P Q S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ doubleCore P Q S, f n + ∑ n ∈ doubleRough P Q S, f n = ∑ n ∈ S, f n := by
  classical
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S
      (fun n => (primeFactorsIn P n).Nonempty ∧ (primeFactorsIn Q n).Nonempty) f
  have hrough : {n ∈ S | ¬ ((primeFactorsIn P n).Nonempty ∧ (primeFactorsIn Q n).Nonempty)}
      = doubleRough P Q S := by
    refine Finset.filter_congr ?_
    intro n _
    constructor
    · intro h
      rcases not_and_or.1 h with h' | h'
      · exact Or.inl (Finset.not_nonempty_iff_eq_empty.1 h')
      · exact Or.inr (Finset.not_nonempty_iff_eq_empty.1 h')
    · intro h
      rcases h with h | h
      · exact fun hc => (Finset.not_nonempty_iff_eq_empty.2 h) hc.1
      · exact fun hc => (Finset.not_nonempty_iff_eq_empty.2 h) hc.2
  rw [doubleCore, ← hrough]
  exact hsplit

/-- **The double Ramaré expansion of the core.**  Exact: no variance, no error. -/
theorem sum_doubleCore_eq_double_ramare (P Q S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ doubleCore P Q S, f n
      = ∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ {n ∈ doubleCore P Q S | p ∣ n ∧ q ∣ n},
          f n / ((primeFactorsIn P n).card : ℂ) / ((primeFactorsIn Q n).card : ℂ) := by
  classical
  set C : Finset ℕ := doubleCore P Q S with hC
  set g : ℕ → ℂ := fun n =>
    f n / ((primeFactorsIn P n).card : ℂ) / ((primeFactorsIn Q n).card : ℂ) with hg
  set F : ℕ → ℕ → ℕ → ℂ := fun p q n =>
    (if p ∣ n then (1 : ℂ) else 0) * (if q ∣ n then (1 : ℂ) else 0) * g n with hF
  have hfil : ∀ p ∈ P, ∀ q ∈ Q,
      (∑ n ∈ {n ∈ C | p ∣ n ∧ q ∣ n}, g n) = ∑ n ∈ C, F p q n := by
    intro p _ q _
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hF, hp, hq]
  have hinner : ∀ n ∈ C, (∑ p ∈ P, ∑ q ∈ Q, F p q n) = f n := by
    intro n hn
    rw [hC, doubleCore, Finset.mem_filter] at hn
    obtain ⟨-, hPn, hQn⟩ := hn
    have hPc : 0 < (primeFactorsIn P n).card := Finset.card_pos.2 hPn
    have hQc : 0 < (primeFactorsIn Q n).card := Finset.card_pos.2 hQn
    have hPC : (((primeFactorsIn P n).card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hPc.ne'
    have hQC : (((primeFactorsIn Q n).card : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hQc.ne'
    have hp : (∑ p ∈ P, (if p ∣ n then (1 : ℂ) else 0))
        = ((primeFactorsIn P n).card : ℂ) := by
      rw [← Finset.sum_filter]
      have hset : {p ∈ P | p ∣ n} = primeFactorsIn P n := rfl
      rw [hset, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hq : (∑ q ∈ Q, (if q ∣ n then (1 : ℂ) else 0))
        = ((primeFactorsIn Q n).card : ℂ) := by
      rw [← Finset.sum_filter]
      have hset : {q ∈ Q | q ∣ n} = primeFactorsIn Q n := rfl
      rw [hset, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hprod : (∑ p ∈ P, ∑ q ∈ Q, F p q n)
        = ((∑ p ∈ P, (if p ∣ n then (1 : ℂ) else 0))
            * (∑ q ∈ Q, (if q ∣ n then (1 : ℂ) else 0))) * g n := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_mul]
    rw [hprod, hp, hq, hg]
    field_simp
  refine Eq.symm ?_
  calc (∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ {n ∈ C | p ∣ n ∧ q ∣ n}, g n)
      = ∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ C, F p q n :=
        Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hfil p hp q hq
    _ = ∑ p ∈ P, ∑ n ∈ C, ∑ q ∈ Q, F p q n :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ n ∈ C, ∑ p ∈ P, ∑ q ∈ Q, F p q n := Finset.sum_comm
    _ = ∑ n ∈ C, f n := Finset.sum_congr rfl hinner

/-- **The complete double Ramaré decomposition.** -/
theorem sum_eq_doubleRamare_add_rough (P Q S : Finset ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ S, f n
      = (∑ p ∈ P, ∑ q ∈ Q, ∑ n ∈ {n ∈ doubleCore P Q S | p ∣ n ∧ q ∣ n},
            f n / ((primeFactorsIn P n).card : ℂ) / ((primeFactorsIn Q n).card : ℂ))
        + ∑ n ∈ doubleRough P Q S, f n := by
  rw [← sum_doubleCore_eq_double_ramare, sum_doubleCore_add_doubleRough]

/-- The rough class is contained in the union of the two single-range rough classes. -/
theorem doubleRough_subset_union (P Q S : Finset ℕ) :
    doubleRough P Q S
      ⊆ {n ∈ S | primeFactorsIn P n = ∅} ∪ {n ∈ S | primeFactorsIn Q n = ∅} := by
  classical
  intro n hn
  rw [doubleRough, Finset.mem_filter] at hn
  rcases hn.2 with h | h
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hn.1, h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hn.1, h⟩)

/-- The rough class is small: its cardinality is at most the sum of the two sifted counts. -/
theorem card_doubleRough_le (P Q S : Finset ℕ) :
    ((doubleRough P Q S).card : ℝ)
      ≤ (({n ∈ S | primeFactorsIn P n = ∅}).card : ℝ)
        + (({n ∈ S | primeFactorsIn Q n = ∅}).card : ℝ) := by
  classical
  have h1 := Finset.card_le_card (doubleRough_subset_union P Q S)
  have h2 := Finset.card_union_le
    ({n ∈ S | primeFactorsIn P n = ∅}) ({n ∈ S | primeFactorsIn Q n = ∅})
  have : (doubleRough P Q S).card
      ≤ ({n ∈ S | primeFactorsIn P n = ∅}).card + ({n ∈ S | primeFactorsIn Q n = ∅}).card :=
    le_trans h1 h2
  exact_mod_cast this

end RHTower.Sieve
