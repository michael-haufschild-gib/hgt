import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Peak.Occupations

/-! # The first excitation in an unrestricted fixed-count sector -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak

open Finset

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Move precisely one particle from the ground mode to the first excited mode. -/
def firstExcitation (n : ℕ) (l q : I) : Boson I (n+1) := combine (pure n l) (pure 1 q)

theorem first_gap (n : ℕ) (l q : I) (e : I → ℝ) :
    read e (firstExcitation n l q) - read e (pure (n+1) l) = e q - e l := by
  simp only [firstExcitation, read_combine, read_pure, Nat.cast_add, Nat.cast_one, one_mul]
  ring

private theorem two_counts (n : ℕ) {l q : I} (hne : l ≠ q) (x : Boson I (n+1))
    (h : ∀ i, i ≠ l → i ≠ q → count x i = 0) : count x l + count x q = n+1 := by
  have eqv : (∑ i ∈ ({l,q} : Finset I), count x i) = ∑ i, count x i :=
    sum_subset (subset_univ _) (fun j _ hj => by
      have hp : j ≠ l ∧ j ≠ q := by simpa only [mem_insert, mem_singleton, not_or] using hj
      exact h j hp.1 hp.2)
  rw [sum_insert (fun hi => hne (mem_singleton.mp hi)), sum_singleton, count_sum] at eqv
  exact eqv

private theorem two_or_more (n : ℕ) {l q : I} (hne : l ≠ q) (x : Boson I (n+1))
    (hu : x ≠ pure (n+1) l) (hv : x ≠ firstExcitation n l q)
    (h : ∀ i, i ≠ l → i ≠ q → count x i = 0) : 2 ≤ count x q := by
  have hs := two_counts n hne x h
  by_contra! ht
  rcases (show count x q = 0 ∨ count x q = 1 by omega) with hq | hq
  · apply hu
    apply state_ext
    intro i
    rw [count_pure]
    by_cases hi : l = i
    · subst i; rw [if_pos rfl]; omega
    · rw [if_neg hi]
      by_cases hj : i = q
      · subst i; exact hq
      · exact h i (Ne.symm hi) hj
  · apply hv
    apply state_ext
    intro i
    simp only [firstExcitation, count_combine, count_pure]
    by_cases hi : l = i
    · subst i; rw [if_pos rfl, if_neg hne.symm]; omega
    · rw [if_neg hi, zero_add]
      by_cases hj : q = i
      · subst i; rw [if_pos rfl]; exact hq
      · rw [if_neg hj]; exact h i (Ne.symm hi) (Ne.symm hj)

/-- Every state other than the ground and the one-particle excitation lies strictly
above the first gap. Either a higher mode is occupied or at least two particles occupy q. -/
theorem above_first_gap (n : ℕ) (e : I → ℝ) (l q : I) (hlq : e l < e q)
    (hrest : ∀ i, i ≠ l → i ≠ q → e q < e i) (x : Boson I (n+1))
    (hu : x ≠ pure (n+1) l) (hv : x ≠ firstExcitation n l q) :
    e q - e l < read e x - read e (pure (n+1) l) := by
  have hne : l ≠ q := fun h => hlq.ne (congrArg e h)
  have nonneg (i : I) : 0 ≤ e i-e l := by
    by_cases h : i = l
    · rw [h, sub_self]
    by_cases hq : i = q
    · rw [hq]; exact sub_nonneg.mpr hlq.le
    exact sub_nonneg.mpr (hlq.trans (hrest i h hq)).le
  have part (i : I) : (count x i : ℝ)*(e i-e l) ≤ read e x - read e (pure (n+1) l) := by
    rw [read_pure, ← read_const x, read, read, ← sum_sub_distrib]
    simpa only [mul_sub] using (single_le_sum (s := univ)
      (f := fun j => (count x j : ℝ)*(e j-e l))
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (nonneg j)) (mem_univ i))
  by_cases high : ∃ i, i ≠ l ∧ i ≠ q ∧ 0 < count x i
  · obtain ⟨i, hil, hiq, hc⟩ := high
    have hc' : (1 : ℝ) ≤ count x i := by exact_mod_cast Nat.succ_le_of_lt hc
    have hm := mul_le_mul_of_nonneg_right hc' (nonneg i)
    rw [one_mul] at hm
    exact (sub_lt_sub_right (hrest i hil hiq) _).trans_le (hm.trans (part i))
  · have z (i : I) (hl : i ≠ l) (hq : i ≠ q) : count x i = 0 := by
      by_contra hh
      exact high ⟨i, hl, hq, Nat.pos_of_ne_zero hh⟩
    have h₂ := two_or_more n hne x hu hv z
    have hc : (1 : ℝ) < count x q := by exact_mod_cast (show 1 < count x q by omega)
    have hm := mul_lt_mul_of_pos_right hc (sub_pos.mpr hlq)
    rw [one_mul] at hm
    exact hm.trans_le (part q)

#print axioms first_gap
#print axioms above_first_gap

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount.Peak
