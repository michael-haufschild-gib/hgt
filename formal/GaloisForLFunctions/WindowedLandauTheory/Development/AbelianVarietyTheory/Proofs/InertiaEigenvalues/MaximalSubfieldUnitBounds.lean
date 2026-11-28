import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! The sum of the orders of the maximal proper subfield unit groups
is small compared with the full multiplicative group. -/

open Finset

namespace GlobalTheory.EllipticCharacters

def properSubfieldUnitBound (g n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1)

private theorem geom (g : ℕ) (hg : 2 ≤ g) (M : ℕ) : ∑ d ∈ range (M + 1), g ^ d ≤ 2 * g ^ M := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linarith [ih, Nat.mul_le_mul_left (g ^ k) hg]

private theorem properSubfieldUnitBound_le_geometric (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n) : properSubfieldUnitBound g n ≤ 2 * g ^ (n / 2) := by
  unfold properSubfieldUnitBound
  have hsub : ∑ p ∈ n.primeFactors, (g ^ (n / p) - 1) ≤ ∑ p ∈ n.primeFactors, g ^ (n / p) :=
    Finset.sum_le_sum fun p _ => Nat.sub_le _ _
  have hinj : Set.InjOn (fun p => n / p) (n.primeFactors : Set ℕ) := by
    intro p hp q hq hpq
    have hp' := Nat.dvd_of_mem_primeFactors hp
    have hq' := Nat.dvd_of_mem_primeFactors hq
    simp only at hpq
    rw [← Nat.div_div_self hp' hn.ne', hpq, Nat.div_div_self hq' hn.ne']
  have himg : ∑ p ∈ n.primeFactors, g ^ (n / p)
      = ∑ d ∈ n.primeFactors.image (fun p => n / p), g ^ d :=
    (Finset.sum_image hinj).symm
  have hsubset : n.primeFactors.image (fun p => n / p) ⊆ range (n / 2 + 1) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.div_le_div_left (Nat.prime_of_mem_primeFactors hp).two_le (by norm_num)
  calc _ ≤ _ := hsub
    _ = _ := himg
    _ ≤ ∑ d ∈ range (n / 2 + 1), g ^ d := Finset.sum_le_sum_of_subset hsubset
    _ ≤ 2 * g ^ (n / 2) := geom g hg (n / 2)

private theorem two_pow (m : ℕ) (hm : 6 ≤ m) : 8 * m + 1 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ]
    omega

private theorem bound_of_degree_ge_twelve (g n : ℕ) (hg : 2 ≤ g) (hn : 12 ≤ n) : 2 * n * properSubfieldUnitBound g n + 1 < g ^ n := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hm : 6 ≤ m := by omega
    have hb := properSubfieldUnitBound_le_geometric g (2 * m) hg (by omega)
    rw [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] at hb
    have hA : 8 * m + 1 ≤ g ^ m := le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)
    have hp : g ^ (2 * m) = g ^ m * g ^ m := by rw [two_mul, pow_add]
    rw [hp]
    generalize properSubfieldUnitBound g (2 * m) = B at hb ⊢
    generalize g ^ m = A at hA hb ⊢
    nlinarith [Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA]
  · have hm : 6 ≤ m := by omega
    have hb := properSubfieldUnitBound_le_geometric g (2 * m + 1) hg (by omega)
    have hd : (2 * m + 1) / 2 = m := by omega
    rw [hd] at hb
    have hA : 8 * m + 1 ≤ g ^ m := le_trans (two_pow m hm) (Nat.pow_le_pow_left hg m)
    have hp : g ^ (2 * m + 1) = g ^ m * g ^ m * g := by rw [pow_succ, two_mul, pow_add]
    rw [hp]
    generalize properSubfieldUnitBound g (2 * m + 1) = B at hb ⊢
    generalize g ^ m = A at hA hb ⊢
    nlinarith [Nat.mul_le_mul_left m hb, Nat.mul_le_mul_left A hA, Nat.mul_le_mul_left (A * A) hg,
      Nat.mul_le_mul_right A hm]

private theorem pf2 : Nat.primeFactors 2 = {2} := by
  simp [Nat.prime_two]
private theorem pf3 : Nat.primeFactors 3 = {3} := by
  simp [Nat.prime_three]
private theorem pf4 : Nat.primeFactors 4 = {2} :=
  Nat.primeFactors_prime_pow (by omega : (2 : ℕ) ≠ 0) Nat.prime_two
private theorem pf5 : Nat.primeFactors 5 = {5} := by
  simp [Nat.prime_five]
private theorem pf6 : Nat.primeFactors 6 = {2, 3} := by
  change (2 * 3).primeFactors = {2, 3}
  rw [Nat.primeFactors_mul (by omega) (by omega), pf2, pf3]
  rfl
private theorem pf7 : Nat.primeFactors 7 = {7} := by
  simp [Nat.prime_seven]
private theorem pf8 : Nat.primeFactors 8 = {2} :=
  Nat.primeFactors_prime_pow (by omega : (3 : ℕ) ≠ 0) Nat.prime_two
private theorem pf9 : Nat.primeFactors 9 = {3} :=
  Nat.primeFactors_prime_pow (by omega : (2 : ℕ) ≠ 0) Nat.prime_three
private theorem pf10 : Nat.primeFactors 10 = {2, 5} := by
  change (2 * 5).primeFactors = {2, 5}
  rw [Nat.primeFactors_mul (by omega) (by omega), pf2, pf5]
  rfl
private theorem pf11 : Nat.primeFactors 11 = {11} := by
  simp [Nat.prime_eleven]

private theorem bd_two (g : ℕ) : properSubfieldUnitBound g 2 = g - 1 := by simp [properSubfieldUnitBound, pf2]
private theorem bd_three (g : ℕ) : properSubfieldUnitBound g 3 = g - 1 := by simp [properSubfieldUnitBound, pf3]
private theorem bd_four (g : ℕ) : properSubfieldUnitBound g 4 = g ^ 2 - 1 := by simp [properSubfieldUnitBound, pf4]
private theorem bd_five (g : ℕ) : properSubfieldUnitBound g 5 = g - 1 := by simp [properSubfieldUnitBound, pf5]
private theorem bd_six (g : ℕ) : properSubfieldUnitBound g 6 = (g ^ 3 - 1) + (g ^ 2 - 1) := by simp [properSubfieldUnitBound, pf6]
private theorem bd_seven (g : ℕ) : properSubfieldUnitBound g 7 = g - 1 := by simp [properSubfieldUnitBound, pf7]
private theorem bd_eight (g : ℕ) : properSubfieldUnitBound g 8 = g ^ 4 - 1 := by simp [properSubfieldUnitBound, pf8]
private theorem bd_nine (g : ℕ) : properSubfieldUnitBound g 9 = g ^ 3 - 1 := by simp [properSubfieldUnitBound, pf9]
private theorem bd_ten (g : ℕ) : properSubfieldUnitBound g 10 = (g ^ 5 - 1) + (g ^ 2 - 1) := by simp [properSubfieldUnitBound, pf10]
private theorem bd_eleven (g : ℕ) : properSubfieldUnitBound g 11 = g - 1 := by simp [properSubfieldUnitBound, pf11]

private theorem cast_pred (h c k : ℕ) (hc : 1 ≤ c) : (((h + c) ^ k - 1 : ℕ) : ℤ) = ((h : ℤ) + c) ^ k - 1 := by
  have h1 : 1 ≤ (h + c) ^ k := Nat.one_le_pow _ _ (by omega)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_add, Nat.cast_one]

private theorem cast_pred1 (h c : ℕ) (hc : 1 ≤ c) : (((h + c) - 1 : ℕ) : ℤ) = ((h : ℤ) + c) - 1 := by
  rw [Nat.cast_sub (by omega : 1 ≤ h + c), Nat.cast_add, Nat.cast_one]

private theorem t2 (h : ℕ) : 2 * 2 * properSubfieldUnitBound (h + 4) 2 + 1 < (h + 4) ^ 2 := by
  rw [bd_two]
  have e0 := cast_pred1 h 4 (by norm_num)
  have key : ((2 * 2 * ((h + 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 4) ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t3 (h : ℕ) : 2 * 3 * properSubfieldUnitBound (h + 2) 3 + 1 < (h + 2) ^ 3 := by
  rw [bd_three]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 3 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 3 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t4 (h : ℕ) : 2 * 4 * properSubfieldUnitBound (h + 3) 4 + 1 < (h + 3) ^ 4 := by
  rw [bd_four]
  have e0 := cast_pred h 3 2 (by norm_num)
  have key : ((2 * 4 * (((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 4 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t5 (h : ℕ) : 2 * 5 * properSubfieldUnitBound (h + 2) 5 + 1 < (h + 2) ^ 5 := by
  rw [bd_five]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 5 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 5 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t6 (h : ℕ) : 2 * 6 * properSubfieldUnitBound (h + 3) 6 + 1 < (h + 3) ^ 6 := by
  rw [bd_six]
  have e0 := cast_pred h 3 3 (by norm_num)
  have e1 := cast_pred h 3 2 (by norm_num)
  have key : ((2 * 6 * (((h + 3) ^ 3 - 1) + ((h + 3) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 3) ^ 6 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t7 (h : ℕ) : 2 * 7 * properSubfieldUnitBound (h + 2) 7 + 1 < (h + 2) ^ 7 := by
  rw [bd_seven]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 7 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 7 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t8 (h : ℕ) : 2 * 8 * properSubfieldUnitBound (h + 2) 8 + 1 < (h + 2) ^ 8 := by
  rw [bd_eight]
  have e0 := cast_pred h 2 4 (by norm_num)
  have key : ((2 * 8 * (((h + 2) ^ 4 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 8 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t9 (h : ℕ) : 2 * 9 * properSubfieldUnitBound (h + 2) 9 + 1 < (h + 2) ^ 9 := by
  rw [bd_nine]
  have e0 := cast_pred h 2 3 (by norm_num)
  have key : ((2 * 9 * (((h + 2) ^ 3 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 9 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t10 (h : ℕ) : 2 * 10 * properSubfieldUnitBound (h + 2) 10 + 1 < (h + 2) ^ 10 := by
  rw [bd_ten]
  have e0 := cast_pred h 2 5 (by norm_num)
  have e1 := cast_pred h 2 2 (by norm_num)
  have key : ((2 * 10 * (((h + 2) ^ 5 - 1) + ((h + 2) ^ 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 10 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_add, e0, e1]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

private theorem t11 (h : ℕ) : 2 * 11 * properSubfieldUnitBound (h + 2) 11 + 1 < (h + 2) ^ 11 := by
  rw [bd_eleven]
  have e0 := cast_pred1 h 2 (by norm_num)
  have key : ((2 * 11 * ((h + 2 - 1)) + 1 : ℕ) : ℤ) < (((h + 2) ^ 11 : ℕ) : ℤ) := by
    rw [Nat.cast_add, Nat.cast_mul, e0]
    push_cast
    rw [← sub_pos]
    ring_nf
    positivity
  exact Nat.cast_lt.mp key

theorem two_mul_degree_mul_properSubfieldBound_lt (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n)
    (hex : ¬ ((g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6))) :
    2 * n * properSubfieldUnitBound g n + 1 < g ^ n := by
  rcases le_or_gt 12 n with h12 | h12
  · exact bound_of_degree_ge_twelve g n hg h12
  · interval_cases n
    · simp [properSubfieldUnitBound]
      omega
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 4 := ⟨g - 4, by omega⟩
      exact t2 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t3 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 3 := ⟨g - 3, by omega⟩
      exact t4 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t5 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 3 := ⟨g - 3, by omega⟩
      exact t6 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t7 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t8 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t9 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t10 k
    · obtain ⟨k, rfl⟩ : ∃ k, g = k + 2 := ⟨g - 2, by omega⟩
      exact t11 k

theorem degree_mul_properSubfieldBound_lt (g n : ℕ) (hg : 2 ≤ g) (hn : 0 < n) : n * properSubfieldUnitBound g n + 1 < g ^ n := by
  by_cases hex : (g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6)
  · rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [bd_two]
      norm_num
    · rw [bd_two]
      norm_num
    · rw [bd_four]
      norm_num
    · rw [bd_six]
      norm_num
  · have h2 := two_mul_degree_mul_properSubfieldBound_lt g n hg hn hex
    linarith [Nat.mul_le_mul_right (properSubfieldUnitBound g n) (show n ≤ 2 * n by omega)]

/-- An exponent divisible by every proper subfield unit-group order
in each of the four cases where the general support bound is too weak. -/
theorem exceptional_twistExponent (g n : ℕ)
    (he : (g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6)) :
    ∃ e : ℕ, (∀ p ∈ n.primeFactors, g ^ (n / p) - 1 ∣ e) ∧
      (¬ ((g ^ n - 1) / Nat.gcd (g ^ n - 1) e ∣ n) ∨
        (g = 2 ∧ n = 6 ∧ (g ^ n - 1) / Nat.gcd (g ^ n - 1) e = 3)) := by
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨1, by simp [pf2], Or.inl (by norm_num)⟩
  · refine ⟨2, by simp [pf2], Or.inl ?_⟩
    change ¬ (8 / Nat.gcd 8 2 ∣ 2)
    rw [Nat.gcd_eq_right (show 2 ∣ 8 from ⟨4, rfl⟩)]
    omega
  · refine ⟨3, by simp [pf4], Or.inl ?_⟩
    change ¬ (15 / Nat.gcd 15 3 ∣ 4)
    rw [Nat.gcd_eq_right (show 3 ∣ 15 from ⟨5, rfl⟩)]
    omega
  · refine ⟨21, ?_, Or.inr ⟨rfl, rfl, ?_⟩⟩
    · intro p hp
      simp only [pf6, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl <;> norm_num
    · change 63 / Nat.gcd 63 21 = 3
      rw [Nat.gcd_eq_right (show 21 ∣ 63 from ⟨3, rfl⟩)]

end GlobalTheory.EllipticCharacters
