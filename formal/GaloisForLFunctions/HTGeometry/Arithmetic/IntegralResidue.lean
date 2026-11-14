import GaloisForLFunctions.HTGeometry.RationalTameData
import GaloisForLFunctions.HTGeometry.Arithmetic.IntegralTests
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationSums

/-!
# Residues of integral rationals

The rational residue map preserves addition and multiplication whenever
its arguments are integral at the chosen prime. This extends reduction
from units to the whole local ring, including elements with zero residue.
Finite sums and products can consequently be reduced term by term.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

theorem den_residue_ne_zero_of_integral {q : ℚ} (hq : 0 ≤ padicValRat p q) :
    (q.den : ZMod p) ≠ 0 := by
  rw [Ne, den_zmod_eq_zero_iff]
  exact (nonneg_val_iff_not_dvd_den p q).mp hq

@[simp] theorem ratRes_zero : ratRes p (0 : ℚ) = 0 := by simp [ratRes]

theorem ratRes_eq_zero_of_val_pos {q : ℚ} (hq : 0 < padicValRat p q) :
    ratRes p q = 0 := by
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  have hnum := (props_of_padicValRat_pos hq0 hq).1
  simp only [ratRes, hnum, zero_div]

theorem val_eq_zero_of_ratRes_ne_zero {q : ℚ} (hq : ratRes p q ≠ 0) :
    padicValRat p q = 0 :=
  (padicValRat_eq_zero_iff (isPadicUnit_of_ratRes_ne_zero hq).ne_zero).mpr
    (isPadicUnit_of_ratRes_ne_zero hq)

theorem val_add_nonneg {q r : ℚ} (hq : 0 ≤ padicValRat p q)
    (hr : 0 ≤ padicValRat p r) : 0 ≤ padicValRat p (q + r) := by
  by_cases hs : q + r = 0
  · simp [hs]
  exact (le_min hq hr).trans (padicValRat.min_le_padicValRat_add hs)

theorem val_mul_nonneg {q r : ℚ} (hq : 0 ≤ padicValRat p q)
    (hr : 0 ≤ padicValRat p r) : 0 ≤ padicValRat p (q * r) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  by_cases hr0 : r = 0
  · simp [hr0]
  rw [padicValRat.mul hq0 hr0]
  exact add_nonneg hq hr

/-- Reduction respects multiplication of all integral rationals. -/
theorem ratRes_mul_integral {q r : ℚ} (hq : 0 ≤ padicValRat p q)
    (hr : 0 ≤ padicValRat p r) : ratRes p (q * r) = ratRes p q * ratRes p r := by
  have hqd := den_residue_ne_zero_of_integral hq
  have hrd := den_residue_ne_zero_of_integral hr
  have hden : (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero hqd hrd
  have hpres : q * r = ((q.num * r.num : ℤ) : ℚ) /
      (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [num_eq_mul_den q, num_eq_mul_den r]
    field_simp
  rw [ratRes_of_eq_div hden hpres]
  simp only [ratRes]
  push_cast
  rw [div_mul_div_comm]

/-- Reduction respects addition even when the residues cancel. -/
theorem ratRes_add_integral {q r : ℚ} (hq : 0 ≤ padicValRat p q)
    (hr : 0 ≤ padicValRat p r) : ratRes p (q + r) = ratRes p q + ratRes p r := by
  have hqd := den_residue_ne_zero_of_integral hq
  have hrd := den_residue_ne_zero_of_integral hr
  have hden : (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact mul_ne_zero hqd hrd
  have hpres : q + r = ((q.num * (r.den : ℤ) + r.num * (q.den : ℤ) : ℤ) : ℚ) /
      (((q.den : ℤ) * (r.den : ℤ) : ℤ) : ℚ) := by
    push_cast
    rw [num_eq_mul_den q, num_eq_mul_den r]
    field_simp
  rw [ratRes_of_eq_div hden hpres]
  simp only [ratRes]
  push_cast
  field_simp

theorem ratRes_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ padicValRat p (f i)) :
    ratRes p (∑ i ∈ s, f i) = ∑ i ∈ s, ratRes p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hrest : ∀ i ∈ s, 0 ≤ padicValRat p (f i) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      ratRes_add_integral (hf a (Finset.mem_insert_self a s))
        (val_finset_sum_nonneg s f hrest), ih hrest]

theorem val_finset_prod_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ padicValRat p (f i)) :
    0 ≤ padicValRat p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact val_mul_nonneg (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem ratRes_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, 0 ≤ padicValRat p (f i)) :
    ratRes p (∏ i ∈ s, f i) = ∏ i ∈ s, ratRes p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, ratRes_one]
  | @insert a s ha ih =>
    have hrest : ∀ i ∈ s, 0 ≤ padicValRat p (f i) :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      ratRes_mul_integral (hf a (Finset.mem_insert_self a s))
        (val_finset_prod_nonneg s f hrest), ih hrest]

#print axioms ratRes_add_integral
#print axioms ratRes_finset_prod

end GaloisForLFunctions.HTGeometry.Arithmetic
