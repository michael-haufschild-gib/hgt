import GaloisForLFunctions.HTGeometry.RatFuncShiftDegree

/-!
# Degree calculus for the unit shift on rational functions

Bookkeeping lemmas for the degree at infinity: the shift preserves it, a sum is bounded by the
larger summand, a strictly dominant summand fixes it, and the shift difference always drops it by
one — by two when the degree is zero and the function is not constant.  The "zero or bounded" shape
is used throughout, because `intDegree 0 = 0` is larger than a negative degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

theorem intDegree_ratShift (f : RatFunc ℂ) : (ratShift f).intDegree = f.intDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  have hpS : f.num.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hp
  have hqS : f.denom.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hsh : ratShift f = algebraMap ℂ[X] (RatFunc ℂ) (f.num.comp (X + C 1))
      / algebraMap ℂ[X] (RatFunc ℂ) (f.denom.comp (X + C 1)) := by
    rw [eq_div_iff (algebraMap_poly_ne_zero hqS)]
    exact ratShift_mul_denom_comp f
  rw [hsh, intDegree_algebraMap_div hpS hqS, natDegree_comp_X_add_one, natDegree_comp_X_add_one]
  rfl

theorem intDegree_algebraMap_complex (κ : ℂ) :
    (algebraMap ℂ (RatFunc ℂ) κ).intDegree = 0 := by
  rw [← algebraMap_polyC, RatFunc.intDegree_polynomial, Polynomial.natDegree_C]
  rfl

theorem intDegree_add_le_of_le {x y : RatFunc ℂ} {t : ℤ}
    (hx : x = 0 ∨ x.intDegree ≤ t) (hy : y = 0 ∨ y.intDegree ≤ t) :
    x + y = 0 ∨ (x + y).intDegree ≤ t := by
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · left; simp
    · right; simpa using hy
  · rcases hy with rfl | hy
    · right; simpa using hx
    · rcases eq_or_ne y 0 with rfl | hy0
      · right; simpa using hx
      · rcases eq_or_ne (x + y) 0 with h | h
        · left; exact h
        · right
          exact le_trans (RatFunc.intDegree_add_le hy0 h) (max_le hx hy)

theorem intDegree_mul_le_of_le {b x : RatFunc ℂ} {t : ℤ} (hb : b ≠ 0)
    (hx : x = 0 ∨ x.intDegree ≤ t) :
    b * x = 0 ∨ (b * x).intDegree ≤ b.intDegree + t := by
  rcases hx with rfl | hx
  · left; simp
  · rcases eq_or_ne x 0 with rfl | hx0
    · left; simp
    · right
      rw [RatFunc.intDegree_mul hb hx0]
      omega

theorem intDegree_add_eq_left {u v : RatFunc ℂ} (hu : u ≠ 0)
    (hlt : v = 0 ∨ v.intDegree < u.intDegree) :
    u + v ≠ 0 ∧ (u + v).intDegree = u.intDegree := by
  rcases hlt with rfl | hlt
  · simpa using hu
  have hne : u + v ≠ 0 := by
    intro h
    have huv : u = -v := by linear_combination h
    rw [huv, RatFunc.intDegree_neg] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hne, le_antisymm ?_ ?_⟩
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact le_trans (RatFunc.intDegree_add_le hv hne) (max_le le_rfl hlt.le)
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have h2 : u = (u + v) + (-v) := by ring
      have hvneg : (-v) ≠ 0 := neg_ne_zero.mpr hv
      have hsum : (u + v) + (-v) ≠ 0 := by rw [← h2]; exact hu
      have hbnd := RatFunc.intDegree_add_le hvneg hsum
      rw [← h2, RatFunc.intDegree_neg] at hbnd
      rcases max_cases (u + v).intDegree v.intDegree with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm] at hbnd; exact hbnd
      · rw [hm] at hbnd; exact absurd (lt_of_le_of_lt hbnd hlt) (lt_irrefl _)

/-- The shift difference drops the degree at infinity by at least one. -/
theorem ratShift_sub_le (f : RatFunc ℂ) :
    ratShift f - f = 0 ∨ (ratShift f - f).intDegree ≤ f.intDegree - 1 := by
  rcases eq_or_ne (ratShift f) f with h | h
  · left; rw [h, sub_self]
  rcases eq_or_ne f 0 with rfl | hf
  · left; simp
  rcases eq_or_ne f.intDegree 0 with h0 | h0
  · obtain ⟨-, hb⟩ := intDegree_ratShift_sub_le_of_intDegree_zero h0 h
    right; omega
  · obtain ⟨-, hb⟩ := intDegree_ratShift_sub hf h0
    right; omega

/-- Twice-shifted difference. -/
theorem ratShift_two_sub_le (f : RatFunc ℂ) :
    ratShift (ratShift f) - f = 0 ∨
      (ratShift (ratShift f) - f).intDegree ≤ f.intDegree - 1 := by
  have hsplit : ratShift (ratShift f) - f
      = (ratShift (ratShift f) - ratShift f) + (ratShift f - f) := by ring
  have h1 : ratShift (ratShift f) - ratShift f = 0 ∨
      (ratShift (ratShift f) - ratShift f).intDegree ≤ f.intDegree - 1 := by
    have := ratShift_sub_le (ratShift f)
    rwa [intDegree_ratShift f] at this
  have h2 := ratShift_sub_le f
  rw [hsplit]
  exact intDegree_add_le_of_le h1 h2

end

end GaloisForLFunctions.HTGeometry
