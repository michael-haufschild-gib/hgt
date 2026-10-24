import GaloisForLFunctions.ArithmeticLocalDivisorGeometry.LocalFactors

/-!
# Exact coefficient transitions at central divisor points

Central zero factors shift coefficient indices. Positive scalar normalizations preserve every
coefficient sign. Both operations are reversible on the coefficient cone, including its boundary.
-/

open Polynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticLocalDivisorGeometry

noncomputable section

/-- Central multiplicity shifts coefficient indices without changing their signs. -/
theorem coeffNonneg_mul_X_pow_iff (p : ℝ[X]) (a : ℕ) :
    CoeffNonneg (p * X ^ a) ↔ CoeffNonneg p := by
  constructor
  · intro h n
    simpa only [coeff_mul_X_pow] using h (n + a)
  · intro h n
    rw [coeff_mul_X_pow']
    split_ifs
    · exact h _
    · exact le_rfl

theorem coeffNonneg_X_pow_mul_iff (p : ℝ[X]) (a : ℕ) :
    CoeffNonneg (X ^ a * p) ↔ CoeffNonneg p := by
  rw [mul_comm, coeffNonneg_mul_X_pow_iff]

/-- Positive scalar normalizations are harmless even when individual coefficients vanish. -/
theorem coeffNonneg_C_mul_iff (p : ℝ[X]) {c : ℝ} (hc : 0 < c) :
    CoeffNonneg (C c * p) ↔ CoeffNonneg p := by
  change (∀ n, 0 ≤ (C c * p).coeff n) ↔ ∀ n, 0 ≤ p.coeff n
  simp only [coeff_C_mul, mul_nonneg_iff_of_pos_left hc]

/-- A positive normalization and any central multiplicity can be removed together. -/
theorem coeffNonneg_positive_monomial_mul_iff (p : ℝ[X]) (a : ℕ) {c : ℝ} (hc : 0 < c) :
    CoeffNonneg ((C c * X ^ a) * p) ↔ CoeffNonneg p := by
  rw [mul_assoc, coeffNonneg_C_mul_iff _ hc, coeffNonneg_X_pow_mul_iff]

/-- Changing the unit of squared displacement by a positive amount preserves every sign. -/
theorem coeffNonneg_positive_rescale_iff (p : ℝ[X]) {r : ℝ} (hr : 0 < r) :
    CoeffNonneg (p.comp (C r * X)) ↔ CoeffNonneg p := by
  change (∀ n, 0 ≤ (p.comp (C r * X)).coeff n) ↔ ∀ n, 0 ≤ p.coeff n
  simp only [comp_C_mul_X_coeff, mul_nonneg_iff_of_pos_right (pow_pos hr _)]

/-- A nonzero coefficient-positive polynomial is strictly positive away from the origin. -/
theorem eval_pos_of_coeffNonneg {p : ℝ[X]} (hp : p ≠ 0) (h : CoeffNonneg p)
    {y : ℝ} (hy : 0 < y) : 0 < p.eval y := by
  rw [eval_eq_sum_range]
  apply Finset.sum_pos'
  · intro i hi
    exact mul_nonneg (h i) (pow_pos hy i).le
  · refine ⟨p.natDegree, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    have hc : p.coeff p.natDegree ≠ 0 := by
      simpa only [coeff_natDegree] using (leadingCoeff_ne_zero.mpr hp)
    exact mul_pos (lt_of_le_of_ne (h _) (Ne.symm hc)) (pow_pos hy _)

theorem pairFactor_ne_zero (u δ : ℝ) : pairFactor u δ ≠ 0 := by
  intro h
  have hc := congrArg (fun p : ℝ[X] => p.coeff 2) h
  simp only [pairFactor, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at hc
  norm_num at hc

/-- At its own ordinate an off-line pair has a positive root in squared displacement.
No nonzero polynomial multiplier can put that factor into the coefficient cone. -/
theorem coeffNonneg_pairFactor_at_center_mul_iff (δ : ℝ) (p : ℝ[X]) :
    CoeffNonneg (pairFactor 0 δ * p) ↔ p = 0 ∨ (δ = 0 ∧ CoeffNonneg p) := by
  by_cases hp : p = 0
  · subst p
    simp only [mul_zero, true_or, iff_true]
    intro n
    simp
  by_cases hδ : δ = 0
  · subst δ
    have hfactor : pairFactor 0 0 = (X : ℝ[X]) ^ 2 := by simp [pairFactor]
    simp only [hfactor, coeffNonneg_X_pow_mul_iff, hp, false_or, true_and]
  · constructor
    · intro h
      have hy : 0 < δ ^ 2 := by positivity
      have he := eval_pos_of_coeffNonneg (mul_ne_zero (pairFactor_ne_zero 0 δ) hp) h hy
      have hz : (pairFactor 0 δ * p).eval (δ ^ 2) = 0 := by
        simp only [eval_mul, pairFactor, eval_add, eval_pow, eval_X, eval_C]
        ring
      rw [hz] at he
      exact (lt_irrefl 0 he).elim
    · rintro (h | ⟨h, _⟩)
      · exact (hp h).elim
      · exact (hδ h).elim

end

end GaloisForLFunctions.ArithmeticLocalDivisorGeometry
