import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# A symmetric form changes boundedly along a controlled ground direction

Removing the orthogonal component along a unit vector changes a symmetric
quadratic form by at most three times the norm of the operator on that vector,
multiplied by the original squared norm. This transfers estimates from its
orthogonal complement without requiring an operator norm bound.
-/

noncomputable section

open scoped RealInnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A bounded image of one unit direction controls the change of its symmetric form. -/
theorem abs_symmetricForm_sub_groundProjection_le
    (L : E →ₗ[ℝ] E) (hsym : ∀ x y, ⟪L x, y⟫ = ⟪x, L y⟫)
    {e : E} (he : ‖e‖ = 1) {M : ℝ} (hM : ‖L e‖ ≤ M) (x : E) :
    |⟪L x, x⟫ - ⟪L (x - ⟪x, e⟫ • e), x - ⟪x, e⟫ • e⟫| ≤
      3 * M * ‖x‖ ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have ha : |⟪x, e⟫| ≤ ‖x‖ := by
    have h : ‖(⟪x, e⟫ : ℝ)‖ ≤ ‖x‖ * ‖e‖ := norm_inner_le_norm x e
    simpa only [Real.norm_eq_abs, he, mul_one] using h
  have hax : |⟪L e, x⟫| ≤ M * ‖x‖ := by
    have h : ‖(⟪L e, x⟫ : ℝ)‖ ≤ ‖L e‖ * ‖x‖ := norm_inner_le_norm (L e) x
    rw [Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hae : |⟪L e, e⟫| ≤ M := by
    have h : |⟪L e, e⟫| ≤ ‖L e‖ := by
      have hcs : ‖(⟪L e, e⟫ : ℝ)‖ ≤ ‖L e‖ * ‖e‖ := norm_inner_le_norm (L e) e
      simpa only [Real.norm_eq_abs, he, mul_one] using hcs
    exact h.trans hM
  have ha2 : ⟪x, e⟫ ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) ha
  have heq : ⟪L x, x⟫ - ⟪L (x - ⟪x, e⟫ • e), x - ⟪x, e⟫ • e⟫ =
      2 * ⟪x, e⟫ * ⟪L e, x⟫ - ⟪x, e⟫ ^ 2 * ⟪L e, e⟫ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [hsym x e, real_inner_comm x (L e)]
    ring
  rw [heq]
  calc
    _ ≤ 2 * |⟪x, e⟫| * |⟪L e, x⟫| + ⟪x, e⟫ ^ 2 * |⟪L e, e⟫| := by
      have h := abs_sub (2 * ⟪x, e⟫ * ⟪L e, x⟫) (⟪x, e⟫ ^ 2 * ⟪L e, e⟫)
      rw [abs_mul (2 * ⟪x, e⟫) ⟪L e, x⟫, abs_mul (2 : ℝ) ⟪x, e⟫,
        abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_mul (⟪x, e⟫ ^ 2) ⟪L e, e⟫,
        abs_of_nonneg (sq_nonneg (⟪x, e⟫ : ℝ))] at h
      exact h
    _ ≤ 2 * ‖x‖ * (M * ‖x‖) + ‖x‖ ^ 2 * M := by
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hax
          (abs_nonneg _) (by positivity))
        (mul_le_mul ha2 hae (abs_nonneg _) (sq_nonneg _))
    _ = _ := by ring

end GaloisForLFunctions.HTGeometry
