import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Weighted norm domination bounds dimension

A linear map dominating a strictly positive diagonal quadratic form has
trivial kernel, so its codomain dimension bounds the number of coordinates.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- A map dominating a strictly positive diagonal norm is injective, hence
its target has at least as many coordinates. -/
theorem card_le_of_weighted_norm_sq_le {J : Type*} [Fintype J] {m : ℕ}
    (w : J → ℝ) (hw : ∀ j, 0 < w j)
    (T : (J → ℂ) →ₗ[ℂ] (Fin m → ℂ))
    (h : ∀ c, (∑ j, w j * ‖c j‖ ^ 2) ≤ ∑ i, ‖T c i‖ ^ 2) :
    Fintype.card J ≤ m := by
  classical
  have hker (c : J → ℂ) (hc : T c = 0) : c = 0 := by
    have hsum : (∑ j, w j * ‖c j‖ ^ 2) ≤ 0 := by
      simpa only [hc, Pi.zero_apply, norm_zero, zero_pow two_ne_zero, sum_const_zero] using h c
    funext j
    have hj : w j * ‖c j‖ ^ 2 ≤ 0 :=
      (single_le_sum (fun i _ => mul_nonneg (hw i).le (sq_nonneg ‖c i‖)) (mem_univ j)).trans hsum
    have hz : w j * ‖c j‖ ^ 2 = 0 :=
      le_antisymm hj (mul_nonneg (hw j).le (sq_nonneg _))
    have hsq : ‖c j‖ ^ 2 = 0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw j))
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have hinj : Function.Injective T := by
    intro a b hab
    exact sub_eq_zero.mp (hker (a - b) (by rw [map_sub, hab, sub_self]))
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

end GaloisForLFunctions.HTGeometry
