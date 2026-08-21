import GaloisForLFunctions.HTGeometry.BarycentricSubdivision
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.Module.BigOperators

/-!
# The barycentric shrinking estimate

If every pair of vertices of a simplex is at distance at most `D`, then the barycenter is within
`n/(n+1) · D` of each vertex, and indeed within `n/(n+1) · D` of every point of their convex hull.
Iterating, the simplices produced by repeated barycentric subdivision have diameters tending to
zero; combined with the Lebesgue number lemma this is what makes every singular simplex, after
enough subdivisions, small with respect to a given open cover.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The barycenter of a simplex of diameter at most `D` is within `n/(n+1) · D` of each vertex. -/
theorem norm_bary_sub_vertex_le {n : ℕ} {v : Fin (n + 1) → E} {D : ℝ}
    (h : ∀ i j, ‖v i - v j‖ ≤ D) (i : Fin (n + 1)) :
    ‖bary E v - v i‖ ≤ ((n : ℝ) / ((n : ℝ) + 1)) * D := by
  have hD : 0 ≤ D := by simpa using h i i
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hkey : bary E v - v i = (((n : ℝ) + 1)⁻¹) • ∑ j, (v j - v i) := by
    rw [bary, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_sub]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    push_cast
    rw [inv_mul_cancel₀ (ne_of_gt hpos), one_smul]
  have hsum : ‖∑ j, (v j - v i)‖ ≤ (n : ℝ) * D := by
    have hzero : ∑ j, (v j - v i) = ∑ j ∈ univ.erase i, (v j - v i) := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simp
    rw [hzero]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_card_nsmul _ _ D fun j _ => h j i) ?_
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    simp
  rw [hkey, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ((n : ℝ) + 1)⁻¹ * ‖∑ j, (v j - v i)‖
      ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * D) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (n : ℝ) / ((n : ℝ) + 1) * D := by
        field_simp

/-- The barycenter is within `n/(n+1) · D` of every convex combination of the vertices. -/
theorem norm_bary_sub_combination_le {n : ℕ} {v : Fin (n + 1) → E} {D : ℝ}
    (h : ∀ i j, ‖v i - v j‖ ≤ D) (w : Fin (n + 1) → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) :
    ‖bary E v - ∑ i, w i • v i‖ ≤ ((n : ℝ) / ((n : ℝ) + 1)) * D := by
  have hD : 0 ≤ D := by simpa using h 0 0
  have hB : 0 ≤ ((n : ℝ) / ((n : ℝ) + 1)) * D := by positivity
  have hrepr : bary E v - ∑ i, w i • v i = ∑ i, w i • (bary E v - v i) := by
    have : ∑ i, w i • (bary E v - v i) = (∑ i, w i) • bary E v - ∑ i, w i • v i := by
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
    rw [this, hw1, one_smul]
  rw [hrepr]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ i : Fin (n + 1),
      ‖w i • (bary E v - v i)‖ ≤ w i * (((n : ℝ) / ((n : ℝ) + 1)) * D) := by
    intro i
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw i)]
    exact mul_le_mul_of_nonneg_left (norm_bary_sub_vertex_le h i) (hw i)
  refine le_trans (Finset.sum_le_sum fun i _ => hterm i) ?_
  rw [← Finset.sum_mul, hw1, one_mul]

end GaloisForLFunctions.HTGeometry
