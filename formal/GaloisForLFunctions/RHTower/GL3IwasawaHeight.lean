import GaloisForLFunctions.RHTower.GL3UpperHalfSpace

open Matrix

/-!
# Iwasawa coordinates of `g • z` on `h³`

For positive definite `S`, the Iwasawa point `ofPD S` has
`y₁² = (S₁₁S₂₂ − S₁₂²)/S₂₂²` and `(y₁y₂)² = det S / (S₂₂(S₁₁S₂₂ − S₁₂²))` (`ofPD_y1_sq_eq`,
`ofPD_y1y2_sq_eq`); the second is the Schur-complement identity `qe_eq_det`.

With `M = g · mat z` and rows `r₀, r₁, r₂`, the Gram matrix of `g • z` is `MMᵀ`, so
`y₁(g • z)² = ‖r₁ × r₂‖²/‖r₂‖⁴` (`smul_y1_sq`),
`(y₁y₂)(g • z)² = det(g)²(y₁²y₂)²/(‖r₂‖²‖r₁ × r₂‖²)` (`smul_y1y2_sq`),
`x₁(g • z) = ⟨r₁, r₂⟩/‖r₂‖²` and `x₃(g • z) = ⟨r₀, r₂⟩/‖r₂‖²` (`smul_x1`, `smul_x3`).
These are the heights through the bottom row and the bottom Plücker vector used for Poincaré series
and Jacquet integrals.
-/

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

variable {S : Matrix (Fin 3) (Fin 3) ℝ}

theorem qa_eq (hS : S.PosDef) : qa S = (S 1 1 * S 2 2 - S 1 2 ^ 2) / S 2 2 ^ 2 := by
  have hc := (s22_pos hS).ne'
  simp only [qa, nt]; field_simp

theorem qe_eq_det (hS : S.PosDef) :
    qe S = S.det / (S 2 2 * (S 1 1 * S 2 2 - S 1 2 ^ 2)) := by
  have hc := (s22_pos hS).ne'
  have ha := qa_pos hS
  have hD : S 1 1 * S 2 2 - S 1 2 ^ 2 ≠ 0 := by
    intro h0; rw [qa_eq hS, h0, zero_div] at ha; exact lt_irrefl _ ha
  rw [Matrix.det_fin_three]
  rw [symm_of_posDef hS 0 1, symm_of_posDef hS 0 2, symm_of_posDef hS 1 2]
  simp only [qe, qb, qa, nt]
  have hD' : S 1 1 / S 2 2 - (S 1 2 / S 2 2) ^ 2 ≠ 0 := by
    rw [show S 1 1 / S 2 2 - (S 1 2 / S 2 2) ^ 2 = (S 1 1 * S 2 2 - S 1 2 ^ 2) / S 2 2 ^ 2 by
      field_simp]
    exact div_ne_zero hD (pow_ne_zero 2 hc)
  have hD'' : S 2 2 * S 1 1 - S 1 2 ^ 2 ≠ 0 := by rw [mul_comm]; exact hD
  field_simp
  ring

/-- `y₁² = (S₁₁S₂₂ − S₁₂²)/S₂₂²` for the Iwasawa point of `S`. -/
theorem ofPD_y1_sq_eq (hS : S.PosDef) :
    (ofPD S hS).y1 ^ 2 = (S 1 1 * S 2 2 - S 1 2 ^ 2) / S 2 2 ^ 2 := by
  rw [ofPD_y1_sq, qa_eq hS]

/-- `(y₁y₂)² = det S / (S₂₂ (S₁₁S₂₂ − S₁₂²))` for the Iwasawa point of `S`. -/
theorem ofPD_y1y2_sq_eq (hS : S.PosDef) :
    ((ofPD S hS).y1 * (ofPD S hS).y2) ^ 2 = S.det / (S 2 2 * (S 1 1 * S 2 2 - S 1 2 ^ 2)) := by
  rw [ofPD_y1_mul_y2, Real.sq_sqrt (qe_pos hS).le, qe_eq_det hS]

/-! ### Heights of `g • z` through the bottom rows of `g · mat z` -/

/-- Squared norm of the bottom row of `M`. -/
def rowNormSq (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := M 2 0 ^ 2 + M 2 1 ^ 2 + M 2 2 ^ 2

/-- Squared norm of the cross product of the last two rows of `M` (the Plücker vector of the
bottom `2 × 3` block). -/
def crossNormSq (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (M 1 0 * M 2 1 - M 1 1 * M 2 0) ^ 2 + (M 1 0 * M 2 2 - M 1 2 * M 2 0) ^ 2 +
    (M 1 1 * M 2 2 - M 1 2 * M 2 1) ^ 2

theorem mul_transpose_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (M * Mᵀ) i j = M i 0 * M j 0 + M i 1 * M j 1 + M i 2 * M j 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem gram_conj_eq (g : GL (Fin 3) ℝ) (z : H3) :
    (g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat)ᵀ := by
  simp only [gram, Matrix.transpose_mul, Matrix.mul_assoc]

/-- **Height of `g • z` (first coordinate).** With `M = g · mat z`,
`y₁(g • z)² = ‖r₁ × r₂‖² / ‖r₂‖⁴` where `r₁, r₂` are the last two rows of `M`. -/
theorem smul_y1_sq (g : GL (Fin 3) ℝ) (z : H3) :
    (g • z).y1 ^ 2 = crossNormSq ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) /
      rowNormSq ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) ^ 2 := by
  set M := (g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat
  have hS := posDef_conj g z
  rw [smul_def, ofMat_eq hS, ofPD_y1_sq_eq hS, gram_conj_eq]
  simp only [mul_transpose_apply, crossNormSq, rowNormSq]
  congr 1
  · ring
  · ring

/-- **Height of `g • z` (product).** `(y₁y₂)(g • z)² = det(g)² (y₁²y₂)² / (‖r₂‖² ‖r₁ × r₂‖²)`. -/
theorem smul_y1y2_sq (g : GL (Fin 3) ℝ) (z : H3) :
    ((g • z).y1 * (g • z).y2) ^ 2 = ((g : Matrix (Fin 3) (Fin 3) ℝ).det * (z.y1 ^ 2 * z.y2)) ^ 2 /
      (rowNormSq ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) *
        crossNormSq ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat)) := by
  set M := (g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat
  have hS := posDef_conj g z
  rw [smul_def, ofMat_eq hS, ofPD_y1y2_sq_eq hS, gram_conj_eq]
  have hdet : (M * Mᵀ).det = ((g : Matrix (Fin 3) (Fin 3) ℝ).det * (z.y1 ^ 2 * z.y2)) ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_mul, det_mat]; ring
  rw [hdet]
  simp only [mul_transpose_apply, crossNormSq, rowNormSq]
  congr 1
  ring

/-- The first horizontal coordinate: `x₁(g • z) = ⟨r₁, r₂⟩ / ‖r₂‖²`. -/
theorem smul_x1 (g : GL (Fin 3) ℝ) (z : H3) :
    (g • z).x1 = (((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 1 0 * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 2 0 +
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 1 1 * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 2 1 +
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 1 2 * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 2 2) /
      rowNormSq ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) := by
  have hS := posDef_conj g z
  rw [smul_def, ofMat_eq hS]
  simp only [ofPD, nt]
  rw [gram_conj_eq]
  simp only [mul_transpose_apply, rowNormSq]
  congr 1
  ring

/-- The corner coordinate: `x₃(g • z) = ⟨r₀, r₂⟩ / ‖r₂‖²`. -/
theorem smul_x3 (g : GL (Fin 3) ℝ) (z : H3) :
    (g • z).x3 = (((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 0 0 * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 2 0 +
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 0 1 * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 2 1 +
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 0 2 * ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) 2 2) /
      rowNormSq ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.mat) := by
  have hS := posDef_conj g z
  rw [smul_def, ofMat_eq hS]
  simp only [ofPD, nt]
  rw [gram_conj_eq]
  simp only [mul_transpose_apply, rowNormSq]
  congr 1
  ring

end H3
end GaloisForLFunctions.RHTower.GL3
