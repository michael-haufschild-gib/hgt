import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Planar conductivity duality and coercive nonsymmetric examples

The rotational inverse in Ming–Yu's Lemma 3.1
(https://arxiv.org/abs/2611.17054) is the transpose divided by the determinant.
Adding an arbitrary skew planar field to `I + AᵀA` preserves its coercive
quadratic form. Its determinant has an explicit sum-of-squares decomposition,
so both the inverse and its rotational dual exist for every parameter value.
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace HTGeometry.PlanarConductivityDuality

abbrev Mat := Matrix (Fin 2) (Fin 2) ℝ

/-- Counterclockwise quarter-turn in the plane. -/
def quarterTurn : Mat := !![0, -1; 1, 0]

/-- The planar dual conductivity. -/
noncomputable def dual (B : Mat) : Mat := -quarterTurn * B⁻¹ * quarterTurn

/-- Rotational inversion in dimension two is normalized transposition. -/
theorem dual_eq (B : Mat) : dual B = B.det⁻¹ • Bᵀ := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [dual, quarterTurn, Matrix.inv_def, Ring.inverse_eq_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- A coercive symmetric Gram part with an unrestricted skew perturbation. -/
def conductivity (A : Mat) (t : ℝ) : Mat := 1 + Aᵀ * A + t • quarterTurn

/-- The skew perturbation contributes no quadratic energy. -/
theorem conductivity_energy (A : Mat) (t : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ ((conductivity A t) *ᵥ x) =
      (x 0)^2 + (x 1)^2 + ((A *ᵥ x) 0)^2 + ((A *ᵥ x) 1)^2 := by
  simp [conductivity, quarterTurn, dotProduct, Matrix.mulVec, Matrix.mul_apply,
    Fin.sum_univ_two, pow_two]
  ring

/-- Coercivity is uniform in both the Gram matrix and the skew perturbation. -/
theorem conductivity_coercive (A : Mat) (t : ℝ) (x : Fin 2 → ℝ) :
    (x 0)^2 + (x 1)^2 ≤ x ⬝ᵥ ((conductivity A t) *ᵥ x) := by
  rw [conductivity_energy]
  nlinarith only [sq_nonneg ((A *ᵥ x) 0), sq_nonneg ((A *ᵥ x) 1)]

/-- The determinant separates the Gram energy, oriented area, and skew energy. -/
theorem conductivity_det (A : Mat) (t : ℝ) :
    (conductivity A t).det =
      1 + (A 0 0)^2 + (A 0 1)^2 + (A 1 0)^2 + (A 1 1)^2 + A.det^2 + t^2 := by
  simp [conductivity, quarterTurn, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring

theorem conductivity_det_pos (A : Mat) (t : ℝ) : 0 < (conductivity A t).det := by
  rw [conductivity_det]
  positivity

/-- Transposition reverses the skew field and leaves the coercive part unchanged. -/
theorem conductivity_transpose (A : Mat) (t : ℝ) :
    (conductivity A t)ᵀ = conductivity A (-t) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [conductivity, quarterTurn, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

/-- The dual of every Gram-plus-skew conductivity is explicit and nonsingular. -/
theorem dual_conductivity (A : Mat) (t : ℝ) :
    dual (conductivity A t) = (conductivity A t).det⁻¹ • conductivity A (-t) := by
  rw [dual_eq, conductivity_transpose]

/-- The determinant is inverted by planar duality, including singular matrices. -/
theorem det_dual (B : Mat) : (dual B).det = B.det⁻¹ := by
  rw [dual_eq, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin]
  by_cases h : B.det = 0
  · simp [h]
  · field_simp

/-- Duality is involutive on every Gram-plus-skew conductivity. -/
theorem dual_dual_conductivity (A : Mat) (t : ℝ) :
    dual (dual (conductivity A t)) = conductivity A t := by
  rw [dual_eq, det_dual, inv_inv, dual_eq, Matrix.transpose_smul,
    Matrix.transpose_transpose, smul_smul,
    mul_inv_cancel₀ (conductivity_det_pos A t).ne', one_smul]

/-- Dual energy is the original coercive energy divided by the positive determinant. -/
theorem dual_conductivity_energy (A : Mat) (t : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ ((dual (conductivity A t)) *ᵥ x) =
      ((x 0)^2 + (x 1)^2 + ((A *ᵥ x) 0)^2 + ((A *ᵥ x) 1)^2) /
        (conductivity A t).det := by
  rw [dual_conductivity, Matrix.smul_mulVec, dotProduct_smul, conductivity_energy]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- The dual retains an explicit positive coercivity constant. -/
theorem dual_conductivity_coercive (A : Mat) (t : ℝ) (x : Fin 2 → ℝ) :
    ((x 0)^2 + (x 1)^2) / (conductivity A t).det ≤
      x ⬝ᵥ ((dual (conductivity A t)) *ᵥ x) := by
  rw [dual_conductivity_energy]
  apply div_le_div_of_nonneg_right _ (conductivity_det_pos A t).le
  nlinarith only [sq_nonneg ((A *ᵥ x) 0), sq_nonneg ((A *ᵥ x) 1)]

#print axioms dual_eq
#print axioms conductivity_coercive
#print axioms conductivity_det_pos
#print axioms dual_conductivity
#print axioms dual_dual_conductivity
#print axioms dual_conductivity_coercive

end HTGeometry.PlanarConductivityDuality
