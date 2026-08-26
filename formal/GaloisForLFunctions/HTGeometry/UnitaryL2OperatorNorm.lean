import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Unitary invariance of the finite-matrix L² operator norm

This dependency-light module isolates the generic unitary-conjugation norm identity so tensor
modules can reuse it without importing unrelated spectral-branch infrastructure.
-/

open scoped Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

/-- Unitary conjugation is an isometry of the finite-matrix L² operator norm. -/
theorem l2_opNorm_unitary_conj_eq {V : Matrix d d ℂ} (hV : V ∈ unitary (Matrix d d ℂ))
    (X : Matrix d d ℂ) : ‖V * X * star V‖ = ‖X‖ := by
  have hVnorm : ‖V‖ = 1 := CStarRing.norm_coe_unitary (⟨V, hV⟩ : unitary (Matrix d d ℂ))
  have hVstarnorm : ‖star V‖ = 1 := by
    rw [norm_star]
    exact hVnorm
  have hle : ‖V * X * star V‖ ≤ ‖X‖ := by
    calc
      ‖V * X * star V‖ ≤ ‖V * X‖ * ‖star V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ ‖V‖ * ‖X‖ * ‖star V‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = ‖X‖ := by rw [hVnorm, hVstarnorm]; ring
  refine le_antisymm hle ?_
  have hback : star V * (V * X * star V) * V = X := by
    have h1 : star V * V = 1 := (Unitary.mem_iff.mp hV).1
    calc
      star V * (V * X * star V) * V = (star V * V) * X * (star V * V) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [h1]; simp
  calc
    ‖X‖ = ‖star V * (V * X * star V) * V‖ := by rw [hback]
    _ ≤ ‖star V * (V * X * star V)‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖star V‖ * ‖V * X * star V‖ * ‖V‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    _ = ‖V * X * star V‖ := by rw [hVnorm, hVstarnorm]; ring

end GaloisForLFunctions.HTGeometry
