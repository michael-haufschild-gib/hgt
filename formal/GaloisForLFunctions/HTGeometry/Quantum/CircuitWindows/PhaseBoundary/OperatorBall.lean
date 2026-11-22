import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Polynomial slack matrices for the closed operator ball -/
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

/-- A norm bound is a polynomial matrix identity with one additional
complex matrix variable. The radius can be zero. -/
theorem norm_le_iff_slack {d : Type*} [Fintype d] [DecidableEq d] (M : Matrix d d ℂ) {r : ℝ}
    (hr : 0 ≤ r) : ‖M‖ ≤ r ↔ ∃ B : Matrix d d ℂ, (r^2) • (1 : Matrix d d ℂ) - star M*M = star B*B := by
  letI : CStarAlgebra (Matrix d d ℂ) := {}
  have hsq : ‖M‖ ≤ r ↔ ‖star M*M‖ ≤ r^2 := by
    rw [CStarRing.norm_star_mul_self, ← sq]
    exact (sq_le_sq₀ (norm_nonneg _) hr).symm
  rw [hsq, CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg _) (star_mul_self_nonneg M),
    ←sub_nonneg, CStarAlgebra.nonneg_iff_eq_star_mul_self, Algebra.algebraMap_eq_smul_one]

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
