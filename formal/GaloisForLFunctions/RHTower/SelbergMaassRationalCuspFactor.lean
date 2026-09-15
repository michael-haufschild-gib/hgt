import GaloisForLFunctions.RHTower.SelbergMaassRationalCommensurator
import Mathlib.NumberTheory.ModularForms.Cusps

/-!
# Integral cusp factorization of rational matrices

Every rational invertible matrix has the same image of `∞` as an integral
special-linear matrix. Removing that integral factor leaves an upper-triangular
real matrix, hence a transformation preserving the upper-half-plane infinity
filter. This is the geometric factor needed to transport Maass cusp decay through
rational correspondences.
-/

namespace GaloisForLFunctions.RHTower

open Matrix SpecialLinearGroup GeneralLinearGroup Filter OnePoint
open scoped MatrixGroups LinearAlgebra.Projectivization

noncomputable section

/- A rational invertible matrix is an integral cusp scaling followed by an
upper-triangular real matrix. -/
set_option backward.isDefEq.respectTransparency false in
theorem rationalGL_exists_integral_upperTriangular (g : GL (Fin 2) ℚ) :
    ∃ A : SL2Z,
      (((mapGL ℝ A)⁻¹ * g.map (algebraMap ℚ ℝ) : GL (Fin 2) ℝ) 1 0 = 0) := by
  obtain ⟨A, hA⟩ := OnePoint.exists_mem_SL2 ℤ (g • (∞ : OnePoint ℚ))
  refine ⟨A, smul_infty_eq_self_iff.mp ?_⟩
  have hAreal : mapGL ℝ A • (∞ : OnePoint ℝ) = g.map (algebraMap ℚ ℝ) • ∞ := by
    have hmap := congrArg (OnePoint.map (Rat.castHom ℝ)) hA
    rw [← (Rat.castHom ℝ).algebraMap_toAlgebra] at hmap
    simp only [OnePoint.map_smul, OnePoint.map_infty] at hmap
    rw [Matrix.SpecialLinearGroup.map_mapGL] at hmap
    exact hmap
  rw [mul_smul, ← hAreal, inv_smul_smul]

end

end GaloisForLFunctions.RHTower
