import Mathlib.Analysis.InnerProductSpace.NormDet

/-!
# Conorm lower bounds force volume-Jacobian lower bounds

For a linear map from an `m`-dimensional real inner-product space, a uniform
lower Lipschitz bound `c` forces every singular value to be at least `c`.
Consequently its norm determinant, the exact `m`-dimensional Hausdorff-volume
factor used by coarea, is at least `c ^ m`.
-/

open Module
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A conorm floor `c` forces the rectangular volume Jacobian to be at least
`c ^ m`. -/
theorem linearMap_normDet_lower_of_norm_lower
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (A : E →ₗ[ℝ] F) {m : ℕ} (hm : Module.finrank ℝ E = m)
    {c : ℝ} (hc : 0 ≤ c) (hA : ∀ v, c * ‖v‖ ≤ ‖A v‖) :
    c ^ m ≤ A.normDet := by
  rw [A.normDet_eq_prod_singularValues, hm,
    ← Fin.prod_univ_eq_prod_range]
  have hprod : (∏ _i : Fin m, c) ≤
      ∏ i : Fin m, A.singularValues i := by
    apply Finset.prod_le_prod
    · intro i _
      exact hc
    · intro i _
      have hbNorm :
          ‖(A.isSymmetric_adjoint_comp_self.eigenvectorBasis hm) i‖ = 1 := by
        exact (A.isSymmetric_adjoint_comp_self.eigenvectorBasis hm).orthonormal.1 i
      have hlower :=
        hA ((A.isSymmetric_adjoint_comp_self.eigenvectorBasis hm) i)
      rw [hbNorm, mul_one] at hlower
      have hsq := (sq_le_sq₀ hc (norm_nonneg _)).2 hlower
      apply (sq_le_sq₀ hc (A.singularValues_nonneg i)).mp
      rw [A.sq_singularValues_fin hm]
      let b := A.isSymmetric_adjoint_comp_self.eigenvectorBasis hm
      have heig :=
        A.isSymmetric_adjoint_comp_self.hasEigenvector_eigenvectorBasis hm i
      calc
        c ^ 2 ≤ ‖A (b i)‖ ^ 2 := hsq
        _ = inner ℝ (A (b i)) (A (b i)) :=
          (real_inner_self_eq_norm_sq (A (b i))).symm
        _ = inner ℝ (b i) (A.adjoint (A (b i))) :=
          (LinearMap.adjoint_inner_right A (b i) (A (b i))).symm
        _ = inner ℝ (b i) ((A.adjoint ∘ₗ A) (b i)) := rfl
        _ = inner ℝ (b i)
            (A.isSymmetric_adjoint_comp_self.eigenvalues hm i • b i) := by
          rw [heig.apply_eq_smul]
          rfl
        _ = A.isSymmetric_adjoint_comp_self.eigenvalues hm i := by
          rw [inner_smul_right, real_inner_self_eq_norm_sq, hbNorm]
          simp
  simpa [Fintype.card_fin] using hprod

end

end GaloisForLFunctions.HTGeometry
