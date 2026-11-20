import GaloisForLFunctions.goldbach.LiLiu.OperatorSpectralBounds
import GaloisForLFunctions.goldbach.InfiniteSpectralSquareProduct
import GaloisForLFunctions.HTGeometry.HilbertSchmidtDominatesPointwise

/-! # Convergence of the product over the actual operator eigenvalues

Finite families of unit eigenvectors have total image energy at most the
Hilbert–Schmidt energy. This proves square summability with multiplicities,
including when the span of the nonzero eigenspaces has a kernel complement.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open GaloisForLFunctions.HTGeometry ContinuousLinearMap
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {T : H →L[ℂ] H} [Fact (IsCompactOperator T)]

theorem summable_eigenvalue_sq (hs : T.IsSymmetric) (hT : IsHilbertSchmidt T) :
    Summable (fun i : EigenIndex T => i.1.1.re ^ 2) := by
  classical
  have horth := orthonormal_eigenVec hs
  have he (i : EigenIndex T) : ‖T (eigenVec T i)‖ ^ 2 = i.1.1.re ^ 2 := by
    rw [apply_eigenVec, norm_smul, horth.1 i, mul_one]
    calc
      ‖i.1.1‖ ^ 2 = ‖(i.1.1.re : ℂ)‖ ^ 2 := congrArg (fun z : ℂ => ‖z‖ ^ 2) (eigenValue_real hs i).symm
      _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  apply summable_of_sum_le (c := ContinuousLinearMap.hsNormSq T) (fun i => sq_nonneg _)
  intro S
  have h := _root_.RHTower.sum_norm_sq_apply_le_hsNormSq hT
    (horth.comp (fun i : S => (i : EigenIndex T)) Subtype.val_injective)
  simpa only [Function.comp_apply, he, Finset.sum_coe_sort] using h

/-- Square summability of the normalized list, with every eigenspace counted in full. -/
def scaledEigenvalues (hs : T.IsSymmetric) (hT : IsHilbertSchmidt T) (δ : ℝ) :
    lp (fun _ : EigenIndex T => ℝ) 2 :=
  ⟨fun i => i.1.1.re / δ, (memℓp_gen_iff (by norm_num)).mpr (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs, div_pow,
      div_eq_mul_inv] using (summable_eigenvalue_sq hs hT).mul_right (δ ^ 2)⁻¹)⟩

theorem spectralProduct_differentiable (hs : T.IsSymmetric) (hT : IsHilbertSchmidt T) (δ : ℝ) :
    Differentiable ℂ (spectralProduct T δ) :=
  infiniteSpectralSquareProduct_differentiable (scaledEigenvalues hs hT δ)

theorem spectralProduct_eq_zero_iff (hs : T.IsSymmetric) (hT : IsHilbertSchmidt T) (δ : ℝ) (z : ℂ) :
    spectralProduct T δ z = 0 ↔ ∃ i : EigenIndex T, spectralSquareFactor (i.1.1.re / δ) z = 0 :=
  infiniteSpectralSquareProduct_eq_zero_iff (scaledEigenvalues hs hT δ) z

#print axioms spectralProduct_differentiable
#print axioms spectralProduct_eq_zero_iff
end
end GaloisForLFunctions.Goldbach.LiLiu
