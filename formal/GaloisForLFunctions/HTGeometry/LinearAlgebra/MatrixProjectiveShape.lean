import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Matrix spectral data under algebra transport

An algebra automorphism of a finite matrix algebra is inner after identifying
matrices with endomorphisms. Consequently it preserves characteristic
polynomials, traces and determinants. The determinant-to-trace ratio is also
unchanged by nonzero scalar multiplication, providing a projective invariant.
Inverse transport follows from uniqueness of a two-sided inverse.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Matrix

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

/-- Algebra transport preserves the characteristic polynomial by innerness. -/
theorem matrixAlgEquiv_charpoly (e : Matrix ι ι K ≃ₐ[K] Matrix ι ι K)
    (A : Matrix ι ι K) : (e A).charpoly = A.charpoly := by
  let β : Module.End K (ι → K) ≃ₐ[K] Matrix ι ι K := LinearMap.toMatrixAlgEquiv'
  obtain ⟨T, hT⟩ := ((β.trans e).trans β.symm).eq_linearEquivConjAlgEquiv
  have he : β.symm (e A) = T.conj (β.symm A) := by
    have h := congrArg (fun f : Module.End K (ι → K) ≃ₐ[K] Module.End K (ι → K) =>
      f (β.symm A)) hT
    simpa only [AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply,
      LinearEquiv.conjAlgEquiv_apply, LinearEquiv.conj_apply, LinearMap.comp_assoc] using h
  rw [← Matrix.charpoly_toLin' (e A), ← Matrix.charpoly_toLin' A]
  change (β.symm (e A)).charpoly = (β.symm A).charpoly
  rw [he, LinearEquiv.charpoly_conj]

/-- The trace is a characteristic-polynomial coefficient. -/
theorem matrixAlgEquiv_trace (e : Matrix ι ι K ≃ₐ[K] Matrix ι ι K)
    (A : Matrix ι ι K) : (e A).trace = A.trace := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, matrixAlgEquiv_charpoly,
    ← Matrix.trace_eq_neg_charpoly_nextCoeff]

/-- The determinant is the signed constant characteristic-polynomial coefficient. -/
theorem matrixAlgEquiv_det (e : Matrix ι ι K ≃ₐ[K] Matrix ι ι K)
    (A : Matrix ι ι K) : (e A).det = A.det := by
  rw [Matrix.det_eq_sign_charpoly_coeff, matrixAlgEquiv_charpoly,
    ← Matrix.det_eq_sign_charpoly_coeff]

/-- A scalar-invariant ratio, defined also at zero trace using field division. -/
def matrixProjectiveShape (A : Matrix ι ι K) : K :=
  A.det / A.trace ^ Fintype.card ι

/-- Algebra transport preserves the projective spectral ratio. -/
theorem matrixProjectiveShape_algEquiv (e : Matrix ι ι K ≃ₐ[K] Matrix ι ι K)
    (A : Matrix ι ι K) : matrixProjectiveShape (e A) = matrixProjectiveShape A := by
  rw [matrixProjectiveShape, matrixAlgEquiv_det, matrixAlgEquiv_trace]
  rfl

/-- The determinant and trace power have the same scalar degree. -/
theorem matrixProjectiveShape_smul (A : Matrix ι ι K) (q : K) (hq : q ≠ 0) :
    matrixProjectiveShape (q • A) = matrixProjectiveShape A := by
  rw [matrixProjectiveShape, Matrix.det_smul, Matrix.trace_smul, smul_eq_mul, mul_pow]
  exact mul_div_mul_left A.det (A.trace ^ Fintype.card ι) (pow_ne_zero _ hq)

/-- Transport of invertible matrices forces reciprocal transport of their inverses. -/
theorem matrixAlgEquiv_inverse_of_scale
    (e : Matrix ι ι K ≃ₐ[K] Matrix ι ι K) (A B : Matrix ι ι K)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (q : K) (hq : q ≠ 0)
    (hscale : e A = q • B) : e A⁻¹ = q⁻¹ • B⁻¹ := by
  have hl : e A⁻¹ * e A = 1 := by
    rw [← map_mul, Matrix.nonsing_inv_mul A hA, map_one]
  have hr : e A * (q⁻¹ • B⁻¹) = 1 := by
    rw [hscale, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hq, one_smul, Matrix.mul_nonsing_inv B hB]
  calc
    e A⁻¹ = e A⁻¹ * 1 := (mul_one _).symm
    _ = e A⁻¹ * (e A * (q⁻¹ • B⁻¹)) := by rw [hr]
    _ = (e A⁻¹ * e A) * (q⁻¹ • B⁻¹) := (mul_assoc _ _ _).symm
    _ = q⁻¹ • B⁻¹ := by rw [hl, one_mul]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.matrixAlgEquiv_charpoly
#print axioms GaloisForLFunctions.HTGeometry.matrixProjectiveShape_smul
#print axioms GaloisForLFunctions.HTGeometry.matrixAlgEquiv_inverse_of_scale
