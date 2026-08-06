import GaloisForLFunctions.HTGeometry.TopExteriorPowerDeterminant
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Determinant

/-!
# The Jacobian determinant on top differential forms

The pullback of differentials along a polynomial endomorphism sends `d x_i` to `d (phi x_i)`, and
expanding the latter in the basis of differentials produces exactly the Jacobian matrix of partial
derivatives.  On the top exterior power of the module of differentials the induced map is
therefore multiplication by the Jacobian determinant.

This is the algebraic content of the statement that pulling back a rational top form multiplies it
by the Jacobian, which is what contributes the ramification divisor to the order law.  mathlib has
the module of Kaehler differentials of a polynomial ring and its basis, but no Jacobian and no
statement about the top exterior power.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial KaehlerDifferential

open scoped Matrix

variable (R : Type*) [CommRing R] (σ : Type*) [Fintype σ] [DecidableEq σ]

/-- The Jacobian matrix of a polynomial endomorphism. -/
noncomputable def jacobian (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
    Matrix σ σ (MvPolynomial σ R) :=
  Matrix.of fun i j => pderiv j (φ (X i))

/-- The pullback of differentials in coordinates: the linear map determined by
`d x_i ↦ d (phi x_i)`. -/
noncomputable def pullbackDifferential (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
    KaehlerDifferential R (MvPolynomial σ R) →ₗ[MvPolynomial σ R]
      KaehlerDifferential R (MvPolynomial σ R) :=
  (mvPolynomialBasis R σ).constr (MvPolynomial σ R) fun i => D R (MvPolynomial σ R) (φ (X i))

variable {R σ}

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem pullbackDifferential_D_X (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (i : σ) :
    pullbackDifferential R σ φ (D R (MvPolynomial σ R) (X i)) =
      D R (MvPolynomial σ R) (φ (X i)) := by
  rw [pullbackDifferential, ← mvPolynomialBasis_apply R σ i, Module.Basis.constr_basis]

omit [DecidableEq σ] in
/-- **The differential of a polynomial is its gradient in the basis of differentials.** -/
theorem D_eq_sum_pderiv_smul (p : MvPolynomial σ R) :
    D R (MvPolynomial σ R) p =
      ∑ j : σ, pderiv j p • D R (MvPolynomial σ R) (X j) := by
  have h := (mvPolynomialBasis R σ).sum_repr (D R (MvPolynomial σ R) p)
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mvPolynomialBasis_repr_apply, mvPolynomialBasis_apply]

omit [DecidableEq σ] in
/-- **The Jacobian identity.**  The pullback of `d x_i` expands with the partial derivatives of
`phi x_i` as coefficients. -/
theorem pullbackDifferential_D_X_eq_sum (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (i : σ) :
    pullbackDifferential R σ φ (D R (MvPolynomial σ R) (X i)) =
      ∑ j : σ, jacobian R σ φ i j • D R (MvPolynomial σ R) (X j) := by
  rw [pullbackDifferential_D_X]
  exact D_eq_sum_pderiv_smul _

/-- The matrix of the pullback of differentials is the transposed Jacobian. -/
theorem toMatrix_pullbackDifferential (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
    LinearMap.toMatrix (mvPolynomialBasis R σ) (mvPolynomialBasis R σ)
        (pullbackDifferential R σ φ) = (jacobian R σ φ)ᵀ := by
  ext i j
  rw [LinearMap.toMatrix_apply, mvPolynomialBasis_apply, pullbackDifferential_D_X,
    mvPolynomialBasis_repr_apply]
  rfl

/-- **The determinant of the pullback of differentials is the Jacobian determinant.** -/
theorem det_pullbackDifferential (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) :
    LinearMap.det (pullbackDifferential R σ φ) = (jacobian R σ φ).det := by
  rw [← LinearMap.det_toMatrix (mvPolynomialBasis R σ), toMatrix_pullbackDifferential,
    Matrix.det_transpose]

/-- **The pullback of a top differential form is the Jacobian determinant times the form.** -/
theorem exteriorPower_pullbackDifferential_apply [LinearOrder σ]
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial σ R)
    (x : ⋀[MvPolynomial σ R]^(Fintype.card σ) (KaehlerDifferential R (MvPolynomial σ R))) :
    exteriorPower.map (Fintype.card σ) (pullbackDifferential R σ φ) x =
      (jacobian R σ φ).det • x := by
  rw [exteriorPower_map_card_apply (mvPolynomialBasis R σ), det_pullbackDifferential]

end GaloisForLFunctions.HTGeometry
