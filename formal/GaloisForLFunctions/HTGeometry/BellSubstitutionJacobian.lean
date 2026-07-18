import GaloisForLFunctions.HTGeometry.BellCoordinateJacobian
import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence

/-!
# Jacobian of a substituted Bell family

The Jacobian of the Bell coordinates evaluated on a polynomial jet family factors as the Bell
Jacobian times the Jacobian of that family.  Since the Bell factor has determinant one, Bell
substitution preserves the Jacobian determinant exactly.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions

/-- The conventional row-output polynomial Jacobian. -/
def polynomialOutputJacobian {m : ℕ}
    (f : Fin m → MvPolynomial (Fin m) ℂ) :
    Matrix (Fin m) (Fin m) (MvPolynomial (Fin m) ℂ) :=
  fun i j => pderiv j (f i)

/-- The Bell coordinate family after substituting a polynomial jet family. -/
def bellSubstitutionFamily (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ :=
  fun i => aeval u (bellAt n ((i : ℕ) + 1) i.isLt)

/-- The formal chain-rule factorization of a substituted Bell Jacobian. -/
theorem polynomialOutputJacobian_bellSubstitutionFamily (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    polynomialOutputJacobian (bellSubstitutionFamily n u) =
      ((bellCoordinateJacobian n).map (aeval u)).transpose *
        polynomialOutputJacobian u := by
  funext i j
  rw [Matrix.mul_apply]
  simp only [polynomialOutputJacobian, bellSubstitutionFamily, Matrix.transpose_apply,
    Matrix.map_apply, bellCoordinateJacobian]
  exact pderiv_aeval_chain u (bellAt n ((i : ℕ) + 1) i.isLt) j

/-- **Bell substitution preserves the polynomial Jacobian determinant exactly.** -/
theorem polynomialOutputJacobian_bellSubstitutionFamily_det (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    (polynomialOutputJacobian (bellSubstitutionFamily n u)).det =
      (polynomialOutputJacobian u).det := by
  rw [polynomialOutputJacobian_bellSubstitutionFamily, Matrix.det_mul,
    Matrix.det_transpose]
  have hmap := (aeval u).map_det (bellCoordinateJacobian n)
  rw [bellCoordinateJacobian_det, map_one] at hmap
  have hdet : ((bellCoordinateJacobian n).map (aeval u)).det = 1 := by
    simpa using hmap.symm
  rw [hdet, one_mul]

/-- Bell substitution has a nonzero output Jacobian exactly when the input jet family does. -/
theorem polynomialOutputJacobian_bellSubstitutionFamily_det_ne_zero_iff (n : ℕ)
    (u : Fin (n + 1) → MvPolynomial (Fin (n + 1)) ℂ) :
    (polynomialOutputJacobian (bellSubstitutionFamily n u)).det ≠ 0 ↔
      (polynomialOutputJacobian u).det ≠ 0 := by
  rw [polynomialOutputJacobian_bellSubstitutionFamily_det]

end GaloisForLFunctions

end
