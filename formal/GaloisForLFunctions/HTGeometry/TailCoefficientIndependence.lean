import GaloisForLFunctions.HTGeometry.TailPolynomialTriangularity
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# The tail coefficients are algebraically independent

The coefficients read off the powers of the tail polynomial form a triangular system against the
partial derivatives in the parameters: the derivative vanishes above the diagonal and equals a
nonzero multiple of a power of the first parameter on it.

So the Jacobian is nonsingular and the coefficients are algebraically independent, which is what
makes the coefficient field of the centered equation a rational function field.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- The tail coefficients: the coefficient of `t^j` in the `(n-j)`-th power of the tail. -/
noncomputable def tailCoeff (K : Type*) [Field K] (n : ℕ) (j : Fin n) :
    MvPolynomial (Fin n) K :=
  ((tailPoly K n) ^ (n - (j : ℕ))).coeff (j : ℕ)

/-- The Jacobian of the tail coefficients against the parameter derivatives. -/
noncomputable def tailJacobian (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) K) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (tailCoeff K n j)

omit [CharZero K] in
theorem tailJacobian_upperTriangular {i j : Fin n} (hji : j < i) :
    tailJacobian K n i j = 0 := by
  rw [tailJacobian, Matrix.of_apply, tailCoeff]
  exact pderiv_coeff_tailPoly_pow_eq_zero i _ _ hji

omit [CharZero K] in
theorem tailJacobian_diag (i : Fin n) :
    tailJacobian K n i i =
      ((n - (i : ℕ) : ℕ) : MvPolynomial (Fin n) K) *
        (MvPolynomial.X (⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) i.2⟩ : Fin n)) ^
          (n - (i : ℕ) - 1) := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  rw [tailJacobian, Matrix.of_apply, tailCoeff, pderiv_coeff_tailPoly_pow_diag,
    coeff_zero_tailPoly_pow hn]

theorem tailJacobian_det_ne_zero : (tailJacobian K n).det ≠ 0 := by
  have htri : (tailJacobian K n).BlockTriangular id := fun i j hji =>
    tailJacobian_upperTriangular hji
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [tailJacobian_diag]
  refine mul_ne_zero ?_ (pow_ne_zero _ (MvPolynomial.X_ne_zero _))
  have hi : (i : ℕ) < n := i.2
  exact Nat.cast_ne_zero.2 (by omega)

/-- **The tail coefficients are algebraically independent.** -/
theorem algebraicIndependent_tailCoeff :
    AlgebraicIndependent K (tailCoeff K n) := by
  classical
  exact algebraicIndependent_of_domain_jacobian
    (K := K) (R := MvPolynomial (Fin n) K)
    (tailCoeff K n)
    (fun i f => MvPolynomial.pderiv i f)
    (fun i a b => map_add _ a b)
    (fun i a b => by rw [Derivation.leibniz]; simp only [smul_eq_mul])
    (fun i c => Derivation.map_algebraMap _ c)
    (tailJacobian K n) tailJacobian_det_ne_zero
    (fun i j => rfl)

end GaloisForLFunctions.HTGeometry
