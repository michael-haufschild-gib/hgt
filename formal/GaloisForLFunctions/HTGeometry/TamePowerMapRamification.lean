import GaloisForLFunctions.HTGeometry.KaehlerJacobianTopForm

/-!
# The Jacobian of a tame power map

The coordinatewise power map is the local model of a totally ramified cover of ramification index
`e` along each coordinate hyperplane.  Its Jacobian matrix is diagonal with entries `e x^(e-1)`, so
its determinant is a unit times the `(e-1)`-st power of the product of the coordinates exactly when
`e` is invertible, that is in the tame case.

The order of the Jacobian determinant along each coordinate divisor is therefore `e - 1`, which is
the shift appearing in the ramification order law.  In the wild case the leading factor `e` is not
a unit and the order is strictly larger, so tameness is not a convenience here but the hypothesis
that makes the shift exactly one less than the ramification index.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable (R : Type*) [CommRing R] (σ : Type*) [Fintype σ] [DecidableEq σ]

/-- The coordinatewise power map, the local model of a totally ramified cover. -/
noncomputable def powMap (e : ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun i => (X i : MvPolynomial σ R) ^ e

variable {R σ}

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem powMap_X (e : ℕ) (i : σ) : powMap R σ e (X i) = X i ^ e := by
  simp [powMap]

omit [Fintype σ] in
/-- **The Jacobian of the power map is diagonal.** -/
theorem jacobian_powMap (e : ℕ) :
    jacobian R σ (powMap R σ e) =
      Matrix.diagonal fun i => (e : MvPolynomial σ R) * X i ^ (e - 1) := by
  refine Matrix.ext fun i j => ?_
  rw [jacobian, Matrix.of_apply, powMap_X, pderiv_pow]
  by_cases h : j = i
  · subst h
    rw [pderiv_X_self, Matrix.diagonal_apply_eq, mul_one]
  · rw [pderiv_X_of_ne (Ne.symm h), Matrix.diagonal_apply_ne _ (Ne.symm h), mul_zero]

/-- The Jacobian determinant of the power map. -/
theorem det_jacobian_powMap (e : ℕ) :
    (jacobian R σ (powMap R σ e)).det =
      ∏ i : σ, (e : MvPolynomial σ R) * X i ^ (e - 1) := by
  rw [jacobian_powMap, Matrix.det_diagonal]

/-- **In the tame case the Jacobian determinant is a unit times the `(e-1)`-st power of the
product of the coordinates.**  Its order along each coordinate divisor is therefore exactly
`e - 1`. -/
theorem det_jacobian_powMap_eq_unit_mul (e : ℕ) (hu : IsUnit (e : R)) :
    ∃ u : (MvPolynomial σ R)ˣ,
      (jacobian R σ (powMap R σ e)).det =
        (u : MvPolynomial σ R) * (∏ i : σ, X i) ^ (e - 1) := by
  have hunit : IsUnit ((e : MvPolynomial σ R) ^ Fintype.card σ) := by
    refine IsUnit.pow _ ?_
    have := hu.map (algebraMap R (MvPolynomial σ R))
    simpa using this
  obtain ⟨u, hu'⟩ := hunit
  refine ⟨u, ?_⟩
  rw [det_jacobian_powMap, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow, hu']
  simp

/-- **The tame power map multiplies the top differential form by a unit times the `(e-1)`-st power
of the product of the coordinates.** -/
theorem exteriorPower_pullbackDifferential_powMap [LinearOrder σ] (e : ℕ)
    (x : ⋀[MvPolynomial σ R]^(Fintype.card σ) (KaehlerDifferential R (MvPolynomial σ R))) :
    exteriorPower.map (Fintype.card σ) (pullbackDifferential R σ (powMap R σ e)) x =
      (∏ i : σ, (e : MvPolynomial σ R) * X i ^ (e - 1)) • x := by
  rw [exteriorPower_pullbackDifferential_apply, det_jacobian_powMap]

end GaloisForLFunctions.HTGeometry
