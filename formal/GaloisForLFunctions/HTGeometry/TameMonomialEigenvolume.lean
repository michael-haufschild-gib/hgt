import GaloisForLFunctions.HTGeometry.TamePowerMapRamification

/-!
# The logarithmic volume form is an eigenvolume of a tame monomial map

A monomial map raises each coordinate to its own power, so its ramification index varies from one
coordinate divisor to the next, exactly as the ramification index of an endomorphism varies from
one prime divisor to the next.  Its Jacobian determinant is a unit times the product of the
coordinates raised to the shifted exponents, which is the ramification divisor of the map.

Multiplying by the product of the coordinates turns that into the pullback of the same product, up
to a unit: the logarithmic volume form is an eigenvolume, its horizon is the union of the
coordinate hyperplanes, and its order there is `-1`.  This is the toric model of the eigenvolume
horizon theorem, and it shows the hypotheses of that theorem are consistent and sharp.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable (R : Type*) [CommRing R] (σ : Type*) [Fintype σ] [DecidableEq σ]

/-- A monomial map: each coordinate is raised to its own power. -/
noncomputable def monomialMap (e : σ → ℕ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval fun i => (X i : MvPolynomial σ R) ^ e i

variable {R σ}

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem monomialMap_X (e : σ → ℕ) (i : σ) :
    monomialMap R σ e (X i) = X i ^ e i := by
  simp [monomialMap]

omit [Fintype σ] in
/-- **The Jacobian of a monomial map is diagonal**, with the shifted exponent in each entry. -/
theorem jacobian_monomialMap (e : σ → ℕ) :
    jacobian R σ (monomialMap R σ e) =
      Matrix.diagonal fun i => (e i : MvPolynomial σ R) * X i ^ (e i - 1) := by
  refine Matrix.ext fun i j => ?_
  rw [jacobian, Matrix.of_apply, monomialMap_X, pderiv_pow]
  by_cases h : j = i
  · subst h
    rw [pderiv_X_self, Matrix.diagonal_apply_eq, mul_one]
  · rw [pderiv_X_of_ne (Ne.symm h), Matrix.diagonal_apply_ne _ (Ne.symm h), mul_zero]

/-- The Jacobian determinant of a monomial map. -/
theorem det_jacobian_monomialMap (e : σ → ℕ) :
    (jacobian R σ (monomialMap R σ e)).det =
      ∏ i : σ, (e i : MvPolynomial σ R) * X i ^ (e i - 1) := by
  rw [jacobian_monomialMap, Matrix.det_diagonal]

/-- **The ramification divisor of a tame monomial map.**  The Jacobian determinant is a unit times
the product of the coordinates with the shifted exponents, so its order along the `i`-th coordinate
divisor is exactly `e i - 1`. -/
theorem det_jacobian_monomialMap_eq_unit_mul (e : σ → ℕ) (hu : ∀ i, IsUnit ((e i : R))) :
    ∃ u : (MvPolynomial σ R)ˣ,
      (jacobian R σ (monomialMap R σ e)).det =
        (u : MvPolynomial σ R) * ∏ i : σ, X i ^ (e i - 1) := by
  have hunit : IsUnit (∏ i : σ, (e i : MvPolynomial σ R)) := by
    refine Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one ?_
    intro i _
    have := (hu i).map (algebraMap R (MvPolynomial σ R))
    simpa using this
  obtain ⟨u, hu'⟩ := hunit
  refine ⟨u, ?_⟩
  rw [det_jacobian_monomialMap, Finset.prod_mul_distrib, hu']

omit [DecidableEq σ] in
theorem monomialMap_prod_X (e : σ → ℕ) :
    monomialMap R σ e (∏ i : σ, X i) = ∏ i : σ, X i ^ e i := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => monomialMap_X e i

omit [DecidableEq σ] in
theorem prod_pow_sub_one_mul_prod (e : σ → ℕ) (he : ∀ i, 1 ≤ e i) :
    (∏ i : σ, (X i : MvPolynomial σ R) ^ (e i - 1)) * ∏ i : σ, X i =
      ∏ i : σ, (X i : MvPolynomial σ R) ^ e i := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_succ, Nat.sub_add_cancel (he i)]

/-- **The logarithmic volume form is an eigenvolume of a tame monomial map.**  Multiplying the
Jacobian determinant by the product of the coordinates gives the pullback of that product, up to a
unit: the divisor of the form is unchanged, so its horizon is the union of the coordinate
hyperplanes with order `-1` on each. -/
theorem exists_unit_det_jacobian_mul_prod (e : σ → ℕ) (he : ∀ i, 1 ≤ e i)
    (hu : ∀ i, IsUnit ((e i : R))) :
    ∃ u : (MvPolynomial σ R)ˣ,
      (jacobian R σ (monomialMap R σ e)).det * (∏ i : σ, X i) =
        (u : MvPolynomial σ R) * monomialMap R σ e (∏ i : σ, X i) := by
  obtain ⟨u, hu'⟩ := det_jacobian_monomialMap_eq_unit_mul e hu
  refine ⟨u, ?_⟩
  rw [hu', monomialMap_prod_X, mul_assoc, prod_pow_sub_one_mul_prod e he]

end GaloisForLFunctions.HTGeometry
