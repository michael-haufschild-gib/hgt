import GaloisForLFunctions.HTGeometry.MvPolynomialWaringSmoothHorizon

/-!
# A checkable criterion for projective smoothness

Projective smoothness is a condition at every nonzero point of the affine cone.  It follows from a
single algebraic fact: if some partial derivative is a nonzero constant then no point of the cone is
singular.  Coordinates and nondegenerate linear forms satisfy the criterion, and for the degree-one
Waring form it becomes the nonvanishing of a column sum of the coefficient matrix.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K : Type u} [Field K] {m : ℕ}

/-- **Constant-derivative criterion.**  A nonzero constant partial derivative forces projective
smoothness. -/
theorem mvPolynomialProjectivelySmooth_of_pderiv_eq_C
    {P : MvPolynomial (Fin m) K} {j : Fin m} {c : K}
    (hj : MvPolynomial.pderiv j P = MvPolynomial.C c) (hc : c ≠ 0) :
    MvPolynomialProjectivelySmooth P := by
  intro v _ _
  refine ⟨j, ?_⟩
  rw [hj, MvPolynomial.eval_C]
  exact hc

/-- Every coordinate is projectively smooth. -/
theorem mvPolynomialProjectivelySmooth_X (i : Fin m) :
    MvPolynomialProjectivelySmooth (MvPolynomial.X i : MvPolynomial (Fin m) K) := by
  refine mvPolynomialProjectivelySmooth_of_pderiv_eq_C (j := i) (c := 1) ?_ one_ne_zero
  simp

/-- A linear form with a nonzero coefficient is projectively smooth. -/
theorem mvPolynomialProjectivelySmooth_linear (c : Fin m → K) {j : Fin m} (hj : c j ≠ 0) :
    MvPolynomialProjectivelySmooth
      (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i : MvPolynomial (Fin m) K) := by
  refine mvPolynomialProjectivelySmooth_of_pderiv_eq_C (j := j) (c := c j) ?_ hj
  rw [map_sum]
  simp [MvPolynomial.pderiv_X, Pi.single_apply, Finset.sum_ite_eq' Finset.univ j]

end

end GaloisForLFunctions.HTGeometry
