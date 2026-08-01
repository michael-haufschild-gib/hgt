import GaloisForLFunctions.HTGeometry.UniversalCenteredCoefficients
import GaloisForLFunctions.HTGeometry.DetUpdateRowOne
import GaloisForLFunctions.HTGeometry.TailCoefficientIndependence

/-!
# The centered coefficients are algebraically independent

Take the next-to-leading coefficient together with the centered ones.  Differentiating in a variable
other than the next-to-leading one, the shift contributes nothing: it is a multiple of that variable
alone.  So off the last row the derivative matrix is already the identity.

Specialising the next-to-leading coefficient to zero therefore turns the Jacobian into the identity
with one row replaced, whose determinant is one.  Hence the Jacobian is nonsingular and the family
is algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- The next-to-leading coefficient together with the centered ones. -/
noncomputable def centeredFamily (K : Type*) [Field K] (d : ℕ) (hd : 0 < d) (j : Fin d) :
    MvPolynomial (Fin d) K :=
  if (j : ℕ) = d - 1 then MvPolynomial.X j else universalCenteredCoeff K d hd (j : ℕ)

/-- The Jacobian of that family. -/
noncomputable def centeredJacobian (K : Type*) [Field K] (d : ℕ) (hd : 0 < d) :
    Matrix (Fin d) (Fin d) (MvPolynomial (Fin d) K) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (centeredFamily K d hd j)

omit [CharZero K] in
theorem pderiv_centeringShift_of_ne {i : Fin d} (hd : 0 < d) (hi : (i : ℕ) ≠ d - 1) :
    MvPolynomial.pderiv i (centeringShift K d hd) = 0 := by
  have hne : (⟨d - 1, by omega⟩ : Fin d) ≠ i := by
    intro hcon
    exact hi (by rw [← hcon])
  rw [centeringShift, map_neg, smul_eq_C_mul, Derivation.leibniz, MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X_of_ne hne]
  simp

/-- Setting the next-to-leading coefficient to zero. -/
noncomputable def killLast (K : Type*) [Field K] (d : ℕ) :
    MvPolynomial (Fin d) K →ₐ[K] MvPolynomial (Fin d) K :=
  MvPolynomial.aeval (fun k : Fin d => if (k : ℕ) = d - 1 then 0 else MvPolynomial.X k)

omit [CharZero K] in
theorem killLast_X {j : Fin d} (hj : (j : ℕ) ≠ d - 1) :
    killLast K d (MvPolynomial.X j) = MvPolynomial.X j := by
  rw [killLast, MvPolynomial.aeval_X, if_neg hj]

omit [CharZero K] in
theorem killLast_centeringShift (hd : 0 < d) :
    killLast K d (centeringShift K d hd) = 0 := by
  rw [centeringShift, map_neg, smul_eq_C_mul, map_mul, killLast, MvPolynomial.aeval_X,
    if_pos rfl, mul_zero, neg_zero]

omit [CharZero K] in
/-- **Off the last row the specialised Jacobian is the identity.** -/
theorem killLast_centeredJacobian {i j : Fin d} (hd : 0 < d) (hi : (i : ℕ) ≠ d - 1) :
    killLast K d (centeredJacobian K d hd i j) = if i = j then 1 else 0 := by
  rw [centeredJacobian, Matrix.of_apply, centeredFamily]
  by_cases hj : (j : ℕ) = d - 1
  · rw [if_pos hj]
    have hne : j ≠ i := by
      intro hcon
      exact hi (by rw [← hcon]; exact hj)
    rw [MvPolynomial.pderiv_X_of_ne hne, if_neg (fun hcon => hne hcon.symm), map_zero]
  · rw [if_neg hj]
    obtain ⟨s, hs⟩ := universalCenteredCoeff_eq_add (K := K) hd (j : ℕ)
    rw [hs, map_add, coeff_universalMonic_lt (by omega : (j : ℕ) < d)]
    have hjfin : (⟨(j : ℕ), by omega⟩ : Fin d) = j := Fin.ext rfl
    rw [hjfin, Derivation.leibniz, pderiv_centeringShift_of_ne hd hi, smul_zero, add_zero,
      smul_eq_mul, map_add, map_mul, killLast_centeringShift hd, zero_mul, add_zero]
    by_cases hij : i = j
    · rw [if_pos hij, hij, MvPolynomial.pderiv_X_self, map_one]
    · rw [if_neg hij, MvPolynomial.pderiv_X_of_ne (fun hcon => hij hcon.symm), map_zero]

omit [CharZero K] in
theorem killLast_centeredJacobian_last (hd : 0 < d) :
    killLast K d (centeredJacobian K d hd (⟨d - 1, by omega⟩ : Fin d)
      (⟨d - 1, by omega⟩ : Fin d)) = 1 := by
  rw [centeredJacobian, Matrix.of_apply, centeredFamily, if_pos rfl,
    MvPolynomial.pderiv_X_self, map_one]

omit [CharZero K] in
/-- **The specialised Jacobian is the identity with one row replaced.** -/
theorem killLast_mapMatrix_centeredJacobian (hd : 0 < d) :
    (killLast K d).toRingHom.mapMatrix (centeredJacobian K d hd) =
      Matrix.updateRow (1 : Matrix (Fin d) (Fin d) (MvPolynomial (Fin d) K))
        (⟨d - 1, by omega⟩ : Fin d)
        (fun j => killLast K d
          (centeredJacobian K d hd (⟨d - 1, by omega⟩ : Fin d) j)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.updateRow_apply]
  by_cases hi : i = (⟨d - 1, by omega⟩ : Fin d)
  · rw [if_pos hi, hi]
    rfl
  · rw [if_neg hi]
    have hival : (i : ℕ) ≠ d - 1 := fun hcon => hi (Fin.ext hcon)
    show killLast K d (centeredJacobian K d hd i j) = _
    rw [killLast_centeredJacobian hd hival, Matrix.one_apply]

omit [CharZero K] in
/-- **The Jacobian is nonsingular.** -/
theorem det_centeredJacobian_ne_zero (hd : 0 < d) :
    (centeredJacobian K d hd).det ≠ 0 := by
  intro hcon
  have h : (killLast K d).toRingHom ((centeredJacobian K d hd).det) = 0 := by
    rw [hcon]
    exact map_zero _
  rw [RingHom.map_det, killLast_mapMatrix_centeredJacobian hd, det_updateRow_one,
    killLast_centeredJacobian_last hd] at h
  exact one_ne_zero h

/-- **The centering coefficients are algebraically independent.**  The next-to-leading coefficient
together with the centered ones form an algebraically independent family, so the centered
coefficients are independent over the constants extended by the next-to-leading one. -/
theorem algebraicIndependent_centeredFamily (hd : 0 < d) :
    AlgebraicIndependent K (centeredFamily K d hd) := by
  classical
  exact algebraicIndependent_of_domain_jacobian
    (K := K) (R := MvPolynomial (Fin d) K)
    (centeredFamily K d hd)
    (fun i f => MvPolynomial.pderiv i f)
    (fun i a b => map_add _ a b)
    (fun i a b => by rw [Derivation.leibniz]; simp only [smul_eq_mul])
    (fun i c => Derivation.map_algebraMap _ c)
    (centeredJacobian K d hd) (det_centeredJacobian_ne_zero hd)
    (fun i j => rfl)

end GaloisForLFunctions.HTGeometry
