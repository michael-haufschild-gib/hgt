import GaloisForLFunctions.HTGeometry.FirstOrderIrreducibleDerivativePolynomial

/-!
# Evaluation of the irreducible first-order derivative polynomial

The literal polynomial state ring `ℂ[U][V]` evaluates at any clock/value pair.  When those
coordinates are algebraically independent, this evaluation is faithful and extends canonically to
the rational state field `ℂ(U,V)`.  Substituting the derivative coordinate into the resulting
univariate polynomial recovers the original three-variable relation exactly.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Evaluation of the literal clock/value polynomial ring at the first two entries of a
three-coordinate state. -/
noncomputable def firstOrderStatePolynomialEval
    {M : Type*} [CommRing M] [Algebra ℂ M] (x : Fin 3 → M) :
    FirstOrderStatePolynomialRing →ₐ[ℂ] M :=
  (MvPolynomial.aeval
    (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1)).comp
      firstOrderStatePolynomialEquiv.symm

@[simp]
theorem firstOrderStatePolynomialEval_equiv
    {M : Type*} [CommRing M] [Algebra ℂ M] (x : Fin 3 → M)
    (c : MvPolynomial {j : Fin 3 // j ≠ (2 : Fin 3)} ℂ) :
    firstOrderStatePolynomialEval x (firstOrderStatePolynomialEquiv c) =
      MvPolynomial.aeval
        (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1) c := by
  simp [firstOrderStatePolynomialEval]

/-- Algebraic independence of the clock/value coordinates makes state evaluation faithful. -/
theorem firstOrderStatePolynomialEval_injective_of_algebraicIndependent
    {M : Type*} [CommRing M] [IsDomain M] [Algebra ℂ M] (x : Fin 3 → M)
    (hstate : AlgebraicIndependent ℂ
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1)) :
    Function.Injective (firstOrderStatePolynomialEval x) := by
  exact (algebraicIndependent_iff_injective_aeval.mp hstate).comp
    firstOrderStatePolynomialEquiv.symm.injective

/-- Splitting a relation at the derivative coordinate and evaluating its state coefficients
recovers direct evaluation of the original multivariate polynomial. -/
theorem firstOrderDerivativePolynomialOverStateRing_eval
    {M : Type*} [CommRing M] [Algebra ℂ M] (x : Fin 3 → M)
    (P : MvPolynomial (Fin 3) ℂ) :
    Polynomial.eval₂ (firstOrderStatePolynomialEval x) (x 2)
        (firstOrderDerivativePolynomialOverStateRing P) =
      MvPolynomial.aeval x P := by
  classical
  let g : Fin 3 → M := x
  let e : MvPolynomial {j : Fin 3 // j ≠ (2 : Fin 3)} ℂ →ₐ[ℂ] M :=
    MvPolynomial.aeval
      (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1)
  have hext :
      ((Polynomial.eval₂RingHom e.toRingHom (x 2)).comp
        ((mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)) :
          MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] _).toAlgHom.toRingHom) =
        MvPolynomial.eval₂Hom (algebraMap ℂ M) g := by
    refine MvPolynomial.ringHom_ext ?_ ?_
    · intro r
      show Polynomial.eval₂ e.toRingHom (x 2)
          (mvPolynomialPolynomialEquivAt (2 : Fin 3) (MvPolynomial.C r)) =
        MvPolynomial.eval₂Hom (algebraMap ℂ M) g (MvPolynomial.C r)
      have hC :
          (mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)) (MvPolynomial.C r) =
            Polynomial.C (MvPolynomial.C r) := by
        simpa using
          (mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)).commutes r
      rw [hC, Polynomial.eval₂_C, MvPolynomial.eval₂Hom_C]
      simp [e]
    · intro q
      show Polynomial.eval₂ e.toRingHom (x 2)
          (mvPolynomialPolynomialEquivAt (2 : Fin 3) (MvPolynomial.X q)) =
        MvPolynomial.eval₂Hom (algebraMap ℂ M) g (MvPolynomial.X q)
      rw [MvPolynomial.eval₂Hom_X']
      by_cases hq : q = (2 : Fin 3)
      · subst hq
        rw [mvPolynomialPolynomialEquivAt_X_self, Polynomial.eval₂_X]
      · rw [mvPolynomialPolynomialEquivAt_X_ne hq, Polynomial.eval₂_C]
        simp [e, g]
  rw [firstOrderDerivativePolynomialOverStateRing, Polynomial.eval₂_map]
  have hcomp :
      ((↑(firstOrderStatePolynomialEval x) :
          FirstOrderStatePolynomialRing →+* M).comp
          firstOrderStatePolynomialEquiv.toRingHom) =
        (MvPolynomial.aeval
          (fun j : {j : Fin 3 // j ≠ (2 : Fin 3)} ↦ x j.1)).toRingHom := by
    apply DFunLike.ext _ _
    intro c
    exact firstOrderStatePolynomialEval_equiv x c
  rw [hcomp]
  change
    ((Polynomial.eval₂RingHom e.toRingHom (x 2)).comp
      ((mvPolynomialPolynomialEquivAt (K := ℂ) (2 : Fin 3)) :
        MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] _).toAlgHom.toRingHom) P = _
  simpa only [g, MvPolynomial.coe_eval₂Hom, ← MvPolynomial.aeval_def] using
    congrArg (fun f : MvPolynomial (Fin 3) ℂ →+* M ↦ f P) hext

/-- Injective state evaluation extends canonically to the rational clock/value field. -/
noncomputable def firstOrderRationalStateEval
    {M : Type*} [Field M] [Algebra ℂ M] (x : Fin 3 → M)
    (hinj : Function.Injective (firstOrderStatePolynomialEval x)) :
    FirstOrderRationalStateField →ₐ[ℂ] M :=
  IsFractionRing.liftAlgHom hinj

@[simp]
theorem firstOrderRationalStateEval_algebraMap
    {M : Type*} [Field M] [Algebra ℂ M] (x : Fin 3 → M)
    (hinj : Function.Injective (firstOrderStatePolynomialEval x))
    (p : FirstOrderStatePolynomialRing) :
    firstOrderRationalStateEval x hinj
        (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField p) =
      firstOrderStatePolynomialEval x p := by
  simp only [firstOrderRationalStateEval, IsFractionRing.liftAlgHom,
    IsLocalization.liftAlgHom]
  change (IsLocalization.lift _)
      (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField p) = _
  rw [IsLocalization.lift_eq]
  rfl

/-- The rational-state derivative polynomial has exactly the same value as its original
three-variable relation. -/
theorem firstOrderDerivativePolynomial_eval
    {M : Type*} [Field M] [Algebra ℂ M] (x : Fin 3 → M)
    (hinj : Function.Injective (firstOrderStatePolynomialEval x))
    (P : MvPolynomial (Fin 3) ℂ) :
    Polynomial.eval₂ (firstOrderRationalStateEval x hinj) (x 2)
        (firstOrderDerivativePolynomial P) =
      MvPolynomial.aeval x P := by
  rw [firstOrderDerivativePolynomial, Polynomial.eval₂_map]
  have hcomp :
      (firstOrderRationalStateEval x hinj).toRingHom.comp
          (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField) =
        (firstOrderStatePolynomialEval x).toRingHom := by
    apply DFunLike.ext _ _
    intro p
    exact firstOrderRationalStateEval_algebraMap x hinj p
  change
    Polynomial.eval₂
        ((firstOrderRationalStateEval x hinj).toRingHom.comp
          (algebraMap FirstOrderStatePolynomialRing FirstOrderRationalStateField))
        (x 2) (firstOrderDerivativePolynomialOverStateRing P) = _
  rw [hcomp]
  exact firstOrderDerivativePolynomialOverStateRing_eval x P

end

end GaloisForLFunctions.HTGeometry
