import GaloisForLFunctions.HTGeometry.AlgebraicTorusFractionAction
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import GaloisForLFunctions.HTGeometry.SemilinearKaehlerDescent

/-!
# Diagonal derivation of a rational torus

The logarithmic flow `X_i' = i ω_i X_i` defines a derivation first on the
multivariable polynomial ring and then, by the quotient rule, on its fraction
field.  Coordinate scalings commute with this derivation.  This is the
algebraic bridge needed to keep every rational phase jet inside the same
torus-invariant state field.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {r : ℕ}

/-- Diagonal logarithmic derivation on the multivariate polynomial ring. -/
def rationalDiagonalPolynomialDerivation (omega : Fin r → ℝ) :
    Derivation ℂ (MvPolynomial (Fin r) ℂ) (MvPolynomial (Fin r) ℂ) :=
  MvPolynomial.mkDerivation ℂ fun i =>
    MvPolynomial.C (Complex.I * (omega i : ℂ)) * MvPolynomial.X i

@[simp] theorem rationalDiagonalPolynomialDerivation_X
    (omega : Fin r → ℝ) (i : Fin r) :
    rationalDiagonalPolynomialDerivation omega (MvPolynomial.X i) =
      MvPolynomial.C (Complex.I * (omega i : ℂ)) * MvPolynomial.X i := by
  exact MvPolynomial.mkDerivation_X ℂ _ i

@[simp] theorem rationalTorusScaleEquiv_algebraMap
    (u : Fin r → ℂˣ) (P : MvPolynomial (Fin r) ℂ) :
    rationalTorusScaleEquiv u
        (algebraMap (MvPolynomial (Fin r) ℂ)
          (FractionRing (MvPolynomial (Fin r) ℂ)) P) =
      algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ))
          (mvPolynomialUnitScaleEquiv u P) := by
  change fracRingEquiv (mvPolynomialUnitScaleEquiv u).toRingEquiv
      (algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ)) P) = _
  rw [fracRingEquiv_algebraMap]
  rfl

/-- The diagonal polynomial derivation commutes with unit coordinate scaling. -/
theorem mvPolynomialUnitScaleEquiv_rationalDiagonalPolynomialDerivation
    (omega : Fin r → ℝ) (u : Fin r → ℂˣ)
    (P : MvPolynomial (Fin r) ℂ) :
    mvPolynomialUnitScaleEquiv u (rationalDiagonalPolynomialDerivation omega P) =
      rationalDiagonalPolynomialDerivation omega (mvPolynomialUnitScaleEquiv u P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rationalDiagonalPolynomialDerivation]
  | add P Q hP hQ =>
      calc
        mvPolynomialUnitScaleEquiv u
            (rationalDiagonalPolynomialDerivation omega (P + Q)) =
            mvPolynomialUnitScaleEquiv u
              (rationalDiagonalPolynomialDerivation omega P) +
              mvPolynomialUnitScaleEquiv u
                (rationalDiagonalPolynomialDerivation omega Q) := by simp
        _ = rationalDiagonalPolynomialDerivation omega
              (mvPolynomialUnitScaleEquiv u P) +
              rationalDiagonalPolynomialDerivation omega
                (mvPolynomialUnitScaleEquiv u Q) := by rw [hP, hQ]
        _ = rationalDiagonalPolynomialDerivation omega
              (mvPolynomialUnitScaleEquiv u (P + Q)) := by simp
  | mul_X P i hP =>
      have hX :
          mvPolynomialUnitScaleEquiv u
              (rationalDiagonalPolynomialDerivation omega (MvPolynomial.X i)) =
            rationalDiagonalPolynomialDerivation omega
              (mvPolynomialUnitScaleEquiv u (MvPolynomial.X i)) := by
        calc
          mvPolynomialUnitScaleEquiv u
              (rationalDiagonalPolynomialDerivation omega (MvPolynomial.X i)) =
              MvPolynomial.C (Complex.I * (omega i : ℂ)) *
                (MvPolynomial.C (u i : ℂ) * MvPolynomial.X i) := by
                  rw [rationalDiagonalPolynomialDerivation_X, map_mul,
                    mvPolynomialUnitScaleEquiv_X]
                  simp
          _ = rationalDiagonalPolynomialDerivation omega
                (mvPolynomialUnitScaleEquiv u (MvPolynomial.X i)) := by
                  rw [mvPolynomialUnitScaleEquiv_X, Derivation.leibniz]
                  simp [rationalDiagonalPolynomialDerivation, smul_eq_mul]
                  ring
      calc
        mvPolynomialUnitScaleEquiv u
            (rationalDiagonalPolynomialDerivation omega
              (P * MvPolynomial.X i)) =
            mvPolynomialUnitScaleEquiv u P *
                mvPolynomialUnitScaleEquiv u
                  (rationalDiagonalPolynomialDerivation omega (MvPolynomial.X i)) +
              mvPolynomialUnitScaleEquiv u (MvPolynomial.X i) *
                mvPolynomialUnitScaleEquiv u
                  (rationalDiagonalPolynomialDerivation omega P) := by
                    rw [Derivation.leibniz]
                    simp only [smul_eq_mul, map_add, map_mul]
        _ = mvPolynomialUnitScaleEquiv u P *
                rationalDiagonalPolynomialDerivation omega
                  (mvPolynomialUnitScaleEquiv u (MvPolynomial.X i)) +
              mvPolynomialUnitScaleEquiv u (MvPolynomial.X i) *
                rationalDiagonalPolynomialDerivation omega
                  (mvPolynomialUnitScaleEquiv u P) := by rw [hP, hX]
        _ = rationalDiagonalPolynomialDerivation omega
              (mvPolynomialUnitScaleEquiv u P *
                mvPolynomialUnitScaleEquiv u (MvPolynomial.X i)) := by
                  simpa only [smul_eq_mul] using
                    ((rationalDiagonalPolynomialDerivation omega).leibniz
                      (mvPolynomialUnitScaleEquiv u P)
                      (mvPolynomialUnitScaleEquiv u (MvPolynomial.X i))).symm
        _ = rationalDiagonalPolynomialDerivation omega
              (mvPolynomialUnitScaleEquiv u (P * MvPolynomial.X i)) := by
                exact congrArg (rationalDiagonalPolynomialDerivation omega)
                  (map_mul (mvPolynomialUnitScaleEquiv u) P (MvPolynomial.X i)).symm

/-- Quotient-rule extension of the diagonal derivation to the multivariate
rational function field. -/
def rationalDiagonalDerivation (omega : Fin r → ℝ) :
    Derivation ℂ
      (FractionRing (MvPolynomial (Fin r) ℂ))
      (FractionRing (MvPolynomial (Fin r) ℂ)) :=
  fractionRingDerivation
    ((Algebra.linearMap (MvPolynomial (Fin r) ℂ)
      (FractionRing (MvPolynomial (Fin r) ℂ))).compDer
        (rationalDiagonalPolynomialDerivation omega))

@[simp] theorem rationalDiagonalDerivation_algebraMap
    (omega : Fin r → ℝ) (P : MvPolynomial (Fin r) ℂ) :
    rationalDiagonalDerivation omega
        (algebraMap (MvPolynomial (Fin r) ℂ)
          (FractionRing (MvPolynomial (Fin r) ℂ)) P) =
      algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ))
          (rationalDiagonalPolynomialDerivation omega P) := by
  rw [rationalDiagonalDerivation, fractionRingDerivation_algebraMap]
  rfl

@[simp] theorem rationalDiagonalDerivation_coordinate
    (omega : Fin r → ℝ) (i : Fin r) :
    rationalDiagonalDerivation omega (rationalTorusCoordinate i) =
      algebraMap ℂ (FractionRing (MvPolynomial (Fin r) ℂ))
          (Complex.I * (omega i : ℂ)) * rationalTorusCoordinate i := by
  rw [rationalTorusCoordinate, rationalDiagonalDerivation_algebraMap,
    rationalDiagonalPolynomialDerivation_X, map_mul]
  rfl

/-- Coordinate scaling commutes with the diagonal rational derivation. -/
theorem rationalTorusScaleEquiv_rationalDiagonalDerivation
    (omega : Fin r → ℝ) (u : Fin r → ℂˣ)
    (z : FractionRing (MvPolynomial (Fin r) ℂ)) :
    rationalTorusScaleEquiv u (rationalDiagonalDerivation omega z) =
      rationalDiagonalDerivation omega (rationalTorusScaleEquiv u z) := by
  let sigma := (rationalTorusScaleEquiv u).toRingEquiv
  let D := rationalDiagonalDerivation omega
  let Dc : Derivation ℂ
      (FractionRing (MvPolynomial (Fin r) ℂ))
      (FractionRing (MvPolynomial (Fin r) ℂ)) :=
    conjugateDerivation (RingEquiv.refl ℂ) sigma
      (fun c => by simp [sigma]) D
  have hDc : Dc = D := by
    apply fractionRing_derivation_ext
      (A := MvPolynomial (Fin r) ℂ)
    intro P
    change sigma.symm
        (D (sigma
          (algebraMap (MvPolynomial (Fin r) ℂ)
            (FractionRing (MvPolynomial (Fin r) ℂ)) P))) =
      D (algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ)) P)
    apply sigma.injective
    rw [sigma.apply_symm_apply]
    change rationalDiagonalDerivation omega
        (rationalTorusScaleEquiv u
          (algebraMap (MvPolynomial (Fin r) ℂ)
            (FractionRing (MvPolynomial (Fin r) ℂ)) P)) =
      rationalTorusScaleEquiv u
        (rationalDiagonalDerivation omega
          (algebraMap (MvPolynomial (Fin r) ℂ)
            (FractionRing (MvPolynomial (Fin r) ℂ)) P))
    rw [rationalTorusScaleEquiv_algebraMap,
      rationalDiagonalDerivation_algebraMap,
      rationalDiagonalDerivation_algebraMap,
      rationalTorusScaleEquiv_algebraMap]
    exact congrArg
      (algebraMap (MvPolynomial (Fin r) ℂ)
        (FractionRing (MvPolynomial (Fin r) ℂ)))
      (mvPolynomialUnitScaleEquiv_rationalDiagonalPolynomialDerivation omega u P).symm
  have hz := congrArg (fun E : Derivation ℂ
      (FractionRing (MvPolynomial (Fin r) ℂ))
      (FractionRing (MvPolynomial (Fin r) ℂ)) => E z) hDc
  change sigma.symm (D (sigma z)) = D z at hz
  have hs := congrArg sigma hz
  simpa [sigma, D] using hs.symm

end

end GaloisForLFunctions.HTGeometry
