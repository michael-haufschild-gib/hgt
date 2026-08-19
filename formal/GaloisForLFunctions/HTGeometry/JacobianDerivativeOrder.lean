import GaloisForLFunctions.HTGeometry.MonogenicKaehlerAnnihilator
import GaloisForLFunctions.HTGeometry.PresentationDifferentJacobian
import GaloisForLFunctions.HTGeometry.DifferentExponentTame

/-!
# The presentation Jacobian and the derivative of the minimal polynomial

Both compute the annihilator of the relative differentials of a monogenic extension of a discrete
valuation ring — the Jacobian through the Smith-normal-form computation at corank one, the
derivative through the monogenic normal form — so they generate the same ideal and have the same
divisorial order:

```text
span_jacobian_eq_span_aeval_derivative
    ** (P.jacobian) = (p'(x)) **
addVal_aeval_derivative_eq_addVal_jacobian
    ** v(p'(x)) = v(P.jacobian) **
```

This is the step that converts a statement about the *concrete* Jacobian of a presentation into one
about the different: `DifferentIdealMonogenic.differentIdeal_eq_span_aeval_derivative` makes
`(p'(x))` the different, and `RamificationIndexTwoFromDerivative` turns a derivative of order one
into ramification index two.  So a presentation whose Jacobian has divisorial order one is a simple
fold.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial

variable {A B : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
variable [NoZeroSMulDivisors A B] {N : ℕ}

/-- **The presentation Jacobian and the derivative of the minimal polynomial generate the same
ideal.**  Both compute the annihilator of the relative differentials: the first through the
Smith-normal-form computation at corank one, the second through the monogenic normal form. -/
theorem span_jacobian_eq_span_aeval_derivative
    {x : B} (hx : IsIntegral A x) (hadj : Algebra.adjoin A ({x} : Set B) = ⊤)
    (P : Algebra.PreSubmersivePresentation A B (Fin (N + 1)) (Fin (N + 1)))
    (hmap : P.map = _root_.id)
    (hdet : ((LinearMap.toMatrix' P.aevalDifferential).map (IsLocalRing.residue B)).det = 0)
    {r c : Fin N → Fin (N + 1)}
    (hB : (((LinearMap.toMatrix' P.aevalDifferential).map
      (IsLocalRing.residue B)).submatrix r c).det ≠ 0) :
    Ideal.span {P.jacobian}
      = Ideal.span {Polynomial.aeval x (Polynomial.derivative (minpoly A x))} := by
  rw [← annihilator_kaehler_eq_span_jacobian_of_det_eq_zero P hmap hdet hB,
    annihilator_kaehler_monogenic hx hadj]

/-- **The Jacobian and the derivative of the minimal polynomial have the same divisorial order.** -/
theorem addVal_aeval_derivative_eq_addVal_jacobian
    {x : B} (hx : IsIntegral A x) (hadj : Algebra.adjoin A ({x} : Set B) = ⊤)
    (P : Algebra.PreSubmersivePresentation A B (Fin (N + 1)) (Fin (N + 1)))
    (hmap : P.map = _root_.id)
    (hdet : ((LinearMap.toMatrix' P.aevalDifferential).map (IsLocalRing.residue B)).det = 0)
    {r c : Fin N → Fin (N + 1)}
    (hB : (((LinearMap.toMatrix' P.aevalDifferential).map
      (IsLocalRing.residue B)).submatrix r c).det ≠ 0) :
    IsDiscreteValuationRing.addVal B
        (Polynomial.aeval x (Polynomial.derivative (minpoly A x)))
      = IsDiscreteValuationRing.addVal B P.jacobian :=
  addVal_eq_of_span_singleton_eq
    (span_jacobian_eq_span_aeval_derivative hx hadj P hmap hdet hB).symm

end

end GaloisForLFunctions.HTGeometry
