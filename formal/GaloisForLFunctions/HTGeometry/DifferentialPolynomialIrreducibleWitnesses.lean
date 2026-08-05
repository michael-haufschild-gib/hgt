import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient
import Mathlib.Algebra.MvPolynomial.Division

/-!
# Irreducible differential polynomials exist

The Lüroth component transfer is stated for an irreducible differential polynomial, and nothing
exhibited one.  Every jet variable is prime in the differential polynomial ring — the ring is a
polynomial ring on the jet coordinates over a field — and a prime element of a domain is
irreducible.

So each jet coordinate, at every order, is an irreducible differential polynomial.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- Every jet coordinate is a prime differential polynomial. -/
theorem differentialPolynomial_X_prime {ι K : Type*} [Field K] (c : ι × ℕ) :
    Prime (MvPolynomial.X c : DifferentialPolynomial ι K) :=
  MvPolynomial.X_prime (i := c)

/-- **Every jet coordinate is an irreducible differential polynomial.** -/
theorem differentialPolynomial_X_irreducible {ι K : Type*} [Field K] (c : ι × ℕ) :
    Irreducible (MvPolynomial.X c : DifferentialPolynomial ι K) :=
  (differentialPolynomial_X_prime c).irreducible

/-- Hence the irreducibility premise of the component-transfer layer is realized at every jet
order. -/
theorem exists_irreducible_differentialPolynomial {ι K : Type*} [Field K] [Nonempty ι] (n : ℕ) :
    ∃ P : DifferentialPolynomial ι K, Irreducible P :=
  ⟨MvPolynomial.X (Classical.arbitrary ι, n),
    differentialPolynomial_X_irreducible (Classical.arbitrary ι, n)⟩

/-- **Irreducibility transports along the two-block splitting**, an algebra equivalence. -/
theorem irreducible_differentialPolynomialTwoBlockEquiv {F : Type*} [CommRing F]
    {P : DifferentialPolynomial (Unit ⊕ Unit) F} (hP : Irreducible P) :
    Irreducible (differentialPolynomialTwoBlockEquiv F P) :=
  (MulEquiv.irreducible_iff (differentialPolynomialTwoBlockEquiv F).toMulEquiv).mpr hP

/-- So the two-block layer's irreducibility premise is realized by the image of a jet
coordinate. -/
theorem exists_irreducible_differentialPolynomialTwoBlockEquiv {F : Type*} [Field F] (n : ℕ) :
    ∃ P : DifferentialPolynomial (Unit ⊕ Unit) F,
      Irreducible P ∧ Irreducible (differentialPolynomialTwoBlockEquiv F P) :=
  ⟨MvPolynomial.X (Sum.inl (), n),
    differentialPolynomial_X_irreducible (Sum.inl (), n),
    irreducible_differentialPolynomialTwoBlockEquiv
      (differentialPolynomial_X_irreducible (Sum.inl (), n))⟩

end GaloisForLFunctions
