import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local rings at points of polynomial quotients

These abbreviations and canonical instances name the two local rings in a polynomial quotient
presentation.  Keeping these types explicit avoids repeatedly reducing large nested `let`
expressions in downstream Jacobian-chart declarations.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev quotientPointIdeal {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    Ideal ((MvPolynomial σ ℂ) ⧸ I) := p.asIdeal

abbrev polynomialPointIdeal {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    Ideal (MvPolynomial σ ℂ) :=
  p.asIdeal.comap (Ideal.Quotient.mk I)

abbrev localPolynomialRing {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :=
  Localization.AtPrime (polynomialPointIdeal I p)

abbrev localQuotientRing {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :=
  Localization.AtPrime (quotientPointIdeal I p)

instance {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    (quotientPointIdeal I p).LiesOver (polynomialPointIdeal I p) := ⟨rfl⟩

noncomputable instance {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :
    Algebra (localPolynomialRing I p) (localQuotientRing I p) :=
  Localization.AtPrime.algebraOfLiesOver
    (polynomialPointIdeal I p) (quotientPointIdeal I p)

abbrev localPresentationKernel {σ : Type} (I : Ideal (MvPolynomial σ ℂ))
    (p : PrimeSpectrum ((MvPolynomial σ ℂ) ⧸ I)) :=
  RingHom.ker (algebraMap (localPolynomialRing I p) (localQuotientRing I p))

end

end GaloisForLFunctions.HTGeometry
