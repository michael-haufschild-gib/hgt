/-
Copyright (c) 2026 GaloisForLFunctions contributors. All rights reserved.
-/

import GaloisForLFunctions.HTGeometry.FinitePlaceTransport
import GaloisForLFunctions.RHTower.ArtinNumberFieldLocalEulerFactor

/-!
# Rational-prime Artin local Euler factors

Specializes the choice-free number-field finite-place Euler polynomial to the canonical finite
place of `ℚ` attached to each rational prime.
-/

open scoped NumberField

noncomputable section

namespace GaloisForLFunctions

/-- The canonical finite place of `ℚ` associated with a natural prime. -/
noncomputable def rationalPrimeFinitePlace (p : ℕ) (hp : p.Prime) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  heightOneSpectrumRatOfNatPrime hp

/-- Choice-free Artin local Euler polynomial attached to a rational prime. -/
noncomputable def rationalPrimeLocalEulerPolynomial (L : Type) {G V : Type}
    [Field L] [NumberField L] [Algebra ℚ L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (p : ℕ) (hp : p.Prime)
    (ρ : Representation ℂ G V) : Polynomial ℂ :=
  numberFieldFinitePlaceLocalEulerPolynomial (K := ℚ) (L := L)
    (rationalPrimeFinitePlace p hp) ρ

/-- Every maximal prime above the canonical rational finite place computes its local factor. -/
theorem frobeniusInertiaEulerPolynomial_eq_rationalPrimeLocalEulerPolynomial
    (L : Type) {G V : Type} [Field L] [NumberField L] [Algebra ℚ L]
    [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G ℚ L]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (p : ℕ) (hp : p.Prime) (Q : Ideal (𝓞 L))
    [Q.IsMaximal] [Q.LiesOver (rationalPrimeFinitePlace p hp).asIdeal]
    (ρ : Representation ℂ G V) :
    frobeniusInertiaEulerPolynomial (R := 𝓞 ℚ) Q ρ =
      rationalPrimeLocalEulerPolynomial L p hp ρ :=
  frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
    (K := ℚ) (L := L) (rationalPrimeFinitePlace p hp) Q ρ

end GaloisForLFunctions
