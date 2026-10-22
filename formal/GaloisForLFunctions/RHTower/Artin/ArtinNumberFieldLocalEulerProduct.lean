import GaloisForLFunctions.RHTower.Artin.ArtinNumberFieldLocalEulerFactor
import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerProduct

/-!
# Direct-sum product law at number-field finite places

This is the base-prime version of the genuine local Artin source identity.  It combines the
choice-free finite-place polynomial with the concrete Frobenius--inertia direct-sum product law.
It contains no infinite Euler product, convergence, continuation, or holomorphy assertion.
-/

open scoped NumberField

noncomputable section

universe u

namespace GaloisForLFunctions

variable {K L G V W : Type u}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
variable [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- Choice-free finite-place Artin local Euler polynomials multiply under direct sums. -/
theorem numberFieldFinitePlaceLocalEulerPolynomial_prod
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρV : Representation ℂ G V) (ρW : Representation ℂ G W) :
    numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v (ρV.prod ρW) =
      numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρV *
        numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρW := by
  let p : MaximalSpectrum (𝓞 K) :=
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal }
  let Q := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q.IsMaximal :=
    chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q.IsPrime := (inferInstance : Q.IsMaximal).isPrime
  letI : Finite ((𝓞 L) ⧸ Q) := inferInstance
  change frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q (ρV.prod ρW) =
    frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρV *
      frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρW
  exact frobeniusInertiaEulerPolynomial_prod (R := 𝓞 K) Q ρV ρW

end GaloisForLFunctions
