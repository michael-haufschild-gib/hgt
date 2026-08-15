import GaloisForLFunctions.RHTower.ArtinLocalEulerPrimeDescent
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Base-prime local Euler polynomials for number-field Artin representations

The local Artin Euler polynomial is made into an actual function of a maximal ideal of the ring of
integers of the base number field.  Internally, a maximal ideal above that base prime is chosen by
going-up; the previously proved same-base-prime invariance proves that every other such choice has
the same polynomial.

This is the finite-place local factor only.  It does not form an Euler product or prove any
analytic property of an Artin `L`-function.
-/

open scoped NumberField Pointwise

noncomputable section

universe u

namespace GaloisForLFunctions

section ChosenPrimeAbove

variable {A B : Type u}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [Algebra.IsIntegral A B] [FaithfulSMul A B]

/-- A concrete maximal ideal above a maximal ideal in an integral faithful extension. -/
noncomputable def chosenMaximalPrimeAbove (p : MaximalSpectrum A) : Ideal B :=
  (Ideal.exists_maximal_ideal_liesOver_of_isIntegral p.asIdeal).choose

/-- The chosen ideal above a maximal base ideal is maximal. -/
theorem chosenMaximalPrimeAbove_isMaximal (p : MaximalSpectrum A) :
    (chosenMaximalPrimeAbove (A := A) (B := B) p).IsMaximal :=
  (Ideal.exists_maximal_ideal_liesOver_of_isIntegral p.asIdeal).choose_spec.1

/-- The chosen ideal lies over its prescribed maximal base ideal. -/
theorem chosenMaximalPrimeAbove_liesOver (p : MaximalSpectrum A) :
    (chosenMaximalPrimeAbove (A := A) (B := B) p).LiesOver p.asIdeal :=
  (Ideal.exists_maximal_ideal_liesOver_of_isIntegral p.asIdeal).choose_spec.2

end ChosenPrimeAbove

section NumberField

variable {K L G V : Type u}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The actual Artin local Euler polynomial at a maximal prime of the base number field.
No prime ideal above it appears in the public interface. -/
noncomputable def numberFieldLocalEulerPolynomial
    (p : MaximalSpectrum (𝓞 K)) (ρ : Representation ℂ G V) : Polynomial ℂ :=
  let Q := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q.IsMaximal := chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q.IsPrime := (inferInstance : Q.IsMaximal).isPrime
  letI : Finite ((𝓞 L) ⧸ Q) := inferInstance
  frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρ

/-- Any actual maximal prime above the base prime computes the same base-prime local polynomial. -/
theorem frobeniusInertiaEulerPolynomial_eq_numberFieldLocalEulerPolynomial
    (p : MaximalSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q.LiesOver p.asIdeal]
    (ρ : Representation ℂ G V) :
    frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρ =
      numberFieldLocalEulerPolynomial (K := K) (L := L) p ρ := by
  let Q₀ := chosenMaximalPrimeAbove (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q₀.IsMaximal := chosenMaximalPrimeAbove_isMaximal (A := 𝓞 K) (B := 𝓞 L) p
  letI : Q₀.IsPrime := (inferInstance : Q₀.IsMaximal).isPrime
  letI : Q₀.LiesOver p.asIdeal :=
    chosenMaximalPrimeAbove_liesOver (A := 𝓞 K) (B := 𝓞 L) p
  letI : Finite ((𝓞 L) ⧸ Q₀) := inferInstance
  change frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρ =
    frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q₀ ρ
  apply frobeniusInertiaEulerPolynomial_eq_of_under_eq
  rw [← Ideal.over_def Q p.asIdeal, ← Ideal.over_def Q₀ p.asIdeal]

/-- The local Artin Euler polynomial indexed by a finite prime of the base number field. -/
noncomputable def numberFieldFinitePlaceLocalEulerPolynomial
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (ρ : Representation ℂ G V) : Polynomial ℂ :=
  numberFieldLocalEulerPolynomial (K := K) (L := L)
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal } ρ

/-- Every prime above a finite base prime computes its canonical local Euler polynomial. -/
theorem frobeniusInertiaEulerPolynomial_eq_numberFieldFinitePlaceLocalEulerPolynomial
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (Q : Ideal (𝓞 L)) [Q.IsMaximal] [Q.LiesOver v.asIdeal]
    (ρ : Representation ℂ G V) :
    frobeniusInertiaEulerPolynomial (R := 𝓞 K) Q ρ =
      numberFieldFinitePlaceLocalEulerPolynomial (K := K) (L := L) v ρ := by
  exact frobeniusInertiaEulerPolynomial_eq_numberFieldLocalEulerPolynomial
    { asIdeal := v.asIdeal, isMaximal := v.isMaximal } Q ρ

end NumberField

end GaloisForLFunctions
