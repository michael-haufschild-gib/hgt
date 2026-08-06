import GaloisForLFunctions.HTGeometry.LocalNoetherianNormalDVR
import Mathlib.RingTheory.Localization.Submodule

/-!
# The local ring at a prime divisor is a discrete valuation ring

On a normal variety the local ring along a prime divisor is a discrete valuation ring.  In
commutative algebra this is the statement that a Noetherian integrally closed domain localised at
a height-one prime is a discrete valuation ring.

mathlib provides this only for Dedekind domains, where every nonzero prime already has height one.
The general height-one statement, which is what a variety of arbitrary dimension needs, is proved
here: the localisation is Noetherian and integrally closed, and its Krull dimension is the height
of the prime, so the local criterion for a discrete valuation ring applies.
-/

namespace GaloisForLFunctions.HTGeometry

open IsLocalRing

variable {B : Type*} [CommRing B]

/-- The Krull dimension of the local ring at a prime divisor is one. -/
theorem ringKrullDim_localizationAtPrime {P : Ideal B} [P.IsPrime] (hP : P.height = 1) :
    ringKrullDim (Localization.AtPrime P) = 1 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hP]
  rfl

/-- The local ring at a prime divisor is not a field. -/
theorem not_isField_localizationAtPrime {P : Ideal B} [P.IsPrime] (hP : P.height = 1) :
    ¬ IsField (Localization.AtPrime P) :=
  not_isField_of_ringKrullDim_eq_one (ringKrullDim_localizationAtPrime hP)

/-- Every nonzero prime of the local ring at a prime divisor is maximal. -/
theorem dimensionLEOne_localizationAtPrime [IsDomain B] {P : Ideal B} [P.IsPrime]
    (hP : P.height = 1) :
    Ring.DimensionLEOne (Localization.AtPrime P) :=
  dimensionLEOne_of_ringKrullDim_eq_one (ringKrullDim_localizationAtPrime hP)

/-- **The local ring at a prime divisor of a normal variety is a discrete valuation ring.** -/
theorem isDiscreteValuationRing_localizationAtPrime [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] {P : Ideal B} [P.IsPrime]
    (hP : P.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  haveI : IsIntegrallyClosed (Localization.AtPrime P) :=
    isIntegrallyClosed_of_isLocalization _ P.primeCompl
      (Ideal.primeCompl_le_nonZeroDivisors P)
  exact isDiscreteValuationRing_of_ringKrullDim_eq_one (ringKrullDim_localizationAtPrime hP)

end GaloisForLFunctions.HTGeometry
