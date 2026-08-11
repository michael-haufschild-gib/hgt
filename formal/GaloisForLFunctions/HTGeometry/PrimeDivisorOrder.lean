import GaloisForLFunctions.HTGeometry.LocalizationAtPrimeDivisorDVR
import GaloisForLFunctions.HTGeometry.DivisorSupportFinite
import GaloisForLFunctions.HTGeometry.RingOrdRamification
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The order of a function along a prime divisor

On a normal variety every prime divisor carries a discrete valuation, namely the additive
valuation of the local ring there.  This module packages that valuation as the order of a ring
element along a prime divisor and identifies its support: the order is nonzero exactly at the
prime divisors containing the element, so by finiteness of minimal primes a nonzero element has
finite divisorial support.

This ties the valuation layer of the eigenvolume ramification system to the finiteness layer: the
`hfin` hypothesis of the abstract system is the finiteness proved here, for the order function
actually attached to a ring element.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable (B : Type*) [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]

/-- A prime divisor: a height-one prime ideal. -/
def PrimeDivisor : Type _ := {P : Ideal B // P.IsPrime ∧ P.height = 1}

variable {B}

instance (P : PrimeDivisor B) : P.1.IsPrime := P.2.1

/-- The local ring at a prime divisor is a discrete valuation ring. -/
instance isDiscreteValuationRing_primeDivisor (P : PrimeDivisor B) :
    IsDiscreteValuationRing (Localization.AtPrime P.1) :=
  isDiscreteValuationRing_localizationAtPrime P.2.2

/-- Order of a ring element along a prime divisor. -/
noncomputable def orderAt (P : PrimeDivisor B) (a : B) : ℕ∞ :=
  addVal (Localization.AtPrime P.1) (algebraMap B (Localization.AtPrime P.1) a)

/-- **The order vanishes exactly off the prime divisor.** -/
theorem orderAt_ne_zero_iff (P : PrimeDivisor B) (a : B) :
    orderAt P a ≠ 0 ↔ a ∈ P.1 := by
  constructor
  · intro h
    by_contra hmem
    exact h (addVal_of_isUnit_target ((IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime P.1) P.1 a).mpr hmem))
  · intro hmem hzero
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime P.1) P.1 a).mp (isUnit_of_addVal_eq_zero hzero)) hmem

/-- **A nonzero element has finite divisorial support.** -/
theorem finite_orderAt_support {a : B} (ha : a ≠ 0) :
    {P : PrimeDivisor B | orderAt P a ≠ 0}.Finite := by
  have hsub : (fun P : PrimeDivisor B => P.1) ''
      {P : PrimeDivisor B | orderAt P a ≠ 0} ⊆
      {p : Ideal B | p.IsPrime ∧ p.height = 1 ∧ a ∈ p} := by
    rintro p ⟨P, hP, rfl⟩
    exact ⟨P.2.1, P.2.2, (orderAt_ne_zero_iff P a).mp hP⟩
  have hfin := Set.Finite.subset (finite_heightOneSupport ha) hsub
  exact Set.Finite.of_finite_image hfin (fun _ _ _ _ h => Subtype.ext h)

end GaloisForLFunctions.HTGeometry
