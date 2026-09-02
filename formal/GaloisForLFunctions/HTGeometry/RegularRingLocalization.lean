import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Regular rings survive localization

Mathlib proves that polynomial rings over regular rings are regular, but this toolchain does not
yet provide the complementary localization instance.  A prime-local ring of a localization is the
same localization of the original ring at the contracted prime, so regularity transports through
the canonical localization equivalence.

This is the local-regularity input for the marked observation and source charts, both principal
localizations of multivariable polynomial rings.
-/

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R]

/-- **Every localization of a regular ring is regular.** -/
instance (priority := low) regularRing_localization (M : Submonoid R) [IsRegularRing R] :
    IsRegularRing (Localization M) := by
  rw [isRegularRing_iff]
  intro p hp
  let q := Ideal.under R p
  haveI : q.IsPrime := hp.comap _
  haveI : IsLocalization.AtPrime (Localization.AtPrime p) q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime p) p
  haveI : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularRing.isRegularLocalRing_localization q
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl
      (Localization.AtPrime q) (Localization.AtPrime p)).toRingEquiv

end GaloisForLFunctions.HTGeometry
