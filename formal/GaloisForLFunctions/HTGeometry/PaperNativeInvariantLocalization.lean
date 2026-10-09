import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.LocalizationLND
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.FactorialClosure
import GaloisForLFunctions.HTGeometry.LocalizationDerivationExt
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Invariant localization and the native quotient-rule derivation

The source's invariant-denominator construction equals the corpus's general
localization derivation. Its local nilpotence therefore transfers to that
existing operator. Factorial closure supplies the converse: a locally
nilpotent derivation on a characteristic-zero domain kills every unit.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable {k A S : Type*} [CommRing k] [CommRing A] [CommRing S]
  [Algebra k A] [Algebra A S] [Algebra k S] [IsScalarTower k A S]

/-- The existing quotient-rule extension, with its codomain map made explicit. -/
def paperNativeLocalization (M : Submonoid A) [IsLocalization M S]
    (D : Derivation k A A) : Derivation k S S :=
  localizationDerivation M ((Algebra.linearMap A S).compDer D)

@[simp] theorem paperNativeLocalization_algebraMap
    (M : Submonoid A) [IsLocalization M S] (D : Derivation k A A) (a : A) :
    paperNativeLocalization (S := S) M D (algebraMap A S a) = algebraMap A S (D a) := by
  exact localizationDerivation_algebraMap M _ a

/-- The source extension is literally the native operator on invariant localizations. -/
theorem paperInvariantLocalization_eq_native
    (M : Submonoid A) [IsLocalization M S] (D : Derivation k A A)
    (hM : ∀ a : M, D (a : A) = 0) :
    LocalizationLND.localizeTo D M hM S = paperNativeLocalization M D := by
  have heq := localizationDerivation_ext M
    ((LocalizationLND.localizeTo D M hM S).restrictScalars ℤ)
    ((paperNativeLocalization (S := S) M D).restrictScalars ℤ) (fun a => by
      change LocalizationLND.localizeTo D M hM S (algebraMap A S a) =
        paperNativeLocalization M D (algebraMap A S a)
      rw [LocalizationLND.localizeTo_algebraMap, paperNativeLocalization_algebraMap])
  ext a
  exact congrArg (fun E : Derivation ℤ S S => E a) heq

theorem paperNativeLocalization_locallyNilpotent
    (M : Submonoid A) [IsLocalization M S] (D : Derivation k A A)
    (hM : ∀ a : M, D (a : A) = 0) (hD : IsLocallyNilpotent D) :
    IsLocallyNilpotent (paperNativeLocalization (S := S) M D) := by
  rw [← paperInvariantLocalization_eq_native M D hM]
  exact LocalizationLND.localizeTo_locallyNilpotent D M hM S hD

/-- Factorial closure forces every unit to be fixed. -/
theorem paperLocallyNilpotent_kills_unit [IsDomain A] [CharZero A]
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) (u : Aˣ) : D (u : A) = 0 := by
  exact (lnd_factorial_closure D hD u.ne_zero u⁻¹.ne_zero (by simp)).1

/-- Exact boundary for the native extension of a locally nilpotent derivation.
The zero-denominator case is included, so no nonvanishing premise is needed. -/
theorem paperNativeAway_locallyNilpotent_iff [IsDomain A] [CharZero A]
    (D : Derivation k A A) (hD : IsLocallyNilpotent D) (a : A) :
    IsLocallyNilpotent
      (paperNativeLocalization (S := Localization.Away a) (Submonoid.powers a) D) ↔
        D a = 0 := by
  constructor
  · intro hlocal
    by_cases ha : a = 0
    · simp [ha]
    let S := Localization.Away a
    letI : IsDomain S := IsLocalization.Away.isDomain S ha
    have hinj : Function.Injective (algebraMap A S) :=
      IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
    letI : CharZero S := ⟨fun m n h => Nat.cast_injective
      (hinj (by simpa only [map_natCast] using h))⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units S
      (⟨a, Submonoid.mem_powers a⟩ : Submonoid.powers a)
    have hzero := paperLocallyNilpotent_kills_unit
      (paperNativeLocalization (S := S) (Submonoid.powers a) D) hlocal u
    rw [hu, paperNativeLocalization_algebraMap] at hzero
    apply hinj
    simpa only [map_zero] using hzero
  · intro ha
    exact paperNativeLocalization_locallyNilpotent (Submonoid.powers a) D
      (LocalizationLND.annihilates_powers D a ha) hD

end

end GaloisForLFunctions.HTGeometry
