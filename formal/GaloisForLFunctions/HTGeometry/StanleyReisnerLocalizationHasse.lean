import GaloisForLFunctions.HTGeometry.StanleyReisnerTranslationRegular

/-!
# Hasse detection by Stanley--Reisner translation localization

Inverting all translated vertices does not collapse a global Stanley--Reisner class.  The global
quotient ring is therefore equivalent to the localized classes it actually realizes, and equality
is detected after localization.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v

/-- The global Stanley--Reisner quotient is ring-equivalent to its realized translated-vertex
localization range. -/
noncomputable def stanleyReisnerTranslationLocalizationHasseEquivRealizedRange
    (R : Type u) (α : Type v) [CommRing R] [IsDomain R]
    [Fintype α] [DecidableEq α] (facets : Finset (Finset α)) :
    (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) ≃+*
      RingHom.range (algebraMap
        (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
        (StanleyReisnerTranslationLocalization R α facets)) :=
  RingEquiv.ofBijective
    (RingHom.rangeRestrict (algebraMap
      (MvPolynomial α R ⧸ stanleyReisnerIdeal R facets)
      (StanleyReisnerTranslationLocalization R α facets)))
    ⟨fun _ _ h => stanleyReisnerTranslationLocalization_algebraMap_injective
        (R := R) facets (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- The realized-range equivalence evaluates by the localization algebra map. -/
@[simp] theorem stanleyReisnerTranslationLocalizationHasseEquivRealizedRange_apply
    (R : Type u) (α : Type v) [CommRing R] [IsDomain R]
    [Fintype α] [DecidableEq α] (facets : Finset (Finset α))
    (x : MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    (stanleyReisnerTranslationLocalizationHasseEquivRealizedRange R α facets x).1 =
      algebraMap _ (StanleyReisnerTranslationLocalization R α facets) x := by
  rfl

/-- Two global Stanley--Reisner classes are equal exactly when their translated-vertex
localizations agree. -/
theorem stanleyReisnerTranslationLocalization_congr_hasse_iff
    (R : Type u) (α : Type v) [CommRing R] [IsDomain R]
    [Fintype α] [DecidableEq α] (facets : Finset (Finset α))
    (x y : MvPolynomial α R ⧸ stanleyReisnerIdeal R facets) :
    algebraMap _ (StanleyReisnerTranslationLocalization R α facets) x =
      algebraMap _ (StanleyReisnerTranslationLocalization R α facets) y ↔ x = y := by
  constructor
  · intro h
    exact stanleyReisnerTranslationLocalization_algebraMap_injective (R := R) facets h
  · exact congrArg _

end GaloisForLFunctions.HTGeometry
