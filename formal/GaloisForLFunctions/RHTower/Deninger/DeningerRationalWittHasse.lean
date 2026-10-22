import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittSource

/-!
# Hasse detection for the rational-Witt source

The canonical power-series chart is faithful on Deninger's localized-polynomial source.  Thus its
realized power-series range is ring-equivalent to the global source, and both localized rational
functions and rational-Witt elements satisfy an equality-detection principle in that chart.
-/

namespace RHTower

noncomputable section

/-- Deninger's localized-polynomial source is ring-equivalent to the power-series points it
realizes. -/
noncomputable def deningerRationalWittLocalizationPowerSeriesHasseEquivRange
    (A : Type*) [CommRing A] :
    DeningerRationalWittLocalization A ≃+*
      RingHom.range (deningerRationalWittLocalizationToPowerSeries A) :=
  RingEquiv.ofBijective
    (RingHom.rangeRestrict (deningerRationalWittLocalizationToPowerSeries A))
    ⟨fun _ _ h => deningerRationalWittLocalizationToPowerSeries_injective A
        (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩

/-- The realized-range equivalence evaluates through the canonical power-series chart. -/
@[simp] theorem deningerRationalWittLocalizationPowerSeriesHasseEquivRange_apply
    (A : Type*) [CommRing A]
    (x : DeningerRationalWittLocalization A) :
    (deningerRationalWittLocalizationPowerSeriesHasseEquivRange A x).1 =
      deningerRationalWittLocalizationToPowerSeries A x := by
  rfl

/-- Two localized rational-Witt source elements agree exactly when their formal power-series
charts agree. -/
theorem deningerRationalWittLocalizationPowerSeries_congr_hasse_iff
    (A : Type*) [CommRing A]
    (x y : DeningerRationalWittLocalization A) :
    deningerRationalWittLocalizationToPowerSeries A x =
      deningerRationalWittLocalizationToPowerSeries A y ↔ x = y := by
  constructor
  · intro h
    exact deningerRationalWittLocalizationToPowerSeries_injective A h
  · exact congrArg _

/-- Two rational-Witt elements agree exactly when their big-Witt power-series realizations agree. -/
theorem deningerRationalWittAdditivePowerSeries_congr_hasse_iff
    (A : Type*) [CommRing A]
    (x y : DeningerRationalWittAdditive A) :
    deningerRationalWittToBigWittAdditive A x =
      deningerRationalWittToBigWittAdditive A y ↔ x = y := by
  constructor
  · intro h
    exact deningerRationalWittToBigWittAdditive_injective A h
  · exact congrArg _

end


end RHTower
