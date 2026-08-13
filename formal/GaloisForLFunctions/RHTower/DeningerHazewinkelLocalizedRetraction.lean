import GaloisForLFunctions.RHTower.DeningerHazewinkelLocalizedCoordinates

/-!
# Retraction of the localized Hazewinkel parameter chart

This module maps the finite localized parameter ring back to the localized universal Hazewinkel
stage. The localized recurrence chart followed by this parameter map is proved to be the identity
on the entire finite parameter localization. Thus this module proves the retraction half of the
coordinate theorem. `DeningerHazewinkelLocalizedEquivalence` proves the opposite composite using
the universal Hankel minors and a Schur-complement recurrence; unlocalized saturation remains a
separate theorem.
-/

namespace RHTower
noncomputable section

abbrev DeningerHazewinkelStageLocalization (n : ℕ) :=
  Localization.Away
    (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
      (deningerHazewinkelLeadingDeterminant n))

def deningerHazewinkelParameterToStageLocalizationBase (n : ℕ) :
    DeningerHazewinkelParameterRing n →+*
      DeningerHazewinkelStageLocalization n :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) fun k =>
    algebraMap _ _
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelUniversalCoeff k.val))

theorem deningerHazewinkelParameterToStageLocalizationBase_coeff
    (n : ℕ) {s : ℕ} (hs : s < 2 * n) :
    deningerHazewinkelParameterToStageLocalizationBase n
      (deningerHazewinkelParameterCoeff n s) =
    algebraMap _ _
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelUniversalCoeff s)) := by
  by_cases hs0 : s = 0
  · subst s
    simp [deningerHazewinkelParameterCoeff,
      deningerHazewinkelUniversalCoeff]
  · rw [deningerHazewinkelParameterCoeff, dif_neg hs0, dif_pos hs]
    rw [deningerHazewinkelParameterToStageLocalizationBase,
      MvPolynomial.eval₂Hom_X']

theorem deningerHazewinkelParameterToStageLocalizationBase_leading (n : ℕ) :
    deningerHazewinkelParameterToStageLocalizationBase n
      (deningerHazewinkelParameterLeadingDeterminant n) =
    algebraMap _ _
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelLeadingDeterminant n)) := by
  change deningerHazewinkelParameterToStageLocalizationBase n
      (Matrix.det fun i j : Fin n =>
        deningerHazewinkelParameterCoeff n (i.val + j.val)) =
    algebraMap _ _
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (Matrix.det fun i j : Fin n =>
          deningerHazewinkelUniversalCoeff (i.val + j.val)))
  rw [(deningerHazewinkelParameterToStageLocalizationBase n).map_det]
  rw [(Ideal.Quotient.mk (deningerHazewinkelIdeal n)).map_det,
    (algebraMap (DeningerHazewinkelStageQuotient n)
      (DeningerHazewinkelStageLocalization n)).map_det]
  congr 1
  funext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  exact deningerHazewinkelParameterToStageLocalizationBase_coeff n (by omega)

def deningerHazewinkelParameterToStageLocalization (n : ℕ) :
    DeningerHazewinkelParameterLocalization n →+*
      DeningerHazewinkelStageLocalization n :=
  IsLocalization.Away.lift _
    (show IsUnit
        (deningerHazewinkelParameterToStageLocalizationBase n
          (deningerHazewinkelParameterLeadingDeterminant n)) by
      rw [deningerHazewinkelParameterToStageLocalizationBase_leading]
      exact IsLocalization.Away.algebraMap_isUnit _)

theorem deningerHazewinkelLocalizedStageToParameter_comp_parameterToStage
    (n : ℕ) (hn : 0 < n) :
    (deningerHazewinkelLocalizedStageToParameter n hn).comp
        (deningerHazewinkelParameterToStageLocalization n) =
      RingHom.id (DeningerHazewinkelParameterLocalization n) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (deningerHazewinkelParameterLeadingDeterminant n))
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [deningerHazewinkelParameterToStageLocalization,
      deningerHazewinkelParameterToStageLocalizationBase,
      deningerHazewinkelLocalizedStageToParameter,
      deningerHazewinkelStageLocalizationToParameter]
  · intro k
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [deningerHazewinkelParameterToStageLocalization,
      IsLocalization.Away.lift_eq]
    rw [deningerHazewinkelParameterToStageLocalizationBase,
      MvPolynomial.eval₂Hom_X']
    rw [deningerHazewinkelLocalizedStageToParameter,
      IsLocalization.Away.lift_eq]
    change deningerHazewinkelUniversalToLocalizedParameter n hn
        (deningerHazewinkelUniversalCoeff k.val) =
      algebraMap _ _ (MvPolynomial.X k)
    rw [deningerHazewinkelUniversalToLocalizedParameter_coeff]
    rw [deningerHazewinkelLocalizedSequence_of_lt n hn k.property.2]
    rw [deningerHazewinkelParameterCoeff_pos k.property.1 k.property.2]

end
end RHTower
