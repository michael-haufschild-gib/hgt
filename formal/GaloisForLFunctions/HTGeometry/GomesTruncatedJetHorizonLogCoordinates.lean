import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeHorizonSection
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeLogCoordinates

/-!
# Actual gauge restriction and extension in intrinsic logarithmic coordinates

Restriction drops higher positive resonant weights. The canonical group
section retains every existing logarithmic coefficient and sets every newly
available logarithmic coefficient to zero.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Every positive resonant weight remains positive and resonant at a larger horizon. -/
def gomesTruncatedJetPositiveIndexInclusion (n r : ℕ) (z : ℂ) :
    GomesTruncatedJetPositiveResonantIndex n z → GomesTruncatedJetPositiveResonantIndex (n + r) z :=
  fun k => ⟨gomesTruncatedJetResonantIndexInclusion n r z k.val, by
    intro h
    apply k.property
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun j : GomesTruncatedJetResonantIndex (n + r) z => j.val.val) h⟩

/-- Actual nilpotent horizon restriction drops precisely the higher positive resonant coordinates. -/
theorem gomesTruncatedJetNilpotentHorizon_coordinates (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace (n + r) z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    gomesTruncatedJetNilpotentLinearEquiv n z (gomesTruncatedJetNilpotentHorizon n r z E) k =
      gomesTruncatedJetNilpotentLinearEquiv (n + r) z E (gomesTruncatedJetPositiveIndexInclusion n r z k) :=
  gomesTruncatedJetHorizonRestriction_apply n r z E.val 0 k.val.val

/-- Actual unipotent group restriction is coordinate restriction in the complete logarithmic chart. -/
theorem gomesTruncatedJetUnipotentHorizon_coordinates (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup (n + r) z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z (gomesTruncatedJetUnipotentHorizon n r z u)) k =
      Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates (n + r) z u)
        (gomesTruncatedJetPositiveIndexInclusion n r z k) := by
  change (gomesTruncatedJetUnipotentLogarithm n z (gomesTruncatedJetUnipotentHorizon n r z u)).val.val 0 k.val.val =
    (gomesTruncatedJetUnipotentLogarithm (n + r) z u).val.val 0
      (gomesTruncatedJetPositiveIndexInclusion n r z k).val.val
  rw [← gomesTruncatedJetUnipotentHorizon_logarithm]
  exact gomesTruncatedJetHorizonRestriction_apply n r z
    (gomesTruncatedJetUnipotentLogarithm (n + r) z u).val 0 k.val.val

/-- Removing the scalar coordinate commutes with the actual geometric horizon restriction. -/
theorem gomesTruncatedJetGaugeHorizon_unipotentPart (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup (n + r) z) :
    gomesTruncatedJetUnipotentHorizon n r z (gomesTruncatedJetUnipotentPart (n + r) z u) =
      gomesTruncatedJetUnipotentPart n z (gomesTruncatedJetGaugeHorizon n r z u) := by
  apply Subtype.ext
  change gomesTruncatedJetGaugeHorizon n r z
    ((gomesTruncatedJetScalarSection (n + r) z (gomesTruncatedJetGaugeCharacter (n + r) z u))⁻¹ * u) =
      (gomesTruncatedJetScalarSection n z
        (gomesTruncatedJetGaugeCharacter n z (gomesTruncatedJetGaugeHorizon n r z u)))⁻¹ *
          gomesTruncatedJetGaugeHorizon n r z u
  rw [map_mul, map_inv, gomesTruncatedJetGaugeHorizon_scalarSection, gomesTruncatedJetGaugeHorizon_character]

/-- The complete actual gauge logarithmic chart commutes with dropping higher resonant weights. -/
theorem gomesTruncatedJetGaugeHorizon_logCoordinates (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetGaugeGroup (n + r) z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    Multiplicative.toAdd (gomesTruncatedJetGaugeLogCoordinates n z (gomesTruncatedJetGaugeHorizon n r z u)).2 k =
      Multiplicative.toAdd (gomesTruncatedJetGaugeLogCoordinates (n + r) z u).2
        (gomesTruncatedJetPositiveIndexInclusion n r z k) := by
  change Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z
    (gomesTruncatedJetUnipotentPart n z (gomesTruncatedJetGaugeHorizon n r z u))) k = _
  rw [← gomesTruncatedJetGaugeHorizon_unipotentPart]
  exact gomesTruncatedJetUnipotentHorizon_coordinates n r z (gomesTruncatedJetUnipotentPart (n + r) z u) k

/-- The nilpotent section retains every old positive resonant coordinate. -/
theorem gomesTruncatedJetNilpotentHorizonSection_coordinates (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    gomesTruncatedJetNilpotentLinearEquiv (n + r) z (gomesTruncatedJetNilpotentHorizonSection n r z E)
        (gomesTruncatedJetPositiveIndexInclusion n r z k) = gomesTruncatedJetNilpotentLinearEquiv n z E k := by
  have h := gomesTruncatedJetNilpotentHorizon_coordinates n r z (gomesTruncatedJetNilpotentHorizonSection n r z E) k
  rw [gomesTruncatedJetNilpotentHorizon_section] at h
  exact h.symm

/-- The actual unipotent group section retains every old logarithmic coordinate. -/
theorem gomesTruncatedJetUnipotentHorizonSection_coordinates (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) (k : GomesTruncatedJetPositiveResonantIndex n z) :
    Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates (n + r) z
      (gomesTruncatedJetUnipotentHorizonSection n r z u)) (gomesTruncatedJetPositiveIndexInclusion n r z k) =
        Multiplicative.toAdd (gomesTruncatedJetUnipotentCoordinates n z u) k := by
  change gomesTruncatedJetNilpotentLinearEquiv (n + r) z
    (gomesTruncatedJetUnipotentLogarithm (n + r) z (gomesTruncatedJetUnipotentHorizonSection n r z u))
    (gomesTruncatedJetPositiveIndexInclusion n r z k) = _
  rw [gomesTruncatedJetUnipotentHorizonSection_logarithm]
  exact gomesTruncatedJetNilpotentHorizonSection_coordinates n r z (gomesTruncatedJetUnipotentLogarithm n z u) k

/-- Actual resonant weights which become available only at the higher horizon. -/
abbrev GomesTruncatedJetAddedResonantIndex (n r : ℕ) (z : ℂ) :=
  {k : GomesTruncatedJetResonantIndex (n + r) z // n + 1 ≤ k.val.val}

/-- The intrinsic linear section sets every newly available resonant coefficient to zero. -/
theorem gomesTruncatedJetHorizonLinearSection_added (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) (k : GomesTruncatedJetAddedResonantIndex n r z) :
    (gomesTruncatedJetHorizonLinearSection n r z E).val 0 k.val.val = 0 := by
  change gomesTruncatedJetResonantLinearEquiv (n + r) z
    ((gomesTruncatedJetResonantLinearEquiv (n + r) z).symm
      (gomesTruncatedJetResonantZeroExtend n r z (gomesTruncatedJetResonantLinearEquiv n z E))) k.val = 0
  rw [LinearEquiv.apply_symm_apply]
  change (if h : k.val.val.val < n + 1 then
    gomesTruncatedJetResonantLinearEquiv n z E ⟨⟨k.val.val.val, h⟩, k.val.property⟩ else 0) = 0
  rw [dif_neg (Nat.not_lt.mpr k.property)]

/-- Every newly available logarithmic coordinate of the canonical unipotent group lift is zero. -/
theorem gomesTruncatedJetUnipotentHorizonSection_added_logarithm (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup n z) (k : GomesTruncatedJetAddedResonantIndex n r z) :
    (gomesTruncatedJetUnipotentLogarithm (n + r) z
      (gomesTruncatedJetUnipotentHorizonSection n r z u)).val.val 0 k.val.val = 0 := by
  rw [gomesTruncatedJetUnipotentHorizonSection_logarithm]
  exact gomesTruncatedJetHorizonLinearSection_added n r z (gomesTruncatedJetUnipotentLogarithm n z u).val k

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
