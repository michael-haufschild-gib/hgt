import GaloisForLFunctions.HTGeometry.GomesTruncatedJetHorizonRestriction
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetResonantCoordinates

/-!
# Concrete coefficient restriction and extension across finite horizons

The actual algebra restriction drops higher resonant coefficients. Extending
by zero yields a linear section on the entire joint symmetry algebra, and
therefore proves that every actual lower-horizon symmetry lifts.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- A lower resonant weight is the same resonant weight at any larger horizon. -/
def gomesTruncatedJetResonantIndexInclusion (n r : ℕ) (z : ℂ) :
    GomesTruncatedJetResonantIndex n z → GomesTruncatedJetResonantIndex (n + r) z :=
  fun k => ⟨Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) k.val, k.property⟩

/-- Restriction of actual joint symmetries is restriction of the intrinsic resonant coefficients. -/
theorem gomesTruncatedJetHorizonRestriction_resonant (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra (n + r) z) (k : GomesTruncatedJetResonantIndex n z) :
    gomesTruncatedJetResonantObservation n z (gomesTruncatedJetHorizonRestriction n r z E) k =
      gomesTruncatedJetResonantObservation (n + r) z E (gomesTruncatedJetResonantIndexInclusion n r z k) :=
  gomesTruncatedJetHorizonRestriction_apply n r z E 0 k.val

/-- Extend actual resonant coefficient data by zero at all newly available weights. -/
def gomesTruncatedJetResonantZeroExtend (n r : ℕ) (z : ℂ) :
    (GomesTruncatedJetResonantIndex n z → ℂ) →ₗ[ℂ]
      (GomesTruncatedJetResonantIndex (n + r) z → ℂ) where
  toFun c k := if h : k.val.val < n + 1 then c ⟨⟨k.val.val, h⟩, k.property⟩ else 0
  map_add' c d := by
    funext k
    by_cases h : k.val.val < n + 1
    · simp only [Pi.add_apply, dif_pos h]
    · simp only [Pi.add_apply, dif_neg h, add_zero]
  map_smul' a c := by
    funext k
    by_cases h : k.val.val < n + 1
    · simp only [Pi.smul_apply, dif_pos h]
      rfl
    · simp only [Pi.smul_apply, dif_neg h, smul_zero]

/-- Restriction recovers every coefficient extended by zero. -/
theorem gomesTruncatedJetResonantZeroExtend_inclusion (n r : ℕ) (z : ℂ)
    (c : GomesTruncatedJetResonantIndex n z → ℂ) (k : GomesTruncatedJetResonantIndex n z) :
    gomesTruncatedJetResonantZeroExtend n r z c (gomesTruncatedJetResonantIndexInclusion n r z k) = c k := by
  change (if h : k.val.val < n + 1 then c ⟨⟨k.val.val, h⟩, k.property⟩ else 0) = c k
  rw [dif_pos k.val.isLt]

/-- The actual joint symmetry algebra has a linear horizon section obtained from intrinsic zero extension. -/
def gomesTruncatedJetHorizonLinearSection (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra n z →ₗ[ℂ] gomesTruncatedJetJointAlgebra (n + r) z :=
  (gomesTruncatedJetResonantLinearEquiv (n + r) z).symm.toLinearMap.comp
    ((gomesTruncatedJetResonantZeroExtend n r z).comp
      (gomesTruncatedJetResonantLinearEquiv n z).toLinearMap)

/-- The concrete coefficient extension is a right inverse to the actual algebra restriction. -/
theorem gomesTruncatedJetHorizonRestriction_section (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    gomesTruncatedJetHorizonRestriction n r z (gomesTruncatedJetHorizonLinearSection n r z E) = E := by
  apply gomesTruncatedJetResonantObservation_injective n z
  funext k
  rw [gomesTruncatedJetHorizonRestriction_resonant]
  change gomesTruncatedJetResonantLinearEquiv (n + r) z
    ((gomesTruncatedJetResonantLinearEquiv (n + r) z).symm
      (gomesTruncatedJetResonantZeroExtend n r z (gomesTruncatedJetResonantLinearEquiv n z E)))
    (gomesTruncatedJetResonantIndexInclusion n r z k) = _
  rw [LinearEquiv.apply_symm_apply, gomesTruncatedJetResonantZeroExtend_inclusion]
  rfl

/-- Every lower-horizon joint geometric symmetry is the restriction of an actual higher-horizon joint symmetry. -/
theorem gomesTruncatedJetHorizonRestriction_surjective (n r : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetHorizonRestriction n r z) := by
  intro E
  exact ⟨gomesTruncatedJetHorizonLinearSection n r z E, gomesTruncatedJetHorizonRestriction_section n r z E⟩

/-- Zero extension preserves the actual scalar coordinate. -/
theorem gomesTruncatedJetHorizonLinearSection_augmentation (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra n z) :
    gomesTruncatedJetAugmentation (n + r) z (gomesTruncatedJetHorizonLinearSection n r z E) =
      gomesTruncatedJetAugmentation n z E := by
  rw [← gomesTruncatedJetHorizonRestriction_augmentation n r z,
    gomesTruncatedJetHorizonRestriction_section]

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
