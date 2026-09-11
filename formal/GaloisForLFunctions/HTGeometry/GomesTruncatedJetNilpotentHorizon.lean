import GaloisForLFunctions.HTGeometry.GomesTruncatedJetHorizonCoordinates
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetNilpotentSpace

/-!
# Exact restriction and extension of actual nilpotent symmetry coordinates

Augmentation preservation makes the actual horizon maps restrict to the full
nilpotent spaces. The intrinsic zero extension gives a linear right inverse.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Restrict any actual nilpotent joint symmetry to a lower horizon. -/
def gomesTruncatedJetNilpotentHorizon (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetNilpotentSpace (n + r) z →ₗ[ℂ] gomesTruncatedJetNilpotentSpace n z where
  toFun E := ⟨gomesTruncatedJetHorizonRestriction n r z E.val, by
    apply (gomesTruncatedJetNilpotentSpace_mem_iff n z _).mpr
    rw [gomesTruncatedJetHorizonRestriction_augmentation]
    exact gomesTruncatedJetNilpotentSpace_augmentation (n + r) z E⟩
  map_add' E F := by
    apply Subtype.ext
    exact map_add (gomesTruncatedJetHorizonRestriction n r z) E.val F.val
  map_smul' a E := by
    apply Subtype.ext
    exact map_smul (gomesTruncatedJetHorizonRestriction n r z).toLinearMap a E.val

/-- Lift every nilpotent joint symmetry by zero extension of its resonant coordinates. -/
def gomesTruncatedJetNilpotentHorizonSection (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetNilpotentSpace n z →ₗ[ℂ] gomesTruncatedJetNilpotentSpace (n + r) z where
  toFun E := ⟨gomesTruncatedJetHorizonLinearSection n r z E.val, by
    apply (gomesTruncatedJetNilpotentSpace_mem_iff (n + r) z _).mpr
    rw [gomesTruncatedJetHorizonLinearSection_augmentation]
    exact gomesTruncatedJetNilpotentSpace_augmentation n z E⟩
  map_add' E F := by
    apply Subtype.ext
    exact map_add (gomesTruncatedJetHorizonLinearSection n r z) E.val F.val
  map_smul' a E := by
    apply Subtype.ext
    exact map_smul (gomesTruncatedJetHorizonLinearSection n r z) a E.val

/-- Restriction recovers every nilpotent symmetry lifted by its intrinsic coefficient section. -/
theorem gomesTruncatedJetNilpotentHorizon_section (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace n z) :
    gomesTruncatedJetNilpotentHorizon n r z (gomesTruncatedJetNilpotentHorizonSection n r z E) = E := by
  apply Subtype.ext
  exact gomesTruncatedJetHorizonRestriction_section n r z E.val

/-- Actual nilpotent symmetry restriction is surjective at every pair of finite horizons. -/
theorem gomesTruncatedJetNilpotentHorizon_surjective (n r : ℕ) (z : ℂ) :
    Function.Surjective (gomesTruncatedJetNilpotentHorizon n r z) := by
  intro E
  exact ⟨gomesTruncatedJetNilpotentHorizonSection n r z E, gomesTruncatedJetNilpotentHorizon_section n r z E⟩

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
