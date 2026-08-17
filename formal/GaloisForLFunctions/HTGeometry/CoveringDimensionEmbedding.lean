import GaloisForLFunctions.HTGeometry.CoveringDimensionShrinking

/-!
# Covering dimension transports along a compact embedding

A continuous injection of a compact space into a Hausdorff space is a homeomorphism onto its image,
so the covering dimension of the image bounds the covering dimension of the source.

This is the step the finite-phase law takes with the jet map: the phase carrier is compact and the
jet map is a continuous injection into `ℂ^N`, so any dimension bound for subsets of `ℂ^N` bounds the
dimension of the carrier.
-/

open Set

namespace GaloisForLFunctions

/-- **Covering dimension transports along a continuous injection of a compact space.** -/
theorem hasCoverDimLE_of_continuous_injective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {n : ℕ} {φ : X → Y}
    (hcont : Continuous φ) (hinj : Function.Injective φ)
    (h : HasCoverDimLE (Set.range φ) n) : HasCoverDimLE X n := by
  have hbij : Function.Bijective (fun x : X => (⟨φ x, ⟨x, rfl⟩⟩ : Set.range φ)) := by
    constructor
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
  have hcont' : Continuous (fun x : X => (⟨φ x, ⟨x, rfl⟩⟩ : Set.range φ)) :=
    hcont.subtype_mk _
  let e : X ≃ₜ Set.range φ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hbij) hcont'
  intro ι _ U hU hcov
  exact HasCoverDimLE.of_homeomorph (X := Set.range φ) (Y := X) e.symm h U hU hcov

end GaloisForLFunctions
