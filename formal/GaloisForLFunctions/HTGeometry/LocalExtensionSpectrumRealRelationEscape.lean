import GaloisForLFunctions.HTGeometry.SpectrumRealRelationEscape
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionRealRelationEscape
import GaloisForLFunctions.HTGeometry.LocalExtensionSliceProjectiveGenericity

/-!
# The local-extension slice escapes every real relation

One local extension of a maximally projective base spectrum, with a connected interaction lift,
erases any prescribed nonzero balanced real relation among the extended energies.  Packaging the
onsite shifts and the real edge matrix in one finite coordinate vector turns that into the escape
property of the finite real-affine slice, which is the hypothesis `(L2)` consumes.

## Main results

* `hermitianLocalExtensionSlice_spectrumEscapesRealRelations` — the slice escapes real relations.
* `not_relation_on_open_of_localExtensionSlice` — **(L2) on the local-extension slice.**
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The local-extension slice escapes every real relation.**  For each nonzero balanced real
coefficient vector one point of the slice carries a simple real root packet on which every
relabelling of the relation is nonzero. -/
theorem hermitianLocalExtensionSlice_spectrumEscapesRealRelations
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ) (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) (fun r => (shift₀ r : ℂ))))
    (hlift : (crossLayerLiftGraph (transitionSupportGraph transition) ρ).Preconnected) :
    SpectrumEscapesRealRelations
      (Set.range (hermitianLocalExtensionSliceMatrix (α := α) (ρ := ρ) energy transition)) := by
  intro c hbalanced hc
  obtain ⟨p, extendedEnergy, hinj, hroot, horbit⟩ :=
    exists_hermitianLocalExtension_realRootPacket_orbit_ne_zero
      energy hmax shift₀ transition htransition hsimple hlift c hbalanced hc
  refine ⟨hermitianLocalExtensionSliceMatrix energy transition
      (localExtensionSliceCoordinates p),
    ⟨localExtensionSliceCoordinates p, rfl⟩, extendedEnergy, hinj, ?_,
    (linearRelationOrbitValue_ne_zero_iff c extendedEnergy).mp horbit⟩
  intro i
  rw [hermitianLocalExtensionSliceMatrix, localExtensionSliceParameter_coordinates]
  exact hroot i

/-- The same escape property, stated for the canonical real-affine presentation of the slice. -/
theorem hermitianLocalExtensionSliceAffine_spectrumEscapesRealRelations
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ) (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) (fun r => (shift₀ r : ℂ))))
    (hlift : (crossLayerLiftGraph (transitionSupportGraph transition) ρ).Preconnected) :
    SpectrumEscapesRealRelations
      (Set.range (realAffineMatrix
        (hermitianLocalExtensionSliceBase (ρ := ρ) energy transition)
        (hermitianLocalExtensionSliceGenerator (ρ := ρ) energy transition))) := by
  have hslice :=
    hermitianLocalExtensionSlice_spectrumEscapesRealRelations
      energy hmax shift₀ transition htransition hsimple hlift
  refine hslice.mono ?_
  rintro H ⟨p, rfl⟩
  exact ⟨p, (hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix energy transition p).symm⟩

/-- **(L2) on the local-extension slice.**  No nonzero balanced real relation among the energies of
the extended system holds throughout a nonempty open set of slice parameters. -/
theorem not_relation_on_open_of_localExtensionSlice
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ) (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) (fun r => (shift₀ r : ℂ))))
    (hlift : (crossLayerLiftGraph (transitionSupportGraph transition) ρ).Preconnected)
    {c : α × ρ → ℝ} (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0)
    {U : Set (Fin (localExtensionSliceParameterCount ρ) → ℝ)}
    (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin (localExtensionSliceParameterCount ρ) → ℝ) → α × ρ → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation
        (hermitianLocalExtensionSliceMatrix energy transition q, ((spec q i : ℝ) : ℂ)) = 0)
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = 0) : False := by
  refine not_relation_on_open_of_spectrumEscapes
    (hermitianLocalExtensionSliceBase (ρ := ρ) energy transition)
    (hermitianLocalExtensionSliceGenerator (ρ := ρ) energy transition)
    (hermitianLocalExtensionSliceAffine_spectrumEscapesRealRelations
      energy hmax shift₀ transition htransition hsimple hlift)
    hbalanced hc hU hUne spec hinj ?_ hrel
  intro q hq i
  rw [← hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix]
  exact hroot q hq i

end

end GaloisForLFunctions.HTGeometry
