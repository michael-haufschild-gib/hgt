import GaloisForLFunctions.HTGeometry.AffineRelationObstructionPullback
import GaloisForLFunctions.HTGeometry.HermitianLocalExtensionAffineRelationEscape
import GaloisForLFunctions.HTGeometry.LocalExtensionSpectrumRealRelationEscape

/-!
# Families whose spectra escape every constant real relation

Nondegeneracy of a spectral map rules out combinations of the energies that are *constant* on a
parameter chart, not merely zero.  This file carries the escape property, the obstruction argument
and the local-extension witness across to that affine setting.

## Main results

* `SpectrumEscapesAffineRelations` — the affine escape property of a set of Hamiltonians, and
  `SpectrumEscapesAffineRelations.toRealRelations` recovering the homogeneous one.
* `not_affineRelation_on_open_of_spectrumEscapes` — **(L2') for a real-affine Hermitian family.**
* `hermitianLocalExtensionSlice_spectrumEscapesAffineRelations`,
  `not_affineRelation_on_open_of_localExtensionSlice` — the local-extension slice realizes it.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A set of matrices **escapes affine real relations** when for every nonzero balanced real
coefficient vector and every prescribed value some member has a simple real characteristic-root
packet on which every relabelling of the relation misses that value. -/
def SpectrumEscapesAffineRelations {I : Type*} [Fintype I] [DecidableEq I]
    (S : Set (Matrix I I ℂ)) : Prop :=
  ∀ (c : I → ℝ), ∑ i, c i = 0 → c ≠ 0 → ∀ target : ℝ,
    ∃ H ∈ S, ∃ E : I → ℝ,
      Function.Injective E ∧
      (∀ i, matrixCharpolyRelation (H, ((E i : ℝ) : ℂ)) = 0) ∧
      ∀ σ : Equiv.Perm I, ∑ i, c i * E (σ i) ≠ target

theorem SpectrumEscapesAffineRelations.mono {I : Type*} [Fintype I] [DecidableEq I]
    {S T : Set (Matrix I I ℂ)} (hS : SpectrumEscapesAffineRelations S) (hST : S ⊆ T) :
    SpectrumEscapesAffineRelations T := by
  intro c hbalanced hc target
  obtain ⟨H, hHS, E, hinj, hroot, hesc⟩ := hS c hbalanced hc target
  exact ⟨H, hST hHS, E, hinj, hroot, hesc⟩

/-- The homogeneous escape property is the value-zero case. -/
theorem SpectrumEscapesAffineRelations.toRealRelations {I : Type*} [Fintype I] [DecidableEq I]
    {S : Set (Matrix I I ℂ)} (hS : SpectrumEscapesAffineRelations S) :
    SpectrumEscapesRealRelations S := fun c hbalanced hc => hS c hbalanced hc 0

/-- **(L2') for a real-affine Hermitian family.**  No nonzero balanced real combination of the
energies can be constant throughout a nonempty open set of parameters. -/
theorem not_affineRelation_on_open_of_spectrumEscapes
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hS : SpectrumEscapesAffineRelations (Set.range (realAffineMatrix base generator)))
    {c : I → ℝ} (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0) (target : ℝ)
    {U : Set (Fin m → ℝ)} (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin m → ℝ) → I → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation (realAffineMatrix base generator q, ((spec q i : ℝ) : ℂ)) = 0)
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = target) : False := by
  obtain ⟨H, ⟨p₀, hp₀⟩, E, hEinj, hEroot, hEesc⟩ := hS c hbalanced hc target
  refine not_affineRelation_on_open_of_rootPacket_escape
    (realAffineMatrixPolynomial base generator) p₀ E hEinj ?_ hEesc hU hUne spec hinj ?_ hrel
  · intro i
    rw [eval_realAffineMatrixPolynomial, hp₀]
    exact hEroot i
  · intro q hq i
    rw [eval_realAffineMatrixPolynomial]
    exact hroot q hq i

/-- **The local-extension slice escapes every constant real relation.** -/
theorem hermitianLocalExtensionSlice_spectrumEscapesAffineRelations
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ) (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) (fun r => (shift₀ r : ℂ))))
    (hlift : (crossLayerLiftGraph (transitionSupportGraph transition) ρ).Preconnected) :
    SpectrumEscapesAffineRelations
      (Set.range (hermitianLocalExtensionSliceMatrix (α := α) (ρ := ρ) energy transition)) := by
  intro c hbalanced hc target
  obtain ⟨p, extendedEnergy, hinj, hroot, hesc⟩ :=
    exists_hermitianLocalExtension_realRootPacket_affineOrbit_ne_zero
      energy hmax shift₀ transition htransition hsimple hlift c hbalanced hc target
  refine ⟨hermitianLocalExtensionSliceMatrix energy transition
      (localExtensionSliceCoordinates p),
    ⟨localExtensionSliceCoordinates p, rfl⟩, extendedEnergy, hinj, ?_, hesc⟩
  intro i
  rw [hermitianLocalExtensionSliceMatrix, localExtensionSliceParameter_coordinates]
  exact hroot i

/-- The same escape property, in the canonical real-affine presentation of the slice. -/
theorem hermitianLocalExtensionSliceAffine_spectrumEscapesAffineRelations
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ) (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) (fun r => (shift₀ r : ℂ))))
    (hlift : (crossLayerLiftGraph (transitionSupportGraph transition) ρ).Preconnected) :
    SpectrumEscapesAffineRelations
      (Set.range (realAffineMatrix
        (hermitianLocalExtensionSliceBase (ρ := ρ) energy transition)
        (hermitianLocalExtensionSliceGenerator (ρ := ρ) energy transition))) := by
  have hslice :=
    hermitianLocalExtensionSlice_spectrumEscapesAffineRelations
      energy hmax shift₀ transition htransition hsimple hlift
  refine hslice.mono ?_
  rintro H ⟨p, rfl⟩
  exact ⟨p, (hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix energy transition p).symm⟩

/-- **(L2') on the local-extension slice.** -/
theorem not_affineRelation_on_open_of_localExtensionSlice
    {α ρ : Type*} [Fintype α] [Fintype ρ] [DecidableEq α] [DecidableEq ρ]
    [Nonempty α] [Nonempty ρ]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (shift₀ : ρ → ℝ)
    (transition : Matrix α α ℂ) (htransition : transition.IsHermitian)
    (hsimple :
      Function.Injective
        (layeredEnergy (fun a => (energy a : ℂ)) (fun r => (shift₀ r : ℂ))))
    (hlift : (crossLayerLiftGraph (transitionSupportGraph transition) ρ).Preconnected)
    {c : α × ρ → ℝ} (hbalanced : ∑ i, c i = 0) (hc : c ≠ 0) (target : ℝ)
    {U : Set (Fin (localExtensionSliceParameterCount ρ) → ℝ)}
    (hU : IsOpen U) (hUne : U.Nonempty)
    (spec : (Fin (localExtensionSliceParameterCount ρ) → ℝ) → α × ρ → ℝ)
    (hinj : ∀ q ∈ U, Function.Injective (spec q))
    (hroot : ∀ q ∈ U, ∀ i,
      matrixCharpolyRelation
        (hermitianLocalExtensionSliceMatrix energy transition q, ((spec q i : ℝ) : ℂ)) = 0)
    (hrel : ∀ q ∈ U, ∑ i, c i * spec q i = target) : False := by
  refine not_affineRelation_on_open_of_spectrumEscapes
    (hermitianLocalExtensionSliceBase (ρ := ρ) energy transition)
    (hermitianLocalExtensionSliceGenerator (ρ := ρ) energy transition)
    (hermitianLocalExtensionSliceAffine_spectrumEscapesAffineRelations
      energy hmax shift₀ transition htransition hsimple hlift)
    hbalanced hc target hU hUne spec hinj ?_ hrel
  intro q hq i
  rw [← hermitianLocalExtensionSliceMatrix_eq_realAffineMatrix]
  exact hroot q hq i

end

end GaloisForLFunctions.HTGeometry
