import GaloisForLFunctions.HTGeometry.LocalSpectralExtensionRelationRigidity

/-!
# Componentwise Hasse reconstruction for cross-layer spectral relations

Connected components of the interaction-lift graph are treated as local places.  A compatible
global relation packet is completely determined by one scalar at every component, every component
packet has one unique global relation, and global inequality has a concrete component witness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Two global cross-layer relations agree exactly when every connected-component coordinate
agrees. -/
theorem crossLayerRelation_congr_hasse_iff
    {α ρ : Type*} (G : SimpleGraph α)
    (x y : crossLayerRelationSpace G ρ) :
    x = y ↔ ∀ c : (crossLayerLiftGraph G ρ).ConnectedComponent,
      crossLayerRelationComponentEquiv G ρ x c =
        crossLayerRelationComponentEquiv G ρ y c := by
  constructor
  · rintro rfl c
    rfl
  · intro hlocal
    apply (crossLayerRelationComponentEquiv G ρ).injective
    funext c
    exact hlocal c

/-- A global cross-layer relation is zero exactly when every component-local scalar is zero. -/
theorem crossLayerRelation_eq_zero_hasse_iff
    {α ρ : Type*} (G : SimpleGraph α)
    (x : crossLayerRelationSpace G ρ) :
    x = 0 ↔ ∀ c : (crossLayerLiftGraph G ρ).ConnectedComponent,
      crossLayerRelationComponentEquiv G ρ x c = 0 := by
  rw [crossLayerRelation_congr_hasse_iff G x 0]
  simp

/-- Distinct global relations differ on one connected component of the interaction lift. -/
theorem crossLayerRelation_ne_iff_exists_componentWitness
    {α ρ : Type*} (G : SimpleGraph α)
    (x y : crossLayerRelationSpace G ρ) :
    x ≠ y ↔ ∃ c : (crossLayerLiftGraph G ρ).ConnectedComponent,
      crossLayerRelationComponentEquiv G ρ x c ≠
        crossLayerRelationComponentEquiv G ρ y c := by
  classical
  constructor
  · intro hxy
    by_contra hno
    apply hxy
    apply (crossLayerRelation_congr_hasse_iff G x y).mpr
    intro c
    by_contra hc
    exact hno ⟨c, hc⟩
  · rintro ⟨c, hc⟩ hxy
    exact hc (by rw [hxy])

/-- **Component Hasse gluing.** Every scalar packet on interaction-lift components has one unique
global cross-layer relation. -/
theorem crossLayerRelation_existsUnique_global
    {α ρ : Type*} (G : SimpleGraph α)
    (packet : (crossLayerLiftGraph G ρ).ConnectedComponent → ℂ) :
    ∃! x : crossLayerRelationSpace G ρ,
      crossLayerRelationComponentEquiv G ρ x = packet := by
  refine ⟨(crossLayerRelationComponentEquiv G ρ).symm packet, ?_, ?_⟩
  · exact (crossLayerRelationComponentEquiv G ρ).apply_symm_apply packet
  · intro x hx
    apply (crossLayerRelationComponentEquiv G ρ).injective
    rw [hx]
    exact ((crossLayerRelationComponentEquiv G ρ).apply_symm_apply packet).symm

end


end GaloisForLFunctions.HTGeometry
