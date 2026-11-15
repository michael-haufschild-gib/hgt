import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Sets.Closeds
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Order.Atoms

/-!
# Recovering connected components from the clopen order

When the native connected-component quotient is discrete, each component is
clopen and is an atom of the Boolean algebra of clopens. Conversely, a nonempty
clopen atom equals the component of any of its points. This identifies the
native component space with the type of clopen atoms.

A clopen order isomorphism therefore induces a homeomorphism of component
spaces. If the order isomorphism is pullback under a continuous map, the inverse
homeomorphism is precisely the induced map on native components. Pullback of
the component containing an image point is exactly the component of that point.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.ClopenComponents
open TopologicalSpace Set
variable (X : Type*) [TopologicalSpace X] [DiscreteTopology (ConnectedComponents X)]

/-- A connected component as a bundled clopen, using discreteness of the component quotient. -/
def componentClopen (x : X) : Clopens X :=
  ⟨connectedComponent x, isClosed_connectedComponent,
    ConnectedComponents.discreteTopology_iff.mp inferInstance x⟩

theorem componentClopen_ne_bot (x : X) : componentClopen X x ≠ ⊥ := by
  intro he
  have hx : x ∈ componentClopen X x := mem_connectedComponent
  rw [he] at hx
  exact hx

omit [DiscreteTopology (ConnectedComponents X)] in
private theorem clopen_nonempty (U : Clopens X) (hU : U ≠ ⊥) : (U : Set X).Nonempty :=
  Set.nonempty_iff_ne_empty.mpr (fun h => hU (SetLike.coe_injective h))

/-- A connected component contains no proper nonempty clopen subset. -/
theorem componentClopen_isAtom (x : X) : IsAtom (componentClopen X x) := by
  apply isAtom_iff_le_of_ge.mpr
  refine ⟨componentClopen_ne_bot X x, ?_⟩
  intro U hU hle
  obtain ⟨y, hy⟩ := clopen_nonempty X U hU
  have hyx : y ∈ connectedComponent x := hle hy
  change connectedComponent x ⊆ (U : Set X)
  rw [connectedComponent_eq hyx]
  exact U.isClopen.connectedComponent_subset hy

/-- Every clopen atom is the component of each of its points. -/
theorem componentClopen_eq_of_isAtom (U : Clopens X) (hU : IsAtom U) (x : X) (hx : x ∈ U) :
    componentClopen X x = U :=
  (hU.le_iff_eq (componentClopen_ne_bot X x)).mp (U.isClopen.connectedComponent_subset hx)

/-- The clopen component represented by a native connected-component class. -/
def componentClopenOfClass : ConnectedComponents X → Clopens X :=
  Quotient.lift (componentClopen X) (fun _ _ h => SetLike.coe_injective h)

@[simp] theorem componentClopenOfClass_mk (x : X) :
    componentClopenOfClass X (ConnectedComponents.mk x) = componentClopen X x := rfl

theorem componentClopenOfClass_injective : Function.Injective (componentClopenOfClass X) := by
  intro a b h
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe b
  apply ConnectedComponents.coe_eq_coe.mpr
  exact congrArg (fun U : Clopens X => (U : Set X)) h

theorem componentClopenOfClass_isAtom (c : ConnectedComponents X) :
    IsAtom (componentClopenOfClass X c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  exact componentClopen_isAtom X x

/-- Native connected components are exactly the atoms of the clopen order. -/
def componentAtomEquiv : ConnectedComponents X ≃ {U : Clopens X // IsAtom U} :=
  Equiv.ofBijective
    (fun c => ⟨componentClopenOfClass X c, componentClopenOfClass_isAtom X c⟩)
    ⟨fun _ _ h => componentClopenOfClass_injective X (congrArg Subtype.val h), by
      rintro ⟨U, hU⟩
      obtain ⟨x, hx⟩ := clopen_nonempty X U hU.ne_bot
      exact ⟨ConnectedComponents.mk x, Subtype.ext (componentClopen_eq_of_isAtom X U hU x hx)⟩⟩

variable {X} {Y : Type*} [TopologicalSpace Y] [DiscreteTopology (ConnectedComponents Y)]

/-- Transport native components through an order isomorphism of clopen algebras. -/
def componentsEquivOfClopenOrderIso (e : Clopens X ≃o Clopens Y) :
    ConnectedComponents X ≃ ConnectedComponents Y :=
  (componentAtomEquiv X).trans
    ((e.toEquiv.subtypeEquiv (fun U => (e.isAtom_iff U).symm)).trans (componentAtomEquiv Y).symm)

theorem componentsEquivOfClopenOrderIso_clopen (e : Clopens X ≃o Clopens Y)
    (c : ConnectedComponents X) :
    componentClopenOfClass Y (componentsEquivOfClopenOrderIso e c) =
      e (componentClopenOfClass X c) :=
  congrArg Subtype.val ((componentAtomEquiv Y).apply_symm_apply
    ((e.toEquiv.subtypeEquiv (fun U => (e.isAtom_iff U).symm)) (componentAtomEquiv X c)))

/-- Clopen order transport is a homeomorphism of the discrete component spaces. -/
def componentsHomeomorphOfClopenOrderIso (e : Clopens X ≃o Clopens Y) :
    ConnectedComponents X ≃ₜ ConnectedComponents Y where
  __ := componentsEquivOfClopenOrderIso e
  continuous_toFun := continuous_of_discreteTopology
  continuous_invFun := continuous_of_discreteTopology

/-- For a pullback isomorphism, inverse component transport sends a point to its image class. -/
theorem componentsEquiv_symm_mk_of_pullback (e : Clopens X ≃o Clopens Y) (f : Y → X)
    (he : ∀ U : Clopens X, (e U : Set Y) = f ⁻¹' (U : Set X)) (y : Y) :
    (componentsEquivOfClopenOrderIso e).symm (ConnectedComponents.mk y) =
      ConnectedComponents.mk (f y) := by
  apply (componentsEquivOfClopenOrderIso e).injective
  rw [Equiv.apply_symm_apply]
  apply componentClopenOfClass_injective Y
  rw [componentsEquivOfClopenOrderIso_clopen, componentClopenOfClass_mk,
    componentClopenOfClass_mk]
  apply componentClopen_eq_of_isAtom Y (e (componentClopen X (f y)))
  · exact (e.isAtom_iff _).mpr (componentClopen_isAtom X (f y))
  · change y ∈ (e (componentClopen X (f y)) : Set Y)
    rw [he]
    exact mem_connectedComponent

/-- The inverse transported homeomorphism is the actual map induced on connected components. -/
theorem componentsHomeomorph_symm_eq_inducedMap (e : Clopens X ≃o Clopens Y) (f : Y → X)
    (hf : Continuous f) (he : ∀ U : Clopens X, (e U : Set Y) = f ⁻¹' (U : Set X)) :
    (componentsHomeomorphOfClopenOrderIso e).symm = hf.connectedComponentsMap := by
  funext c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
  exact componentsEquiv_symm_mk_of_pullback e f he y

/-- Pullback of the component containing an image point is precisely the original component. -/
theorem connectedComponent_preimage_eq (e : Clopens X ≃o Clopens Y) (f : Y → X)
    (he : ∀ U : Clopens X, (e U : Set Y) = f ⁻¹' (U : Set X)) (y : Y) :
    f ⁻¹' connectedComponent (f y) = connectedComponent y := by
  have hm : y ∈ e (componentClopen X (f y)) := by
    change y ∈ (e (componentClopen X (f y)) : Set Y)
    rw [he]
    exact mem_connectedComponent
  have hc := componentClopen_eq_of_isAtom Y (e (componentClopen X (f y)))
    ((e.isAtom_iff _).mpr (componentClopen_isAtom X (f y))) y hm
  have hs := congrArg (fun U : Clopens Y => (U : Set Y)) hc
  rw [he] at hs
  exact hs.symm

end GaloisForLFunctions.HTGeometry.ClopenComponents

#print axioms GaloisForLFunctions.HTGeometry.ClopenComponents.componentAtomEquiv
#print axioms GaloisForLFunctions.HTGeometry.ClopenComponents.componentsHomeomorphOfClopenOrderIso
#print axioms GaloisForLFunctions.HTGeometry.ClopenComponents.componentsHomeomorph_symm_eq_inducedMap
#print axioms GaloisForLFunctions.HTGeometry.ClopenComponents.connectedComponent_preimage_eq
