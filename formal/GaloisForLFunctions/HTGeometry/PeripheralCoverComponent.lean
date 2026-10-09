import GaloisForLFunctions.HTGeometry.CoveringComponentRestriction
import GaloisForLFunctions.HTGeometry.AnalyticZeroCoverCap

/-!
# Peripheral component models and analytic source caps

A component above an open punctured-disk chart inherits the covering property.
Classify that component by the checked power/exponential dichotomy. An analytic
zero with a continuous punctured lift forces the power alternative and extends
in its chart with exact multiplicity.
-/

open Topology Set Function Filter

namespace GaloisForLFunctions.HTGeometry

/-- A component above an open punctured-disk chart is itself a power or
exponential covering in that chart. -/
theorem open_cover_component_classification
    [TopologicalSpace E] [TopologicalSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) {U : Set B} (hU : IsOpen U)
    (d : U ≃ₜ PuncturedUnitDisk) (e : p ⁻¹' U) :
    (∃ D : connectedComponent e ≃ₜ LogHalfPlane,
      ∀ y : connectedComponent e, d (U.restrictPreimage p y) = puncturedDiskExp (D y)) ∨
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ D : connectedComponent e ≃ₜ PuncturedUnitDisk,
      ∀ y : connectedComponent e, d (U.restrictPreimage p y) = puncturedDiskPower n hn (D y) := by
  letI : LocallyPathConnectedSpace (p ⁻¹' U) :=
    (hU.preimage hp.continuous).locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace (connectedComponent e) :=
    isOpen_connectedComponent.locallyPathConnectedSpace
  letI : ConnectedSpace (connectedComponent e) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : PathConnectedSpace (connectedComponent e) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact puncturedDisk_cover_classification
    ((isCoveringMap_open_preimage_component hp hU e).homeomorph_comp d)

/-- A continuous map from a connected source into a covering preimage stays
in the component of any chosen source point. -/
def continuousMapToComponent [TopologicalSpace X] [TopologicalSpace E]
    [PreconnectedSpace X] (g : C(X, E)) (x₀ : X) : C(X, connectedComponent (g x₀)) :=
  ⟨fun x => ⟨g x,
    (isPreconnected_range g.continuous).subset_connectedComponent (mem_range_self x₀)
      (mem_range_self x)⟩, g.continuous.subtype_mk _⟩

@[simp] theorem continuousMapToComponent_val [TopologicalSpace X] [TopologicalSpace E]
    [PreconnectedSpace X] (g : C(X, E)) (x₀ x : X) :
    (continuousMapToComponent g x₀ x : E) = g x := rfl

/-- A local analytic zero lifted into a peripheral component forces that whole
component to be finite-sheeted and supplies its analytic cap coordinate. -/
theorem analytic_zero_lift_in_open_cover_component
    [TopologicalSpace E] [TopologicalSpace B]
    [LocallyPathConnectedSpace E] [LocallyPathConnectedSpace B]
    {p : E → B} (hp : IsCoveringMap p) {U : Set B} (hU : IsOpen U)
    (d : U ≃ₜ PuncturedUnitDisk) (e : p ⁻¹' U)
    {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a) (hfa : f a = 0)
    (g : ℂ → connectedComponent e)
    (hgc : ∀ᶠ z in 𝓝[≠] a, ContinuousAt g z)
    (hfg : ∀ᶠ z in 𝓝[≠] a, (d (U.restrictPreimage p (g z)) : ℂ) = f z) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ D : connectedComponent e ≃ₜ PuncturedUnitDisk,
      (∀ y : connectedComponent e, d (U.restrictPreimage p y) = puncturedDiskPower n hn (D y)) ∧
      AnalyticAt ℂ (update (fun z => (D (g z) : ℂ)) a 0) a ∧
      analyticOrderAt f a = n • analyticOrderAt (update (fun z => (D (g z) : ℂ)) a 0) a := by
  letI : LocallyPathConnectedSpace (p ⁻¹' U) :=
    (hU.preimage hp.continuous).locallyPathConnectedSpace
  letI : LocallyPathConnectedSpace (connectedComponent e) :=
    isOpen_connectedComponent.locallyPathConnectedSpace
  letI : ConnectedSpace (connectedComponent e) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : PathConnectedSpace (connectedComponent e) :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact analytic_zero_lift_has_power_chart
    ((isCoveringMap_open_preimage_component hp hU e).homeomorph_comp d) hf hfa g hgc hfg

end GaloisForLFunctions.HTGeometry
