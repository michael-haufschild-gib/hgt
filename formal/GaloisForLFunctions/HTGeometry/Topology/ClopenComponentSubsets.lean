import GaloisForLFunctions.HTGeometry.Topology.ClopenComponents
import Mathlib.Data.Fintype.Powerset

/-!
# Clopens as subsets of the connected-component space

When the connected-component quotient is discrete, every subset of it pulls
back to a clopen subset. Conversely, every clopen is saturated by connected
components. Image and preimage under the quotient map therefore give inverse
bijections between clopens and subsets of the component space.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.ClopenComponents
open TopologicalSpace Set Classical
variable (X : Type*) [TopologicalSpace X] [DiscreteTopology (ConnectedComponents X)]

/-- A subset of the discrete component space pulls back to a clopen subset. -/
def componentSubsetClopen (S : Set (ConnectedComponents X)) : Clopens X :=
  ⟨ConnectedComponents.mk ⁻¹' S,
    (isClosed_discrete S).preimage ConnectedComponents.continuous_coe,
    (isOpen_discrete S).preimage ConnectedComponents.continuous_coe⟩

/-- Clopen subsets are exactly arbitrary unions of connected components whenever
the component quotient is discrete. -/
def clopenComponentSubsetEquiv : Clopens X ≃ Set (ConnectedComponents X) where
  toFun U := ConnectedComponents.mk '' (U : Set X)
  invFun := componentSubsetClopen X
  left_inv U := by
    ext x
    change ConnectedComponents.mk x ∈ ConnectedComponents.mk '' (U : Set X) ↔ x ∈ U
    constructor
    · rintro ⟨y, hy, he⟩
      exact U.isClopen.connectedComponent_subset hy
        (ConnectedComponents.coe_eq_coe'.mp he.symm)
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv S := by
    ext c
    change c ∈ ConnectedComponents.mk '' (ConnectedComponents.mk ⁻¹' S : Set X) ↔ c ∈ S
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hc
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
      exact ⟨x, hc, rfl⟩

#print axioms clopenComponentSubsetEquiv
end GaloisForLFunctions.HTGeometry.ClopenComponents
