import GaloisForLFunctions.HTGeometry.DisjointPointCaps
import GaloisForLFunctions.HTGeometry.OpenCapFamily

/-!
# Fundamental group of the constructed cap completion

The body/cap intersection is exactly the original punctured region. If the cap
model is simply connected and its punctured part is path connected, the old
body maps onto the fundamental group of the completion. The completion is
also path connected when the old body is path connected.
-/

open Topology Set Function
open DifferentialGeometry.Topology.VanKampen

namespace GaloisForLFunctions.HTGeometry.PointCapData

variable {Y D I : Type*} [TopologicalSpace Y] [TopologicalSpace D]
    (c : PointCapData Y D I)

/-- The old body intersects a cap in precisely its original punctured region. -/
theorem old_image_region (i : I) :
    c.old '' c.region i = range c.old ∩ range (c.cap i) := by
  have hi : c.old ⁻¹' range (c.cap i) = c.region i := by
    simpa using c.old_preimage_cap_image i univ
  rw [← hi, image_preimage_eq_inter_range, inter_comm]

theorem isPathConnected_body_cap [PathConnectedSpace {z : D // z ≠ c.center}] (i : I) :
    IsPathConnected (range c.old ∩ range (c.cap i)) := by
  letI : PathConnectedSpace (c.region i) :=
    (c.chart i).surjective.pathConnectedSpace (c.chart i).continuous
  rw [← c.old_image_region]
  exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance).image c.continuous_old

theorem isSimplyConnected_cap [SimplyConnectedSpace D] (i : I) :
    IsSimplyConnected (range (c.cap i)) :=
  (c.isOpenEmbedding_cap i).isEmbedding.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace_iff.mpr
    inferInstance

/-- The constructed completion introduces no new fundamental-group classes. -/
theorem fundamentalGroup_body_surjective [T1Space D] [PathConnectedSpace Y]
    [SimplyConnectedSpace D] [PathConnectedSpace {z : D // z ≠ c.center}]
    (a : range c.old) :
    Surjective (FundamentalGroup.map (subsetToAmbient (range c.old)) a) := by
  apply fundamentalGroup_inclusion_open_caps_surjective
    (range c.old) (fun i => range (c.cap i))
    c.isOpenEmbedding_old.isOpen_range (isPathConnected_range c.continuous_old)
    (fun i => (c.isOpenEmbedding_cap i).isOpen_range) c.isSimplyConnected_cap
    c.isPathConnected_body_cap
  · intro i j hij
    rw [(c.disjoint_cap_ranges hij).inter_eq]
    exact empty_subset _
  · exact c.pieces_cover

/-- Every point of the completion can be joined to an old basepoint. -/
theorem joined_old [PathConnectedSpace Y] [PathConnectedSpace D]
    [PathConnectedSpace {z : D // z ≠ c.center}] (y₀ : Y) (x : c.Space) :
    Joined (c.old y₀) x := by
  cases x with
  | inl y => exact ⟨(PathConnectedSpace.somePath y₀ y).map c.continuous_old⟩
  | inr i =>
    let z : {z : D // z ≠ c.center} := Classical.choice inferInstance
    let y : Y := c.chart i z
    have h₁ : Joined (c.old y₀) (c.old y) :=
      ⟨(PathConnectedSpace.somePath y₀ y).map c.continuous_old⟩
    have h₂ : Joined (c.cap i z) (c.cap i c.center) :=
      ⟨(PathConnectedSpace.somePath (z : D) c.center).map (c.continuous_cap i)⟩
    rw [c.cap_center, c.cap_ne_center i z.property] at h₂
    exact h₁.trans h₂

theorem pathConnectedSpace [PathConnectedSpace Y] [PathConnectedSpace D]
    [PathConnectedSpace {z : D // z ≠ c.center}] : PathConnectedSpace c.Space := by
  let y₀ : Y := Classical.choice inferInstance
  exact ⟨⟨c.old y₀⟩, fun x y => (c.joined_old y₀ x).symm.trans (c.joined_old y₀ y)⟩

end GaloisForLFunctions.HTGeometry.PointCapData
