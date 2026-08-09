import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Crossed modules and their homotopy kernel

A crossed module consists of a group homomorphism together with a compatible action satisfying
the two Peiffer identities.  Its kernel is central, its boundary image is normal, and the ambient
action on the kernel factors through the quotient by the boundary image.  The same algebra shows
that a two-morphism from the identity arrow to itself has an abelian kernel-valued label.
-/

namespace HTGeometry.NomologicalHomotopyGeometry

/-- A crossed module of groups, with the action written as a homomorphism to multiplicative
automorphisms. -/
structure CrossedModule (H G : Type*) [Group H] [Group G] where
  boundary : H →* G
  action : G →* MulAut H
  boundary_action : ∀ g h, boundary (action g h) = g * boundary h * g⁻¹
  peiffer : ∀ h h', action (boundary h) h' = h * h' * h⁻¹

namespace CrossedModule

variable {H G : Type*} [Group H] [Group G] (C : CrossedModule H G)

/-- The second homotopy group of a crossed module, realized as the boundary kernel. -/
abbrev piTwo : Subgroup H := C.boundary.ker

/-- The boundary image is normal by equivariance of the boundary. -/
instance boundaryRangeNormal : C.boundary.range.Normal where
  conj_mem h hh g := by
    rcases hh with ⟨k, rfl⟩
    exact ⟨C.action g k, C.boundary_action g k⟩

/-- The homotopy kernel of a crossed module is central. -/
theorem piTwo_le_center : C.piTwo ≤ Subgroup.center H := by
  intro k hk
  rw [Subgroup.mem_center_iff]
  intro h
  have hconj : h = k * h * k⁻¹ := by
    simpa [hk] using C.peiffer k h
  calc
    h * k = (k * h * k⁻¹) * k := congrArg (· * k) hconj
    _ = k * h := by simp [mul_assoc]

/-- In particular, two elements of the homotopy kernel commute. -/
theorem piTwo_commute (k l : C.piTwo) : (k : H) * l = l * k :=
  (Subgroup.mem_center_iff.mp (C.piTwo_le_center k.property) l).symm

/-- The ambient action preserves the homotopy kernel. -/
private theorem action_mem_piTwo (g : G) (k : C.piTwo) : C.action g k ∈ C.piTwo := by
  change C.boundary (C.action g k) = 1
  rw [C.boundary_action, k.property]
  simp

/-- Restriction of one ambient action automorphism to the homotopy kernel. -/
def kernelActionAut (g : G) : MulAut C.piTwo where
  toFun k := ⟨C.action g k, C.action_mem_piTwo g k⟩
  invFun k := ⟨C.action g⁻¹ k, C.action_mem_piTwo g⁻¹ k⟩
  left_inv k := by
    ext
    simpa using congrArg (fun e : MulAut H => e k) (C.action.map_inv g)
  right_inv k := by
    ext
    simpa using congrArg (fun e : MulAut H => e k) (C.action.map_inv g⁻¹)
  map_mul' k l := by
    ext
    exact (C.action g).map_mul k l

/-- The ambient group acts on the homotopy kernel. -/
def kernelAction : G →* MulAut C.piTwo where
  toFun := C.kernelActionAut
  map_one' := by
    ext k
    change C.action 1 (k : H) = k
    simp
  map_mul' g h := by
    ext k
    change C.action (g * h) (k : H) = C.action g (C.action h k)
    rw [C.action.map_mul]
    rfl

/-- Boundary elements act trivially on the homotopy kernel. -/
theorem boundaryRange_le_kernelAction : C.boundary.range ≤ C.kernelAction.ker := by
  rintro _ ⟨h, rfl⟩
  change C.kernelAction (C.boundary h) = 1
  ext k
  change C.action (C.boundary h) (k : H) = k
  rw [C.peiffer]
  have hcomm : h * (k : H) = k * h :=
    Subgroup.mem_center_iff.mp (C.piTwo_le_center k.property) h
  rw [hcomm]
  simp

/-- The first homotopy group of a crossed module, realized as the quotient by the boundary image. -/
abbrev piOne := G ⧸ C.boundary.range

/-- The action on the homotopy kernel descends through the first homotopy group. -/
def piOneAction : piOne C →* MulAut C.piTwo :=
  QuotientGroup.lift C.boundary.range C.kernelAction C.boundaryRange_le_kernelAction

@[simp]
theorem piOneAction_mk (g : G) : piOneAction C (g : piOne C) = C.kernelAction g :=
  QuotientGroup.lift_mk C.boundary.range C.boundaryRange_le_kernelAction g

/-- A strict crossed-module two-morphism.  A label `h` changes the source one-arrow by its
boundary to obtain the target one-arrow. -/
structure TwoMorphism (source target : G) where
  label : H
  target_eq_boundary_mul_source : target = C.boundary label * source

/-- A based closed surface is a two-morphism from the identity arrow to itself. -/
abbrev ClosedSurface := C.TwoMorphism 1 1

/-- Closed-surface holonomy lands in the homotopy kernel. -/
theorem closedSurface_label_mem_piTwo (σ : C.ClosedSurface) : σ.label ∈ C.piTwo := by
  change C.boundary σ.label = 1
  simpa using σ.target_eq_boundary_mul_source.symm

/-- Closed-surface holonomies commute, even when the ambient crossed module is noncommutative. -/
theorem closedSurface_labels_commute (σ τ : C.ClosedSurface) :
    σ.label * τ.label = τ.label * σ.label :=
  (Subgroup.mem_center_iff.mp (C.piTwo_le_center (C.closedSurface_label_mem_piTwo σ))
    τ.label).symm

end CrossedModule

end HTGeometry.NomologicalHomotopyGeometry
