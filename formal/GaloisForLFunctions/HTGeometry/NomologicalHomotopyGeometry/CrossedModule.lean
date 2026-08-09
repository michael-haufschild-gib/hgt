import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Module

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
    have hk' : C.boundary k = 1 := hk
    have hp := C.peiffer k h
    rw [hk'] at hp
    simpa using hp
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

/-- If the crossed-module boundary is injective, every closed-surface label is trivial. -/
theorem closedSurface_label_eq_one_of_boundary_injective
    (hboundary : Function.Injective C.boundary) (σ : C.ClosedSurface) : σ.label = 1 := by
  apply hboundary
  simpa using C.closedSurface_label_mem_piTwo σ

/-! ## Differential crossed modules in form degrees one through three -/

/-- Degree-`1,2,3` part of the differential-form calculus of a differential crossed module.

`G₁,G₂,G₃` model `Ω¹(M;𝔤),Ω²(M;𝔤),Ω³(M;𝔤)` and `H₂,H₃`
model `Ω²(M;𝔥),Ω³(M;𝔥)`.  The identities are precisely the degree pieces of
`d²=0`, graded Leibniz, graded Jacobi, boundary-chain compatibility, and boundary equivariance
used by a strict 2-connection.  Ordinary Bianchi is deliberately not a field: it is derived below.
-/
structure DifferentialCrossedModuleCalculus
    (G₁ G₂ G₃ H₂ H₃ : Type*)
    [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
    [AddCommGroup H₂] [AddCommGroup H₃]
    [Module ℝ G₁] [Module ℝ G₂] [Module ℝ G₃]
    [Module ℝ H₂] [Module ℝ H₃] where
  dG₁ : G₁ →ₗ[ℝ] G₂
  dG₂ : G₂ →ₗ[ℝ] G₃
  dH₂ : H₂ →ₗ[ℝ] H₃
  boundary₂ : H₂ →ₗ[ℝ] G₂
  boundary₃ : H₃ →ₗ[ℝ] G₃
  bracket₁₁ : G₁ →ₗ[ℝ] G₁ →ₗ[ℝ] G₂
  bracket₁₂ : G₁ →ₗ[ℝ] G₂ →ₗ[ℝ] G₃
  action₁₂ : G₁ →ₗ[ℝ] H₂ →ₗ[ℝ] H₃
  d_sq_zero : ∀ A, dG₂ (dG₁ A) = 0
  d_bracket_self : ∀ A,
    dG₂ (bracket₁₁ A A) = -(2 : ℝ) • bracket₁₂ A (dG₁ A)
  jacobi_self : ∀ A, bracket₁₂ A (bracket₁₁ A A) = 0
  boundary_chain : ∀ B, dG₂ (boundary₂ B) = boundary₃ (dH₂ B)
  boundary_equivariant : ∀ A B,
    bracket₁₂ A (boundary₂ B) = boundary₃ (action₁₂ A B)

namespace DifferentialCrossedModuleCalculus

variable {G₁ G₂ G₃ H₂ H₃ : Type*}
variable [AddCommGroup G₁] [AddCommGroup G₂] [AddCommGroup G₃]
variable [AddCommGroup H₂] [AddCommGroup H₃]
variable [Module ℝ G₁] [Module ℝ G₂] [Module ℝ G₃]
variable [Module ℝ H₂] [Module ℝ H₃]
variable (D : DifferentialCrossedModuleCalculus G₁ G₂ G₃ H₂ H₃)

/-- Curvature `F_A = dA + ½[A,A]` of the one-form component. -/
noncomputable def curvature (A : G₁) : G₂ :=
  D.dG₁ A + (2 : ℝ)⁻¹ • D.bracket₁₁ A A

/-- Covariant differential on adjoint-valued two-forms. -/
def covariantG (A : G₁) (X : G₂) : G₃ :=
  D.dG₂ X + D.bracket₁₂ A X

/-- Fake curvature `F_A - t(B)`. -/
noncomputable def fakeCurvature (A : G₁) (B : H₂) : G₂ :=
  D.curvature A - D.boundary₂ B

/-- Three-curvature `H₃ = dB + A ▹ B`. -/
def threeCurvature (A : G₁) (B : H₂) : H₃ :=
  D.dH₂ B + D.action₁₂ A B

/-- Covariant differentiation is additive in its form argument. -/
theorem covariantG_sub (A : G₁) (X Y : G₂) :
    D.covariantG A (X - Y) = D.covariantG A X - D.covariantG A Y := by
  simp [covariantG, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Ordinary Bianchi identity, derived from square-zero, graded Leibniz, and Jacobi. -/
theorem curvature_bianchi (A : G₁) : D.covariantG A (D.curvature A) = 0 := by
  simp only [covariantG, curvature, map_add, map_smul, D.d_sq_zero,
    D.d_bracket_self, D.jacobi_self, smul_zero, add_zero]
  module

/-- Equivariance of the differential boundary intertwines both covariant differentials. -/
theorem covariantG_boundary (A : G₁) (B : H₂) :
    D.covariantG A (D.boundary₂ B) = D.boundary₃ (D.threeCurvature A B) := by
  simp [covariantG, threeCurvature, D.boundary_chain, D.boundary_equivariant]

/-- Theorem 3.1: fake-curvature transgression `d_A 𝒜 = -t(H₃)`. -/
theorem fakeCurvature_transgression (A : G₁) (B : H₂) :
    D.covariantG A (D.fakeCurvature A B) = -D.boundary₃ (D.threeCurvature A B) := by
  rw [fakeCurvature, covariantG_sub, curvature_bianchi, covariantG_boundary]
  exact zero_sub _

/-- Fake-flat three-curvature is valued in the differential crossed-module kernel. -/
theorem threeCurvature_mem_boundaryKernel_of_fakeFlat (A : G₁) (B : H₂)
    (hfake : D.fakeCurvature A B = 0) :
    D.threeCurvature A B ∈ LinearMap.ker D.boundary₃ := by
  change D.boundary₃ (D.threeCurvature A B) = 0
  have htrans := D.fakeCurvature_transgression A B
  rw [hfake] at htrans
  simpa [covariantG] using htrans

/-- Injective differential boundary kills every fake-flat three-curvature. -/
theorem threeCurvature_eq_zero_of_fakeFlat_of_boundary_injective (A : G₁) (B : H₂)
    (hfake : D.fakeCurvature A B = 0) (hinjective : Function.Injective D.boundary₃) :
    D.threeCurvature A B = 0 := by
  apply hinjective
  simpa using D.threeCurvature_mem_boundaryKernel_of_fakeFlat A B hfake

end DifferentialCrossedModuleCalculus

end CrossedModule

end HTGeometry.NomologicalHomotopyGeometry
