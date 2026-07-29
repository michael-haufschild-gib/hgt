import Mathlib.GroupTheory.Subgroup.Center

/-!
# The Peiffer kernel is central

The second Peiffer identity already forces the kernel of a crossed-module boundary into the
centre of its higher group.  Consequently every group that embeds faithfully into that kernel is
abelian.

The structure below records only the boundary, identity action, and second Peiffer identity used
by the proof.  Every crossed module supplies this data; no other crossed-module axiom is needed.

This is a standard algebraic obstruction.  It does not construct a physical 2-group or identify
any gauge group with a higher symmetry.
-/

namespace GaloisForLFunctions.HTGeometry

universe u v w

/-- Minimal Peiffer data sufficient to prove centrality of a crossed-module boundary kernel. -/
structure PeifferBoundary (G : Type u) (H : Type v) [Group G] [Group H] where
  boundary : H →* G
  action : G → H → H
  action_one : ∀ h, action 1 h = h
  peiffer : ∀ h k, action (boundary h) k = h * k * h⁻¹

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Every element in a Peiffer boundary kernel commutes with the entire higher group. -/
theorem PeifferBoundary.kernel_commutes (P : PeifferBoundary G H)
    {h : H} (hh : h ∈ P.boundary.ker) (k : H) :
    h * k = k * h := by
  have hconj : h * k * h⁻¹ = k := by
    calc
      h * k * h⁻¹ = P.action (P.boundary h) k := (P.peiffer h k).symm
      _ = P.action 1 k := by rw [MonoidHom.mem_ker.mp hh]
      _ = k := P.action_one k
  calc
    h * k = (h * k * h⁻¹) * h := by simp [mul_assoc]
    _ = k * h := by rw [hconj]

/-- The boundary kernel of Peiffer data lies in the centre. -/
theorem PeifferBoundary.ker_le_center (P : PeifferBoundary G H) :
    P.boundary.ker ≤ Subgroup.center H := by
  intro h hh
  rw [Subgroup.mem_center_iff]
  intro k
  exact (P.kernel_commutes hh k).symm

/-- Any two elements of the boundary kernel commute. -/
theorem PeifferBoundary.kernel_pair_commutes (P : PeifferBoundary G H)
    {h k : H} (hh : h ∈ P.boundary.ker) :
    h * k = k * h :=
  P.kernel_commutes hh k

/-- A group that embeds faithfully into a Peiffer boundary kernel must be abelian. -/
theorem PeifferBoundary.injective_kernel_source_commutes
    (P : PeifferBoundary G H) {K : Type w} [Group K]
    (i : K →* H) (hi : Function.Injective i)
    (hker : ∀ x, i x ∈ P.boundary.ker) (x y : K) :
    x * y = y * x := by
  apply hi
  rw [map_mul, map_mul]
  exact P.kernel_commutes (hker x) (i y)

end GaloisForLFunctions.HTGeometry
