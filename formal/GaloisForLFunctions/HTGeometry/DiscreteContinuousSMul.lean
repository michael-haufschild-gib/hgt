import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Continuity of an action on a discrete space

An action of a topological group on a discrete space is continuous exactly when every stabiliser is
open: the preimage of a point is the union over the (open) points of the target of a left coset of a
stabiliser.
-/

namespace HTGeometry

open MulAction
open scoped Pointwise

variable {G B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MulAction G B] [TopologicalSpace B] [DiscreteTopology B]

omit [TopologicalSpace B] [DiscreteTopology B] in
/-- The set of group elements carrying a given point to another is open when the stabiliser is. -/
theorem isOpen_smul_eq_of_isOpen_stabilizer (hstab : ∀ b : B, IsOpen (stabilizer G b : Set G))
    (b c : B) : IsOpen {g : G | g • b = c} := by
  rcases Set.eq_empty_or_nonempty {g : G | g • b = c} with h | ⟨g₀, hg₀⟩
  · rw [h]
    exact isOpen_empty
  · have hset : {g : G | g • b = c} = g₀ • (stabilizer G b : Set G) := by
      ext g
      constructor
      · intro hg
        refine ⟨g₀⁻¹ * g, ?_, ?_⟩
        · show (g₀⁻¹ * g) • b = b
          rw [mul_smul, hg, ← hg₀, inv_smul_smul]
        · simp
      · rintro ⟨s, hs, rfl⟩
        show (g₀ * s) • b = c
        rw [mul_smul, (by exact hs : s • b = b), hg₀]
    rw [hset]
    exact (hstab b).smul g₀

/-- **An action with open stabilisers on a discrete space is continuous.** -/
theorem continuousSMul_of_isOpen_stabilizer (hstab : ∀ b : B, IsOpen (stabilizer G b : Set G)) :
    ContinuousSMul G B := by
  have key : ∀ c : B, IsOpen ((fun p : G × B => p.1 • p.2) ⁻¹' {c}) := by
    intro c
    have hpre : (fun p : G × B => p.1 • p.2) ⁻¹' {c}
        = ⋃ b : B, {g : G | g • b = c} ×ˢ ({b} : Set B) := by
      ext ⟨g, b⟩
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_prod,
        Set.mem_setOf_eq]
      constructor
      · intro h
        exact ⟨b, h, rfl⟩
      · rintro ⟨b', hb', rfl⟩
        exact hb'
    rw [hpre]
    refine isOpen_iUnion fun b => ?_
    exact (isOpen_smul_eq_of_isOpen_stabilizer hstab b c).prod (isOpen_discrete _)
  refine ⟨continuous_def.2 fun U _ => ?_⟩
  have hU : (fun p : G × B => p.1 • p.2) ⁻¹' U
      = ⋃ c ∈ U, (fun p : G × B => p.1 • p.2) ⁻¹' {c} := by
    ext p
    simp
  rw [hU]
  exact isOpen_biUnion fun c _ => key c

end HTGeometry
