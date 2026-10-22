import GaloisForLFunctions.RHTower.Deninger.DeningerLocallyConstantTestSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Every subspace is closed for the finest locally convex topology

A vector outside a subspace of a vector space is separated from it by a linear functional
vanishing on the subspace, and the absolute value of that functional is one of the seminorms
defining the finest locally convex topology.  So the subspace is at positive distance from the
vector for that seminorm: no point outside a subspace is in its closure.

Together with the nuclearity of the finest topology this says that the distinguished subspaces of
a test space presented as a countable strict inductive limit — the closures of families of test
functions — are closed nuclear subspaces.

* `deningerFinest_separating` : a functional separating a vector from a subspace.
* `deningerFinest_subspace_closed` : **a subspace is at positive distance from any vector outside
  it.**
* `deningerTestSubspace_closed` : the same for the locally constant test space.
-/

namespace RHTower

section FinestClosed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- **A vector outside a subspace is separated from it by a defining seminorm.** -/
theorem deningerFinest_separating (F : Submodule 𝕜 E) {x : E} (hx : x ∉ F) :
    ∃ p : Seminorm 𝕜 E, (∀ v ∈ F, p v = 0) ∧ p x ≠ 0 := by
  obtain ⟨f, hfx, hfF⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hfF' : ∀ v ∈ F, f v = 0 := by
    intro v hv
    have hmem : f v ∈ Submodule.map f F := ⟨v, hv, rfl⟩
    rw [hfF] at hmem
    simpa using hmem
  refine ⟨(normSeminorm 𝕜 𝕜).comp f, fun v hv => ?_, ?_⟩
  · show ‖f v‖ = 0
    rw [hfF' v hv, norm_zero]
  · show ‖f x‖ ≠ 0
    exact norm_ne_zero_iff.mpr hfx

/-- **A subspace is closed for the finest locally convex topology**: a vector outside it is at
positive distance from every point of it, for one of the defining seminorms. -/
theorem deningerFinest_subspace_closed (F : Submodule 𝕜 E) {x : E} (hx : x ∉ F) :
    ∃ (p : Seminorm 𝕜 E) (c : ℝ), 0 < c ∧ ∀ v ∈ F, c ≤ p (x - v) := by
  obtain ⟨f, hfx, hfF⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  have hfF' : ∀ v ∈ F, f v = 0 := by
    intro v hv
    have hmem : f v ∈ Submodule.map f F := ⟨v, hv, rfl⟩
    rw [hfF] at hmem
    simpa using hmem
  refine ⟨(normSeminorm 𝕜 𝕜).comp f, ‖f x‖, norm_pos_iff.mpr hfx, fun v hv => ?_⟩
  show ‖f x‖ ≤ ‖f (x - v)‖
  rw [map_sub, hfF' v hv, sub_zero]

end FinestClosed

section TestSubspace

variable {Y : Type*} [TopologicalSpace Y]

/-- **Every subspace of the locally constant test space is closed** for its finest locally convex
topology. -/
theorem deningerTestSubspace_closed (F : Submodule ℝ (DeningerTestSpace Y))
    {g : DeningerTestSpace Y} (hg : g ∉ F) :
    ∃ (p : Seminorm ℝ (DeningerTestSpace Y)) (c : ℝ), 0 < c ∧ ∀ v ∈ F, c ≤ p (g - v) :=
  deningerFinest_subspace_closed F hg

end TestSubspace

end RHTower
