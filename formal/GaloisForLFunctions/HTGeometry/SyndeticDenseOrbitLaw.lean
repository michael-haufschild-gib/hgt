import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.Data.Real.Basic

/-!
# Syndetic visits of dense compact-group flows

A dense one-parameter subgroup of a compact topological group cannot leave a
nonempty open target unvisited for arbitrarily long intervals.  Compactness
upgrades mere density to a uniform, target-dependent gap bound.

This is the topological recurrence mechanism needed below for autonomous
complexity: once an open set of hard endpoints exists on the orbit closure,
hard endpoints occur in every sufficiently long time interval, not only with
positive completed-time frequency.
-/

open Set Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Syndetic dense-orbit law.** Let a real one-parameter subgroup have dense
range in a compact topological group.  Every nonempty open target is hit in
every interval of one fixed finite length.

No metric, measure, differentiability, finite dimension, or rate assumption is
used.  The gap length depends on the orbit and target. -/
theorem denseAddOrbit_open_hits_syndetically
    {X : Type*} [TopologicalSpace X] [AddGroup X]
    [IsTopologicalAddGroup X] [CompactSpace X]
    (orbit : ℝ →+ X) (hdense : DenseRange orbit)
    {U : Set X} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a : ℝ,
      ∃ t ∈ Icc a (a + L), orbit t ∈ U := by
  let V : ℝ → Set X := fun s ↦ {x | x + orbit s ∈ U}
  have hVopen : ∀ s : ℝ, IsOpen (V s) := by
    intro s
    exact hUopen.preimage (continuous_id.add continuous_const)
  have hcover : Set.univ ⊆ ⋃ s : ℝ, V s := by
    intro x hx
    have hopen : IsOpen ((fun y : X ↦ x + y) ⁻¹' U) :=
      hUopen.preimage (continuous_const.add continuous_id)
    have hne : ((fun y : X ↦ x + y) ⁻¹' U).Nonempty := by
      obtain ⟨u, hu⟩ := hUne
      refine ⟨-x + u, ?_⟩
      simpa [add_assoc] using hu
    obtain ⟨s, hs⟩ := hdense.exists_mem_open hopen hne
    exact Set.mem_iUnion.mpr ⟨s, hs⟩
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover V hVopen hcover
  have hSne : S.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    subst S
    have hx := hS (Set.mem_univ (0 : X))
    simp at hx
  let lo := S.min' hSne
  let hi := S.max' hSne
  refine ⟨hi - lo, sub_nonneg.mpr (S.min'_le (S.max' hSne)
    (S.max'_mem hSne)), fun a ↦ ?_⟩
  have hx : orbit (a - lo) ∈ Set.univ := Set.mem_univ _
  have hxin : orbit (a - lo) ∈ ⋃ s ∈ S, V s := hS hx
  simp only [Set.mem_iUnion] at hxin
  obtain ⟨s, hsS, hVs⟩ := hxin
  refine ⟨a - lo + s, ?_, ?_⟩
  · constructor
    · have hlo : lo ≤ s := S.min'_le s hsS
      linarith
    · have hhi : s ≤ hi := S.le_max' s hsS
      linarith
  · change orbit (a - lo) + orbit s ∈ U at hVs
    simpa [map_add] using hVs

end GaloisForLFunctions.HTGeometry
