import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Minimal vectors of a lattice

The first layer of reduction theory.  A discrete `ℤ`-submodule of a finite-dimensional real normed
space is closed, so it meets every closed ball in a compact discrete — hence finite — set.
Consequently a nonzero lattice has a **shortest nonzero vector**, and the set of shortest vectors is
finite and nonempty.

These are the objects the well-rounded retract is built from: a lattice is *well-rounded* when its
minimal vectors span, and the well-rounded locus is the contractible complex on which `SL_n(𝒪)`
acts cocompactly with finite stabilizers — which is what makes `H_i(SL_n(𝒪), ℤ)` finitely
generated, the integral input that Borel's rank theorem needs and that no finite-coefficient
argument can supply (`divisibility_firewall`).

* `discreteSubmodule_isClosed` : a discrete submodule is closed.
* `finite_lattice_inter_closedBall` : **it meets every closed ball in a finite set.**
* `exists_minimal_norm` : **a nonzero lattice has a shortest nonzero vector.**
* `latticeMinimum`, `latticeMinimalVectors` : the minimum and the set attaining it.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedSpace ℝ E] [ProperSpace E] in
/-- A discrete `ℤ`-submodule of a normed space is closed. -/
theorem discreteSubmodule_isClosed (L : Submodule ℤ E) [DiscreteTopology L] :
    IsClosed (L : Set E) := by
  haveI : DiscreteTopology (↥(L.toAddSubgroup)) := ‹DiscreteTopology ↥L›
  exact AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)

omit [NormedSpace ℝ E] in
/-- **A discrete submodule meets every bounded set in a finite set.** -/
theorem finite_lattice_inter_of_bounded (L : Submodule ℤ E) [DiscreteTopology L]
    {s : Set E} (hs : Bornology.IsBounded s) : (s ∩ (L : Set E)).Finite :=
  Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hs
    (discreteSubmodule_isClosed L)

omit [NormedSpace ℝ E] in
/-- **A nonzero discrete submodule has a shortest nonzero vector.** -/
theorem exists_minimal_norm (L : Submodule ℤ E) [DiscreteTopology L]
    (hne : ∃ v ∈ L, v ≠ (0 : E)) :
    ∃ v ∈ L, v ≠ (0 : E) ∧ ∀ w ∈ L, w ≠ (0 : E) → ‖v‖ ≤ ‖w‖ := by
  classical
  obtain ⟨v₀, hv₀L, hv₀⟩ := hne
  have hbdd : Bornology.IsBounded (closedBall (0 : E) ‖v₀‖) := Metric.isBounded_closedBall
  have hfin : ((closedBall (0 : E) ‖v₀‖) ∩ (L : Set E)).Finite :=
    finite_lattice_inter_of_bounded L hbdd
  set S : Set E := {w | w ∈ (closedBall (0 : E) ‖v₀‖) ∩ (L : Set E) ∧ w ≠ 0} with hS
  have hfinS : S.Finite := hfin.subset (fun _ hw => hw.1)
  have hv₀mem : v₀ ∈ S := by
    refine ⟨⟨?_, hv₀L⟩, hv₀⟩
    simp [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨v, hvS, hvmin⟩ :=
    hfinS.toFinset.exists_min_image (fun w => ‖w‖) ⟨v₀, hfinS.mem_toFinset.2 hv₀mem⟩
  have hvS' : v ∈ S := hfinS.mem_toFinset.1 hvS
  refine ⟨v, hvS'.1.2, hvS'.2, fun w hwL hw => ?_⟩
  by_cases hball : ‖w‖ ≤ ‖v₀‖
  · have hwS : w ∈ S := by
      refine ⟨⟨?_, hwL⟩, hw⟩
      simpa [Metric.mem_closedBall, dist_zero_right] using hball
    exact hvmin w (hfinS.mem_toFinset.2 hwS)
  · push Not at hball
    have hv₀le : ‖v‖ ≤ ‖v₀‖ := by
      have := hvS'.1.1
      simpa [Metric.mem_closedBall, dist_zero_right] using this
    exact le_trans hv₀le hball.le

end GaloisForLFunctions.HTGeometry
