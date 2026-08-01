import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.Support

/-!
# Uniform limits of uniformly Cauchy sequences, and their supports

A uniformly Cauchy sequence of functions into a complete space converges uniformly: the pointwise
limits exist by completeness, and uniform Cauchyness upgrades pointwise convergence to uniform
convergence.  mathlib has the upgrade but not the existence statement.

A pointwise limit of functions vanishing outside a closed set again vanishes outside it, so the
support condition of a test space passes to limits.

* `exists_tendstoUniformly_of_uniformCauchySeq` : the limit exists.
* `tsupport_subset_of_tendsto` : the support condition passes to the limit.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

section UniformLimit

variable {alpha F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

/-- **A uniformly Cauchy sequence into a complete space converges uniformly.** -/
theorem exists_tendstoUniformly_of_uniformCauchySeq {f : ℕ → alpha → F}
    (h : UniformCauchySeqOn f Filter.atTop Set.univ) :
    ∃ g : alpha → F, TendstoUniformly f g Filter.atTop := by
  have hpt : ∀ x : alpha, CauchySeq (fun n => f n x) := by
    intro x
    have hmono : UniformCauchySeqOn f Filter.atTop {x} :=
      h.mono (Set.subset_univ {x})
    rw [Metric.uniformCauchySeqOn_iff] at hmono
    rw [Metric.cauchySeq_iff]
    intro eps heps
    obtain ⟨N, hN⟩ := hmono eps heps
    exact ⟨N, fun m hm n hn => hN m hm n hn x rfl⟩
  choose g hg using fun x : alpha => cauchySeq_tendsto_of_complete (hpt x)
  refine ⟨g, ?_⟩
  rw [← tendstoUniformlyOn_univ]
  exact h.tendstoUniformlyOn_of_tendsto fun x _ => hg x

end UniformLimit

section Support

variable {F : Type*} [NormedAddCommGroup F] {J : Set ℝ}

/-- A pointwise limit of functions vanishing outside a set vanishes outside it. -/
theorem eq_zero_of_tendsto_of_forall_eq_zero {f : ℕ → ℝ → F} {g : ℝ → F}
    (hg : ∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x)))
    (hzero : ∀ (n : ℕ) (x : ℝ), x ∉ J → f n x = 0) {x : ℝ} (hx : x ∉ J) : g x = 0 := by
  have hconst : Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (0 : F)) := by
    have hEq : (fun n : ℕ => f n x) = fun _ => (0 : F) := funext fun n => hzero n x hx
    rw [hEq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hg x) hconst

/-- **The support condition passes to a pointwise limit** when the ambient set is closed. -/
theorem tsupport_subset_of_tendsto (hJ : IsClosed J) {f : ℕ → ℝ → F} {g : ℝ → F}
    (hg : ∀ x, Filter.Tendsto (fun n => f n x) Filter.atTop (𝓝 (g x)))
    (hsupp : ∀ n, tsupport (f n) ⊆ J) : tsupport g ⊆ J := by
  have hzero : ∀ (n : ℕ) (x : ℝ), x ∉ J → f n x = 0 := by
    intro n x hx
    by_contra hne
    exact hx (hsupp n (subset_tsupport (f n) hne))
  have hsub : Function.support g ⊆ J := by
    intro x hx
    by_contra hxJ
    exact hx (eq_zero_of_tendsto_of_forall_eq_zero hg hzero hxJ)
  exact hJ.closure_subset_iff.mpr hsub

end Support

end GaloisForLFunctions.HTGeometry
