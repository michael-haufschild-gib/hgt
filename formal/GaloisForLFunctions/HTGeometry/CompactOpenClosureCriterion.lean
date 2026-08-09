import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Membership in a compact-open closure from uniform approximation on compacta

Convergence in the compact-open topology on `C(X, ℂ)` is uniform convergence on every compact set.
So a function approximable, on each compact set and to each accuracy, by members of a subalgebra
lies in that subalgebra's closure: run the approximation along a compact exhaustion with error
`1/(n+1)` and the resulting sequence converges.

This is the bridge from an analytic approximation theorem to a statement about topological closures
of subalgebras of continuous functions.

* `HTGeometry.mem_topologicalClosure_of_forall_isCompact_approx`.
-/

open Filter Topology

namespace HTGeometry

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]

/-- **Uniform approximation on compacta gives membership in the compact-open closure.** -/
theorem mem_topologicalClosure_of_forall_isCompact_approx
    (S : Subalgebra ℂ C(X, ℂ)) (f : C(X, ℂ))
    (h : ∀ K : Set X, IsCompact K → ∀ ε : ℝ, 0 < ε →
      ∃ g ∈ S, ∀ x ∈ K, ‖f x - g x‖ < ε) :
    f ∈ S.topologicalClosure := by
  classical
  set e : CompactExhaustion X := CompactExhaustion.choice X with he
  have hchoice : ∀ n : ℕ, ∃ g : C(X, ℂ), g ∈ S ∧
      ∀ x ∈ e n, ‖f x - g x‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨g, hgS, hg⟩ := h (e n) (e.isCompact n) (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨g, hgS, hg⟩
  choose g hgS hg using hchoice
  have htend : Tendsto g atTop (𝓝 f) := by
    rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    obtain ⟨m, hm⟩ := e.exists_superset_of_isCompact hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine eventually_atTop.2 ⟨max m N, fun n hn x hx => ?_⟩
    have hmn : m ≤ n := le_trans (le_max_left _ _) hn
    have hNn : N ≤ n := le_trans (le_max_right _ _) hn
    have hxe : x ∈ e n := CompactExhaustion.subset e hmn (hm hx)
    have hbound := hg n x hxe
    have hεn : 1 / ((n : ℝ) + 1) < ε := by
      have hNr : (1 : ℝ) / ε < (N : ℝ) := hN
      have hNn' : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
      have hlt : (1 : ℝ) / ε < (n : ℝ) + 1 := by linarith
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hlt
      linarith
    rw [Complex.dist_eq]
    exact lt_trans hbound hεn
  have hmem : f ∈ closure (S : Set C(X, ℂ)) :=
    mem_closure_of_tendsto htend (Eventually.of_forall fun n => hgS n)
  rw [← SetLike.mem_coe, Subalgebra.topologicalClosure_coe]
  exact hmem

end HTGeometry
