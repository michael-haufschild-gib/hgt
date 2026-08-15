import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Finite-dimensional approximation gives total boundedness

A bounded set which every finite tolerance approximates by a finite-dimensional subspace is totally
bounded: the approximants live in a bounded piece of that subspace, which is compact because the
subspace is finite dimensional, and a finite net there is a finite net for the original set after
paying the approximation tolerance twice.

This is the abstract half of the Kolmogorov–Riesz criterion: all the analysis of a compactness proof
goes into exhibiting the approximating subspaces, and none into the covering argument.
-/

open Metric Set

namespace GaloisForLFunctions.HTGeometry

/-- **Finite-dimensional approximation implies total boundedness.** -/
theorem totallyBounded_of_finiteDimensional_approx {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Set E} {M : ℝ} (hM : ∀ f ∈ S, ‖f‖ ≤ M)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ V : Submodule ℝ E, FiniteDimensional ℝ V ∧
      ∀ f ∈ S, ∃ v : E, v ∈ V ∧ ‖f - v‖ ≤ ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  rcases Set.eq_empty_or_nonempty S with rfl | ⟨f₀, hf₀⟩
  · exact ⟨∅, Set.finite_empty, by simp⟩
  have hM0 : 0 ≤ M := le_trans (norm_nonneg f₀) (hM f₀ hf₀)
  obtain ⟨V, hV, happ⟩ := happrox (ε / 3) (by linarith)
  have hVfd : FiniteDimensional ℝ V := hV
  -- the approximants live in a compact ball of the finite-dimensional subspace
  have hcompact : IsCompact ((fun w : V => (w : E)) '' (Metric.closedBall (0 : V) (M + ε / 3))) :=
    (isCompact_closedBall (0 : V) (M + ε / 3)).image continuous_subtype_val
  obtain ⟨t, htfin, htcover⟩ :=
    Metric.totallyBounded_iff.1 hcompact.totallyBounded (ε / 3) (by linarith)
  refine ⟨t, htfin, fun f hf => ?_⟩
  obtain ⟨v, hvV, hvf⟩ := happ f hf
  have hvnorm : ‖v‖ ≤ M + ε / 3 := by
    have h1 : ‖v‖ ≤ ‖f‖ + ‖f - v‖ := by
      have h2 : ‖v‖ - ‖f‖ ≤ ‖v - f‖ := norm_sub_norm_le v f
      have h3 : ‖v - f‖ = ‖f - v‖ := norm_sub_rev v f
      linarith [h2, h3.le, h3.ge]
    have h3 : ‖f‖ ≤ M := hM f hf
    linarith
  have hvmem : v ∈ (fun w : V => (w : E)) '' (Metric.closedBall (0 : V) (M + ε / 3)) := by
    refine ⟨⟨v, hvV⟩, ?_, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hvnorm
  obtain ⟨y, hyt, hvy⟩ := Set.mem_iUnion₂.1 (htcover hvmem)
  refine Set.mem_iUnion₂.2 ⟨y, hyt, ?_⟩
  rw [Metric.mem_ball] at hvy ⊢
  have hdist : dist f v = ‖f - v‖ := dist_eq_norm f v
  calc dist f y ≤ dist f v + dist v y := dist_triangle f v y
    _ < ε / 3 + ε / 3 := by
        rw [hdist]
        linarith [hvf, hvy]
    _ < ε := by linarith

end GaloisForLFunctions.HTGeometry
