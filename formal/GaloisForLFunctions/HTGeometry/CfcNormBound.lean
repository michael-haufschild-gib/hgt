import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-!
# Norm bounds for the continuous functional calculus

The isometric continuous functional calculus makes the operator norm of `cfc f a` the supremum of
`‖f‖` over the spectrum of `a`.  Two consequences used when a family of symbols is controlled only
on the spectrum: a pointwise bound bounds the operator, and symbols that become uniformly small on
the spectrum give operators converging to zero in norm.

This is the step that converts an estimate on rational symbols into a norm estimate on the
corresponding functions of a bounded self-adjoint operator.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ContinuousFunctionalCalculus
open Filter Topology

variable {𝕜 A : Type*} {p : outParam (A → Prop)}
variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
variable [IsometricContinuousFunctionalCalculus 𝕜 A p] [Nontrivial A]

/-- **CFC norm bound.**  A pointwise bound for the symbol on the spectrum bounds the norm of the
resulting operator, because that norm is attained as `‖f x‖` at some spectral point. -/
theorem norm_cfc_le_of_forall_le (f : 𝕜 → 𝕜) (a : A) {C : ℝ}
    (hf : ContinuousOn f (spectrum 𝕜 a)) (ha : p a)
    (h : ∀ x ∈ spectrum 𝕜 a, ‖f x‖ ≤ C) : ‖cfc f a‖ ≤ C := by
  obtain ⟨⟨x, hx, hxeq⟩, -⟩ := IsGreatest.norm_cfc (𝕜 := 𝕜) f a hf ha
  rw [← hxeq]
  exact h x hx

/-- **Norm convergence from uniform symbol smallness.**  If the symbols are eventually uniformly
small on the spectrum, the corresponding operators tend to zero in norm. -/
theorem tendsto_norm_cfc_zero {ι : Type*} {l : Filter ι} (g : ι → 𝕜 → 𝕜) (a : A) (ha : p a)
    (hcont : ∀ i, ContinuousOn (g i) (spectrum 𝕜 a))
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x ∈ spectrum 𝕜 a, ‖g i x‖ ≤ ε) :
    Tendsto (fun i => ‖cfc (g i) a‖) l (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  filter_upwards [h (ε / 2) (by linarith)] with i hi
  have hb := norm_cfc_le_of_forall_le (g i) a (hcont i) ha hi
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  linarith

end GaloisForLFunctions.HTGeometry
