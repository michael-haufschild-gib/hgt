/-
# Montel's theorem for holomorphic families — foundation (the `J_c` natural-boundary layer)

The final brick of connected-case E–vS rigidity (the `J_c` natural boundary, hence repelling-cycle
density) rests on **Montel's theorem**: a locally uniformly bounded family of holomorphic functions is
normal (locally-uniformly precompact). mathlib has the three ingredients — the Cauchy derivative
estimate (`norm_deriv_le_of_forall_mem_sphere_norm_le`), Arzelà–Ascoli, and that a locally-uniform
limit of holomorphic functions is holomorphic (`TendstoLocallyUniformlyOn.differentiableOn`) — but not
Montel itself, nor any Julia/Fatou theory. This file begins that layer.

**First brick — equicontinuity via Cauchy.** A holomorphic `f` bounded by `C` on `ball c R` has
`‖f'‖ ≤ 2C/R` on `ball c (R/2)`, hence is `(2C/R)`-Lipschitz there. Uniform in `f` over a bounded
family, this is the equicontinuity that Arzelà–Ascoli turns into normality.

New file (Montel/Julia lane for the connected-case natural boundary); Mathlib only.
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Tactic

open Complex Metric Set

namespace Bottcher

/-- **Cauchy derivative bound on the half-ball.** If `f` is holomorphic on `ball c R` and `‖f‖ ≤ C`
there, then `‖f'‖ ≤ 2C/R` on `ball c (R/2)`. -/
theorem norm_deriv_le_of_bounded_on_ball {f : ℂ → ℂ} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hbd : ∀ z ∈ ball c R, ‖f z‖ ≤ C) :
    ∀ z ∈ ball c (R / 2), ‖deriv f z‖ ≤ 2 * C / R := by
  intro z hz
  rw [mem_ball] at hz
  have hRhalf : 0 < R / 2 := by linarith
  have hcball : closedBall z (R / 2) ⊆ ball c R := by
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    calc dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
      _ < R / 2 + R / 2 := by linarith
      _ = R := by ring
  have hd : DiffContOnCl ℂ f (ball z (R / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z (ne_of_gt hRhalf)]
    exact hf.mono hcball
  have hsphere : ∀ w ∈ sphere z (R / 2), ‖f w‖ ≤ C := by
    intro w hw
    exact hbd w (hcball (sphere_subset_closedBall hw))
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRhalf hd hsphere
  calc ‖deriv f z‖ ≤ C / (R / 2) := hcauchy
    _ = 2 * C / R := by field_simp

/-- **Equicontinuity (uniform Lipschitz bound) of a bounded holomorphic family.** Every `f` in a
family holomorphic on `ball c R` and bounded by `C` is `(2C/R)`-Lipschitz on `ball c (R/2)`, with the
constant independent of `f` — the equicontinuity feeding Arzelà–Ascoli toward Montel. -/
theorem norm_sub_le_of_bounded_on_ball {f : ℂ → ℂ} {c : ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hbd : ∀ z ∈ ball c R, ‖f z‖ ≤ C)
    {z w : ℂ} (hz : z ∈ ball c (R / 2)) (hw : w ∈ ball c (R / 2)) :
    ‖f z - f w‖ ≤ (2 * C / R) * ‖z - w‖ := by
  have hconv : Convex ℝ (ball c (R / 2)) := convex_ball c (R / 2)
  have hdb : ∀ x ∈ ball c (R / 2), ‖deriv f x‖ ≤ 2 * C / R :=
    norm_deriv_le_of_bounded_on_ball hR hf hbd
  have hsub : ball c (R / 2) ⊆ ball c R :=
    ball_subset_ball (by linarith)
  have hdiff : ∀ x ∈ ball c (R / 2), HasDerivAt f (deriv f x) x := fun x hx =>
    (hf.differentiableAt ((isOpen_ball).mem_nhds (hsub hx))).hasDerivAt
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hdiff x hx).hasDerivWithinAt) hdb hconv hw hz

/-- **Equicontinuity of a uniformly bounded holomorphic family** — the Arzelà–Ascoli input toward
Montel. If every `f i` is holomorphic on `ball c R` and bounded there by a common `C`, then the
family restricted to a compact closed ball `closedBall c r` (`r < R/2`) is `Equicontinuous`: the
`(2C/R)`-Lipschitz bound is uniform in the index `i`. This is the equicontinuity half of the
Arzelà–Ascoli hypotheses; pointwise relative compactness (the other half) is immediate in `ℂ` from
the uniform bound `C`. -/
theorem equicontinuous_family_of_bounded {ι : Type*} {f : ι → ℂ → ℂ} {c : ℂ} {R C r : ℝ}
    (hR : 0 < R) (hr : r < R / 2)
    (hf : ∀ i, DifferentiableOn ℂ (f i) (ball c R))
    (hbd : ∀ i, ∀ z ∈ ball c R, ‖f i z‖ ≤ C) :
    Equicontinuous (fun (i : ι) (p : ↥(closedBall c r)) => f i p.1) := by
  have hsub : closedBall c r ⊆ ball c (R / 2) := closedBall_subset_ball hr
  refine Metric.equicontinuous_of_continuity_modulus (fun d => (2 * C / R) * d) ?_ _ ?_
  · have hcont : Continuous (fun d : ℝ => (2 * C / R) * d) := continuous_const.mul continuous_id
    simpa using hcont.tendsto 0
  · intro x y i
    rw [Complex.dist_eq, Subtype.dist_eq, Complex.dist_eq]
    exact norm_sub_le_of_bounded_on_ball hR (hf i) (hbd i) (hsub x.2) (hsub y.2)

end Bottcher
