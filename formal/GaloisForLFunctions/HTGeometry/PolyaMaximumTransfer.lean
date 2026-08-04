import GaloisForLFunctions.HTGeometry.CompositionImageCircle

/-!
# Transferring a maximum through a composition

If the image of a disc under the inner function contains a whole circle, then the maximum principle
carries a bound for the composition on the disc to a bound for the outer function on the whole disc
that circle encloses.  This is the mechanism behind composition-growth estimates: a bound for
`f ∘ g` controls `f` on a disc whose radius is the size of `g`, and for a transcendental outer
function that disc's maximum is enormous.

Unlike the connectedness argument, which only produces one point of each modulus and hence only the
*minimum* of the outer function there, this uses the outer function's **maximum**.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

/-- **Maximum modulus on a ball at an arbitrary centre.** -/
theorem norm_le_of_sphere_bound_centre {g : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hM : ∀ w ∈ sphere c R, ‖g w‖ ≤ M) :
    ∀ w ∈ closedBall c R, ‖g w‖ ≤ M := by
  intro w hw
  have hRne : R ≠ 0 := ne_of_gt hR
  have hdiff : DifferentiableOn ℂ g (ball c R) :=
    (hg.differentiableOn).mono ball_subset_closedBall
  have hclos : closure (ball c R) = closedBall c R := closure_ball c hRne
  have hcont : ContinuousOn g (closure (ball c R)) := by
    rw [hclos]
    exact hg.continuousOn
  have hdc : DiffContOnCl ℂ g (ball c R) := ⟨hdiff, hcont⟩
  have hfront : ∀ v ∈ frontier (ball c R), ‖g v‖ ≤ M := by
    intro v hv
    rw [frontier_ball c hRne] at hv
    exact hM v hv
  have hwmem : w ∈ closure (ball c R) := by
    rw [hclos]
    exact hw
  exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc hfront hwmem

/-- **A circle in the image transfers the bound.**  If every point of the circle `sphere c ρ` is a
value of the inner function on the disc, then a bound for the composition on that disc bounds the
outer function on the whole closed ball of radius `ρ` around `c`. -/
theorem norm_le_of_sphere_subset_image {f g : ℂ → ℂ} {c : ℂ} {ρ r K : ℝ} (hρ : 0 < ρ)
    (hf : AnalyticOnNhd ℂ f (closedBall c ρ))
    (hsub : sphere c ρ ⊆ g '' (closedBall (0 : ℂ) r))
    (hK : ∀ z ∈ closedBall (0 : ℂ) r, ‖f (g z)‖ ≤ K) :
    ∀ w ∈ closedBall c ρ, ‖f w‖ ≤ K := by
  refine norm_le_of_sphere_bound_centre hρ hf ?_
  intro w hw
  obtain ⟨z, hz, hzw⟩ := hsub hw
  rw [← hzw]
  exact hK z hz

/-! ## A circle floor puts a disc in the image -/

/-- **A lower bound on a circle forces a disc in the image.**  If the inner function differs from its
central value by at least `ε` on the circle of radius `s`, and is not locally constant, then its image
of the closed disc contains the ball of radius `ε/2` about that central value.

This is mathlib's quantitative open mapping theorem in the form the composition estimate needs: the
hypothesis is exactly a minimum-modulus statement for the *shifted inner* function, and the
conclusion is the disc that `norm_le_of_sphere_subset_image` consumes. -/
theorem ball_subset_image_of_circle_floor {g : ℂ → ℂ} {s ε : ℝ} (hs : 0 < s)
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s))
    (hfloor : ∀ z : ℂ, ‖z‖ = s → ε ≤ ‖g z - g 0‖)
    (hnc : ¬ ∀ᶠ z in nhds (0 : ℂ), g z = g 0) :
    ball (g 0) (ε / 2) ⊆ g '' closedBall (0 : ℂ) s := by
  have hdiff : DifferentiableOn ℂ g (ball (0 : ℂ) s) :=
    (hg.differentiableOn).mono ball_subset_closedBall
  have hclos : closure (ball (0 : ℂ) s) = closedBall (0 : ℂ) s := closure_ball 0 (ne_of_gt hs)
  have hcont : ContinuousOn g (closure (ball (0 : ℂ) s)) := by
    rw [hclos]
    exact hg.continuousOn
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) s) := ⟨hdiff, hcont⟩
  have hsphere : ∀ z ∈ sphere (0 : ℂ) s, ε ≤ ‖g z - g 0‖ := by
    intro z hz
    refine hfloor z ?_
    simpa [mem_sphere_iff_norm] using hz
  have hfreq : ∃ᶠ z in nhds (0 : ℂ), g z ≠ g 0 := Filter.not_eventually.mp hnc
  exact hdc.ball_subset_image_closedBall hs hsphere hfreq

/-- **The composition bound controls the outer function on a disc.**  If the inner function differs
from its central value by at least `ε` on the circle of radius `s` and is not locally constant, then
any bound for `f ∘ g` on the closed disc of radius `s` bounds `f` on the closed disc of radius `ρ`
about `g 0`, for every `ρ < ε/2`.

This is the composition-growth inequality: the outer function is controlled on a disc whose radius is
half the inner function's minimum displacement, so a transcendental outer function forces the
composition to be large. -/
theorem norm_le_of_circle_floor {f g : ℂ → ℂ} {s ε ρ K : ℝ}
    (hs : 0 < s) (hρ : 0 < ρ) (hρε : ρ < ε / 2)
    (hg : AnalyticOnNhd ℂ g (closedBall (0 : ℂ) s))
    (hfloor : ∀ z : ℂ, ‖z‖ = s → ε ≤ ‖g z - g 0‖)
    (hnc : ¬ ∀ᶠ z in nhds (0 : ℂ), g z = g 0)
    (hf : AnalyticOnNhd ℂ f (closedBall (g 0) ρ))
    (hK : ∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K) :
    ∀ w ∈ closedBall (g 0) ρ, ‖f w‖ ≤ K := by
  have himg := ball_subset_image_of_circle_floor hs hg hfloor hnc
  have hsub : sphere (g 0) ρ ⊆ g '' closedBall (0 : ℂ) s := by
    refine subset_trans ?_ himg
    intro w hw
    have hdist : dist w (g 0) = ρ := by
      simpa [mem_sphere_iff_norm, dist_eq_norm] using hw
    simp only [mem_ball, hdist]
    linarith
  exact norm_le_of_sphere_subset_image hρ hf hsub hK

/-- **The composition is large when the outer function is.**  Contrapositive of the composition
bound: if the outer function exceeds `K` somewhere on the disc it controls, then the composition
exceeds `K` somewhere on the source disc. -/
theorem exists_norm_comp_gt {f g : ℂ → ℂ} {c : ℂ} {s ρ K : ℝ}
    (hcomp : (∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K) → ∀ w ∈ closedBall c ρ, ‖f w‖ ≤ K)
    {w₀ : ℂ} (hw₀ : w₀ ∈ closedBall c ρ) (hlarge : K < ‖f w₀‖) :
    ∃ z ∈ closedBall (0 : ℂ) s, K < ‖f (g z)‖ := by
  by_contra hcon
  have hall : ∀ z ∈ closedBall (0 : ℂ) s, ‖f (g z)‖ ≤ K := by
    intro z hz
    by_contra hc
    exact hcon ⟨z, hz, not_le.mp hc⟩
  exact absurd (hcomp hall w₀ hw₀) (not_le.mpr hlarge)

end GaloisForLFunctions.HTGeometry
