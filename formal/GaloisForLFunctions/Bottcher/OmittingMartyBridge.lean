/-
# Omitting lifts and Marty bounds

This file supplies the derivative-bound bridge between omitted-value disk lifts and Marty theory.
If a family factors through strict disk-valued lifts and the fixed target map has bounded spherical
derivative on the open unit disk, then the pushed-forward family has uniformly bounded spherical
derivative on a smaller ball.  Combined with `CrossRatioMartyBridge`, this rules out such lifts for
genuine frontier cross-ratio families.
-/
import GaloisForLFunctions.Bottcher.CrossRatioMartyBridge

open Complex Metric Set Filter Topology

namespace Bottcher

noncomputable section

/-- Spherical derivative chain-rule bound. -/
theorem sphericalDeriv_comp_le {μ g : ℂ → ℂ} {z : ℂ} {A B : ℝ}
    (hμ : DifferentiableAt ℂ μ (g z)) (hg : DifferentiableAt ℂ g z)
    (hμbd : sphericalDeriv μ (g z) ≤ A)
    (hgbd : ‖deriv g z‖ ≤ B) :
    sphericalDeriv (fun y => μ (g y)) z ≤ A * B := by
  have hderiv : deriv (fun y => μ (g y)) z = deriv μ (g z) * deriv g z := by
    exact (hμ.hasDerivAt.comp z hg.hasDerivAt).deriv
  have hdenpos : 0 < (1 : ℝ) + ‖μ (g z)‖ ^ (2 : ℕ) := by positivity
  have hσeq : sphericalDeriv (fun y => μ (g y)) z =
      sphericalDeriv μ (g z) * ‖deriv g z‖ := by
    unfold sphericalDeriv
    rw [hderiv, norm_mul]
    field_simp [hdenpos.ne']
  rw [hσeq]
  have hA0 : 0 ≤ A := le_trans (sphericalDeriv_nonneg μ (g z)) hμbd
  exact mul_le_mul hμbd hgbd (norm_nonneg _) hA0

/-- Spherical derivative is unchanged by equality in a neighbourhood. -/
theorem sphericalDeriv_congr_nhds {f g : ℂ → ℂ} {z : ℂ}
    (h : f =ᶠ[𝓝 z] g) : sphericalDeriv f z = sphericalDeriv g z := by
  unfold sphericalDeriv
  rw [h.deriv_eq, h.eq_of_nhds]

/-- A strict disk-valued lift through a fixed target with bounded spherical derivative gives a
spherical-derivative bound for the pushed-forward function on the half ball. -/
theorem sphericalDeriv_le_of_strict_disk_lift {μ f g : ℂ → ℂ} {c : ℂ} {R A : ℝ}
    (hR : 0 < R)
    (hμdiff : ∀ w : ℂ, ‖w‖ < 1 → DifferentiableAt ℂ μ w)
    (hμbd : ∀ w : ℂ, ‖w‖ < 1 → sphericalDeriv μ w ≤ A)
    (hgdiff : DifferentiableOn ℂ g (ball c R))
    (hgbd : ∀ z ∈ ball c R, ‖g z‖ < 1)
    (heq : Set.EqOn (fun z => μ (g z)) f (ball c R)) :
    ∀ z ∈ ball c (R / 2), sphericalDeriv f z ≤ A * (2 * 1 / R) := by
  intro z hz
  have hsub : ball c (R / 2) ⊆ ball c R := ball_subset_ball (by linarith)
  have hzR : z ∈ ball c R := hsub hz
  have hevent : f =ᶠ[𝓝 z] fun y => μ (g y) :=
    (eventuallyEq_of_mem (isOpen_ball.mem_nhds hzR) heq).symm
  rw [sphericalDeriv_congr_nhds hevent]
  have hgAt : DifferentiableAt ℂ g z := hgdiff.differentiableAt (isOpen_ball.mem_nhds hzR)
  have hgzbd : ‖g z‖ < 1 := hgbd z hzR
  have hgbd_le : ∀ y ∈ ball c R, ‖g y‖ ≤ 1 := fun y hy => le_of_lt (hgbd y hy)
  have hgderiv : ‖deriv g z‖ ≤ 2 * 1 / R :=
    norm_deriv_le_of_bounded_on_ball hR hgdiff hgbd_le z hz
  exact sphericalDeriv_comp_le (hμdiff (g z) hgzbd) hgAt (hμbd (g z) hgzbd) hgderiv

/-- A genuine frontier cross-ratio family cannot have strict disk lifts through any fixed target whose
spherical derivative is bounded on the open unit disk. -/
theorem no_spherical_strict_omitting_lift_of_bounded_target_sphericalDeriv_crossRatio_of_frontier
    {c α β z₀ : ℂ} {ρ Rlift A : ℝ} {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {μ : ℂ → ℂ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hμdiff : ∀ w : ℂ, ‖w‖ < 1 → DifferentiableAt ℂ μ w)
    (hμbd : ∀ w : ℂ, ‖w‖ < 1 → sphericalDeriv μ w ≤ A)
    (hlift : ∀ n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧ Set.EqOn (fun z => μ (g z))
        (Rseq n) (ball z₀ Rlift)) : False := by
  choose g hgdiff hgbd heq using hlift
  have hRlift : 0 < Rlift := by linarith
  have hhalf_sub : ball z₀ (Rlift / 2) ⊆ ball z₀ Rlift := ball_subset_ball (by linarith)
  have hdiff : ∀ n z, z ∈ ball z₀ (Rlift / 2) → DifferentiableAt ℂ (Rseq n) z := by
    intro n z hz
    have hzR : z ∈ ball z₀ Rlift := hhalf_sub hz
    have hcomp : DifferentiableAt ℂ (fun y => μ (g n y)) z :=
      (hμdiff (g n z) (hgbd n z hzR)).comp z
        ((hgdiff n).differentiableAt (isOpen_ball.mem_nhds hzR))
    have hevent : Rseq n =ᶠ[𝓝 z] fun y => μ (g n y) :=
      (eventuallyEq_of_mem (isOpen_ball.mem_nhds hzR) (heq n)).symm
    exact hcomp.congr_of_eventuallyEq hevent
  have hM : ∀ n z, z ∈ ball z₀ (Rlift / 2) →
      sphericalDeriv (Rseq n) z ≤ A * (2 * 1 / Rlift) := by
    intro n z hz
    exact sphericalDeriv_le_of_strict_disk_lift hRlift hμdiff hμbd (hgdiff n) (hgbd n)
      (heq n) z hz
  exact not_sphericalDeriv_bounded_crossRatio_on_frontier_ball
    (Rball := Rlift / 2) (M := A * (2 * 1 / Rlift)) hzfront hρ0 hρR hU hαβ hβ hα
    hpreα hzβ hR hdiff hM

end

end Bottcher
