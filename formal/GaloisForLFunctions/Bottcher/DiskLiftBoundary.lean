/-
# Boundary hit for bounded disk-valued lift limits

This file isolates the maximum-modulus step needed in the omitted-values normality assembly:
a holomorphic limit into the closed unit disk either stays strictly inside locally or, if it hits
the unit circle at an interior point, is constant on the connected ball.
-/
import GaloisForLFunctions.Bottcher.MontelNormal
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.Uniqueness

open Complex Metric Topology Filter Set

namespace Bottcher

noncomputable section

/-- A holomorphic map bounded by the closed unit disk on a ball and hitting the boundary at one
interior point is constant on the whole ball. -/
theorem eqOn_const_of_closedDisk_bound_boundary_hit {g : ℂ → ℂ} {c z₀ : ℂ} {R : ℝ}
    (hz₀ : z₀ ∈ ball c R)
    (hgdiff : DifferentiableOn ℂ g (ball c R))
    (hbd : ∀ z ∈ ball c R, ‖g z‖ ≤ 1)
    (hz₀bd : ‖g z₀‖ = 1) :
    Set.EqOn g (fun _ => g z₀) (ball c R) := by
  have hgan : AnalyticOnNhd ℂ g (ball c R) := hgdiff.analyticOnNhd isOpen_ball
  have hdiff : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ g z := by
    filter_upwards [isOpen_ball.mem_nhds hz₀] with z hz
    exact (hgan z hz).differentiableAt
  have hlm : IsLocalMax (norm ∘ g) z₀ := by
    filter_upwards [isOpen_ball.mem_nhds hz₀] with z hz
    show ‖g z‖ ≤ ‖g z₀‖
    rw [hz₀bd]
    exact hbd z hz
  have hconst : ∀ᶠ z in 𝓝 z₀, g z = g z₀ := eventually_eq_of_isLocalMax_norm hdiff hlm
  exact hgan.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
    (convex_ball c R).isPreconnected hz₀ hconst

/-- Centered version of `eqOn_const_of_closedDisk_bound_boundary_hit`. -/
theorem eqOn_const_of_closedDisk_bound_center_boundary_hit {g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hgdiff : DifferentiableOn ℂ g (ball c R))
    (hbd : ∀ z ∈ ball c R, ‖g z‖ ≤ 1)
    (hcbd : ‖g c‖ = 1) :
    Set.EqOn g (fun _ => g c) (ball c R) :=
  eqOn_const_of_closedDisk_bound_boundary_hit (mem_ball_self hR) hgdiff hbd hcbd

/-- If a continuous disk-limit is strictly inside the unit disk at the center, then on a smaller
closed ball it is uniformly bounded by some `s < 1`. -/
theorem exists_closedBall_norm_bound_lt_one_of_continuousOn {g : ℂ → ℂ} {z₀ : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hgcont : ContinuousOn g (closedBall z₀ ρ))
    (hz₀ : ‖g z₀‖ < 1) :
    ∃ r s : ℝ, 0 < r ∧ s < 1 ∧ closedBall z₀ r ⊆ closedBall z₀ ρ ∧
      ∀ z ∈ closedBall z₀ r, ‖g z‖ ≤ s := by
  let s : ℝ := (‖g z₀‖ + 1) / 2
  have hz₀s : ‖g z₀‖ < s := by
    dsimp [s]
    linarith
  have hs1 : s < 1 := by
    dsimp [s]
    linarith
  have hzmem : z₀ ∈ closedBall z₀ ρ := mem_closedBall_self hρ.le
  have hnorm_cont : ContinuousWithinAt (fun z => ‖g z‖) (closedBall z₀ ρ) z₀ :=
    continuous_norm.continuousAt.comp_continuousWithinAt (hgcont z₀ hzmem)
  rw [Metric.continuousWithinAt_iff] at hnorm_cont
  have hε : 0 < s - ‖g z₀‖ := by
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := hnorm_cont (s - ‖g z₀‖) hε
  let r : ℝ := min ρ δ / 2
  have hrpos : 0 < r := by
    dsimp [r]
    positivity
  refine ⟨r, s, hrpos, hs1, ?_, ?_⟩
  · intro z hz
    rw [mem_closedBall] at hz ⊢
    have hrleρ : r ≤ ρ := by
      dsimp [r]
      have hmin : min ρ δ ≤ ρ := min_le_left _ _
      linarith
    exact hz.trans hrleρ
  · intro z hz
    have hzρ : z ∈ closedBall z₀ ρ := by
      rw [mem_closedBall] at hz ⊢
      have hrleρ : r ≤ ρ := by
        dsimp [r]
        have hmin : min ρ δ ≤ ρ := min_le_left _ _
        linarith
      exact hz.trans hrleρ
    have hdistδ : dist z z₀ < δ := by
      rw [mem_closedBall] at hz
      have hrltδ : r < δ := by
        dsimp [r]
        have hmin : min ρ δ ≤ δ := min_le_right _ _
        linarith
      exact lt_of_le_of_lt hz hrltδ
    have hdist : dist ‖g z‖ ‖g z₀‖ < s - ‖g z₀‖ := hδ hzρ hdistδ
    rw [Real.dist_eq] at hdist
    have hle : ‖g z‖ - ‖g z₀‖ ≤ |‖g z‖ - ‖g z₀‖| := le_abs_self _
    linarith

end

end Bottcher
