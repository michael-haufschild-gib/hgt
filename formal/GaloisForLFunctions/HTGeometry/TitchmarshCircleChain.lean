import GaloisForLFunctions.HTGeometry.ThreeCircles

/-!
# The quantitative circle step in Titchmarsh's zero-gap argument

This module isolates the hard complex-analysis mechanism of Titchmarsh, Theorem 9.12.  A one-sided
bound for the real part of a holomorphic logarithm is first converted by Borel--Carathéodory into a
modulus bound on a smaller circle.  Hadamard's three-circles theorem then interpolates that bound
with the previous overlapping circle.

Radii `h/8, h/4, h/2` are used.  Their logarithmic interpolation weight is exactly `1/2`; this is a
slightly cleaner rescaling of Titchmarsh's four-circle construction and produces the same
`1 / log log log T` zero-gap rate.
-/

open Complex Set Metric

namespace GaloisForLFunctions.HTGeometry

/-- Borel--Carathéodory translated to an arbitrary centre. -/
theorem norm_le_of_re_le_ball {g : ℂ → ℂ} {c : ℂ} {A R : ℝ}
    (hA : 0 < A) (hg : DifferentiableOn ℂ g (ball c R))
    (hre : ∀ z ∈ ball c R, (g z).re ≤ A) (hR : 0 < R)
    {z : ℂ} (hz : z ∈ ball c R) :
    ‖g z‖ ≤ 2 * A * ‖z - c‖ / (R - ‖z - c‖) +
      ‖g c‖ * (R + ‖z - c‖) / (R - ‖z - c‖) := by
  let G : ℂ → ℂ := fun w => g (c + w)
  have hGdiff : DifferentiableOn ℂ G (ball 0 R) := by
    intro w hw
    have hcw : c + w ∈ ball c R := by
      rw [mem_ball_iff_norm]
      simpa using mem_ball_zero_iff.mp hw
    exact ((hg.differentiableAt (isOpen_ball.mem_nhds hcw)).comp w (by fun_prop)).differentiableWithinAt
  have hGmaps : MapsTo G (ball 0 R) {u : ℂ | u.re ≤ A} := by
    intro w hw
    have hcw : c + w ∈ ball c R := by
      rw [mem_ball_iff_norm]
      simpa using mem_ball_zero_iff.mp hw
    exact hre (c + w) hcw
  have hzc : z - c ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, ← mem_ball_iff_norm]
    exact hz
  have hmain := Complex.borelCaratheodory hA hGdiff hGmaps hR hzc
  have hzero : G 0 = g c := by simp [G]
  have hpoint : G (z - c) = g z := by simp [G]
  rwa [hzero, hpoint] at hmain

/-- At the Titchmarsh radii, Borel--Carathéodory has the clean constants `4` and `5`. -/
theorem norm_le_titchmarsh_borel {g : ℂ → ℂ} {c : ℂ} {A h Q : ℝ}
    (hA : 0 < A) (hh : 0 < h)
    (hg : DifferentiableOn ℂ g (ball c (3 * h / 4)))
    (hre : ∀ z ∈ ball c (3 * h / 4), (g z).re ≤ A)
    (hc : ‖g c‖ ≤ Q) {z : ℂ} (hz : ‖z - c‖ ≤ h / 2) :
    ‖g z‖ ≤ 4 * A + 5 * Q := by
  have hR : 0 < 3 * h / 4 := by positivity
  have hzmem : z ∈ ball c (3 * h / 4) := by
    rw [mem_ball_iff_norm]
    linarith
  have hmain := norm_le_of_re_le_ball hA hg hre hR hzmem
  have hden : 0 < 3 * h / 4 - ‖z - c‖ := by linarith
  have hdenHalf : 0 < 3 * h / 4 - h / 2 := by linarith
  have hfirst :
      2 * A * ‖z - c‖ / (3 * h / 4 - ‖z - c‖) ≤ 4 * A := by
    rw [div_le_iff₀ hden]
    nlinarith [norm_nonneg (z - c)]
  have hsecond :
      ‖g c‖ * (3 * h / 4 + ‖z - c‖) / (3 * h / 4 - ‖z - c‖) ≤ 5 * Q := by
    have hQ0 : 0 ≤ Q := (norm_nonneg _).trans hc
    rw [div_le_iff₀ hden]
    have hmul : ‖g c‖ * (3 * h / 4 + ‖z - c‖) ≤
        Q * (3 * h / 4 + h / 2) := by
      exact mul_le_mul hc (by linarith) (by positivity) hQ0
    nlinarith
  linarith

/-- The logarithmic interpolation weight of the radii `h/8, h/4, h/2` is `1/2`. -/
theorem titchmarsh_logarithmic_weight {h : ℝ} (hh : 0 < h) :
    (Real.log (h / 4) - Real.log (h / 8)) /
        (Real.log (h / 2) - Real.log (h / 8)) = 1 / 2 := by
  have hhne : h ≠ 0 := hh.ne'
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have h4 : (4 : ℝ) ≠ 0 := by norm_num
  have h8 : (8 : ℝ) ≠ 0 := by norm_num
  rw [Real.log_div hhne h4, Real.log_div hhne h8,
    Real.log_div hhne h2]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [hlog4, hlog8]
  have hlog2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  ring_nf
  rw [mul_inv_cancel₀ hlog2]
  norm_num

/-- One overlapping-circle step.  An inner-circle bound `m`, a centre bound `Q`, and a real-part
bound `A` give the geometric-mean bound on the middle circle. -/
theorem norm_le_titchmarsh_circle_step {g : ℂ → ℂ} {c : ℂ} {A h m Q : ℝ}
    (hA : 0 < A) (hh : 0 < h)
    (hg : DifferentiableOn ℂ g (ball c (3 * h / 4)))
    (hre : ∀ z ∈ ball c (3 * h / 4), (g z).re ≤ A)
    (hc : ‖g c‖ ≤ Q)
    (hinner : ∀ z : ℂ, ‖z - c‖ = h / 8 → ‖g z‖ ≤ m)
    {z : ℂ} (hz : ‖z - c‖ = h / 4) :
    ‖g z‖ ≤ m ^ (1 / 2 : ℝ) * (4 * A + 5 * Q) ^ (1 / 2 : ℝ) := by
  have h1 : 0 < h / 8 := by positivity
  have h13 : h / 8 < h / 2 := by linarith
  have h3R : h / 2 < 3 * h / 4 := by linarith
  have houter : ∀ w : ℂ, ‖w - c‖ = h / 2 → ‖g w‖ ≤ 4 * A + 5 * Q := by
    intro w hw
    exact norm_le_titchmarsh_borel hA hh hg hre hc (le_of_eq hw)
  have hmain := norm_le_of_three_circles_center h1 h13 h3R hg hinner houter
    (z := z) (by rw [hz]; linarith) (by rw [hz]; linarith)
  have hweight := titchmarsh_logarithmic_weight hh
  rw [hz, hweight] at hmain
  norm_num at hmain ⊢
  exact hmain

/-- Local maximum principle: a sphere bound controls the enclosed closed ball when holomorphy is
available on a slightly larger ball. -/
theorem norm_le_on_closedBall_of_sphere_of_differentiableOn
    {g : ℂ → ℂ} {c : ℂ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hg : DifferentiableOn ℂ g (ball c R))
    (hsphere : ∀ z ∈ sphere c r, ‖g z‖ ≤ M) :
    ∀ z ∈ closedBall c r, ‖g z‖ ≤ M := by
  intro z hz
  have hdiffcl : DiffContOnCl ℂ g (ball c r) := by
    constructor
    · intro w hw
      have hwR : w ∈ ball c R := ball_subset_ball (le_of_lt hrR) hw
      exact (hg.differentiableAt (isOpen_ball.mem_nhds hwR)).differentiableWithinAt
    · intro w hw
      rw [closure_ball c hr.ne'] at hw
      have hwR : w ∈ ball c R := by
        rw [mem_ball_iff_norm]
        rw [mem_closedBall_iff_norm] at hw
        exact lt_of_le_of_lt hw hrR
      exact (hg.differentiableAt (isOpen_ball.mem_nhds hwR)).continuousAt.continuousWithinAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdiffcl ?_ ?_
  · intro w hw
    rw [frontier_ball c hr.ne'] at hw
    exact hsphere w hw
  · rw [closure_ball c hr.ne']
    exact hz

/-- Closed-disc version of one Titchmarsh circle step. -/
theorem norm_le_titchmarsh_circle_step_closedBall {g : ℂ → ℂ} {c : ℂ} {A h m Q : ℝ}
    (hA : 0 < A) (hh : 0 < h)
    (hg : DifferentiableOn ℂ g (ball c (3 * h / 4)))
    (hre : ∀ z ∈ ball c (3 * h / 4), (g z).re ≤ A)
    (hc : ‖g c‖ ≤ Q)
    (hinner : ∀ z : ℂ, ‖z - c‖ = h / 8 → ‖g z‖ ≤ m) :
    ∀ z ∈ closedBall c (h / 4),
      ‖g z‖ ≤ m ^ (1 / 2 : ℝ) * (4 * A + 5 * Q) ^ (1 / 2 : ℝ) := by
  apply norm_le_on_closedBall_of_sphere_of_differentiableOn (by positivity)
    (by linarith : h / 4 < 3 * h / 4) hg
  intro z hz
  exact norm_le_titchmarsh_circle_step hA hh hg hre hc hinner (by simpa using hz)

end GaloisForLFunctions.HTGeometry
