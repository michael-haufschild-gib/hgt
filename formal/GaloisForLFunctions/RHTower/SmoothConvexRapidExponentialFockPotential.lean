import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SmoothConvexTransition
import GaloisForLFunctions.HTGeometry.CompactPrimitive
import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry

/-!
# A smooth convex rapid exponential Fock potential

A smooth monotone step is integrated to a convex radial coordinate that is constant near the
origin and exactly the identity from radius one onward.  Exponentiating this coordinate gives a
genuinely `C∞` radial function on the complex plane, equal to `exp (2 a |z|)` on the full tail.
Its radial Laplacian is nonnegative and agrees exactly with the rapid exponential density past the
transition.  Flatness near zero removes the norm cusp without altering any tail geometry.
-/

open Filter Topology

namespace RHTower

noncomputable section

private abbrev rapidSmoothCutScale : ℝ := 1 / 2

/-- Smooth nondecreasing step from zero on `(-∞,1/2]` to one on `[1,∞)`. -/
def smoothConvexRapidFockStep (r : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutProfile rapidSmoothCutScale r

/-- Smooth convex radial coordinate, normalized to equal `r` from radius one onward. -/
def smoothConvexRapidFockCoordinate (r : ℝ) : ℝ :=
  GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutPrimitive rapidSmoothCutScale r -
    (GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutPrimitive rapidSmoothCutScale 1 - 1)

/-- Globally smooth flat-head potential equal to `exp (2 a r)` for `r ≥ 1`. -/
def smoothConvexRapidExponentialFockPotential (a r : ℝ) : ℝ :=
  Real.exp (2 * a * smoothConvexRapidFockCoordinate r)

theorem contDiff_top_smoothConvexRapidFockStep :
    ContDiff ℝ (⊤ : ℕ∞) smoothConvexRapidFockStep := by
  exact GaloisForLFunctions.HTGeometry.DaiYoshikawa.contDiff_cutProfile
    rapidSmoothCutScale ⊤

theorem contDiff_top_smoothConvexRapidFockCoordinate :
    ContDiff ℝ (⊤ : ℕ∞) smoothConvexRapidFockCoordinate := by
  unfold smoothConvexRapidFockCoordinate
  exact (GaloisForLFunctions.HTGeometry.contDiff_primitive
    (GaloisForLFunctions.HTGeometry.DaiYoshikawa.contDiff_cutProfile
      rapidSmoothCutScale ⊤) 0).sub contDiff_const

theorem contDiff_top_smoothConvexRapidExponentialFockPotential (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothConvexRapidExponentialFockPotential a) := by
  unfold smoothConvexRapidExponentialFockPotential
  exact (contDiff_const.mul contDiff_id |>.comp
    contDiff_top_smoothConvexRapidFockCoordinate).exp

theorem smoothConvexRapidFockStep_nonneg (r : ℝ) :
    0 ≤ smoothConvexRapidFockStep r := by
  exact GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutProfile_nonneg _ _

theorem smoothConvexRapidFockStep_le_one (r : ℝ) :
    smoothConvexRapidFockStep r ≤ 1 := by
  exact GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutProfile_le_one _ _

theorem monotone_smoothConvexRapidFockStep : Monotone smoothConvexRapidFockStep := by
  exact GaloisForLFunctions.HTGeometry.DaiYoshikawa.monotone_cutProfile
    (by norm_num : (0 : ℝ) < rapidSmoothCutScale)

theorem deriv_smoothConvexRapidFockStep_nonneg (r : ℝ) :
    0 ≤ deriv smoothConvexRapidFockStep r :=
  monotone_smoothConvexRapidFockStep.deriv_nonneg

theorem smoothConvexRapidFockStep_eq_zero {r : ℝ} (hr : r ≤ 1 / 2) :
    smoothConvexRapidFockStep r = 0 := by
  exact GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutProfile_eq_zero
    (by norm_num : (0 : ℝ) < rapidSmoothCutScale) (by simpa using hr)

theorem smoothConvexRapidFockStep_eq_one {r : ℝ} (hr : 1 ≤ r) :
    smoothConvexRapidFockStep r = 1 := by
  exact GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutProfile_eq_one
    (by norm_num : (0 : ℝ) < rapidSmoothCutScale) (by simpa using hr)

theorem hasDerivAt_smoothConvexRapidFockCoordinate (r : ℝ) :
    HasDerivAt smoothConvexRapidFockCoordinate (smoothConvexRapidFockStep r) r := by
  unfold smoothConvexRapidFockCoordinate smoothConvexRapidFockStep
  simpa using
    (GaloisForLFunctions.HTGeometry.DaiYoshikawa.hasDerivAt_cutPrimitive
      rapidSmoothCutScale r).sub_const

theorem smoothConvexRapidFockCoordinate_eq_tail {r : ℝ} (hr : 1 ≤ r) :
    smoothConvexRapidFockCoordinate r = r := by
  unfold smoothConvexRapidFockCoordinate
  rw [GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutPrimitive_eq_add
    (by norm_num : (0 : ℝ) < rapidSmoothCutScale) (by simpa using hr)]
  ring

theorem smoothConvexRapidFockCoordinate_eq_head
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    smoothConvexRapidFockCoordinate r = smoothConvexRapidFockCoordinate 0 := by
  unfold smoothConvexRapidFockCoordinate
  rw [GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutPrimitive_eq_zero
      (by norm_num : (0 : ℝ) < rapidSmoothCutScale) hr0 (by simpa using hr)]
  simp [GaloisForLFunctions.HTGeometry.DaiYoshikawa.cutPrimitive]

theorem smoothConvexRapidExponentialFockPotential_eq_tail
    {a r : ℝ} (hr : 1 ≤ r) :
    smoothConvexRapidExponentialFockPotential a r = rapidExponentialFockPotential a r := by
  rw [smoothConvexRapidExponentialFockPotential, smoothConvexRapidFockCoordinate_eq_tail hr]
  rfl

theorem smoothConvexRapidExponentialFockPotential_eq_head
    {a r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    smoothConvexRapidExponentialFockPotential a r =
      smoothConvexRapidExponentialFockPotential a 0 := by
  unfold smoothConvexRapidExponentialFockPotential
  rw [smoothConvexRapidFockCoordinate_eq_head hr0 hr]

/-- Smooth radial potential on the complex plane. Flatness near zero removes the norm cusp. -/
def smoothConvexRapidExponentialFockPlanePotential (a : ℝ) (z : ℂ) : ℝ :=
  smoothConvexRapidExponentialFockPotential a ‖z‖

theorem contDiff_top_smoothConvexRapidExponentialFockPlanePotential (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothConvexRapidExponentialFockPlanePotential a) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · subst z
    have hev : smoothConvexRapidExponentialFockPlanePotential a =ᶠ[nhds (0 : ℂ)]
        fun _ => smoothConvexRapidExponentialFockPotential a 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)]
        with w hw
      unfold smoothConvexRapidExponentialFockPlanePotential
      apply smoothConvexRapidExponentialFockPotential_eq_head (norm_nonneg w)
      have hw' : ‖w‖ < 1 / 2 := by
        simpa [Metric.mem_ball, dist_zero_right] using hw
      exact hw'.le
    exact (contDiff_const.contDiffAt).congr_of_eventuallyEq hev
  · unfold smoothConvexRapidExponentialFockPlanePotential
    exact contDiff_top_smoothConvexRapidExponentialFockPotential a |>.contDiffAt.comp z
      (contDiffAt_norm ℂ hz)

theorem hasDerivAt_smoothConvexRapidExponentialFockPotential (a r : ℝ) :
    HasDerivAt (smoothConvexRapidExponentialFockPotential a)
      (2 * a * smoothConvexRapidFockStep r *
        smoothConvexRapidExponentialFockPotential a r) r := by
  unfold smoothConvexRapidExponentialFockPotential
  have hlin := (hasDerivAt_smoothConvexRapidFockCoordinate r).const_mul (2 * a)
  convert hlin.exp using 1 <;> ring

theorem hasDerivAt_smoothConvexRapidFockStep (r : ℝ) :
    HasDerivAt smoothConvexRapidFockStep (deriv smoothConvexRapidFockStep r) r := by
  exact (contDiff_top_smoothConvexRapidFockStep.differentiable
    (by simp)).differentiableAt.hasDerivAt

theorem hasDerivAt_smoothConvexRapidExponentialFockSlope (a r : ℝ) :
    HasDerivAt
      ((fun x => 2 * a * smoothConvexRapidFockStep x) *
        smoothConvexRapidExponentialFockPotential a)
      ((2 * a * deriv smoothConvexRapidFockStep r +
          4 * a ^ 2 * smoothConvexRapidFockStep r ^ 2) *
        smoothConvexRapidExponentialFockPotential a r) r := by
  have hstep := (hasDerivAt_smoothConvexRapidFockStep r).const_mul (2 * a)
  have hpot := hasDerivAt_smoothConvexRapidExponentialFockPotential a r
  exact (hstep.mul hpot).congr_deriv (by ring)

/-- Exact radial Laplacian density of the smooth convex rapid potential away from zero. -/
def smoothConvexRapidExponentialFockLaplacianDensity (a r : ℝ) : ℝ :=
  ((2 * a * deriv smoothConvexRapidFockStep r +
      4 * a ^ 2 * smoothConvexRapidFockStep r ^ 2) +
    (2 * a * smoothConvexRapidFockStep r) / r) *
      smoothConvexRapidExponentialFockPotential a r

theorem smoothConvexRapidExponentialFockLaplacianDensity_nonneg
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 ≤ smoothConvexRapidExponentialFockLaplacianDensity a r := by
  unfold smoothConvexRapidExponentialFockLaplacianDensity
  have hs := smoothConvexRapidFockStep_nonneg r
  have hds := deriv_smoothConvexRapidFockStep_nonneg r
  have h₁ : 0 ≤ 2 * a * deriv smoothConvexRapidFockStep r := by positivity
  have h₂ : 0 ≤ 4 * a ^ 2 * smoothConvexRapidFockStep r ^ 2 := by positivity
  have h₃ : 0 ≤ 2 * a * smoothConvexRapidFockStep r / r := by positivity
  have hp : 0 ≤ smoothConvexRapidExponentialFockPotential a r := by
    unfold smoothConvexRapidExponentialFockPotential
    positivity
  exact mul_nonneg (add_nonneg (add_nonneg h₁ h₂) h₃) hp

theorem smoothConvexRapidExponentialFockLaplacianDensity_eq_tail
    {a r : ℝ} (hr : 1 < r) :
    smoothConvexRapidExponentialFockLaplacianDensity a r =
      rapidExponentialFockLaplacianDensity a r := by
  have hstep : smoothConvexRapidFockStep r = 1 :=
    smoothConvexRapidFockStep_eq_one hr.le
  have hderiv : deriv smoothConvexRapidFockStep r = 0 := by
    have hev : smoothConvexRapidFockStep =ᶠ[nhds r] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with x hx
      exact smoothConvexRapidFockStep_eq_one hx.le
    rw [Filter.EventuallyEq.deriv_eq hev, deriv_const]
  rw [smoothConvexRapidExponentialFockLaplacianDensity,
    hstep, hderiv, smoothConvexRapidExponentialFockPotential_eq_tail hr.le]
  unfold rapidExponentialFockLaplacianDensity rapidExponentialFockPotential
  ring

end

end RHTower
