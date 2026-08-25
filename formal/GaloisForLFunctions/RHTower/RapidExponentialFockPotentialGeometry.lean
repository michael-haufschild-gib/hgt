import Mathlib

/-!
# Rapid exponential Fock radial geometry

This file isolates the exact large-radius geometry of the rapid Fock potential
`phi_a(r) = exp (2 a r)`.  The global carrier may be smoothed near the origin; every statement
below is on the positive radial tail where the card uses this literal formula.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Literal exponential radial potential on the unsmoothed positive tail. -/
def rapidExponentialFockPotential (a r : ℝ) : ℝ :=
  Real.exp (2 * a * r)

/-- Exact radial slope of `exp (2 a r)`. -/
def rapidExponentialFockRadialSlope (a r : ℝ) : ℝ :=
  2 * a * Real.exp (2 * a * r)

/-- Exact radial curvature of `exp (2 a r)`. -/
def rapidExponentialFockRadialCurvature (a r : ℝ) : ℝ :=
  4 * a ^ 2 * Real.exp (2 * a * r)

/-- Planar radial Laplacian density `phi''(r) + phi'(r) / r` on `r > 0`. -/
def rapidExponentialFockLaplacianDensity (a r : ℝ) : ℝ :=
  (4 * a ^ 2 + 2 * a / r) * Real.exp (2 * a * r)

/-- Exact reciprocal-square-root adapted radius on the exponential tail. -/
def rapidExponentialFockAdaptedRadius (a r : ℝ) : ℝ :=
  (Real.sqrt (rapidExponentialFockLaplacianDensity a r))⁻¹

theorem hasDerivAt_rapidExponentialFockPotential (a r : ℝ) :
    HasDerivAt (rapidExponentialFockPotential a)
      (rapidExponentialFockRadialSlope a r) r := by
  unfold rapidExponentialFockPotential rapidExponentialFockRadialSlope
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id r).const_mul (2 * a)).exp)

theorem hasDerivAt_rapidExponentialFockRadialSlope (a r : ℝ) :
    HasDerivAt (rapidExponentialFockRadialSlope a)
      (rapidExponentialFockRadialCurvature a r) r := by
  unfold rapidExponentialFockRadialSlope rapidExponentialFockRadialCurvature
  have hin : HasDerivAt (fun x : ℝ => Real.exp (2 * a * x))
      (2 * a * Real.exp (2 * a * r)) r := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id r).const_mul (2 * a)).exp)
  exact (hin.const_mul (2 * a)).congr_deriv (by ring)

/-- The algebraic radial-Laplacian identity used by rapid Fock geometry. -/
theorem rapidExponentialFockLaplacianDensity_eq
    (a r : ℝ) (hr : r ≠ 0) :
    rapidExponentialFockRadialCurvature a r +
        rapidExponentialFockRadialSlope a r / r =
      rapidExponentialFockLaplacianDensity a r := by
  unfold rapidExponentialFockRadialCurvature rapidExponentialFockRadialSlope
    rapidExponentialFockLaplacianDensity
  field_simp [hr]

theorem rapidExponentialFockLaplacianDensity_pos
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 < rapidExponentialFockLaplacianDensity a r := by
  unfold rapidExponentialFockLaplacianDensity
  positivity

/-- Lower tail comparison with the exact exponential density scale. -/
theorem rapidExponentialFockLaplacianDensity_lower
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    4 * a ^ 2 * Real.exp (2 * a * r) ≤
      rapidExponentialFockLaplacianDensity a r := by
  unfold rapidExponentialFockLaplacianDensity
  have hnonneg : 0 ≤ 2 * a / r := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- Uniform upper tail comparison, valid from radius one onward. -/
theorem rapidExponentialFockLaplacianDensity_upper
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    rapidExponentialFockLaplacianDensity a r ≤
      (4 * a ^ 2 + 2 * a) * Real.exp (2 * a * r) := by
  unfold rapidExponentialFockLaplacianDensity
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdiv : 2 * a / r ≤ 2 * a := by
    rw [div_le_iff₀ hr0]
    nlinarith
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

theorem rapidExponentialFockAdaptedRadius_pos
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    0 < rapidExponentialFockAdaptedRadius a r := by
  unfold rapidExponentialFockAdaptedRadius
  exact inv_pos.mpr
    (Real.sqrt_pos.2 (rapidExponentialFockLaplacianDensity_pos ha hr))

private theorem sqrt_exp_two_mul (a r : ℝ) :
    Real.sqrt (Real.exp (2 * a * r)) = Real.exp (a * r) := by
  have hsq : Real.exp (a * r) ^ 2 = Real.exp (2 * a * r) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rw [← hsq, Real.sqrt_sq (Real.exp_pos _).le]

/-- Adapted radius is at most `(2a)⁻¹ exp (-ar)` on the positive tail. -/
theorem rapidExponentialFockAdaptedRadius_upper
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    rapidExponentialFockAdaptedRadius a r ≤
      (2 * a)⁻¹ * Real.exp (-a * r) := by
  have hdensityPos := rapidExponentialFockLaplacianDensity_pos ha hr
  have hlowerPos : 0 < 4 * a ^ 2 * Real.exp (2 * a * r) := by positivity
  unfold rapidExponentialFockAdaptedRadius
  have hsqrtExact :
      Real.sqrt (4 * a ^ 2 * Real.exp (2 * a * r)) =
        2 * a * Real.exp (a * r) := by
    rw [show 4 * a ^ 2 * Real.exp (2 * a * r) =
        (2 * a) ^ 2 * Real.exp (2 * a * r) by ring,
      Real.sqrt_mul (sq_nonneg (2 * a)), Real.sqrt_sq_eq_abs,
      abs_of_pos (by positivity), sqrt_exp_two_mul]
  have hscale :
      (2 * a)⁻¹ * Real.exp (-a * r) =
        (Real.sqrt (4 * a ^ 2 * Real.exp (2 * a * r)))⁻¹ := by
    rw [hsqrtExact, show -a * r = -(a * r) by ring, Real.exp_neg]
    field_simp
  rw [hscale, inv_le_inv₀ (Real.sqrt_pos.2 hdensityPos) (Real.sqrt_pos.2 hlowerPos)]
  exact Real.sqrt_le_sqrt (rapidExponentialFockLaplacianDensity_lower ha hr)

/-- Adapted radius is at least the corresponding uniform exponential lower scale from radius one. -/
theorem rapidExponentialFockAdaptedRadius_lower
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    (Real.sqrt (4 * a ^ 2 + 2 * a))⁻¹ * Real.exp (-a * r) ≤
      rapidExponentialFockAdaptedRadius a r := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hdensityPos := rapidExponentialFockLaplacianDensity_pos ha hr0
  have hcoeffPos : 0 < 4 * a ^ 2 + 2 * a := by positivity
  have hupperPos : 0 < (4 * a ^ 2 + 2 * a) * Real.exp (2 * a * r) := by positivity
  unfold rapidExponentialFockAdaptedRadius
  have hsqrtExact :
      Real.sqrt ((4 * a ^ 2 + 2 * a) * Real.exp (2 * a * r)) =
        Real.sqrt (4 * a ^ 2 + 2 * a) * Real.exp (a * r) := by
    rw [Real.sqrt_mul hcoeffPos.le, sqrt_exp_two_mul]
  have hscale :
      (Real.sqrt (4 * a ^ 2 + 2 * a))⁻¹ * Real.exp (-a * r) =
        (Real.sqrt ((4 * a ^ 2 + 2 * a) * Real.exp (2 * a * r)))⁻¹ := by
    rw [hsqrtExact, show -a * r = -(a * r) by ring, Real.exp_neg]
    field_simp
  rw [hscale, inv_le_inv₀ (Real.sqrt_pos.2 hupperPos) (Real.sqrt_pos.2 hdensityPos)]
  exact Real.sqrt_le_sqrt (rapidExponentialFockLaplacianDensity_upper ha hr)

/-- The rapid adapted radius vanishes along the positive real tail. -/
theorem tendsto_rapidExponentialFockAdaptedRadius_atTop
    {a : ℝ} (ha : 0 < a) :
    Tendsto (rapidExponentialFockAdaptedRadius a) atTop (nhds 0) := by
  have hupper : ∀ᶠ r in atTop,
      rapidExponentialFockAdaptedRadius a r ≤
        (2 * a)⁻¹ * Real.exp (-a * r) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact rapidExponentialFockAdaptedRadius_upper ha hr
  have hnonneg : ∀ᶠ r in atTop, 0 ≤ rapidExponentialFockAdaptedRadius a r := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact (rapidExponentialFockAdaptedRadius_pos ha hr).le
  refine squeeze_zero' hnonneg hupper ?_
  have hpos : Tendsto (fun r : ℝ => a * r) atTop atTop := by
    simpa using tendsto_id.const_mul_atTop ha
  have hlin : Tendsto (fun r : ℝ => r * (-a)) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp hpos using 1
    funext r
    simp [Function.comp_apply, mul_comm]
  have hdecay : Tendsto (fun r : ℝ => Real.exp (-a * r)) atTop (nhds 0) := by
    convert Real.tendsto_exp_atBot.comp hlin using 1
    funext r
    congr 1
    ring
  have hc : Tendsto (fun _ : ℝ => (2 * a)⁻¹) atTop (nhds (2 * a)⁻¹) :=
    tendsto_const_nhds
  simpa using hc.mul hdecay

end

end RHTower
