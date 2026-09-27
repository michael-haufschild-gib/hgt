import GaloisForLFunctions.RHTower.XiGaussianThreeHalvesTrace
import GaloisForLFunctions.HTGeometry.GaussianParabolicSlopeBounds

/-!
# A cubic degree/time region from full-polynomial fractional phase control

Both pointwise error endpoints are balanced at height (d+3)²/u. Their
three-halves sum costs u√u after normalization, independently of degree.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section
namespace RHTower

/-- Spatial scale corresponding to a cubic heat-time degree penalty. -/
def xiGaussianCubicScale (d : ℕ) (τ : ℝ) : {r : ℝ // 0 < r} :=
  ⟨Real.exp τ / (((d : ℝ) + 3) * Real.sqrt ((d : ℝ) + 3)), by positivity⟩

/-- Interpolation height balancing the unweighted and coordinate-square endpoints. -/
def xiGaussianCubicInterpolationScale (d : ℕ) (τ : ℝ) : {L : ℝ // 0 < L} :=
  ⟨((d : ℝ) + 3) ^ 2 / Real.exp τ, by positivity⟩

/-- The degree-independent fractional phase loss is of order u√u near zero. -/
def xiGaussianCubicPhaseEnvelope (u : ℝ) : ℝ :=
  xiHeatThreeHalvesMass / 2 * u * Real.sqrt u * (1 + 2 * Real.sqrt (4 * π)) *
    (normalizedGaussianVerticalSlope (u / 2) ^ 2 +
      2 * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2)

theorem xiGaussianCubicScale_sqrtDegree_le (d : ℕ) (τ : ℝ) :
    (xiGaussianCubicScale d τ : ℝ) * Real.sqrt ((d : ℝ) + 3) ≤ Real.exp τ := by
  have hD : 1 ≤ (d : ℝ) + 3 := by linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hv : 0 < Real.sqrt ((d : ℝ) + 3) := Real.sqrt_pos.mpr (by positivity)
  change Real.exp τ / (((d : ℝ) + 3) * Real.sqrt ((d : ℝ) + 3)) *
    Real.sqrt ((d : ℝ) + 3) ≤ _
  calc
    _ = Real.exp τ / ((d : ℝ) + 3) := by field_simp
    _ ≤ Real.exp τ := div_le_self (Real.exp_pos τ).le hD

/-- The new full-divisor debt has a single coefficient- and degree-uniform ceiling. -/
theorem xiGaussianThreeHalvesPhaseBudget_cubicScale_le (d : ℕ) (τ : ℝ) :
    (xiGaussianCubicScale d τ : ℝ) *
      xiGaussianThreeHalvesPhaseBudget d (xiGaussianCubicScale d τ)
        (xiGaussianCubicInterpolationScale d τ) ≤
      xiGaussianCubicPhaseEnvelope (Real.exp τ) := by
  let u := Real.exp τ
  let D := (d : ℝ) + 3
  let v := Real.sqrt D
  let r := xiGaussianCubicScale d τ
  let L := xiGaussianCubicInterpolationScale d τ
  let ε : ℝ≥0 := ⟨u / 2, by dsimp [u]; positivity⟩
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  let S : ℝ≥0 := ⟨(ε : ℝ) / v, by dsimp [v, D]; positivity⟩
  let A := 1 + 2 * Real.sqrt (4 * π)
  have hD : 0 < D := by dsimp [D]; positivity
  have hv : 0 < v := Real.sqrt_pos.mpr hD
  have hv2 : v ^ 2 = D := Real.sq_sqrt hD.le
  have hu : 0 < u := Real.exp_pos τ
  have hrv := xiGaussianCubicScale_sqrtDegree_le d τ
  have hRS : R ≤ S := by
    change (r : ℝ) / 2 ≤ (u / 2) / v
    rw [le_div_iff₀ hv]
    change (r : ℝ) * v ≤ u at hrv
    linarith only [hrv]
  have hp := mul_le_mul_of_nonneg_left (gaussianVerticalDefectSlope_radius_mono d hRS)
    (gaussianStripSamplingFactor_nonneg d 1)
  have hp2 := (pow_le_pow_left₀ (mul_nonneg (gaussianStripSamplingFactor_nonneg d 1)
    (gaussianVerticalDefectSlope_nonneg d R)) hp 2).trans
      (gaussianPointVerticalSlope_sqrtDegree_sq_le d ε)
  have hc2 := (pow_le_pow_left₀ (gaussianCoordinateVerticalSlope_nonneg d R)
    (gaussianCoordinateVerticalSlope_radius_mono d hRS) 2).trans
      (gaussianCoordinateVerticalSlope_sqrtDegree_sq_le d ε)
  have hbalance : (r : ℝ) ^ 2 * (L : ℝ) ^ 2 = D := by
    change (u / (D * v)) ^ 2 * (D ^ 2 / u) ^ 2 = D
    field_simp
    nlinarith only [hv2]
  have hsL : Real.sqrt (L : ℝ) = D / Real.sqrt u := by
    change Real.sqrt (D ^ 2 / u) = _
    rw [Real.sqrt_div (sq_nonneg D), Real.sqrt_sq_eq_abs, abs_of_pos hD]
  have hcancel : (r : ℝ) * gaussianDegreeWeight d / Real.sqrt (L : ℝ) =
      u * Real.sqrt u := by
    rw [hsL]
    change (u / (D * v)) * (D ^ 2 * v) / (D / Real.sqrt u) = _
    field_simp
  have hinner := add_le_add (mul_le_mul_of_nonneg_left hp2 hD.le)
    (mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ 2))
  have hinner' :
      (r : ℝ) ^ 2 * (L : ℝ) ^ 2 *
          (gaussianStripSamplingFactor d 1 * gaussianVerticalDefectSlope d ((r : ℝ) / 2)) ^ 2 +
        2 * gaussianCoordinateVerticalSlope d ((r : ℝ) / 2) ^ 2 ≤
      A * gaussianDegreeWeight d *
        (normalizedGaussianVerticalSlope (u / 2) ^ 2 +
          2 * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2) := by
    rw [hbalance]
    change D * (gaussianStripSamplingFactor d 1 * gaussianVerticalDefectSlope d ((r : ℝ) / 2)) ^ 2 +
      2 * gaussianCoordinateVerticalSlope d ((r : ℝ) / 2) ^ 2 ≤
      D * (A * (D * v) * normalizedGaussianVerticalSlope (u / 2) ^ 2) +
      2 * (A * (D ^ 2 * v) * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2) at hinner
    refine hinner.trans_eq ?_
    change _ = A * (D ^ 2 * v) * _
    ring
  have hb := mul_le_mul_of_nonneg_left hinner'
    (show 0 ≤ (r : ℝ) * (xiHeatThreeHalvesMass / (2 * Real.sqrt (L : ℝ))) from
      mul_nonneg r.property.le (div_nonneg xiHeatThreeHalvesMass_nonneg (by positivity)))
  unfold xiGaussianThreeHalvesPhaseBudget xiGaussianCubicPhaseEnvelope
  change (r : ℝ) * (_ * _) ≤ _
  calc
    _ ≤ ((r : ℝ) * (xiHeatThreeHalvesMass / (2 * Real.sqrt (L : ℝ)))) *
        (A * gaussianDegreeWeight d *
          (normalizedGaussianVerticalSlope (u / 2) ^ 2 +
            2 * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2)) := by
      simpa only [mul_assoc] using hb
    _ = xiHeatThreeHalvesMass / 2 *
        ((r : ℝ) * gaussianDegreeWeight d / Real.sqrt (L : ℝ)) * A *
          (normalizedGaussianVerticalSlope (u / 2) ^ 2 +
            2 * gaussianNormalizedSlopeEnvelope (u / 2) ^ 2) := by ring
    _ = _ := by rw [hcancel]; dsimp only [A, u]; ring

/-- Uniform total loss, retaining both energy-floor errors and the full phase budget. -/
def xiGaussianCubicTraceEnvelope (C h u : ℝ) : ℝ :=
  C * u + (1 + 2 * h * Real.sqrt (4 * π) * u) * parabolicGaussianDefect (u / 2) ^ 2 +
    h * xiGaussianCubicPhaseEnvelope u

/-- Every finite polynomial degree shares this one total-loss envelope. -/
theorem xiGaussianThreeHalvesTraceLoss_cubicScale_le (C h : ℝ≥0) (d : ℕ) (τ : ℝ) :
    xiGaussianThreeHalvesTraceLoss C h d (xiGaussianCubicScale d τ)
        (xiGaussianCubicInterpolationScale d τ) ≤
      xiGaussianCubicTraceEnvelope C h (Real.exp τ) := by
  let u := Real.exp τ
  let r := xiGaussianCubicScale d τ
  let v := Real.sqrt ((d : ℝ) + 3)
  let ε : ℝ≥0 := ⟨u / 2, by dsimp [u]; positivity⟩
  let R : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  let S : ℝ≥0 := ⟨(ε : ℝ) / v, by dsimp [v]; positivity⟩
  have hr := r.property
  have hv : 0 < v := Real.sqrt_pos.mpr (by positivity)
  have hrv := xiGaussianCubicScale_sqrtDegree_le d τ
  have hRS : R ≤ S := by
    change (r : ℝ) / 2 ≤ (u / 2) / v
    rw [le_div_iff₀ hv]
    change (r : ℝ) * v ≤ u at hrv
    linarith only [hrv]
  have hE := (verticalPolynomialGaussianDefect_radius_mono d hRS).trans
    (verticalPolynomialGaussianDefect_sqrtDegree_le d ε)
  have hsqrt₁ : Real.sqrt ((d : ℝ) + 1) ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hsqrt₂ : Real.sqrt ((d : ℝ) + 2) ≤ v := Real.sqrt_le_sqrt (by linarith)
  have hr₁ := (mul_le_mul_of_nonneg_left hsqrt₁ hr.le).trans hrv
  have hr₂ := (mul_le_mul_of_nonneg_left hsqrt₂ hr.le).trans hrv
  have hfirst := mul_le_mul_of_nonneg_left hr₁ C.coe_nonneg
  have hfactor : 1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * π * ((d : ℝ) + 2)) ≤
      1 + 2 * (h : ℝ) * Real.sqrt (4 * π) * u := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 4 * π)]
    have hs := mul_le_mul_of_nonneg_left hr₂
      (show 0 ≤ 2 * (h : ℝ) * Real.sqrt (4 * π) by positivity)
    nlinarith only [hs]
  have herror := mul_le_mul hfactor
    (pow_le_pow_left₀ (verticalPolynomialGaussianDefect_nonneg d R) hE 2)
    (sq_nonneg _) (by positivity)
  have hphase := mul_le_mul_of_nonneg_left
    (xiGaussianThreeHalvesPhaseBudget_cubicScale_le d τ) h.coe_nonneg
  unfold xiGaussianThreeHalvesTraceLoss xiGaussianCubicTraceEnvelope
  change _ ≤ C * u + _ + _
  change (1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * π * ((d : ℝ) + 2))) *
    verticalPolynomialGaussianDefect d ((r : ℝ) / 2) ^ 2 ≤
    (1 + 2 * (h : ℝ) * Real.sqrt (4 * π) * u) * parabolicGaussianDefect (u / 2) ^ 2 at herror
  dsimp only [u, r] at hfirst herror hphase ⊢
  nlinarith only [hfirst, herror, hphase]

/-- The single degree-uniform envelope vanishes at zero spatial scale. -/
theorem xiGaussianCubicTraceEnvelope_tendsto_zero (C h : ℝ) :
    Tendsto (xiGaussianCubicTraceEnvelope C h) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (xiGaussianCubicTraceEnvelope C h) := by
    unfold xiGaussianCubicTraceEnvelope xiGaussianCubicPhaseEnvelope
      gaussianNormalizedSlopeEnvelope normalizedGaussianVerticalSlope parabolicGaussianDefect
    fun_prop
  simpa [xiGaussianCubicTraceEnvelope, xiGaussianCubicPhaseEnvelope, parabolicGaussianDefect]
    using hc.tendsto 0

/-- One cutoff controls all coefficients and all finite degree ceilings. -/
theorem eventually_forall_xiGaussianThreeHalvesTraceLoss_cubicScale_lt (C h : ℝ≥0) :
    ∀ᶠ τ : ℝ in atBot, ∀ d : ℕ,
      xiGaussianThreeHalvesTraceLoss C h d (xiGaussianCubicScale d τ)
        (xiGaussianCubicInterpolationScale d τ) < 1 / 8 := by
  have he := ((xiGaussianCubicTraceEnvelope_tendsto_zero C h).comp
    Real.tendsto_exp_atBot).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < 1 / 8))
  filter_upwards [he] with τ hτ d
  exact (xiGaussianThreeHalvesTraceLoss_cubicScale_le C h d τ).trans_lt hτ

end RHTower
