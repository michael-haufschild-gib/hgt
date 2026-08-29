import GaloisForLFunctions.HTGeometry.LogDerivCountingBound
import GaloisForLFunctions.HTGeometry.PoleMassRatioRadius

/-!
# The logarithmic-derivative estimate at an arbitrary comparison radius

`circleAverage_posLog_logDeriv_le_counting` compares the divisor weight with the counting functions
at `2R`.  For the Borel argument the comparison radius must be close to `R`, because the
characteristic of an entire function at twice the radius is not controlled by its value at the
radius.  The general-ratio counting bridge supplies exactly that.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn

/-- **Nevanlinna's logarithmic-derivative estimate against the counting functions, at an arbitrary
comparison radius.**  The counting functions are evaluated at any `R' > R`, at the cost of the factor
`log(R'/R)⁻¹`.  Taking `R'` close to `R` is what the Borel argument needs, since the characteristic
at twice the radius is not controlled by its value at the radius. -/
theorem circleAverage_posLog_logDeriv_le_counting_ratio {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R R' : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 1 ≤ R) (hRR' : R < R') {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hbd : ∀ u ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = 0) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
        Real.posLog ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖
      ≤ (1 / α) * Real.log (1 +
          ((2 * π)⁻¹ * (((Real.log (R' / R))⁻¹
              * (logCounting f ⊤ R' + logCounting f 0 R'))
            * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α)))
          + (2 * R / (R - r) ^ 2
              * (2 * characteristic f ⊤ R
                + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)) ^ α)) := by
  have hfm : Meromorphic f := fun z => ((hf.analyticAt z).meromorphicAt)
  have hbase := circleAverage_posLog_logDeriv_le_of_entire hα0 hα1 hr hrR hR hf hf0 hbd
  refine le_trans hbase ?_
  -- the divisor weight is at most the counting bound
  have hRpos : (0 : ℝ) < R := by linarith
  have hlogR : (0 : ℝ) < Real.log (R' / R) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ hRpos]
    linarith
  have hmass := divisorMass_rpow_le (f := f) (R := R) hα0 hα1.le
  have hcount := log_ratio_mul_divisorMass_le_logCounting hfm hR hRR'
  have hW : (∑ᶠ u : ℂ, (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
      ≤ (Real.log (R' / R))⁻¹ * (logCounting f ⊤ R' + logCounting f 0 R') := by
    rw [le_inv_mul_iff₀ hlogR]
    have hscaled := mul_le_mul_of_nonneg_left hmass hlogR.le
    linarith [hscaled, hcount]
  have hcoef : (0 : ℝ) ≤ r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α) := by
    have h1 : (0 : ℝ) ≤ r ^ (-α) * sinNegPowerConst α := by
      have := sinNegPowerConst_nonneg α
      positivity
    have h2 : (0 : ℝ) ≤ 2 * π * (R - r) ^ (-α) := by positivity
    linarith
  have hstep : (∑ᶠ u : ℂ, (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
      * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α))
      ≤ ((Real.log (R' / R))⁻¹ * (logCounting f ⊤ R' + logCounting f 0 R'))
      * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α)) :=
    mul_le_mul_of_nonneg_right hW hcoef
  have hπ : (0 : ℝ) ≤ (2 * π)⁻¹ := by positivity
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Real.log_le_log ?_ ?_
  · have hweight : (0 : ℝ) ≤ (∑ᶠ u : ℂ,
        (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α) := by
      refine finsum_nonneg fun u => ?_
      positivity
    have hBbase : (0 : ℝ) ≤ 2 * R / (R - r) ^ 2
        * (2 * characteristic f ⊤ R
          + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) := by
      have hchar : 0 ≤ characteristic f ⊤ R := by
        have h1 : (0 : ℝ) ≤ proximity f ⊤ R := proximity_nonneg R
        have h2 : (0 : ℝ) ≤ logCounting f ⊤ R := logCounting_nonneg hR
        have hsplit : characteristic f ⊤ R = proximity f ⊤ R + logCounting f ⊤ R := rfl
        linarith
      have hmax : 0 ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| :=
        le_trans (abs_nonneg _) (le_max_left _ _)
      have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
      have hcoef2 : (0 : ℝ) ≤ 2 * R / (R - r) ^ 2 := by positivity
      exact mul_nonneg hcoef2 (by linarith)
    have hB : (0 : ℝ) ≤ (2 * R / (R - r) ^ 2
        * (2 * characteristic f ⊤ R
          + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)) ^ α :=
      Real.rpow_nonneg hBbase α
    have hprod : (0 : ℝ) ≤ (2 * π)⁻¹ * ((∑ᶠ u : ℂ,
        (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
        * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α))) :=
      mul_nonneg hπ (mul_nonneg hweight hcoef)
    linarith
  · have := mul_le_mul_of_nonneg_left hstep hπ
    linarith


end GaloisForLFunctions.HTGeometry
