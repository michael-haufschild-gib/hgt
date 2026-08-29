import GaloisForLFunctions.HTGeometry.LogDerivProximityBound
import GaloisForLFunctions.HTGeometry.DivisorMassCounting

/-!
# The logarithmic-derivative estimate against the counting functions

Replacing the divisor weight of the `α`-power logarithmic-derivative estimate by the counting
functions, through the two bridges

```text
∑_u |n_u|^α ≤ ∑_u |n_u|,      log 2 · ∑_u |n_u| ≤ N(2R, f) + N(2R, 1/f).
```

What comes out is Nevanlinna's estimate in the shape the second main theorem consumes: the proximity
of a logarithmic derivative costs only the logarithm of a counting function, of `1/(R − r)`, and of
the characteristic.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real ValueDistribution MeromorphicOn

/-- **Nevanlinna's logarithmic-derivative estimate against the counting functions.** -/
theorem circleAverage_posLog_logDeriv_le_counting {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 1 ≤ R) {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hf0 : ∀ z, meromorphicOrderAt f z ≠ ⊤)
    (hbd : ∀ u ∈ sphere (0 : ℂ) |R|,
      MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u = 0) :
    (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
        Real.posLog ‖logDeriv f ((r : ℂ) * Complex.exp (θ * Complex.I))‖
      ≤ (1 / α) * Real.log (1 +
          ((2 * π)⁻¹ * (((Real.log 2)⁻¹
              * (logCounting f ⊤ (2 * R) + logCounting f 0 (2 * R)))
            * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α)))
          + (2 * R / (R - r) ^ 2
              * (2 * characteristic f ⊤ R
                + max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖|)) ^ α)) := by
  have hfm : Meromorphic f := fun z => ((hf.analyticAt z).meromorphicAt)
  have hbase := circleAverage_posLog_logDeriv_le_of_entire hα0 hα1 hr hrR hR hf hf0 hbd
  refine le_trans hbase ?_
  -- the divisor weight is at most the counting bound
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hmass := divisorMass_rpow_le (f := f) (R := R) hα0 hα1.le
  have hcount := log_two_mul_divisorMass_le_logCounting hfm hR
  have hW : (∑ᶠ u : ℂ, (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
      ≤ (Real.log 2)⁻¹ * (logCounting f ⊤ (2 * R) + logCounting f 0 (2 * R)) := by
    rw [le_inv_mul_iff₀ hlog2]
    have hscaled := mul_le_mul_of_nonneg_left hmass hlog2.le
    linarith [hscaled, hcount]
  have hcoef : (0 : ℝ) ≤ r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α) := by
    have h1 : (0 : ℝ) ≤ r ^ (-α) * sinNegPowerConst α := by
      have := sinNegPowerConst_nonneg α
      positivity
    have h2 : (0 : ℝ) ≤ 2 * π * (R - r) ^ (-α) := by positivity
    linarith
  have hstep : (∑ᶠ u : ℂ, (|(MeromorphicOn.divisor f (closedBall (0 : ℂ) |R|) u : ℤ)| : ℝ) ^ α)
      * (r ^ (-α) * sinNegPowerConst α + 2 * π * (R - r) ^ (-α))
      ≤ ((Real.log 2)⁻¹ * (logCounting f ⊤ (2 * R) + logCounting f 0 (2 * R)))
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
