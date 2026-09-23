import GaloisForLFunctions.RHTower.GammaDampedVerticalBound
import GaloisForLFunctions.HTGeometry.GammaCyclicDensityTail

/-!
# The far field of the damped spectral symbol

Away from the pole window the symbol is controlled by the two vertical-line bounds: the series
itself is `O(log|u|)` and its derivative is `O(log|u|/ε)`, while the first logarithmic moment is
`O(1/ε)`.  Hence

```text
|Im D(σ, u)| ≤ (12/(σ-1)) (log(2|u|) + 6)        (|u| ≥ 3),
```

which is exactly the weight whose square is integrable against the Gamma cyclic density.
-/

namespace RHTower

noncomputable section

/-- **The far-field bound for the spectral symbol.** -/
theorem abs_im_gammaDampedSymbol_le {σ u : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) (hu : 3 ≤ |u|) :
    |(gammaDampedSymbol σ u).im| ≤ 12 / (σ - 1) * (Real.log (2 * |u|) + 6) := by
  have hε : (0 : ℝ) < σ - 1 := by linarith
  have hre : (gammaDampedCriticalLinePoint σ u).re = (σ + 1) / 2 :=
    gammaDampedCriticalLinePoint_re σ u
  have him : (gammaDampedCriticalLinePoint σ u).im = -u := by
    simp [gammaDampedCriticalLinePoint]
  have habs : |(gammaDampedCriticalLinePoint σ u).im| = |u| := by
    rw [him, abs_neg]
  have hupos : (0 : ℝ) < |u| := by linarith
  have hlogu : Real.log |u| ≤ Real.log (2 * |u|) :=
    Real.log_le_log hupos (by linarith)
  have hlognn : (0 : ℝ) ≤ Real.log (2 * |u|) := Real.log_nonneg (by linarith)
  -- the two vertical-line bounds
  have hF : ‖LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖
      ≤ 2 * (Real.log (2 * |u|) + 5) + 1 / 2 := by
    have h := norm_lSeries_gammaDampedCoeff_le (z := gammaDampedCriticalLinePoint σ u)
      (by rw [hre]; linarith) (by rw [hre]; linarith) (by rw [habs]; linarith)
    rw [habs] at h
    linarith
  have hF' : ‖deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u)‖
      ≤ (2 * (Real.log (2 * |u|) + 5) + 1 / 2) / ((σ - 1) / 4) :=
    norm_deriv_lSeries_gammaDampedCoeff_le hσ1 hσ2 hu
  -- assemble
  have hnorm : ‖gammaDampedSymbol σ u‖
      ≤ ‖deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u)‖ +
        squarefreeMobiusLogMoment 1 σ *
          ‖LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖ := by
    rw [gammaDampedSymbol]
    calc ‖-deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u) -
          ((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) *
            LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖
        ≤ ‖-deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u)‖ +
          ‖((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) *
            LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖ := norm_sub_le _ _
      _ = ‖deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u)‖ +
          squarefreeMobiusLogMoment 1 σ *
            ‖LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖ := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm0]
  have hsplit : ‖deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u)‖ +
      squarefreeMobiusLogMoment 1 σ *
        ‖LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖
      ≤ 12 / (σ - 1) * (Real.log (2 * |u|) + 6) := by
    have hFnn : (0 : ℝ) ≤ ‖LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖ :=
      norm_nonneg _
    have hmF : squarefreeMobiusLogMoment 1 σ *
        ‖LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u)‖
        ≤ 2 / (σ - 1) * (2 * (Real.log (2 * |u|) + 5) + 1 / 2) := by
      refine mul_le_mul hm hF hFnn (by positivity)
    have hdiv : (2 * (Real.log (2 * |u|) + 5) + 1 / 2) / ((σ - 1) / 4)
        = 8 / (σ - 1) * (Real.log (2 * |u|) + 5) + 2 / (σ - 1) := by
      field_simp
      ring
    rw [hdiv] at hF'
    have hkey : 8 / (σ - 1) * (Real.log (2 * |u|) + 5) + 2 / (σ - 1) +
        2 / (σ - 1) * (2 * (Real.log (2 * |u|) + 5) + 1 / 2)
        ≤ 12 / (σ - 1) * (Real.log (2 * |u|) + 6) := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, ← sub_nonneg]
      have hexp : 12 * (Real.log (2 * |u|) + 6) / (σ - 1) -
          (8 * (Real.log (2 * |u|) + 5) / (σ - 1) + 2 / (σ - 1) +
            2 * (2 * (Real.log (2 * |u|) + 5) + 1 / 2) / (σ - 1))
          = (9 : ℝ) / (σ - 1) := by
        field_simp
        ring
      rw [hexp]
      positivity
    linarith
  calc |(gammaDampedSymbol σ u).im| ≤ ‖gammaDampedSymbol σ u‖ :=
        Complex.abs_im_le_norm _
    _ ≤ _ := le_trans hnorm hsplit

/-! ### The far-field energy -/

open MeasureTheory

theorem analyticAt_lSeries_gammaDampedCoeff {σ : ℝ} (hσ : 1 < σ) (u : ℝ) :
    AnalyticAt ℂ (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u) := by
  refine LSeries_analyticOnNhd gammaDampedCoeff _ ?_
  refine lt_of_le_of_lt abscissaOfAbsConv_gammaDampedCoeff_le ?_
  rw [show ((1 : EReal)) = ((1 : ℝ) : EReal) from rfl, gammaDampedCriticalLinePoint_re]
  exact_mod_cast (by linarith : (1 : ℝ) < (σ + 1) / 2)

theorem continuous_gammaDampedSymbol {σ : ℝ} (hσ : 1 < σ) :
    Continuous fun u : ℝ => gammaDampedSymbol σ u := by
  have hpath : Continuous fun u : ℝ => gammaDampedCriticalLinePoint σ u := by
    unfold gammaDampedCriticalLinePoint
    fun_prop
  have hF : Continuous fun u : ℝ =>
      LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ u) :=
    continuous_iff_continuousAt.mpr fun u =>
      ((analyticAt_lSeries_gammaDampedCoeff hσ u).continuousAt).comp hpath.continuousAt
  have hF' : Continuous fun u : ℝ =>
      deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ u) :=
    continuous_iff_continuousAt.mpr fun u =>
      (((analyticAt_lSeries_gammaDampedCoeff hσ u).deriv).continuousAt).comp hpath.continuousAt
  unfold gammaDampedSymbol
  exact hF'.neg.sub (continuous_const.mul hF)

/-- The far-field weight in the density variable. -/
theorem abs_im_gammaDampedSymbol_scaled_le {σ x : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) (hx : 3 ≤ |x|) :
    |(gammaDampedSymbol σ (2 * Real.pi * x)).im|
      ≤ 12 / (σ - 1) * (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  have habs : |2 * Real.pi * x| = 2 * Real.pi * |x| := by
    rw [abs_mul, abs_of_pos hπ]
  have hu : 3 ≤ |2 * Real.pi * x| := by
    rw [habs]
    have h2π : (2 : ℝ) ≤ 2 * Real.pi := by
      have := Real.pi_gt_three
      linarith
    nlinarith
  have hlog : Real.log (2 * |2 * Real.pi * x|)
      = Real.log (2 * |x|) + Real.log (2 * Real.pi) := by
    rw [habs, show 2 * (2 * Real.pi * |x|) = (2 * Real.pi) * (2 * |x|) by ring,
      Real.log_mul (ne_of_gt hπ) (by positivity)]
    ring
  have h := abs_im_gammaDampedSymbol_le (u := 2 * Real.pi * x) hσ1 hσ2 hm0 hm hu
  rw [hlog] at h
  calc |(gammaDampedSymbol σ (2 * Real.pi * x)).im|
      ≤ 12 / (σ - 1) * (Real.log (2 * |x|) + Real.log (2 * Real.pi) + 6) := h
    _ = 12 / (σ - 1) * (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) := by ring

/-- The far-field energy integrand is integrable. -/
theorem integrableOn_farEnergy {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) :
    IntegrableOn (fun x : ℝ =>
      ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ (2 : ℕ) * HTGeometry.gammaCyclicDensity x)
      {x : ℝ | 3 ≤ |x|} := by
  have hmeas : MeasurableSet {x : ℝ | 3 ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have htail := HTGeometry.integrableOn_log_sq_mul_gammaCyclicDensity
    (6 + Real.log (2 * Real.pi))
  refine Integrable.mono' (htail.const_mul ((12 / (σ - 1)) ^ (2 : ℕ))) ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    refine Measurable.mul ?_ HTGeometry.continuous_gammaCyclicDensity.measurable
    have hc : Continuous fun x : ℝ => (gammaDampedSymbol σ (2 * Real.pi * x)).im :=
      Complex.continuous_im.comp ((continuous_gammaDampedSymbol hσ1).comp (by fun_prop))
    exact (hc.measurable).pow measurable_const
  · filter_upwards [ae_restrict_mem hmeas] with x hx
    have hx3 : 3 ≤ |x| := hx
    have hpt := abs_im_gammaDampedSymbol_scaled_le hσ1 hσ2 hm0 hm hx3
    have hρ : (0 : ℝ) ≤ HTGeometry.gammaCyclicDensity x := HTGeometry.gammaCyclicDensity_nonneg x
    have hsq : ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ (2 : ℕ)
        ≤ (12 / (σ - 1)) ^ (2 : ℕ) * (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) ^ (2 : ℕ) := by
      have hnn : (0 : ℝ) ≤ 12 / (σ - 1) * (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) :=
        le_trans (abs_nonneg _) hpt
      have hsq' := mul_self_le_mul_self (abs_nonneg _) hpt
      rw [← sq_abs, ← mul_pow]
      nlinarith [hsq', sq_abs ((gammaDampedSymbol σ (2 * Real.pi * x)).im)]
    have hnn : (0 : ℝ) ≤ ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ (2 : ℕ) *
        HTGeometry.gammaCyclicDensity x := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [hsq, hρ]

/-- **The far-field energy is `O(1/(σ-1)²)`.** -/
theorem gammaDampedFarEnergy_le {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (hm0 : 0 ≤ squarefreeMobiusLogMoment 1 σ)
    (hm : squarefreeMobiusLogMoment 1 σ ≤ 2 / (σ - 1)) :
    (∫ x in {x : ℝ | 3 ≤ |x|},
        ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ (2 : ℕ) * HTGeometry.gammaCyclicDensity x)
      ≤ (12 / (σ - 1)) ^ (2 : ℕ) * ∫ x in {x : ℝ | 3 ≤ |x|},
          (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) ^ (2 : ℕ) *
            HTGeometry.gammaCyclicDensity x := by
  have hmeas : MeasurableSet {x : ℝ | 3 ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have htail := HTGeometry.integrableOn_log_sq_mul_gammaCyclicDensity
    (6 + Real.log (2 * Real.pi))
  have hbound : ∀ x ∈ {x : ℝ | 3 ≤ |x|},
      ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ (2 : ℕ) * HTGeometry.gammaCyclicDensity x
        ≤ (12 / (σ - 1)) ^ (2 : ℕ) *
          ((Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) ^ (2 : ℕ) *
            HTGeometry.gammaCyclicDensity x) := by
    intro x hx
    have hx3 : 3 ≤ |x| := hx
    have hpt := abs_im_gammaDampedSymbol_scaled_le hσ1 hσ2 hm0 hm hx3
    have hρ : (0 : ℝ) ≤ HTGeometry.gammaCyclicDensity x := HTGeometry.gammaCyclicDensity_nonneg x
    have hsq : ((gammaDampedSymbol σ (2 * Real.pi * x)).im) ^ (2 : ℕ)
        ≤ (12 / (σ - 1)) ^ (2 : ℕ) * (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) ^ (2 : ℕ) := by
      have hnn : (0 : ℝ) ≤ 12 / (σ - 1) * (Real.log (2 * |x|) + (6 + Real.log (2 * Real.pi))) := by
        refine le_trans (abs_nonneg _) hpt
      have hsq' := mul_self_le_mul_self (abs_nonneg _) hpt
      rw [← sq_abs, ← mul_pow]
      nlinarith [hsq', sq_abs ((gammaDampedSymbol σ (2 * Real.pi * x)).im)]
    nlinarith [hsq, hρ]
  have hint := integrableOn_farEnergy hσ1 hσ2 hm0 hm
  rw [← MeasureTheory.integral_const_mul]
  exact setIntegral_mono_on hint (htail.const_mul _) hmeas hbound

end

end RHTower
