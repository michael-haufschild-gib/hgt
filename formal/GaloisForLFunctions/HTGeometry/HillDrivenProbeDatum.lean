import GaloisForLFunctions.HTGeometry.HillDrivenChartWave
import GaloisForLFunctions.HTGeometry.KleinGordonProbeExamples

/-!
# A datum whose driven field is positive at a prescribed event

The driven evolution starts at the datum damped by one power of the frequency and by the weight, so
its field at time zero is the integral of the datum against a *positive* factor. Modulating the
corpus's symmetrised bump by the conjugate character at the chosen point cancels the character, and
what is left is the integral of a nonnegative function which is at least one on a ball: positive.

That is the nonvanishing a clock probe needs, and continuity of the chart field spreads it to a
neighbourhood of the event.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory BoundedContinuousFunction

section Datum

variable {d N : ℕ}

/-- The symmetrised bump, as a real function. -/
noncomputable def kgBumpReal (d : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ :=
  kgBump d ξ + kgBump d (-ξ)

theorem kgBumpFun_eq_ofReal (d : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    kgBumpFun d ξ = ((kgBumpReal d ξ : ℝ) : ℂ) := rfl

theorem kgBumpReal_nonneg (d : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : 0 ≤ kgBumpReal d ξ :=
  add_nonneg (kgBump d).nonneg (kgBump d).nonneg

theorem kgBumpReal_le_two (d : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : kgBumpReal d ξ ≤ 2 := by
  have h1 := (kgBump d).le_one (x := ξ)
  have h2 := (kgBump d).le_one (x := -ξ)
  rw [kgBumpReal]
  linarith

theorem continuous_kgBumpReal (d : ℕ) : Continuous (kgBumpReal d) :=
  (kgBump d).continuous.add ((kgBump d).continuous.comp continuous_neg)

theorem one_le_kgBumpReal {d : ℕ} {ξ : EuclideanSpace ℝ (Fin d)} (h : ‖ξ‖ ≤ 1) :
    1 ≤ kgBumpReal d ξ := by
  have hmem : ξ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (kgBump d).rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h
  have hone : (kgBump d) ξ = 1 := (kgBump d).one_of_mem_closedBall hmem
  have hnn : 0 ≤ (kgBump d) (-ξ) := (kgBump d).nonneg
  rw [kgBumpReal, hone]
  linarith

/-- The bump, as a bounded continuous function. -/
noncomputable def kgBumpBCF (d : ℕ) : EuclideanSpace ℝ (Fin d) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (kgBumpFun d) (continuous_kgBumpFun d) 2
    (fun ξ => by
      rw [kgBumpFun_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (kgBumpReal_nonneg d ξ)]
      exact kgBumpReal_le_two d ξ)

theorem kgBumpBCF_apply (d : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    kgBumpBCF d ξ = ((kgBumpReal d ξ : ℝ) : ℂ) := rfl

/-- The datum of the driven probe at a prescribed point. -/
noncomputable def hillDrivenProbeDatum (d : ℕ) (x₀ : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ᵇ ℂ := kgConjChar x₀ * kgBumpBCF d

theorem hillDrivenProbeDatum_apply (d : ℕ) (x₀ ξ : EuclideanSpace ℝ (Fin d)) :
    hillDrivenProbeDatum d x₀ ξ
      = (starRingEnd ℂ) (kgChar x₀ ξ) * ((kgBumpReal d ξ : ℝ) : ℂ) := rfl

/-! ## The value of the field at the initial time -/

/-- The weight the evolution puts on the datum at time zero. -/
noncomputable def hillDrivenStartWeight (a : HillSpeed) (N : ℕ)
    (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := (kgFreq ξ ^ N)⁻¹ * ((a.freq ξ 0)⁻¹ * kgBumpReal d ξ)

theorem hillDrivenStartWeight_nonneg (a : HillSpeed) (N : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    0 ≤ hillDrivenStartWeight a N ξ := by
  have h1 : (0 : ℝ) ≤ (kgFreq ξ ^ N)⁻¹ := inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le
  have h2 : (0 : ℝ) ≤ (a.freq ξ 0)⁻¹ := inv_nonneg.mpr (a.freq_pos ξ 0).le
  exact mul_nonneg h1 (mul_nonneg h2 (kgBumpReal_nonneg d ξ))

theorem continuous_hillDrivenStartWeight (a : HillSpeed) (N : ℕ) :
    Continuous (hillDrivenStartWeight (d := d) a N) := by
  have hfreq : Continuous fun ξ : EuclideanSpace ℝ (Fin d) => (kgFreq ξ ^ N)⁻¹ := by
    refine Continuous.inv₀ (continuous_kgFreq.pow N) fun ξ => (pow_pos (kgFreq_pos ξ) N).ne'
  have hmass : Continuous fun ξ : EuclideanSpace ℝ (Fin d) => (a.freq ξ 0)⁻¹ := by
    refine Continuous.inv₀ (continuous_massiveFreq_freq a.mass a.speed 0) fun ξ => ?_
    exact (a.freq_pos ξ 0).ne'
  exact hfreq.mul (hmass.mul (continuous_kgBumpReal d))

theorem integrable_hillDrivenStartWeight (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N)
    (a : HillSpeed) :
    Integrable (hillDrivenStartWeight (d := d) a N) (volume) := by
  refine Integrable.mono' ((integrable_kgFreq_inv_pow (E := EuclideanSpace ℝ (Fin d)) hN).mul_const
      (a.mass⁻¹ * 2)) (continuous_hillDrivenStartWeight a N).aestronglyMeasurable ?_
  filter_upwards with ξ
  have hfreqinv : (0 : ℝ) ≤ (kgFreq ξ ^ N)⁻¹ := inv_nonneg.mpr (pow_pos (kgFreq_pos ξ) N).le
  have hmass : (a.freq ξ 0)⁻¹ ≤ a.mass⁻¹ := by
    refine inv_anti₀ a.mass_pos ?_
    have hsq : a.mass ^ 2 ≤ a.freq ξ 0 ^ 2 := by
      show a.mass ^ 2 ≤ massiveFreq a.mass a.speed ‖ξ‖ 0 ^ 2
      rw [massiveFreq_sq a.mass_pos]
      nlinarith [sq_nonneg (a.speed 0 * ‖ξ‖)]
    nlinarith [a.freq_pos ξ 0, a.mass_pos]
  rw [Real.norm_eq_abs, abs_of_nonneg (hillDrivenStartWeight_nonneg a N ξ), hillDrivenStartWeight]
  refine mul_le_mul_of_nonneg_left ?_ hfreqinv
  exact mul_le_mul hmass (kgBumpReal_le_two d ξ) (kgBumpReal_nonneg d ξ)
    (le_of_lt (inv_pos.mpr a.mass_pos))

/-- **The integral of the starting weight is positive.** -/
theorem integral_hillDrivenStartWeight_pos
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N) (a : HillSpeed) :
    0 < ∫ ξ : EuclideanSpace ℝ (Fin d), hillDrivenStartWeight a N ξ := by
  rw [integral_pos_iff_support_of_nonneg (fun ξ => hillDrivenStartWeight_nonneg a N ξ)
    (integrable_hillDrivenStartWeight hN a)]
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆
      Function.support (hillDrivenStartWeight (d := d) a N) := by
    intro ξ hξ
    have hnorm : ‖ξ‖ ≤ 1 := by
      have := Metric.mem_ball.mp hξ
      rw [dist_zero_right] at this
      exact le_of_lt this
    have hbump : 1 ≤ kgBumpReal d ξ := one_le_kgBumpReal hnorm
    have hpos : 0 < hillDrivenStartWeight a N ξ := by
      have h1 : (0 : ℝ) < (kgFreq ξ ^ N)⁻¹ := inv_pos.mpr (pow_pos (kgFreq_pos ξ) N)
      have h2 : (0 : ℝ) < (a.freq ξ 0)⁻¹ := inv_pos.mpr (a.freq_pos ξ 0)
      have h3 : (0 : ℝ) < kgBumpReal d ξ := lt_of_lt_of_le zero_lt_one hbump
      rw [hillDrivenStartWeight]
      positivity
    exact ne_of_gt hpos
  have hball : 0 < (volume : Measure (EuclideanSpace ℝ (Fin d)))
      (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  exact lt_of_lt_of_le hball (measure_mono hsub)

/-- **The field of the driven evolution at the initial time is the integral of the starting
weight.** -/
theorem hillDrivenField_zero_apply (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (x₀ : EuclideanSpace ℝ (Fin d)) :
    hillDrivenField a b (hillDrivenProbeDatum d x₀) 0 x₀
      = ((∫ ξ : EuclideanSpace ℝ (Fin d), hillDrivenStartWeight a N ξ : ℝ) : ℂ) := by
  rw [hillDrivenField, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show kgChar x₀ ξ * hillDrivenDensity a b (hillDrivenProbeDatum d x₀) 0 ξ
    = ((hillDrivenStartWeight a N ξ : ℝ) : ℂ)
  have hflow : hillPotentialFlow a b (hillDrivenProbeDatum d x₀) 0 ξ
      = ((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * hillDrivenProbeDatum d x₀ ξ :=
    hillPotentialFlow_zero a b (hillDrivenProbeDatum d x₀) ξ
  have hchar : kgChar x₀ ξ * (starRingEnd ℂ) (kgChar x₀ ξ) = 1 := kgChar_mul_kgConjChar x₀ ξ
  rw [hillDrivenDensity, kgWeighted, hflow, hillDrivenProbeDatum_apply, hillDrivenStartWeight,
    Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_inv]
  calc kgChar x₀ ξ * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ *
        (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * ((starRingEnd ℂ) (kgChar x₀ ξ) * ((kgBumpReal d ξ : ℝ) : ℂ))))
      = (kgChar x₀ ξ * (starRingEnd ℂ) (kgChar x₀ ξ)) * (((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ *
        (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * ((kgBumpReal d ξ : ℝ) : ℂ))) := by ring
    _ = ((kgFreq ξ ^ N : ℝ) : ℂ)⁻¹ *
        (((a.freq ξ 0 : ℝ) : ℂ)⁻¹ * ((kgBumpReal d ξ : ℝ) : ℂ)) := by rw [hchar, one_mul]

/-- **The chart field of the driven evolution is positive at the chart event.** -/
theorem hillDrivenChartField_event_pos
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < N) (a : HillSpeed)
    (b : WienerFamily (EuclideanSpace ℝ (Fin d)) N) (x₀ : EuclideanSpace ℝ (Fin d)) :
    0 < hillDrivenChartField a b (hillDrivenProbeDatum d x₀) (kgChartEvent d x₀) := by
  have hval : hillDrivenChartField a b (hillDrivenProbeDatum d x₀) (kgChartEvent d x₀)
      = (hillDrivenField a b (hillDrivenProbeDatum d x₀)
          (kgChartEvent d x₀ 0) (kgSpatial d (kgChartEvent d x₀))).re := rfl
  rw [hval, kgChartEvent_zero, kgSpatial_kgChartEvent, hillDrivenField_zero_apply,
    Complex.ofReal_re]
  exact integral_hillDrivenStartWeight_pos hN a

end Datum

end GaloisForLFunctions.HTGeometry
