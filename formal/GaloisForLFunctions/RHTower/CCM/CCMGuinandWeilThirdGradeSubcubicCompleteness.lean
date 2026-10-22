import GaloisForLFunctions.RHTower.CCM.CCMGuinandWeilThirdGradeAbelCompleteness

/-!
# CCM Guinand--Weil third-grade subcubic completeness

The exact completed-error flux from the four-unit source--codiagonal incidence has a universal
grade--growth threshold.  If the literal completed critical-Mellin error has any power bound
`|E(h)| ≤ C h^alpha` with `alpha < 3`, then its cubic endpoint is `o(1)` and its differentiated
bulk is absolutely integrable.  The completed third-grade window therefore has an explicit
cofinal limit.  The Abel-completeness theorem then forces the Riemann hypothesis.

Thus third grade does not merely single out a convenient quadratic estimate: every subcubic
power bound is RH-complete.  Contrapositively, failure of RH forces `E` to escape every fixed
subcubic power envelope beyond every positive wall.  The exponent `3` is the intrinsic boundary
of this absolute-convergence mechanism: the endpoint has degree `alpha - 3`, while the bulk has
degree `alpha - 4`, whose integrability condition is the same strict inequality `alpha < 3`.
-/

open Complex Filter Function Set MeasureTheory Topology
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-! ## Measurability of the literal completed error -/

/-- The completed critical-Mellin error is measurable despite its prime staircase. -/
theorem measurable_criticalMellinCompletedError :
    Measurable criticalMellinCompletedError := by
  rw [show criticalMellinCompletedError = fun h : ℝ =>
      4 * Real.sinh (h / 2) - criticalMellinPrimeMass h by
    funext h
    exact criticalMellinCompletedError_eq_polar_sub_primeMass h]
  exact (Real.continuous_sinh.comp (continuous_id.div_const 2)).const_mul 4
    |>.measurable.sub measurable_criticalMellinPrimeMass

/-! ## The subcubic endpoint and bulk laws -/

/-- Every subcubic power bound kills the cubic completed-error endpoint. -/
theorem tendsto_criticalMellinCompletedError_div_cube_of_rpow_bound
    {b C alpha : ℝ} (hb : 0 < b) (halpha : alpha < 3)
    (hpower : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ alpha) :
    Tendsto
      (fun H : ℝ => criticalMellinCompletedError H / H ^ 3)
      atTop (nhds 0) := by
  have hmajor : Tendsto (fun H : ℝ => C * H ^ (-(3 - alpha)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (y := 3 - alpha) (by linarith)).const_mul C
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_gt_atTop b] with H hH
  have hH0 : 0 < H := hb.trans hH
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos hH0]
  calc
    |criticalMellinCompletedError H| / H ^ 3 ≤
        (C * H ^ alpha) / H ^ 3 :=
      div_le_div_of_nonneg_right (hpower H hH) (pow_nonneg hH0.le 3)
    _ = C * H ^ (-(3 - alpha)) := by
      calc
        C * H ^ alpha / H ^ 3 = C * (H ^ alpha / H ^ 3) := by ring
        _ = C * H ^ (alpha - 3) := by
          rw [← Real.rpow_natCast H 3, ← Real.rpow_sub hH0]
          norm_num
        _ = C * H ^ (-(3 - alpha)) := by ring_nf

/-- Every subcubic power bound makes the differentiated cubic bulk absolutely integrable. -/
theorem integrableOn_criticalMellinCompletedError_div_fourth_of_rpow_bound
    {b C alpha : ℝ} (hb : 0 < b) (halpha : alpha < 3)
    (hpower : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ alpha) :
    IntegrableOn
      (fun h : ℝ => 96 * criticalMellinCompletedError h / h ^ 4)
      (Set.Ioi b) := by
  have hmajor : IntegrableOn
      (fun h : ℝ => (96 * C) * h ^ (alpha - 4))
      (Set.Ioi b) :=
    (integrableOn_Ioi_rpow_of_lt (a := alpha - 4) (by linarith) hb).const_mul
      (96 * C)
  apply hmajor.mono'
  · exact ((measurable_const.mul measurable_criticalMellinCompletedError).div
      (measurable_id.pow_const 4)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : 0 < h := hb.trans hh
    rw [Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 96), abs_pow,
      abs_of_pos hh0]
    calc
      96 * |criticalMellinCompletedError h| / h ^ 4 ≤
          96 * (C * h ^ alpha) / h ^ 4 := by
        gcongr
        exact hpower h hh
      _ = 96 * C * h ^ (alpha - 4) := by
        calc
          96 * (C * h ^ alpha) / h ^ 4 =
              96 * C * (h ^ alpha / h ^ 4) := by ring
          _ = 96 * C * h ^ (alpha - 4) := by
            rw [← Real.rpow_natCast h 4, ← Real.rpow_sub hh0]
            norm_num

/-! ## Exact flux and completed-window limits -/

/-- Endpoint decay plus absolute bulk integrability gives the exact completed-error flux limit. -/
theorem tendsto_ccmGuinandWeilCompletedErrorThirdGradeFlux_of_integrable
    {b : ℝ}
    (hend : Tendsto
      (fun H : ℝ => criticalMellinCompletedError H / H ^ 3)
      atTop (nhds 0))
    (hint : IntegrableOn
      (fun h : ℝ => 96 * criticalMellinCompletedError h / h ^ 4)
      (Set.Ioi b)) :
    Tendsto (ccmGuinandWeilCompletedErrorThirdGradeFlux b) atTop
      (nhds (-(∫ h in Set.Ioi b,
        96 * criticalMellinCompletedError h / h ^ 4))) := by
  have hendpoint : Tendsto
      (fun H : ℝ => -32 * criticalMellinCompletedError H / H ^ 3)
      atTop (nhds 0) := by
    have hmul := hend.const_mul (-32)
    convert hmul using 1
    · funext H
      ring
    · norm_num
  have hintegral : Tendsto
      (fun H : ℝ => ∫ h in b..H,
        96 * criticalMellinCompletedError h / h ^ 4)
      atTop
      (nhds (∫ h in Set.Ioi b,
        96 * criticalMellinCompletedError h / h ^ 4)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi b hint tendsto_id
  have hsub := hendpoint.sub hintegral
  change Tendsto
    (fun H : ℝ => -32 * criticalMellinCompletedError H / H ^ 3 -
      ∫ h in b..H, 96 * criticalMellinCompletedError h / h ^ 4)
    atTop
    (nhds (-(∫ h in Set.Ioi b,
      96 * criticalMellinCompletedError h / h ^ 4)))
  simpa only [zero_sub] using hsub

/-- A subcubic completed-error envelope gives the exact completed-error flux limit. -/
theorem tendsto_ccmGuinandWeilCompletedErrorThirdGradeFlux_of_subcubic_rpow_bound
    {b C alpha : ℝ} (hb : 0 < b) (halpha : alpha < 3)
    (hpower : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ alpha) :
    Tendsto (ccmGuinandWeilCompletedErrorThirdGradeFlux b) atTop
      (nhds (-(∫ h in Set.Ioi b,
        96 * criticalMellinCompletedError h / h ^ 4))) :=
  tendsto_ccmGuinandWeilCompletedErrorThirdGradeFlux_of_integrable
    (tendsto_criticalMellinCompletedError_div_cube_of_rpow_bound
      hb halpha hpower)
    (integrableOn_criticalMellinCompletedError_div_fourth_of_rpow_bound
      hb halpha hpower)

/-- A subcubic completed-error envelope gives the exact completed third-grade window limit. -/
theorem tendsto_ccmGuinandWeilCompletedThirdGradeRateWindow_of_subcubic_rpow_bound
    {b C alpha : ℝ} (hb : 0 < b) (halpha : alpha < 3)
    (hpower : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ alpha) :
    Tendsto (ccmGuinandWeilCompletedThirdGradeRateWindow b) atTop
      (nhds
        (32 * criticalMellinCompletedError b / b ^ 3 -
          (∫ h in Set.Ioi b,
            96 * criticalMellinCompletedError h / h ^ 4) +
          ∫ h in Set.Ioi b,
            ccmGuinandWeilThirdGradeWeight h *
              ccmPublishedArchimedeanDensity h)) := by
  have hbase : Tendsto
      (fun _ : ℝ => 32 * criticalMellinCompletedError b / b ^ 3)
      atTop (nhds (32 * criticalMellinCompletedError b / b ^ 3)) :=
    tendsto_const_nhds
  have hflux :=
    tendsto_ccmGuinandWeilCompletedErrorThirdGradeFlux_of_subcubic_rpow_bound
      hb halpha hpower
  have hgamma := tendsto_ccmGuinandWeilGammaThirdGradeRateWindow hb
  have hsum := (hbase.add hflux).add hgamma
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop b] with H hH
  rw [ccmGuinandWeilCompletedThirdGradeRateWindow_eq_base_add_errorFlux_add_gamma
    hb hH]

/-! ## Completeness and non-RH escape -/

/-- **Subcubic completeness.** Any fixed subcubic power envelope for the literal completed
critical-Mellin error forces the Riemann hypothesis. -/
theorem riemannHypothesis_of_subcubic_criticalMellinCompletedError
    {b C alpha : ℝ} (hb : 0 < b) (halpha : alpha < 3)
    (hpower : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ alpha) :
    RiemannHypothesis := by
  exact riemannHypothesis_of_tendsto_ccmGuinandWeilCompletedThirdGradeRateWindow
    hb
    (tendsto_ccmGuinandWeilCompletedThirdGradeRateWindow_of_subcubic_rpow_bound
      hb halpha hpower)

/-- If RH fails, the completed error escapes every fixed subcubic power envelope after every
positive wall. -/
theorem criticalMellinCompletedError_subcubic_escape_of_not_riemannHypothesis
    (hRH : ¬RiemannHypothesis) {alpha : ℝ} (halpha : alpha < 3)
    {b : ℝ} (hb : 0 < b) (C : ℝ) :
    ∃ h : ℝ, b < h ∧
      C * h ^ alpha < |criticalMellinCompletedError h| := by
  by_contra hescape
  have hpower : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ alpha := by
    intro h hh
    exact le_of_not_gt fun hgt => hescape ⟨h, hh, hgt⟩
  exact hRH
    (riemannHypothesis_of_subcubic_criticalMellinCompletedError
      hb halpha hpower)

/-- Quadratic specialization of subcubic completeness. -/
theorem riemannHypothesis_of_quadratic_criticalMellinCompletedError
    {b C : ℝ} (hb : 0 < b)
    (hquadratic : ∀ h : ℝ, b < h →
      |criticalMellinCompletedError h| ≤ C * h ^ 2) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_subcubic_criticalMellinCompletedError
    (C := C) (alpha := (2 : ℝ)) hb (by norm_num) ?_
  intro h hh
  calc
    |criticalMellinCompletedError h| ≤ C * h ^ (2 : ℕ) := hquadratic h hh
    _ = C * Real.rpow h (2 : ℝ) :=
      congrArg (fun x : ℝ => C * x) (Real.rpow_natCast h 2).symm

end

end RHTower
