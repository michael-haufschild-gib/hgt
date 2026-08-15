import GaloisForLFunctions.RHTower.CCMGuinandWeilLiteralPolarPrimeSource
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Singular archimedean odd source

The published archimedean density has a first-order pole at logarithmic position zero, so it is
not another raw finite-measure channel in the continuous dual of `C([0,1], R)`.  This file proves
its exact principal coefficient and performs the endpoint cancellation at the physical sine test
before integration.

The resulting odd coordinate is genuinely integrable and, after affine horizon transport, equals
the published archimedean sine coefficient.  Adding it to the separately constructed pole--prime
functional gives the entire published odd source family at physical modes.  The archimedean
weighted-cosine diagonal still requires the endpoint-renormalized restricted-Weil distribution;
this file does not pretend that singular channel is an order-zero measure.
-/

noncomputable section

open scoped BigOperators Interval

namespace RHTower

open Matrix MeasureTheory Set Filter Topology

/-- Exact principal coefficient of the one-sided archimedean density at its endpoint. -/
theorem tendsto_h_mul_ccmPublishedArchimedeanDensity :
    Tendsto (fun h : ℝ => h * ccmPublishedArchimedeanDensity h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
  have hd : HasDerivAt (fun h : ℝ => Real.exp (2 * h)) 2 0 := by
    have hinner : HasDerivAt (fun h : ℝ => 2 * h) 2 0 :=
      hasDerivAt_const_mul (x := (0 : ℝ)) 2
    simpa using hinner.exp
  have hslope := hd.tendsto_slope_zero_right
  have hslope' :
      Tendsto (fun h : ℝ => (Real.exp (2 * h) - 1) / h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    simpa [div_eq_mul_inv, mul_comm] using hslope
  have hinv :
      Tendsto (fun h : ℝ => h / (Real.exp (2 * h) - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
    simpa only [inv_div, one_div] using
      hslope'.inv₀ (by norm_num : (2 : ℝ) ≠ 0)
  have hexp :
      Tendsto (fun h : ℝ => Real.exp (3 * h / 2))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hc : ContinuousAt (fun h : ℝ => Real.exp (3 * h / 2)) 0 := by
      fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmul := hexp.mul hinv
  have hmul' :
      Tendsto (fun h : ℝ => Real.exp (3 * h / 2) *
        (h / (Real.exp (2 * h) - 1)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2 : ℝ)) := by
    simpa using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : 0 < h := hh
  rw [ccmPublishedArchimedeanDensity]
  have henh : Real.exp (-h) ≠ 0 := (Real.exp_pos (-h)).ne'
  have hden : Real.exp (2 * h) - 1 ≠ 0 := by
    have : 1 < Real.exp (2 * h) := Real.one_lt_exp_iff.mpr (by linarith)
    linarith
  rw [show Real.exp h - Real.exp (-h) =
      Real.exp (-h) * (Real.exp (2 * h) - 1) by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring]
  field_simp [henh, hden]
  rw [← Real.exp_add]
  congr 2
  ring

/-- The physical sine removes the pole and leaves endpoint value `xi/2`. -/
theorem tendsto_sin_mul_ccmPublishedArchimedeanDensity (xi : ℝ) :
    Tendsto (fun h : ℝ => Real.sin (xi * h) *
        ccmPublishedArchimedeanDensity h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (xi / 2)) := by
  have hd : HasDerivAt (fun h : ℝ => Real.sin (xi * h)) xi 0 := by
    have hinner : HasDerivAt (fun h : ℝ => xi * h) xi 0 :=
      hasDerivAt_const_mul (x := (0 : ℝ)) xi
    simpa using hinner.sin
  have hslope := hd.tendsto_slope_zero_right
  have hslope' :
      Tendsto (fun h : ℝ => Real.sin (xi * h) / h)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds xi) := by
    simpa [div_eq_mul_inv, mul_comm] using hslope
  have hmul := hslope'.mul tendsto_h_mul_ccmPublishedArchimedeanDensity
  have hmul' :
      Tendsto (fun h : ℝ => (Real.sin (xi * h) / h) *
          (h * ccmPublishedArchimedeanDensity h))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (xi / 2)) := by
    simpa only [div_eq_mul_inv, one_mul] using hmul
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : h ≠ 0 := ne_of_gt hh
  field_simp

/-- Regular positive-half-line form of the archimedean density. -/
theorem ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div
    {h : ℝ} (hh : 0 < h) :
    ccmPublishedArchimedeanDensity h =
      Real.exp (-h / 2) / (1 - Real.exp (-2 * h)) := by
  rw [ccmPublishedArchimedeanDensity]
  have heh : Real.exp h ≠ 0 := (Real.exp_pos h).ne'
  have hden : 1 - Real.exp (-2 * h) ≠ 0 := by
    have : Real.exp (-2 * h) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  rw [show Real.exp h - Real.exp (-h) =
      Real.exp h * (1 - Real.exp (-2 * h)) by
    rw [mul_sub, mul_one, ← Real.exp_add]
    congr 2
    ring]
  field_simp [heh, hden]
  rw [← Real.exp_add]
  congr 2
  ring

/-- The endpoint-cancelled archimedean sine channel is integrable on every positive aperture. -/
theorem ccmGuinandWeil_intervalIntegrable_sin_mul_archimedeanDensity
    {L xi : ℝ} (hL : 0 < L) :
    IntervalIntegrable
      (fun h : ℝ => Real.sin (xi * h) * ccmPublishedArchimedeanDensity h)
      volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL.le]
  apply Measure.integrableOn_of_bounded (M := |xi| * (1 + 2 * L) / 2)
    measure_Ioc_lt_top.ne
  · apply Measurable.aestronglyMeasurable
    unfold ccmPublishedArchimedeanDensity
    measurability
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    have hh0 : 0 < h := hh.1
    have hhL : h ≤ L := hh.2
    have hadd : 1 + 2 * h ≤ Real.exp (2 * h) := by
      simpa [add_comm] using Real.add_one_le_exp (2 * h)
    have hlin : 0 < 1 + 2 * h := by linarith
    have hinv :
        Real.exp (-2 * h) ≤ (1 + 2 * h)⁻¹ := by
      rw [show -2 * h = -(2 * h) by ring, Real.exp_neg]
      exact (inv_le_inv₀ (Real.exp_pos (2 * h)) hlin).2 hadd
    have hdenLower :
        (2 * h) / (1 + 2 * h) ≤ 1 - Real.exp (-2 * h) := by
      calc
        (2 * h) / (1 + 2 * h) =
            1 - (1 + 2 * h)⁻¹ := by
              field_simp
              ring
        _ ≤ 1 - Real.exp (-2 * h) := by linarith
    have hdenPos : 0 < 1 - Real.exp (-2 * h) := by
      exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
    have hlowerPos : 0 < (2 * h) / (1 + 2 * h) :=
      div_pos (by linarith) hlin
    have hsin : |Real.sin (xi * h)| ≤ |xi| * h := by
      calc
        |Real.sin (xi * h)| ≤ |xi * h| := Real.abs_sin_le_abs
        _ = |xi| * h := by rw [abs_mul, abs_of_pos hh0]
    have hexpLe : Real.exp (-h / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    rw [ccmGuinandWeilArchimedeanDensity_eq_exp_neg_half_div hh0,
      Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (Real.exp_pos _), abs_of_pos hdenPos]
    rw [← mul_div_assoc]
    calc
      |Real.sin (xi * h)| * Real.exp (-h / 2) /
          (1 - Real.exp (-2 * h)) ≤
          (|xi| * h) / (1 - Real.exp (-2 * h)) := by
            apply div_le_div_of_nonneg_right _ hdenPos.le
            calc
              |Real.sin (xi * h)| * Real.exp (-h / 2) ≤
                  (|xi| * h) * Real.exp (-h / 2) :=
                mul_le_mul_of_nonneg_right hsin (Real.exp_pos _).le
              _ ≤ (|xi| * h) * 1 :=
                mul_le_mul_of_nonneg_left hexpLe
                  (mul_nonneg (abs_nonneg _) hh0.le)
              _ = |xi| * h := by ring
      _ ≤ (|xi| * h) / ((2 * h) / (1 + 2 * h)) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (abs_nonneg _) hh0.le) hlowerPos hdenLower
      _ = |xi| * (1 + 2 * h) / 2 := by
        field_simp
      _ ≤ |xi| * (1 + 2 * L) / 2 := by
        gcongr

/-- Archimedean odd coordinate formed only after the physical sine cancels the endpoint pole. -/
def ccmGuinandWeilArchimedeanOddSourceValue (a : ℝ) (n : ℕ) : ℝ :=
  -(∫ h in (0 : ℝ)..(2 * a),
      ccmGuinandWeilSineCoordinate (n : ℤ)
          (ccmGuinandWeilLogToHorizon a h) *
        ccmPublishedArchimedeanDensity h) / Real.pi

/-- The horizon form of the archimedean odd source is genuinely interval integrable. -/
theorem ccmGuinandWeil_intervalIntegrable_archimedeanOddSourceIntegrand
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    IntervalIntegrable
      (fun h : ℝ =>
        ccmGuinandWeilSineCoordinate (n : ℤ)
            (ccmGuinandWeilLogToHorizon a h) *
          ccmPublishedArchimedeanDensity h)
      volume 0 (2 * a) := by
  have hsin := ccmGuinandWeil_intervalIntegrable_sin_mul_archimedeanDensity
    (L := 2 * a) (xi := ccmPublishedPhysicalFrequency a n) (by positivity)
  refine hsin.neg.congr ?_
  intro h hh
  rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at hh
  have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := ⟨hh.1.le, hh.2⟩
  change -(Real.sin (ccmPublishedPhysicalFrequency a n * h) *
      ccmPublishedArchimedeanDensity h) =
    ccmGuinandWeilSineCoordinate (n : ℤ)
        (ccmGuinandWeilLogToHorizon a h) *
      ccmPublishedArchimedeanDensity h
  rw [ccmGuinandWeilSineCoordinate_logToHorizon ha n hh']
  ring

/-- Physical archimedean source landing, including reflection sign and `pi` normalization. -/
theorem ccmGuinandWeilArchimedeanOddSourceValue_eq_published
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ccmGuinandWeilArchimedeanOddSourceValue a n =
      ccmPublishedArchimedeanSineCoefficient a
        (ccmPublishedPhysicalFrequency a n) := by
  let xi := ccmPublishedPhysicalFrequency a n
  have hcoordinate :
      (∫ h in (0 : ℝ)..(2 * a),
        ccmGuinandWeilSineCoordinate (n : ℤ)
            (ccmGuinandWeilLogToHorizon a h) *
          ccmPublishedArchimedeanDensity h) =
        -∫ h in (0 : ℝ)..(2 * a),
          Real.sin (xi * h) * ccmPublishedArchimedeanDensity h := by
    calc
      _ = ∫ h in (0 : ℝ)..(2 * a),
          (-Real.sin (xi * h)) * ccmPublishedArchimedeanDensity h := by
        apply intervalIntegral.integral_congr
        intro h hh
        have hh' : h ∈ Set.Icc (0 : ℝ) (2 * a) := by
          simpa [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] using hh
        change ccmGuinandWeilSineCoordinate (n : ℤ)
              (ccmGuinandWeilLogToHorizon a h) *
              ccmPublishedArchimedeanDensity h =
          (-Real.sin (xi * h)) * ccmPublishedArchimedeanDensity h
        rw [ccmGuinandWeilSineCoordinate_logToHorizon ha n hh']
      _ = _ := by
        rw [← intervalIntegral.integral_neg]
        apply intervalIntegral.integral_congr
        intro h _hh
        ring
  rw [ccmGuinandWeilArchimedeanOddSourceValue, hcoordinate,
    ccmPublishedArchimedeanSineCoefficient,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * a)]
  ring

/-- Full physical odd source: order-zero pole--prime functional plus sine-renormalized Gamma jet. -/
def ccmGuinandWeilCompletedPhysicalOddSourceValue
    {a : ℝ} (ha : 0 < a) (n : ℕ) : ℝ :=
  ccmGuinandWeilContinuousSourceValue
      (ccmGuinandWeilPolarPrimeSourceFunctional ha) (n : ℤ) +
    ccmGuinandWeilArchimedeanOddSourceValue a n

/-- **Complete odd-source dictionary.** The mixed-order source is exactly the published CCM odd
coefficient at every physical mode. -/
theorem ccmGuinandWeilCompletedPhysicalOddSourceValue_eq_published
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ccmGuinandWeilCompletedPhysicalOddSourceValue ha n =
      ccmPublishedSourceSineCoefficient a
        (ccmPublishedPhysicalFrequency a n) := by
  rw [ccmGuinandWeilCompletedPhysicalOddSourceValue,
    ccmGuinandWeilPolarPrimeSourceValue_physical_eq_published ha n,
    ccmGuinandWeilArchimedeanOddSourceValue_eq_published ha n,
    ccmPublishedSourceSineCoefficient]
  ring

end RHTower
