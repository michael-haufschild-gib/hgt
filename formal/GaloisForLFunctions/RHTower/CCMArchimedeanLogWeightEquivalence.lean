import GaloisForLFunctions.RHTower.CCMArchimedeanHilbertFormDomain

/-!
# Exact CCM archimedean weight is equivalent to Suzuki's logarithmic weight

Connes--Consani's exact archimedean form uses the digamma-derived density
`ccmArchimedeanFormWeight`, while the classical restricted Weil form domain is commonly
described using `1 + log⁺ |xi|`.  Asymptotic equivalence alone is insufficient to transport
form cores or Galerkin limits.  This module proves a global two-sided pointwise comparison and
the corresponding two-sided domination of weighted measures.

The constant is deliberately symbolic and coarse.  Its proof uses the unconditional global
digamma estimate in `HardyZPhaseAsymptotic`; no sampled value, numerical diagonalization, or
finite-rank certificate is used.
-/

open MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology

noncomputable section

namespace RHTower

/-- Uniform large-frequency error bound specialized to the unitary Fourier scaling. -/
theorem gammaHardyPhaseRate_log_abs_le_thirtyFour {r : ℝ} (hr : 1 ≤ r) :
    |gammaHardyPhaseRate (2 * Real.pi * r) - Real.log r / 2| ≤ 34 := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have ht : 0 < 2 * Real.pi * r := mul_pos (mul_pos (by norm_num) Real.pi_pos) hrpos
  have h := gammaHardyPhaseRate_sub_log_conductor_bound ht
  have harg : (2 * Real.pi * r) / (2 * Real.pi) = r := by
    field_simp [Real.pi_ne_zero]
  rw [harg] at h
  refine h.trans ?_
  have hsq : 1 ≤ (2 * Real.pi * r) ^ 2 := by
    have hbase : 1 ≤ 2 * Real.pi * r := by
      nlinarith [Real.pi_gt_three]
    nlinarith
  have hdenpos : 0 < 16 * (2 * Real.pi * r) ^ 2 := by positivity
  have hfirst : 33 / (16 * (2 * Real.pi * r) ^ 2) ≤ 33 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith
  have htwopos : 0 < 2 * (2 * Real.pi * r) := by positivity
  have hsecond : Real.pi / (2 * (2 * Real.pi * r)) ≤ 1 := by
    rw [div_le_one htwopos]
    nlinarith [Real.pi_pos]
  linarith

/-- A symbolic comparison constant; no decimal or finite-rank computation enters its value. -/
def ccmArchimedeanLogComparisonConstant : ℝ :=
  69 + 2 * |gammaHardyPhaseRate 0|

theorem one_le_ccmArchimedeanLogComparisonConstant :
    1 ≤ ccmArchimedeanLogComparisonConstant := by
  unfold ccmArchimedeanLogComparisonConstant
  nlinarith [abs_nonneg (gammaHardyPhaseRate 0)]

/-- Global upper comparison of exact digamma and logarithmic weights. -/
theorem ccmArchimedeanFormWeight_le_logComparison (xi : ℝ) :
    ccmArchimedeanFormWeight xi ≤
      ccmArchimedeanLogComparisonConstant * suzukiLogWeight xi := by
  have hC : 1 ≤ ccmArchimedeanLogComparisonConstant :=
    one_le_ccmArchimedeanLogComparisonConstant
  by_cases hxi : |xi| ≤ 1
  · have hmono := ccmArchimedeanFourierWeight.monotoneOn_nonneg
      (Set.mem_Ici.mpr (abs_nonneg xi)) (Set.mem_Ici.mpr zero_le_one) hxi
    have hmono' : ccmArchimedeanFormWeight xi ≤ ccmArchimedeanFormWeight 1 := by
      simpa [ccmArchimedeanFourierWeight, ccmArchimedeanFormWeight] using hmono
    have hp := gammaHardyPhaseRate_log_abs_le_thirtyFour (r := (1 : ℝ)) le_rfl
    simp only [mul_one, Real.log_one, zero_div, sub_zero, abs_le] at hp
    have hone : ccmArchimedeanFormWeight 1 ≤
        ccmArchimedeanLogComparisonConstant := by
      unfold ccmArchimedeanFormWeight ccmArchimedeanLogComparisonConstant
      simp only [abs_one, mul_one]
      nlinarith [neg_le_abs (gammaHardyPhaseRate 0)]
    have hscale := mul_le_mul_of_nonneg_left
      (one_le_suzukiLogWeight xi) (zero_le_one.trans hC)
    calc
      ccmArchimedeanFormWeight xi ≤ ccmArchimedeanFormWeight 1 := hmono'
      _ ≤ ccmArchimedeanLogComparisonConstant := hone
      _ = ccmArchimedeanLogComparisonConstant * 1 := by ring
      _ ≤ ccmArchimedeanLogComparisonConstant * suzukiLogWeight xi := hscale
  · have hr : 1 ≤ |xi| := le_of_not_ge hxi
    have hlog : 0 ≤ Real.log |xi| := Real.log_nonneg hr
    have hp := gammaHardyPhaseRate_log_abs_le_thirtyFour hr
    have hpupper := (abs_le.mp hp).2
    have hfirst : ccmArchimedeanFormWeight xi ≤
        ccmArchimedeanLogComparisonConstant + Real.log |xi| := by
      unfold ccmArchimedeanFormWeight ccmArchimedeanLogComparisonConstant
      nlinarith [neg_le_abs (gammaHardyPhaseRate 0)]
    have hprod : 0 ≤
        (ccmArchimedeanLogComparisonConstant - 1) * Real.log |xi| :=
      mul_nonneg (sub_nonneg.mpr hC) hlog
    rw [suzukiLogWeight, max_eq_left hlog]
    calc
      ccmArchimedeanFormWeight xi ≤
          ccmArchimedeanLogComparisonConstant + Real.log |xi| := hfirst
      _ ≤ ccmArchimedeanLogComparisonConstant * (1 + Real.log |xi|) := by
        nlinarith

/-- Global reverse comparison of logarithmic and exact digamma weights. -/
theorem suzukiLogWeight_le_ccmArchimedeanComparison (xi : ℝ) :
    suzukiLogWeight xi ≤
      ccmArchimedeanLogComparisonConstant * ccmArchimedeanFormWeight xi := by
  have hC : 1 ≤ ccmArchimedeanLogComparisonConstant :=
    one_le_ccmArchimedeanLogComparisonConstant
  by_cases hxi : |xi| ≤ 1
  · have hlog : Real.log |xi| ≤ 0 := Real.log_nonpos (abs_nonneg xi) hxi
    rw [suzukiLogWeight, max_eq_right hlog, add_zero]
    have hweight := one_le_ccmArchimedeanFormWeight xi
    nlinarith [mul_nonneg (zero_le_one.trans hC)
      (zero_le_one.trans hweight)]
  · have hr : 1 ≤ |xi| := le_of_not_ge hxi
    have hlog : 0 ≤ Real.log |xi| := Real.log_nonneg hr
    have hp := gammaHardyPhaseRate_log_abs_le_thirtyFour hr
    have hplower := (abs_le.mp hp).1
    have hsum : suzukiLogWeight xi ≤
        ccmArchimedeanFormWeight xi +
          (ccmArchimedeanLogComparisonConstant - 1) := by
      rw [suzukiLogWeight, max_eq_left hlog]
      unfold ccmArchimedeanFormWeight ccmArchimedeanLogComparisonConstant
      nlinarith [le_abs_self (gammaHardyPhaseRate 0)]
    have hweight := one_le_ccmArchimedeanFormWeight xi
    have hnonneg : 0 ≤ ccmArchimedeanLogComparisonConstant - 1 := sub_nonneg.mpr hC
    calc
      suzukiLogWeight xi ≤ ccmArchimedeanFormWeight xi +
          (ccmArchimedeanLogComparisonConstant - 1) := hsum
      _ ≤ ccmArchimedeanLogComparisonConstant * ccmArchimedeanFormWeight xi := by
        nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hweight)]

def ccmArchimedeanLogComparisonENNReal : ℝ≥0∞ :=
  (Real.toNNReal ccmArchimedeanLogComparisonConstant : ℝ≥0∞)

theorem ccmArchimedeanLogComparisonENNReal_ne_top :
    ccmArchimedeanLogComparisonENNReal ≠ ∞ := by
  simp [ccmArchimedeanLogComparisonENNReal]

/-- Exact CCM weighted measure is dominated by a finite multiple of Suzuki's measure. -/
theorem ccmArchimedeanFormMeasure_le_logComparison_smul :
    ccmArchimedeanFormMeasure ≤
      ccmArchimedeanLogComparisonENNReal • suzukiHlogMeasure := by
  unfold ccmArchimedeanFormMeasure suzukiHlogMeasure
  rw [← withDensity_smul ccmArchimedeanLogComparisonENNReal
    measurable_suzukiLogWeightNNReal.coe_nnreal_ennreal]
  apply withDensity_mono
  filter_upwards with xi
  simp only [Pi.smul_apply, smul_eq_mul]
  have hreal :
      (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ) ≤
        (Real.toNNReal ccmArchimedeanLogComparisonConstant : ℝ) *
          (Real.toNNReal (suzukiLogWeight xi) : ℝ) := by
    rw [Real.coe_toNNReal _ (ccmArchimedeanFormWeight_pos xi).le,
      Real.coe_toNNReal _ (zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant),
      Real.coe_toNNReal _ (suzukiLogWeight_nonneg xi)]
    exact ccmArchimedeanFormWeight_le_logComparison xi
  unfold ccmArchimedeanLogComparisonENNReal
  exact_mod_cast hreal

/-- Suzuki's weighted measure is dominated by the same finite multiple of exact CCM measure. -/
theorem suzukiHlogMeasure_le_ccmArchimedeanComparison_smul :
    suzukiHlogMeasure ≤
      ccmArchimedeanLogComparisonENNReal • ccmArchimedeanFormMeasure := by
  unfold ccmArchimedeanFormMeasure suzukiHlogMeasure
  rw [← withDensity_smul ccmArchimedeanLogComparisonENNReal
    measurable_ccmArchimedeanFormWeightNNReal.coe_nnreal_ennreal]
  apply withDensity_mono
  filter_upwards with xi
  simp only [Pi.smul_apply, smul_eq_mul]
  have hreal :
      (Real.toNNReal (suzukiLogWeight xi) : ℝ) ≤
        (Real.toNNReal ccmArchimedeanLogComparisonConstant : ℝ) *
          (Real.toNNReal (ccmArchimedeanFormWeight xi) : ℝ) := by
    rw [Real.coe_toNNReal _ (suzukiLogWeight_nonneg xi),
      Real.coe_toNNReal _ (zero_le_one.trans one_le_ccmArchimedeanLogComparisonConstant),
      Real.coe_toNNReal _ (ccmArchimedeanFormWeight_pos xi).le]
    exact suzukiLogWeight_le_ccmArchimedeanComparison xi
  unfold ccmArchimedeanLogComparisonENNReal
  exact_mod_cast hreal

end RHTower
