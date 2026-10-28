import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVarianceRemainder
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteCellVariancePayment
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheSelfEnergyOfAnAtomHasConstantOne

/-!
# A sibling rectangle pays the whole parent variance

The exact adjacent-interval variance split retains both child variances and
both actual means. The Gamma kernel on a short sibling rectangle therefore
pays a fixed fraction of its parent variance. Actual logarithmic cells have
uniformly balanced children, including after arbitrary real translation.
-/

noncomputable section

open MeasureTheory Set Filter RHTower
open scoped ENNReal

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticCastelnuovoSeveri.IntervalVariance
open ArithmeticCastelnuovoSeveri.MeanZeroIntervals
open ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry
open SpacingScaleHarmonicAnalysis
open HTGeometry.CauchyDifference

private theorem integral_adjacent {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {F : ℝ → ℝ} (hl : IntegrableOn F (Ioo a b)) (hr : IntegrableOn F (Ioo b c)) :
    (∫ x in Ioo a b, F x) + (∫ x in Ioo b c, F x) = ∫ x in Ioo a c, F x := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).mpr hl)
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le hbc.le).mpr hr)
  simpa only [intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_of_le hbc.le, intervalIntegral.integral_of_le (hab.trans hbc).le,
    integral_Ioc_eq_integral_Ioo] using h

private theorem integral_eq_width_mean {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∫ x in Ioo a b, f x) = (b - a) * intervalMean a b f := by
  rw [intervalMean]
  field_simp [ne_of_gt (sub_pos.mpr hab)]

/-- Adjacent variances split exactly, retaining the actual mean displacement. -/
theorem intervalVariance_adjacent_eq {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    intervalVariance a c f = intervalVariance a b f + intervalVariance b c f +
      (b - a) * (c - b) / (c - a) * (intervalMean a b f - intervalMean b c f) ^ 2 := by
  have hfl : MemLp f 2 (volume.restrict (Ioo a b)) := hf.restrict _
  have hfr : MemLp f 2 (volume.restrict (Ioo b c)) := hf.restrict _
  have hm := integral_adjacent hab hbc (hfl.integrable one_le_two) (hfr.integrable one_le_two)
  rw [integral_eq_width_mean hab, integral_eq_width_mean hbc,
    integral_eq_width_mean (hab.trans hbc)] at hm
  have hmean : intervalMean a c f =
      ((b - a) * intervalMean a b f + (c - b) * intervalMean b c f) / (c - a) := by
    apply (eq_div_iff (ne_of_gt (sub_pos.mpr (hab.trans hbc)))).mpr
    linarith only [hm]
  have hl := integral_sub_const_sq_eq_variance hab hfl (intervalMean a c f)
  have hr := integral_sub_const_sq_eq_variance hbc hfr (intervalMean a c f)
  have hs := integral_adjacent hab hbc
    ((hfl.sub (memLp_const (intervalMean a c f))).integrable_sq)
    ((hfr.sub (memLp_const (intervalMean a c f))).integrable_sq)
  simp only [Pi.sub_apply] at hs
  change _ = intervalVariance a c f at hs
  rw [hl, hr] at hs
  rw [← hs, hmean]
  field_simp [ne_of_gt (sub_pos.mpr (hab.trans hbc))]
  ring

private theorem min_width_mul_variance_le {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    min (b - a) (c - b) * intervalVariance a c f ≤
      (c - b) * intervalVariance a b f + (b - a) * intervalVariance b c f +
        (b - a) * (c - b) * (intervalMean a b f - intervalMean b c f) ^ 2 := by
  have hD : 0 < c - a := sub_pos.mpr (hab.trans hbc)
  have hC : 0 ≤ (b - a) * (c - b) / (c - a) *
      (intervalMean a b f - intervalMean b c f) ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg (sub_pos.mpr hab).le (sub_pos.mpr hbc).le) hD.le)
      (sq_nonneg _)
  have hmin : min (b - a) (c - b) ≤ c - a :=
    (min_le_left _ _).trans (by linarith only [hbc])
  have h1 := mul_le_mul_of_nonneg_right (min_le_right (b - a) (c - b))
    (intervalVariance_nonneg a b f)
  have h2 := mul_le_mul_of_nonneg_right (min_le_left (b - a) (c - b))
    (intervalVariance_nonneg b c f)
  have h3 := mul_le_mul_of_nonneg_right hmin hC
  rw [intervalVariance_adjacent_eq hab hbc hf, mul_add, mul_add]
  have he : (c - a) * ((b - a) * (c - b) / (c - a) *
      (intervalMean a b f - intervalMean b c f) ^ 2) =
      (b - a) * (c - b) * (intervalMean a b f - intervalMean b c f) ^ 2 := by
    field_simp [ne_of_gt hD]
  rw [he] at h3
  exact add_le_add (add_le_add h1 h2) h3

/-- The actual sibling Gamma charge pays the parent variance, with its precise width cost. -/
theorem sibling_gamma_ge_parent_variance {a b c : ℝ}
    (hab : a < b) (hbc : b < c) (hwidth : c - a ≤ 1)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ENNReal.ofReal (min (b - a) (c - b) / (2 * (c - a)) * intervalVariance a c f) ≤
      ∫⁻ x in Ioo a b, ∫⁻ y in Ioo b c, gammaDifference f x y := by
  let κ : ℝ := 1 / (2 * (c - a))
  have hD : 0 < c - a := sub_pos.mpr (hab.trans hbc)
  have hκ : 0 ≤ κ := by dsimp only [κ]; positivity
  have huniform := productWeight_twoInterval_mean_variance_le hab hbc
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1)
    (hf.restrict _) (hf.restrict _)
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ)))
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simp only [setIntegral_const, Real.volume_real_Ioo_of_le hab.le,
    Real.volume_real_Ioo_of_le hbc.le, smul_eq_mul, mul_one, one_mul] at huniform
  have hlow := mul_le_mul_of_nonneg_left
    ((min_width_mul_variance_le hab hbc hf).trans huniform) hκ
  have hkernel (x : ℝ) (hx : x ∈ Ioo a b) (y : ℝ) (hy : y ∈ Ioo b c) :
      κ ≤ archLevyDensity |y - x| := by
    have hxy : 0 < y - x := by linarith only [hx.2, hy.1]
    rw [abs_of_pos hxy]
    exact (archLevyDensity_ge_inv_two_mul hD hwidth).trans
      (strictAntiOn_archLevyDensity.antitoneOn hxy hD
        (by linarith only [hx.1, hy.2]))
  calc
    _ = ENNReal.ofReal (κ * (min (b - a) (c - b) * intervalVariance a c f)) := by
      congr 1
      dsimp only [κ]
      ring
    _ ≤ ENNReal.ofReal (κ * ∫ x in Ioo a b, ∫ y in Ioo b c, (f x - f y) ^ 2) :=
      ENNReal.ofReal_le_ofReal hlow
    _ = ENNReal.ofReal (∫ x in Ioo a b, ∫ y in Ioo b c, κ * (f x - f y) ^ 2) := by
      simp only [integral_const_mul]
    _ ≤ ∫⁻ x in Ioo a b, ENNReal.ofReal (∫ y in Ioo b c, κ * (f x - f y) ^ 2) :=
      ofReal_setIntegral_le_setLIntegral fun _ => integral_nonneg fun _ =>
        mul_nonneg hκ (sq_nonneg _)
    _ ≤ ∫⁻ x in Ioo a b, ∫⁻ y in Ioo b c, ENNReal.ofReal (κ * (f x - f y) ^ 2) :=
      lintegral_mono fun _ => ofReal_setIntegral_le_setLIntegral fun _ =>
        mul_nonneg hκ (sq_nonneg _)
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
      exact ENNReal.ofReal_le_ofReal (by
        nlinarith only [mul_le_mul_of_nonneg_right (hkernel x hx y hy) (sq_nonneg (f x - f y))])

/-- Left endpoint of the literal translated logarithmic sibling pair. -/
def logCellSiblingLeft (t : ℝ) (a : ℕ+) : ℝ := t + Real.log ((2 * (a : ℕ) : ℕ) : ℝ)

/-- Shared endpoint of the two literal logarithmic children. -/
def logCellSiblingMiddle (t : ℝ) (a : ℕ+) : ℝ :=
  t + Real.log ((2 * (a : ℕ) + 1 : ℕ) : ℝ)

/-- Right endpoint of the literal translated logarithmic sibling pair. -/
def logCellSiblingRight (t : ℝ) (a : ℕ+) : ℝ :=
  t + Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ)

theorem logCellSibling_widths (t : ℝ) (a : ℕ+) :
    logCellSiblingMiddle t a - logCellSiblingLeft t a = logCellWidth (2 * (a : ℕ)) ∧
    logCellSiblingRight t a - logCellSiblingMiddle t a = logCellWidth (2 * (a : ℕ) + 1) ∧
    logCellSiblingRight t a - logCellSiblingLeft t a = logCellWidth a := by
  refine ⟨?_, ?_, ?_⟩
  · unfold logCellSiblingMiddle logCellSiblingLeft logCellWidth
    push_cast
    ring
  · unfold logCellSiblingRight logCellSiblingMiddle logCellWidth
    push_cast
    rw [show 2 * (a : ℝ) + 1 + 1 = 2 * (a : ℝ) + 2 by ring]
    ring
  · calc
      _ = Real.log ((2 * (a : ℕ) + 2 : ℕ) : ℝ) - Real.log ((2 * (a : ℕ) : ℕ) : ℝ) := by
        unfold logCellSiblingRight logCellSiblingLeft
        ring
      _ = _ := haarPairWidth a.pos

private theorem width_le_four_child {a k : ℕ} (ha : 1 ≤ a) (hk : 1 ≤ k)
    (hka : k + 1 ≤ 4 * a) : logCellWidth a ≤ 4 * logCellWidth k := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  calc
    _ ≤ 1 / (a : ℝ) := logCellWidth_le_inv ha
    _ ≤ 4 / ((k : ℝ) + 1) := by
      apply (div_le_div_iff₀ ha0 hk0).mpr
      norm_num only [one_mul]
      exact_mod_cast hka
    _ = 4 * (1 / ((k : ℝ) + 1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inv_add_one_le_logCellWidth hk) (by norm_num)

/-- Both actual logarithmic children retain at least a quarter of the parent width. -/
theorem logCellSibling_child_balance (t : ℝ) (a : ℕ+) :
    (logCellSiblingRight t a - logCellSiblingLeft t a) / 4 ≤
      min (logCellSiblingMiddle t a - logCellSiblingLeft t a)
        (logCellSiblingRight t a - logCellSiblingMiddle t a) := by
  obtain ⟨hl, hr, hp⟩ := logCellSibling_widths t a
  rw [hl, hr, hp]
  have ha := a.pos
  apply le_min
  · have h := width_le_four_child ha (show 1 ≤ 2 * (a : ℕ) by omega) (by omega)
    linarith only [h]
  · have h := width_le_four_child ha (show 1 ≤ 2 * (a : ℕ) + 1 by omega) (by omega)
    linarith only [h]

/-- A literal logarithmic sibling rectangle pays one eighth of its full parent variance. -/
theorem logCellSibling_gamma_ge_variance (t : ℝ) (a : ℕ+)
    {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ENNReal.ofReal (intervalVariance (logCellSiblingLeft t a) (logCellSiblingRight t a) f / 8) ≤
      ∫⁻ x in Ioo (logCellSiblingLeft t a) (logCellSiblingMiddle t a),
        ∫⁻ y in Ioo (logCellSiblingMiddle t a) (logCellSiblingRight t a), gammaDifference f x y := by
  obtain ⟨hl, hr, hp⟩ := logCellSibling_widths t a
  have ha := a.pos
  have hL : logCellSiblingLeft t a < logCellSiblingMiddle t a := by
    apply sub_pos.mp
    rw [hl]
    exact logCellWidth_pos (by omega)
  have hR : logCellSiblingMiddle t a < logCellSiblingRight t a := by
    apply sub_pos.mp
    rw [hr]
    exact logCellWidth_pos (by omega)
  have hD := sub_pos.mpr (hL.trans hR)
  have hwidth : logCellSiblingRight t a - logCellSiblingLeft t a ≤ 1 := by
    rw [hp]
    exact (logCellWidth_le_inv ha).trans
      ((div_le_one (by exact_mod_cast ha : (0 : ℝ) < (a : ℕ))).mpr (by exact_mod_cast ha))
  have hbalance := logCellSibling_child_balance t a
  have hcoef : (1 : ℝ) / 8 ≤
      min (logCellSiblingMiddle t a - logCellSiblingLeft t a)
        (logCellSiblingRight t a - logCellSiblingMiddle t a) /
          (2 * (logCellSiblingRight t a - logCellSiblingLeft t a)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hD)).mpr
    linarith only [hbalance]
  have hmul := mul_le_mul_of_nonneg_right hcoef
    (intervalVariance_nonneg (logCellSiblingLeft t a) (logCellSiblingRight t a) f)
  exact (ENNReal.ofReal_le_ofReal (by nlinarith only [hmul])).trans
    (sibling_gamma_ge_parent_variance hL hR hwidth hf)

/-- Complete arithmetic cell sources retain the same sibling payment with all means free. -/
theorem completePair_logCellSibling_gamma_ge_variance (q d : ℕ → ℝ) (X : ℕ)
    (t : ℝ) (a : ℕ+) :
    ENNReal.ofReal (intervalVariance (logCellSiblingLeft t a) (logCellSiblingRight t a)
      (completePairProfile q d X) / 8) ≤
      ∫⁻ x in Ioo (logCellSiblingLeft t a) (logCellSiblingMiddle t a),
        ∫⁻ y in Ioo (logCellSiblingMiddle t a) (logCellSiblingRight t a),
          gammaDifference (completePairProfile q d X) x y :=
  logCellSibling_gamma_ge_variance t a
    (memLp_compact_bv (completePairProfile_bv q d X) (completePairProfile_compact q d X))

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.intervalVariance_adjacent_eq
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.sibling_gamma_ge_parent_variance
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellSibling_gamma_ge_variance
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.completePair_logCellSibling_gamma_ge_variance
