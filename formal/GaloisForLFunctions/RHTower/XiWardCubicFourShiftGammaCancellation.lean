import GaloisForLFunctions.RHTower.XiWardCubicTranslationEnergySeparator

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

def fourShiftGammaCancelledPolynomial (q x : ℝ) : ℝ :=
  -q * x + (1 + q + q ^ 2) * x ^ 2 -
    (1 + q + q ^ 2) * x ^ 3 + q * x ^ 4

theorem fourShiftGammaCancelledPolynomial_factor (q x : ℝ) :
    fourShiftGammaCancelledPolynomial q x =
      x * (1 - x) * (1 - q * x) * (x - q) := by
  rw [fourShiftGammaCancelledPolynomial]
  ring

def fourShiftGammaCancelledEnergyFeature (r a : ℝ) : ℝ :=
  fourShiftGammaCancelledPolynomial (Real.exp (-2 * r))
    (Real.exp (-2 * a * r))

theorem fourShiftGammaCancelledEnergyFeature_eq_factor (r a : ℝ) :
    fourShiftGammaCancelledEnergyFeature r a =
      Real.exp (-2 * a * r) * (1 - Real.exp (-2 * a * r)) *
        (1 - Real.exp (-2 * r) * Real.exp (-2 * a * r)) *
          (Real.exp (-2 * a * r) - Real.exp (-2 * r)) := by
  rw [fourShiftGammaCancelledEnergyFeature,
    fourShiftGammaCancelledPolynomial_factor]

theorem fourShiftGammaCancelledEnergyFeature_zero (r : ℝ) :
    fourShiftGammaCancelledEnergyFeature r 0 = 0 := by
  rw [fourShiftGammaCancelledEnergyFeature_eq_factor]
  norm_num

theorem fourShiftGammaCancelledEnergyFeature_pos
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < fourShiftGammaCancelledEnergyFeature r a := by
  rw [fourShiftGammaCancelledEnergyFeature_eq_factor]
  have hx0 : 0 < Real.exp (-2 * a * r) := Real.exp_pos _
  have hx1 : Real.exp (-2 * a * r) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hq1 : Real.exp (-2 * r) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hqx1 : Real.exp (-2 * r) * Real.exp (-2 * a * r) < 1 := by
    calc
      Real.exp (-2 * r) * Real.exp (-2 * a * r) <
          1 * Real.exp (-2 * a * r) :=
        mul_lt_mul_of_pos_right hq1 hx0
      _ < 1 := by simpa using hx1
  have hqx : Real.exp (-2 * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  positivity

theorem centeredRealSourceShiftEnergyGain_nat_mul
    (n : ℕ) (r : ℝ) (z : ℂ) :
    centeredRealSourceShiftEnergyGain (n * r) z =
      centeredRealSourceShiftEnergyGain r z ^ n := by
  rw [centeredRealSourceShiftEnergyGain_eq_exp,
    centeredRealSourceShiftEnergyGain_eq_exp, ← Real.exp_nat_mul]
  congr 1
  ring

theorem fourShiftGammaCancelledEnergyFeature_eq_sourceEnergy
    (r : ℝ) (z : ℂ) :
    fourShiftGammaCancelledEnergyFeature r (-z.im) =
      -Real.exp (-2 * r) * centeredRealSourceShiftEnergyGain r z +
        (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
          centeredRealSourceShiftEnergyGain (2 * r) z -
        (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
          centeredRealSourceShiftEnergyGain (3 * r) z +
        Real.exp (-2 * r) * centeredRealSourceShiftEnergyGain (4 * r) z := by
  rw [fourShiftGammaCancelledEnergyFeature,
    fourShiftGammaCancelledPolynomial,
    show Real.exp (-2 * -z.im * r) =
        centeredRealSourceShiftEnergyGain r z by
      rw [centeredRealSourceShiftEnergyGain_eq_exp]
      congr 1
      ring,
    show centeredRealSourceShiftEnergyGain (2 * r) z =
        centeredRealSourceShiftEnergyGain r z ^ 2 by
      simpa using centeredRealSourceShiftEnergyGain_nat_mul 2 r z,
    show centeredRealSourceShiftEnergyGain (3 * r) z =
        centeredRealSourceShiftEnergyGain r z ^ 3 by
      simpa using centeredRealSourceShiftEnergyGain_nat_mul 3 r z,
    show centeredRealSourceShiftEnergyGain (4 * r) z =
        centeredRealSourceShiftEnergyGain r z ^ 4 by
      simpa using centeredRealSourceShiftEnergyGain_nat_mul 4 r z]

theorem fourShiftGammaCancelledCoefficient_sum (q : ℝ) :
    -q + (1 + q + q ^ 2) - (1 + q + q ^ 2) + q = 0 := by ring

theorem fourShiftGammaCancelledCoefficient_qsum (q : ℝ) :
    (-q) * q + (1 + q + q ^ 2) * q ^ 2 -
      (1 + q + q ^ 2) * q ^ 3 + q * q ^ 4 = 0 := by ring

theorem norm_criticalShiftSymbol_sq_of_nonneg
    {L x : ℝ} (hL : 0 ≤ L) (hx : 0 ≤ x) :
    ‖criticalShiftSymbol L x‖ ^ 2 = Real.exp (-2 * L) := by
  rw [norm_criticalShiftSymbol_sq, radialRiggingShiftEnergyRatio]
  simp only [radialRiggingWeight, one_mul]
  rw [abs_of_nonneg hx, abs_of_nonneg (add_nonneg hx hL)]
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem norm_criticalShiftSymbol_sq_of_add_nonpos
    {L x : ℝ} (hL : 0 ≤ L) (hx : x + L ≤ 0) :
    ‖criticalShiftSymbol L x‖ ^ 2 = 1 := by
  have hx0 : x ≤ 0 := le_trans (by linarith : x ≤ x + L) hx
  rw [norm_criticalShiftSymbol_sq, radialRiggingShiftEnergyRatio]
  simp only [radialRiggingWeight, one_mul]
  rw [abs_of_nonpos hx0, abs_of_nonpos hx]
  rw [div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  rw [show -L + -x + -(-(x + L)) = 0 by ring, Real.exp_zero]

def fourShiftCriticalSymbolEnergyCurrent (r x : ℝ) : ℝ :=
  -Real.exp (-2 * r) * ‖criticalShiftSymbol r x‖ ^ 2 +
    (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
      ‖criticalShiftSymbol (2 * r) x‖ ^ 2 -
    (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
      ‖criticalShiftSymbol (3 * r) x‖ ^ 2 +
    Real.exp (-2 * r) * ‖criticalShiftSymbol (4 * r) x‖ ^ 2

theorem fourShiftCriticalSymbolEnergyCurrent_rightTail
    {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    fourShiftCriticalSymbolEnergyCurrent r x = 0 := by
  rw [fourShiftCriticalSymbolEnergyCurrent,
    norm_criticalShiftSymbol_sq_of_nonneg hr hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 2 * r) hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 3 * r) hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 4 * r) hx]
  have h2 : Real.exp (-2 * (2 * r)) = Real.exp (-2 * r) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-2 * (3 * r)) = Real.exp (-2 * r) ^ 3 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : Real.exp (-2 * (4 * r)) = Real.exp (-2 * r) ^ 4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h2, h3, h4]
  exact fourShiftGammaCancelledCoefficient_qsum (Real.exp (-2 * r))

theorem fourShiftCriticalSymbolEnergyCurrent_leftTail
    {r x : ℝ} (hr : 0 ≤ r) (hx : x + 4 * r ≤ 0) :
    fourShiftCriticalSymbolEnergyCurrent r x = 0 := by
  rw [fourShiftCriticalSymbolEnergyCurrent,
    norm_criticalShiftSymbol_sq_of_add_nonpos hr (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) hx]
  simpa using fourShiftGammaCancelledCoefficient_sum (Real.exp (-2 * r))

def fourShiftCriticalEvaluationEnergyCurrent
    (r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hz : |z.im| < 1 / 2)
    (f : CriticalL2) : ℝ :=
  -Real.exp (-2 * r) * (Real.exp r * Complex.normSq
    (criticalEvaluation z hz (criticalShift r hr f))) +
  (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
    (Real.exp (2 * r) * Complex.normSq
      (criticalEvaluation z hz
        (criticalShift (2 * r) (by nlinarith) f))) -
  (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
    (Real.exp (3 * r) * Complex.normSq
      (criticalEvaluation z hz
        (criticalShift (3 * r) (by nlinarith) f))) +
  Real.exp (-2 * r) * (Real.exp (4 * r) * Complex.normSq
    (criticalEvaluation z hz
      (criticalShift (4 * r) (by nlinarith) f)))

theorem fourShiftCriticalEvaluationEnergyCurrent_eq
    (r : ℝ) (hr : 0 ≤ r) (z : ℂ) (hz : |z.im| < 1 / 2)
    (f : CriticalL2) :
    fourShiftCriticalEvaluationEnergyCurrent r hr z hz f =
      fourShiftGammaCancelledEnergyFeature r (-z.im) *
        Complex.normSq (criticalEvaluation z hz f) := by
  rw [fourShiftCriticalEvaluationEnergyCurrent,
    criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    criticalEvaluation_criticalShift,
    Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_mul, Complex.normSq_mul]
  have henergy (L : ℝ) :
      Real.exp L * (Complex.normSq (normalizedRealSourceShiftMultiplier L z) *
          Complex.normSq (criticalEvaluation z hz f)) =
        centeredRealSourceShiftEnergyGain L z *
          Complex.normSq (criticalEvaluation z hz f) := by
    rw [centeredRealSourceShiftEnergyGain]
    ring
  rw [henergy r, henergy (2 * r), henergy (3 * r), henergy (4 * r)]
  change
    -Real.exp (-2 * r) *
          (centeredRealSourceShiftEnergyGain r z *
            Complex.normSq (criticalEvaluation z hz f)) +
        (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
          (centeredRealSourceShiftEnergyGain (2 * r) z *
            Complex.normSq (criticalEvaluation z hz f)) -
        (1 + Real.exp (-2 * r) + Real.exp (-2 * r) ^ 2) *
          (centeredRealSourceShiftEnergyGain (3 * r) z *
            Complex.normSq (criticalEvaluation z hz f)) +
        Real.exp (-2 * r) *
          (centeredRealSourceShiftEnergyGain (4 * r) z *
            Complex.normSq (criticalEvaluation z hz f)) = _
  rw [fourShiftGammaCancelledEnergyFeature_eq_sourceEnergy]
  ring

theorem fourShiftGammaCancelledEnergyFeature_abs_le
    {r lambda : ℝ} (hr : 0 ≤ r) (hlambda : 1 ≤ lambda) :
    |fourShiftGammaCancelledEnergyFeature r lambda| ≤
      Real.exp (-2 * lambda * r) := by
  rw [fourShiftGammaCancelledEnergyFeature_eq_factor]
  have hq0 : 0 < Real.exp (-2 * r) := Real.exp_pos _
  have hx0 : 0 < Real.exp (-2 * lambda * r) := Real.exp_pos _
  have hq1 : Real.exp (-2 * r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hxq : Real.exp (-2 * lambda * r) ≤ Real.exp (-2 * r) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hx1 : Real.exp (-2 * lambda * r) ≤ 1 := hxq.trans hq1
  have hqx1 : Real.exp (-2 * r) * Real.exp (-2 * lambda * r) ≤ 1 := by
    calc
      Real.exp (-2 * r) * Real.exp (-2 * lambda * r) ≤
          1 * Real.exp (-2 * lambda * r) :=
        mul_le_mul_of_nonneg_right hq1 hx0.le
      _ ≤ 1 := by simpa using hx1
  have hqx0 : 0 ≤ Real.exp (-2 * r) * Real.exp (-2 * lambda * r) :=
    mul_nonneg hq0.le hx0.le
  rw [abs_mul, abs_mul, abs_mul,
    abs_of_nonneg hx0.le,
    abs_of_nonneg (sub_nonneg.mpr hx1),
    abs_of_nonneg (sub_nonneg.mpr hqx1),
    abs_of_nonpos (sub_nonpos.mpr hxq), neg_sub]
  calc
    Real.exp (-2 * lambda * r) *
          (1 - Real.exp (-2 * lambda * r)) *
          (1 - Real.exp (-2 * r) * Real.exp (-2 * lambda * r)) *
          (Real.exp (-2 * r) - Real.exp (-2 * lambda * r)) ≤
        Real.exp (-2 * lambda * r) * 1 * 1 * 1 := by
      gcongr <;> linarith
    _ = Real.exp (-2 * lambda * r) := by ring

def fourShiftGammaCancelledSelfEnergy (a : ℝ) : ℝ :=
  ∫ r : ℝ in Ioi 0,
    r ^ 2 * fourShiftGammaCancelledEnergyFeature r a ^ 2

private theorem integral_fourShift_cubic_majorant {lambda : ℝ}
    (hlambda : 0 < lambda) :
    (∫ r : ℝ in Ioi 0, r ^ 2 * Real.exp (-(4 * lambda * r))) =
      1 / (32 * lambda ^ 3) := by
  have hrate : 0 < 4 * lambda := mul_pos (by norm_num) hlambda
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := 4 * lambda) (by norm_num) hrate
  simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two] at h
  have hgamma : Real.Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
      Real.Gamma_nat_eq_factorial]
    norm_num
  rw [hgamma] at h
  norm_num at h ⊢
  rw [show (fun r : ℝ => r ^ 2 * Real.exp (-(4 * lambda * r))) =
      fun r : ℝ => r ^ 2 * Real.exp (-((4 * lambda) * r)) by
    funext r
    rfl, h]
  field_simp [hlambda.ne']
  ring

private theorem integrableOn_fourShift_cubic_majorant {lambda : ℝ}
    (hlambda : 0 < lambda) :
    IntegrableOn (fun r : ℝ => r ^ 2 * Real.exp (-(4 * lambda * r)))
      (Ioi 0) := by
  have hvalue := integral_fourShift_cubic_majorant hlambda
  have hne : (∫ r : ℝ in Ioi 0,
      r ^ 2 * Real.exp (-(4 * lambda * r))) ≠ 0 := by
    rw [hvalue]
    positivity
  exact Integrable.of_integral_ne_zero hne

theorem fourShiftGammaCancelledSelfEnergy_le
    {lambda : ℝ} (hlambda : 1 ≤ lambda) :
    fourShiftGammaCancelledSelfEnergy lambda ≤
      1 / (32 * lambda ^ 3) := by
  have hlambda0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hmajor := integrableOn_fourShift_cubic_majorant hlambda0
  have hpoint (r : ℝ) (hr : 0 ≤ r) :
      r ^ 2 * fourShiftGammaCancelledEnergyFeature r lambda ^ 2 ≤
        r ^ 2 * Real.exp (-(4 * lambda * r)) := by
    have habs := fourShiftGammaCancelledEnergyFeature_abs_le hr hlambda
    have hsq : fourShiftGammaCancelledEnergyFeature r lambda ^ 2 ≤
        Real.exp (-2 * lambda * r) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have hexp : Real.exp (-2 * lambda * r) ^ 2 =
        Real.exp (-(4 * lambda * r)) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hsq
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg r)
  have hcurrent : IntegrableOn (fun r : ℝ =>
      r ^ 2 * fourShiftGammaCancelledEnergyFeature r lambda ^ 2) (Ioi 0) := by
    apply hmajor.mono'
    · apply Continuous.aestronglyMeasurable
      unfold fourShiftGammaCancelledEnergyFeature
        fourShiftGammaCancelledPolynomial
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hnon : 0 ≤ r ^ 2 *
          fourShiftGammaCancelledEnergyFeature r lambda ^ 2 := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      exact hpoint r hr.le
  rw [fourShiftGammaCancelledSelfEnergy,
    ← integral_fourShift_cubic_majorant hlambda0]
  apply MeasureTheory.integral_mono_ae hcurrent hmajor
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact hpoint r hr.le

end

end RHTower
