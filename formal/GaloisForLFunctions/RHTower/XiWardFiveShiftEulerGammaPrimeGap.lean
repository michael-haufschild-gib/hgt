import GaloisForLFunctions.RHTower.XiWardCubicFourShiftGammaQuantitative

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

open HedenmalmThetaSource

def fiveShiftEulerGammaPolynomial (q t u x : ℝ) : ℝ :=
  x * (1 - x) * (x - t) * (x - q) * (x - u)

theorem fiveShiftEulerGammaPolynomial_eq_coefficients (q t u x : ℝ) :
    fiveShiftEulerGammaPolynomial q t u x =
      -(t * q * u) * x +
      (t * q + t * u + q * u + t * q * u) * x ^ (2 : ℕ) -
      (t + q + u + t * q + t * u + q * u) * x ^ (3 : ℕ) +
      (1 + t + q + u) * x ^ (4 : ℕ) - x ^ (5 : ℕ) := by
  rw [fiveShiftEulerGammaPolynomial]
  ring

def fiveShiftEulerGammaFeature (r a : ℝ) : ℝ :=
  fiveShiftEulerGammaPolynomial
    (Real.exp (-2 * r))
    (Real.exp (-(6 / 5 : ℝ) * r))
    (Real.exp (-(21 / 10 : ℝ) * r))
    (Real.exp (-2 * a * r))

theorem fiveShiftEulerGammaFeature_zero (r : ℝ) :
    fiveShiftEulerGammaFeature r 0 = 0 := by
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  norm_num

theorem fiveShiftEulerGammaFeature_pos
    {r a : ℝ} (hr : 0 < r) (ha0 : 0 < a) (ha : a ≤ 1 / 2) :
    0 < fiveShiftEulerGammaFeature r a := by
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  have hx0 : 0 < Real.exp (-2 * a * r) := Real.exp_pos _
  have hx1 : Real.exp (-2 * a * r) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    have har := mul_pos ha0 hr
    nlinarith
  have htx : Real.exp (-(6 / 5 : ℝ) * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    have har : 2 * a * r ≤ r := by
      have := mul_le_mul_of_nonneg_right ha hr.le
      nlinarith
    nlinarith
  have hqx : Real.exp (-2 * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    have har : 2 * a * r ≤ r := by
      have := mul_le_mul_of_nonneg_right ha hr.le
      nlinarith
    nlinarith
  have hux : Real.exp (-(21 / 10 : ℝ) * r) < Real.exp (-2 * a * r) := by
    apply Real.exp_lt_exp.mpr
    have har : 2 * a * r ≤ r := by
      have := mul_le_mul_of_nonneg_right ha hr.le
      nlinarith
    nlinarith
  positivity

theorem fiveShiftEulerGammaFeature_nonpos_of_firstPrimeGap
    {r lambda : ℝ} (hr : 0 ≤ r)
    (hlower : 3 / 5 < lambda) (hupper : lambda < 1) :
    fiveShiftEulerGammaFeature r lambda ≤ 0 := by
  by_cases hr0 : r = 0
  · subst r
    simp [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  have hx0 : 0 < Real.exp (-2 * lambda * r) := Real.exp_pos _
  have hx1 : Real.exp (-2 * lambda * r) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (by linarith : 0 < lambda) hrp]
  have hxt : Real.exp (-2 * lambda * r) <
      Real.exp (-(6 / 5 : ℝ) * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (sub_pos.mpr hlower) hrp]
  have hqx : Real.exp (-2 * r) < Real.exp (-2 * lambda * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (sub_pos.mpr hupper) hrp]
  have huq : Real.exp (-(21 / 10 : ℝ) * r) < Real.exp (-2 * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith
  have hxu : Real.exp (-(21 / 10 : ℝ) * r) <
      Real.exp (-2 * lambda * r) := huq.trans hqx
  have hnon : 0 ≤ Real.exp (-2 * lambda * r) *
      (1 - Real.exp (-2 * lambda * r)) *
      (Real.exp (-2 * lambda * r) - Real.exp (-2 * r)) *
      (Real.exp (-2 * lambda * r) - Real.exp (-(21 / 10 : ℝ) * r)) := by
    positivity
  nlinarith

theorem fiveShiftEulerGammaFeature_nonpos_of_laterPrimeGap
    {r lambda : ℝ} (hr : 0 ≤ r) (hlower : 21 / 20 < lambda) :
    fiveShiftEulerGammaFeature r lambda ≤ 0 := by
  by_cases hr0 : r = 0
  · subst r
    simp [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial]
  have hx0 : 0 < Real.exp (-2 * lambda * r) := Real.exp_pos _
  have hx1 : Real.exp (-2 * lambda * r) < 1 := by
    rw [← Real.exp_zero]
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (by linarith : 0 < lambda) hrp]
  have hxt : Real.exp (-2 * lambda * r) <
      Real.exp (-(6 / 5 : ℝ) * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (by linarith : 0 < lambda - 3 / 5) hrp]
  have hxq : Real.exp (-2 * lambda * r) < Real.exp (-2 * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (by linarith : 0 < lambda - 1) hrp]
  have hxu : Real.exp (-2 * lambda * r) <
      Real.exp (-(21 / 10 : ℝ) * r) := by
    apply Real.exp_lt_exp.mpr
    nlinarith [mul_pos (sub_pos.mpr hlower) hrp]
  have hnon : 0 ≤ Real.exp (-2 * lambda * r) *
      (1 - Real.exp (-2 * lambda * r)) *
      (Real.exp (-(6 / 5 : ℝ) * r) - Real.exp (-2 * lambda * r)) *
      (Real.exp (-2 * r) - Real.exp (-2 * lambda * r)) *
      (Real.exp (-(21 / 10 : ℝ) * r) - Real.exp (-2 * lambda * r)) := by
    positivity
  nlinarith

theorem fiveShiftEulerGammaFeature_vonMangoldt_nonpos
    {r : ℝ} (hr : 0 ≤ r) {n : ℕ} (hn : 2 ≤ n) :
    fiveShiftEulerGammaFeature r (Real.log n) ≤ 0 := by
  by_cases hn2 : n = 2
  · subst n
    apply fiveShiftEulerGammaFeature_nonpos_of_firstPrimeGap hr
    · linarith [Real.log_two_gt_d9]
    · norm_num
      exact Real.log_two_lt_d9.trans (by norm_num)
  · have hn3 : 3 ≤ n := by omega
    apply fiveShiftEulerGammaFeature_nonpos_of_laterPrimeGap hr
    have hlog3 : (21 / 20 : ℝ) < Real.log 3 := by
      linarith [Real.log_three_gt_d9]
    have hlogle : Real.log 3 ≤ Real.log n := by
      exact Real.log_le_log (by norm_num) (by exact_mod_cast hn3)
    exact hlog3.trans_le hlogle

/-- Finite literal von Mangoldt trace of the five-shift source current. -/
def finiteFiveShiftVonMangoldtTrace (M : ℕ) (r : ℝ) : ℝ :=
  ∑ n : Fin M,
    (ArithmeticFunction.vonMangoldt ((n : ℕ) + 2) / ((n : ℕ) + 2)) *
      fiveShiftEulerGammaFeature r (Real.log ((n : ℕ) + 2))

set_option maxHeartbeats 800000 in
/-- Every finite literal Euler trace has the opposite sign from a strict-right zero. -/
theorem finiteFiveShiftVonMangoldtTrace_nonpos
    (M : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    finiteFiveShiftVonMangoldtTrace M r ≤ 0 := by
  rw [finiteFiveShiftVonMangoldtTrace]
  apply Finset.sum_nonpos
  intro n hn
  have hfeature := fiveShiftEulerGammaFeature_vonMangoldt_nonpos
    hr (by omega : 2 ≤ (n : ℕ) + 2)
  exact mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hfeature)

theorem fiveShiftEulerGammaCoefficient_sum (q t u : ℝ) :
    -(t * q * u) + (t * q + t * u + q * u + t * q * u) -
      (t + q + u + t * q + t * u + q * u) +
      (1 + t + q + u) - 1 = 0 := by ring

theorem fiveShiftEulerGammaCoefficient_qsum (q t u : ℝ) :
    -(t * q * u) * q +
      (t * q + t * u + q * u + t * q * u) * q ^ (2 : ℕ) -
      (t + q + u + t * q + t * u + q * u) * q ^ (3 : ℕ) +
      (1 + t + q + u) * q ^ (4 : ℕ) - q ^ (5 : ℕ) = 0 := by ring

theorem fiveShiftEulerGammaFeature_eq_sourceEnergy (r : ℝ) (z : ℂ) :
    fiveShiftEulerGammaFeature r (-z.im) =
      -(Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) *
          Real.exp (-(21 / 10 : ℝ) * r)) *
        centeredRealSourceShiftEnergyGain r z +
      (Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-2 * r) * Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) *
            Real.exp (-(21 / 10 : ℝ) * r)) *
        centeredRealSourceShiftEnergyGain (2 * r) z -
      (Real.exp (-(6 / 5 : ℝ) * r) + Real.exp (-2 * r) +
          Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-2 * r) +
          Real.exp (-(6 / 5 : ℝ) * r) * Real.exp (-(21 / 10 : ℝ) * r) +
          Real.exp (-2 * r) * Real.exp (-(21 / 10 : ℝ) * r)) *
        centeredRealSourceShiftEnergyGain (3 * r) z +
      (1 + Real.exp (-(6 / 5 : ℝ) * r) + Real.exp (-2 * r) +
          Real.exp (-(21 / 10 : ℝ) * r)) *
        centeredRealSourceShiftEnergyGain (4 * r) z -
      centeredRealSourceShiftEnergyGain (5 * r) z := by
  rw [fiveShiftEulerGammaFeature, fiveShiftEulerGammaPolynomial_eq_coefficients]
  have hx : Real.exp (-2 * -z.im * r) =
      centeredRealSourceShiftEnergyGain r z := by
    rw [centeredRealSourceShiftEnergyGain_eq_exp]
    congr 1
    ring
  rw [hx]
  rw [show centeredRealSourceShiftEnergyGain (2 * r) z =
      centeredRealSourceShiftEnergyGain r z ^ (2 : ℕ) by
        simpa using centeredRealSourceShiftEnergyGain_nat_mul 2 r z,
    show centeredRealSourceShiftEnergyGain (3 * r) z =
      centeredRealSourceShiftEnergyGain r z ^ (3 : ℕ) by
        simpa using centeredRealSourceShiftEnergyGain_nat_mul 3 r z,
    show centeredRealSourceShiftEnergyGain (4 * r) z =
      centeredRealSourceShiftEnergyGain r z ^ (4 : ℕ) by
        simpa using centeredRealSourceShiftEnergyGain_nat_mul 4 r z,
    show centeredRealSourceShiftEnergyGain (5 * r) z =
      centeredRealSourceShiftEnergyGain r z ^ (5 : ℕ) by
        simpa using centeredRealSourceShiftEnergyGain_nat_mul 5 r z]

def fiveShiftCriticalSymbolEnergyCurrent (r x : ℝ) : ℝ :=
  let q := Real.exp (-2 * r)
  let t := Real.exp (-(6 / 5 : ℝ) * r)
  let u := Real.exp (-(21 / 10 : ℝ) * r)
  (-(t * q * u) * ‖criticalShiftSymbol r x‖ ^ (2 : ℕ) +
    (t * q + t * u + q * u + t * q * u) *
      ‖criticalShiftSymbol (2 * r) x‖ ^ (2 : ℕ) -
    (t + q + u + t * q + t * u + q * u) *
      ‖criticalShiftSymbol (3 * r) x‖ ^ (2 : ℕ) +
    (1 + t + q + u) * ‖criticalShiftSymbol (4 * r) x‖ ^ (2 : ℕ) -
    ‖criticalShiftSymbol (5 * r) x‖ ^ (2 : ℕ))

theorem fiveShiftCriticalSymbolEnergyCurrent_rightTail
    {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) :
    fiveShiftCriticalSymbolEnergyCurrent r x = 0 := by
  rw [fiveShiftCriticalSymbolEnergyCurrent]
  rw [norm_criticalShiftSymbol_sq_of_nonneg hr hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 2 * r) hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 3 * r) hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 4 * r) hx,
    norm_criticalShiftSymbol_sq_of_nonneg (by nlinarith : 0 ≤ 5 * r) hx]
  have h2 : Real.exp (-2 * (2 * r)) = Real.exp (-2 * r) ^ (2 : ℕ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have h3 : Real.exp (-2 * (3 * r)) = Real.exp (-2 * r) ^ (3 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : Real.exp (-2 * (4 * r)) = Real.exp (-2 * r) ^ (4 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h5 : Real.exp (-2 * (5 * r)) = Real.exp (-2 * r) ^ (5 : ℕ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h2, h3, h4, h5]
  exact fiveShiftEulerGammaCoefficient_qsum _ _ _

theorem fiveShiftCriticalSymbolEnergyCurrent_leftTail
    {r x : ℝ} (hr : 0 ≤ r) (hx : x + 5 * r ≤ 0) :
    fiveShiftCriticalSymbolEnergyCurrent r x = 0 := by
  rw [fiveShiftCriticalSymbolEnergyCurrent]
  rw [norm_criticalShiftSymbol_sq_of_add_nonpos hr (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) (by nlinarith),
    norm_criticalShiftSymbol_sq_of_add_nonpos (by nlinarith) hx]
  simpa using fiveShiftEulerGammaCoefficient_sum
    (Real.exp (-2 * r)) (Real.exp (-(6 / 5 : ℝ) * r))
      (Real.exp (-(21 / 10 : ℝ) * r))

theorem hasCompactSupport_fiveShiftCriticalSymbolEnergyCurrent
    {r : ℝ} (hr : 0 ≤ r) :
    HasCompactSupport (fiveShiftCriticalSymbolEnergyCurrent r) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -5 * r) (b := 0)) fun x hx => ?_
  rw [mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · rw [not_le] at hx
    apply fiveShiftCriticalSymbolEnergyCurrent_leftTail hr
    linarith
  · rw [not_le] at hx
    exact fiveShiftCriticalSymbolEnergyCurrent_rightTail hr hx.le

end

end RHTower
