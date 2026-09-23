import GaloisForLFunctions.HTGeometry.ThermalFisherClock

/-!
# Fisher time lost by a vacuum-versus-click observer

A geometric occupation law has nonvacuum probability `q`. Forgetting the
occupation count and retaining only that binary event reduces the Fisher
information by exactly `1-q`. Its accumulated clock is `2 arcsin (sqrt q)`,
which has a finite range, while the full-count clock is hyperbolic.
This realizes the measurement-model distinction in arXiv:2605.03958, §5.1.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- The probabilities of a click and of vacuum, in that order. -/
def radiationClickProbability (tau : ℝ) : Fin 2 → ℝ :=
  ![thermalRatio tau, 1 - thermalRatio tau]

/-- Exact statistical score of the binary observation. -/
def radiationClickScore (tau : ℝ) : Fin 2 → ℝ :=
  ![-Real.exp tau, Real.exp tau * thermalRatio tau / (1 - thermalRatio tau)]

def radiationClickFisher (tau : ℝ) : ℝ :=
  ∑ i, radiationClickProbability tau i * radiationClickScore tau i ^ (2 : ℕ)

/-- The click probability is the sum of all strictly positive occupations. -/
theorem radiationClickProbability_hasSum (tau : ℝ) :
    HasSum (fun n : ℕ => radiationMass tau (n + 1)) (thermalRatio tau) := by
  have h := (radiationMass_hasSum tau).mul_left (thermalRatio tau)
  simpa [radiationMass, canonicalThermalMass_succ, mul_one] using h

theorem radiationClickProbability_pos (tau : ℝ) (i : Fin 2) :
    0 < radiationClickProbability tau i := by
  fin_cases i
  · exact thermalRatio_pos tau
  · exact sub_pos.mpr (thermalRatio_lt_one tau)

theorem radiationClickProbability_sum (tau : ℝ) :
    ∑ i, radiationClickProbability tau i = 1 := by
  simp [radiationClickProbability, Fin.sum_univ_two]

/-- Scores are derivatives of actual logarithmic event probabilities. -/
theorem radiationClickScore_hasDerivAt (tau : ℝ) (i : Fin 2) :
    HasDerivAt (fun s => Real.log (radiationClickProbability s i))
      (radiationClickScore tau i) tau := by
  fin_cases i
  · have h := (thermalRatio_hasDerivAt tau).log (thermalRatio_pos tau).ne'
    apply h.congr_deriv
    change -Real.exp tau * thermalRatio tau / thermalRatio tau = -Real.exp tau
    field_simp [(thermalRatio_pos tau).ne']
  · have h := (((hasDerivAt_const tau (1 : ℝ)).sub (thermalRatio_hasDerivAt tau)).log
      (sub_pos.mpr (thermalRatio_lt_one tau)).ne')
    apply h.congr_deriv
    change (0 - -Real.exp tau * thermalRatio tau) / (1 - thermalRatio tau) =
      Real.exp tau * thermalRatio tau / (1 - thermalRatio tau)
    ring

theorem radiationClickScore_centered (tau : ℝ) :
    ∑ i, radiationClickProbability tau i * radiationClickScore tau i = 0 := by
  simp only [Fin.sum_univ_two, radiationClickProbability, radiationClickScore,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

theorem radiationClickFisher_formula (tau : ℝ) :
    radiationClickFisher tau = Real.exp tau ^ (2 : ℕ) * thermalRatio tau / (1 - thermalRatio tau) := by
  unfold radiationClickFisher
  simp only [Fin.sum_univ_two, radiationClickProbability, radiationClickScore,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

/-- Exact data-processing loss when a number-resolving observer becomes a click detector. -/
theorem radiationClickFisher_retention (tau : ℝ) :
    radiationClickFisher tau = (1 - thermalRatio tau) * radiationNumberFisher tau := by
  rw [radiationClickFisher_formula, radiationNumberFisher_formula, radiationNumberVariance_formula]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne']

theorem radiationClickFisher_strict_loss (tau : ℝ) :
    0 < radiationClickFisher tau ∧ radiationClickFisher tau < radiationNumberFisher tau := by
  rw [radiationClickFisher_retention]
  constructor
  · exact mul_pos (sub_pos.mpr (thermalRatio_lt_one tau)) (radiationNumberFisher_pos tau)
  · nlinarith [mul_pos (thermalRatio_pos tau) (radiationNumberFisher_pos tau)]

/-- Circular Fisher coordinate for the coarse binary observation. -/
def radiationClickClock (tau : ℝ) : ℝ := 2 * Real.arcsin (coherentRadius tau)

theorem radiationClickClock_speed (tau : ℝ) :
    Real.sqrt (radiationClickFisher tau) =
      Real.exp tau * coherentRadius tau / Real.sqrt (1 - thermalRatio tau) := by
  have hs := Real.sq_sqrt (sub_pos.mpr (thermalRatio_lt_one tau)).le
  have he : radiationClickFisher tau =
      (Real.exp tau * coherentRadius tau / Real.sqrt (1 - thermalRatio tau)) ^ (2 : ℕ) := by
    rw [radiationClickFisher_formula, div_pow, mul_pow, hs, coherentRadius_sq]
  rw [he, Real.sqrt_sq_eq_abs, abs_of_pos]
  exact div_pos (mul_pos (Real.exp_pos tau) (coherentRadius_pos tau))
    (Real.sqrt_pos.mpr (sub_pos.mpr (thermalRatio_lt_one tau)))

theorem radiationClickClock_hasDerivAt (tau : ℝ) :
    HasDerivAt radiationClickClock (-Real.sqrt (radiationClickFisher tau)) tau := by
  have h := ((Real.hasDerivAt_arcsin
    (by linarith [coherentRadius_pos tau] : coherentRadius tau ≠ -1)
    (coherentRadius_lt_one tau).ne).comp tau (coherentRadius_hasDerivAt tau)).const_mul 2
  apply h.congr_deriv
  rw [radiationClickClock_speed, coherentRadius_sq]
  ring

theorem radiationClickClock_bounds (tau : ℝ) :
    0 < radiationClickClock tau ∧ radiationClickClock tau < Real.pi := by
  have h0 := Real.arcsin_lt_arcsin (by norm_num : (-1 : ℝ) ≤ 0)
    (coherentRadius_pos tau) (coherentRadius_lt_one tau).le
  have h1 := Real.arcsin_lt_arcsin (by linarith [coherentRadius_pos tau] : -1 ≤ coherentRadius tau)
    (coherentRadius_lt_one tau) le_rfl
  simp only [Real.arcsin_zero, Real.arcsin_one] at h0 h1
  unfold radiationClickClock
  constructor <;> linarith

theorem radiationClickClock_strictAnti : StrictAnti radiationClickClock := by
  apply strictAnti_of_deriv_neg
  intro tau
  rw [(radiationClickClock_hasDerivAt tau).deriv]
  exact neg_neg_of_pos (Real.sqrt_pos.mpr (radiationClickFisher_strict_loss tau).1)

/-- The complete observed Fisher integral has an exact finite-angle primitive. -/
theorem radiationClickClock_integral (a b : ℝ) :
    (∫ tau : ℝ in a..b, Real.sqrt (radiationClickFisher tau)) =
      radiationClickClock a - radiationClickClock b := by
  have hc : Continuous (fun tau => Real.sqrt (radiationClickFisher tau)) := by
    simp_rw [radiationClickClock_speed]
    have hq : Continuous thermalRatio := Real.continuous_exp.comp Real.continuous_exp.neg
    exact (Real.continuous_exp.mul hq.sqrt).div (continuous_const.sub hq).sqrt
      (fun tau => (Real.sqrt_pos.mpr (sub_pos.mpr (thermalRatio_lt_one tau))).ne')
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun tau _ => radiationClickClock_hasDerivAt tau)
    (hc.neg.intervalIntegrable a b)
  rw [intervalIntegral.integral_neg] at h
  linarith

/-- Despite information loss, every finite source scale still has an exact calibration. -/
theorem radiationClickClock_calibration (tau : ℝ) :
    Real.log (-2 * Real.log (Real.sin (radiationClickClock tau / 2))) = tau := by
  rw [radiationClickClock, show 2 * Real.arcsin (coherentRadius tau) / 2 =
      Real.arcsin (coherentRadius tau) by ring,
    Real.sin_arcsin (by linarith [coherentRadius_pos tau]) (coherentRadius_lt_one tau).le,
    coherentRadius_exp, Real.log_exp]
  convert Real.log_exp tau using 1
  congr 1
  ring

end GaloisForLFunctions.HTGeometry.CPV
