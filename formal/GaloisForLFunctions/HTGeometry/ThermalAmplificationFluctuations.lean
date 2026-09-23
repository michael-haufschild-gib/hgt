import GaloisForLFunctions.HTGeometry.ThermalStepAmplification
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability

/-!
# Occupation fluctuations, Fisher information, and charged-step amplification

The thermal calibration of the signed-channel mechanism in arXiv:2608.21406
connects the actual step reflection amplitude to the corpus's geometric
occupation law. Reusing the Euler valuation variance theorem, we identify its
infinite centered variance, the derivative of reflection, and the Fisher
information computed from derivatives of the actual logarithmic probabilities.
These identities concern the explicit calibrated step, not an arbitrary
black-hole scattering coefficient.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Actual infinite mean occupation. -/
def radiationNumberMean (tau : ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * radiationMass tau n

/-- Actual centered second moment of the complete occupation distribution. -/
def radiationNumberVariance (tau : ℝ) : ℝ :=
  ∑' n : ℕ, radiationMass tau n * ((n : ℝ) - radiationNumberMean tau) ^ (2 : ℕ)

/-- Statistical score from the derivative of each actual logarithmic probability. -/
def radiationLogScore (tau : ℝ) (n : ℕ) : ℝ :=
  deriv (fun s => Real.log (radiationMass s n)) tau

/-- Fisher information in the real inverse-scale parameter. -/
def radiationNumberFisher (tau : ℝ) : ℝ :=
  ∑' n : ℕ, radiationMass tau n * radiationLogScore tau n ^ (2 : ℕ)

theorem radiationNumberMean_formula (tau : ℝ) :
    radiationNumberMean tau = thermalRatio tau / (1 - thermalRatio tau) :=
  (radiationMass_mean tau).tsum_eq

/-- The thermal occupation measure is the corpus Euler conditional valuation measure. -/
theorem radiationMass_eq_euler_valuation (tau : ℝ) :
    radiationMass tau = RHTower.diagonalActivationConditionalValuationMass (thermalRatio tau) := rfl

/-- The complete centered variance series converges, by the existing Euler valuation theorem. -/
theorem radiationNumberVariance_hasSum (tau : ℝ) :
    HasSum (fun n : ℕ => radiationMass tau n * ((n : ℝ) - radiationNumberMean tau)^(2 : ℕ))
      (thermalRatio tau / (1 - thermalRatio tau)^(2 : ℕ)) := by
  have h := RHTower.hasSum_diagonalActivationConditionalValuationMass_mul_score_sq
    (thermalRatio_pos tau).le (thermalRatio_lt_one tau)
  apply h.congr_fun
  intro n
  rw [radiationMass_eq_euler_valuation, radiationNumberMean_formula]
  unfold RHTower.diagonalActivationValuationScore
  ring

theorem radiationNumberVariance_formula (tau : ℝ) :
    radiationNumberVariance tau = thermalRatio tau / (1 - thermalRatio tau)^(2 : ℕ) :=
  (radiationNumberVariance_hasSum tau).tsum_eq

theorem radiationNumberVariance_pos (tau : ℝ) : 0 < radiationNumberVariance tau := by
  rw [radiationNumberVariance_formula]
  exact div_pos (thermalRatio_pos tau) (sq_pos_of_pos (sub_pos.mpr (thermalRatio_lt_one tau)))

/-- Exact bosonic fluctuation law, with both mean and variance defined by infinite expectations. -/
theorem radiationNumberVariance_bose (tau : ℝ) :
    radiationNumberVariance tau = radiationNumberMean tau * (1 + radiationNumberMean tau) := by
  rw [radiationNumberVariance_formula, radiationNumberMean_formula]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

/-- Reflection determines the centered thermal fluctuation exactly. -/
theorem thermalStepReflection_variance (e tau : ℝ) :
    thermalStepReflection e tau ^ (2 : ℕ) - thermalStepReflection e tau = radiationNumberVariance tau := by
  rw [thermalStepReflection_formula, radiationNumberVariance_formula]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne']
  ring

/-- Excess reflected power decomposes into the actual occupation variance and mean. -/
theorem thermalStepReflection_gain_decomposition (e tau : ℝ) :
    thermalStepReflection e tau ^ (2 : ℕ) - 1 = radiationNumberVariance tau + radiationNumberMean tau := by
  rw [← thermalStepReflection_variance e tau]
  have h : thermalStepReflection e tau = 1 + radiationNumberMean tau := thermalStepReflection_occupation e tau
  linarith

/-- Purity determines the same centered fluctuation without truncating the density matrix. -/
theorem radiationNumberVariance_purity (tau : ℝ) :
    (∑' n, radiationMass tau n ^ (2 : ℕ))^(2 : ℕ) * (1 + 4 * radiationNumberVariance tau) = 1 := by
  rw [radiationMass_purity, radiationNumberVariance_formula]
  field_simp [(sub_pos.mpr (thermalRatio_lt_one tau)).ne',
    (show 1 + thermalRatio tau ≠ 0 by linarith [thermalRatio_pos tau])]
  ring

theorem thermalRatio_hasDerivAt (tau : ℝ) :
    HasDerivAt thermalRatio (-Real.exp tau * thermalRatio tau) tau := by
  have h : HasDerivAt thermalRatio (thermalRatio tau * -Real.exp tau) tau :=
    (Real.hasDerivAt_exp tau).neg.exp
  exact h.congr_deriv (by ring)

/-- The actual derivative of reflection is minus the thermal variance times the scale Jacobian. -/
theorem thermalStepReflection_hasDerivAt (e tau : ℝ) :
    HasDerivAt (thermalStepReflection e) (-Real.exp tau * radiationNumberVariance tau) tau := by
  rw [show thermalStepReflection e = (fun s => 1 / (1 - thermalRatio s)) from
    funext (thermalStepReflection_formula e), radiationNumberVariance_formula]
  have h : HasDerivAt (fun s => 1 / (1 - thermalRatio s))
      ((0 * (1 - thermalRatio tau) - 1 * (0 - -Real.exp tau * thermalRatio tau)) /
        (1 - thermalRatio tau)^(2 : ℕ)) tau :=
    (hasDerivAt_const tau (1 : ℝ)).div
      ((hasDerivAt_const tau (1 : ℝ)).sub (thermalRatio_hasDerivAt tau))
      (sub_pos.mpr (thermalRatio_lt_one tau)).ne'
  exact h.congr_deriv (by ring)

/-- Increasing inverse thermal scale strictly decreases amplification amplitude. -/
theorem thermalStepReflection_strictAnti (e : ℝ) : StrictAnti (thermalStepReflection e) := by
  apply strictAnti_of_deriv_neg
  intro tau
  rw [(thermalStepReflection_hasDerivAt e tau).deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos tau)) (radiationNumberVariance_pos tau)

/-- Increasing inverse thermal scale strictly decreases reflected power as well. -/
theorem thermalStepReflection_power_strictAnti (e : ℝ) :
    StrictAnti (fun tau => thermalStepReflection e tau ^ (2 : ℕ)) := by
  intro s t hst
  have h := thermalStepReflection_strictAnti e hst
  have hs := chargedStepReflection_gt_one (thermalStepA e s) (thermalStepB e s)
  have ht := chargedStepReflection_gt_one (thermalStepA e t) (thermalStepB e t)
  change 1 < thermalStepReflection e s at hs
  change 1 < thermalStepReflection e t at ht
  nlinarith

/-- Exact logarithmic mass, before taking the statistical score. -/
theorem radiationMass_log_formula (tau : ℝ) (n : ℕ) :
    Real.log (radiationMass tau n) = Real.log (1 - thermalRatio tau) - (n : ℝ) * Real.exp tau := by
  unfold radiationMass canonicalThermalMass
  rw [Real.log_mul (sub_pos.mpr (thermalRatio_lt_one tau)).ne' (pow_pos (thermalRatio_pos tau) n).ne',
    Real.log_pow]
  unfold thermalRatio
  rw [Real.log_exp]
  ring

/-- Every logarithmic probability is differentiated as an actual real function. -/
theorem radiationMass_log_hasDerivAt (tau : ℝ) (n : ℕ) :
    HasDerivAt (fun s => Real.log (radiationMass s n))
      (Real.exp tau * (radiationNumberMean tau - n)) tau := by
  rw [show (fun s => Real.log (radiationMass s n)) =
    (fun s => Real.log (1 - thermalRatio s) - (n : ℝ) * Real.exp s) from
      funext fun s => radiationMass_log_formula s n, radiationNumberMean_formula]
  have h : HasDerivAt (fun s => Real.log (1 - thermalRatio s) - (n : ℝ) * Real.exp s)
      ((0 - -Real.exp tau * thermalRatio tau) / (1 - thermalRatio tau) - (n : ℝ) * Real.exp tau) tau :=
    (((hasDerivAt_const tau (1 : ℝ)).sub (thermalRatio_hasDerivAt tau)).log
      (sub_pos.mpr (thermalRatio_lt_one tau)).ne').sub ((Real.hasDerivAt_exp tau).const_mul (n : ℝ))
  exact h.congr_deriv (by ring)

theorem radiationLogScore_formula (tau : ℝ) (n : ℕ) :
    radiationLogScore tau n = Real.exp tau * (radiationNumberMean tau - n) :=
  (radiationMass_log_hasDerivAt tau n).deriv

/-- The score is centered under the complete infinite occupation law. -/
theorem radiationLogScore_hasSum_zero (tau : ℝ) :
    HasSum (fun n : ℕ => radiationMass tau n * radiationLogScore tau n) 0 := by
  have h := (RHTower.hasSum_diagonalActivationConditionalValuationMass_mul_score
    (thermalRatio_pos tau).le (thermalRatio_lt_one tau)).mul_left (Real.exp tau)
  simp only [mul_zero] at h
  apply h.congr_fun
  intro n
  rw [radiationMass_eq_euler_valuation, radiationLogScore_formula, radiationNumberMean_formula]
  unfold RHTower.diagonalActivationValuationScore
  ring

/-- The infinite squared-score series converges to the scaled centered variance. -/
theorem radiationNumberFisher_hasSum (tau : ℝ) :
    HasSum (fun n : ℕ => radiationMass tau n * radiationLogScore tau n ^ (2 : ℕ))
      (Real.exp tau ^ (2 : ℕ) * radiationNumberVariance tau) := by
  rw [radiationNumberVariance_formula]
  apply ((radiationNumberVariance_hasSum tau).mul_left (Real.exp tau ^ (2 : ℕ))).congr_fun
  intro n
  rw [radiationLogScore_formula]
  ring

theorem radiationNumberFisher_formula (tau : ℝ) :
    radiationNumberFisher tau = Real.exp tau ^ (2 : ℕ) * radiationNumberVariance tau :=
  (radiationNumberFisher_hasSum tau).tsum_eq

theorem radiationNumberFisher_pos (tau : ℝ) : 0 < radiationNumberFisher tau := by
  rw [radiationNumberFisher_formula]
  exact mul_pos (sq_pos_of_pos (Real.exp_pos tau)) (radiationNumberVariance_pos tau)

/-- Fisher information equals the actual amplification response with the exact coordinate factor. -/
theorem thermalStepReflection_fisher_response (e tau : ℝ) :
    radiationNumberFisher tau = -Real.exp tau * deriv (thermalStepReflection e) tau := by
  rw [radiationNumberFisher_formula, (thermalStepReflection_hasDerivAt e tau).deriv]
  ring

end GaloisForLFunctions.HTGeometry.CPV
