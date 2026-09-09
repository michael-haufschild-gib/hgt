import GaloisForLFunctions.HTGeometry.ConservativeDissipativeThermalPopulationTree
import GaloisForLFunctions.HTGeometry.GADCTreePopulationRG

/-!
# Exact rational GADC realization by thermal Kraus evolution

The dissipation mechanism of arXiv:2609.04530 is applied through the thermal
semigroup constructed in this corpus. Rational coordinates construct admissible
damping and bath populations. A logarithmic physical time calibrates the exact
analytic survival to rational survival, so the existing GADC homogeneous tree
map and its polynomial multiplier are literal measurements and derivatives of
that quantum dynamics. No numerical exponential evaluation is used.
-/

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- A rational damping or bath population constructed strictly below one. -/
def spinRationalPopulation (q : ℚ) : ℚ := q ^ 2 / (1 + q ^ 2)

/-- Every unrestricted rational coordinate constructs an admissible population. -/
theorem spinRationalPopulation_bounds (q : ℚ) : 0 ≤ spinRationalPopulation q ∧ spinRationalPopulation q < 1 := by
  unfold spinRationalPopulation
  constructor
  · positivity
  · apply (div_lt_one (by positivity : 0 < 1 + q ^ 2)).mpr
    linarith

/-- A physical time whose exact surviving population is rational. -/
def spinThermalCalibrationTime (s : ℝ) (q : ℚ) : NNReal :=
  ⟨Real.log (1 + (q : ℝ) ^ 2) / (2 * (Real.exp s) ^ 2),
    div_nonneg (Real.log_nonneg (by linarith [sq_nonneg (q : ℝ)])) (by positivity)⟩

/-- Exact calibration of the analytic exponential decay without evaluating a numerical exponential. -/
theorem spinThermalCalibration_mass (s : ℝ) (q : ℚ) :
    spinDecayMass (Real.exp s) (spinThermalCalibrationTime s q) = (1 + (q : ℝ) ^ 2)⁻¹ := by
  change Real.exp (-2 * (Real.exp s) ^ 2 * (Real.log (1 + (q : ℝ) ^ 2) / (2 * (Real.exp s) ^ 2))) = (1 + (q : ℝ) ^ 2)⁻¹
  have h : -2 * Real.exp s ^ 2 * (Real.log (1 + (q : ℝ) ^ 2) / (2 * Real.exp s ^ 2)) =
      -Real.log (1 + (q : ℝ) ^ 2) := by
    field_simp
  rw [h, Real.exp_neg, Real.exp_log (by positivity : 0 < 1 + (q : ℝ) ^ 2)]

/-- The calibrated analytic survival equals the rational GADC survival. -/
theorem spinThermalCalibration_survival (s : ℝ) (q : ℚ) :
    spinDecayMass (Real.exp s) (spinThermalCalibrationTime s q) = ((1 - spinRationalPopulation q : ℚ) : ℝ) := by
  rw [spinThermalCalibration_mass]
  unfold spinRationalPopulation
  push_cast
  field_simp
  ring

/-- The actual stationary lower population is the chosen rational GADC bath parameter. -/
theorem spinBathLower_rational (r : ℚ) : spinBathLower (r : ℝ) = (spinRationalPopulation r : ℝ) := by
  unfold spinBathLower spinBathUpper spinMixRadius spinRationalPopulation
  push_cast
  field_simp
  ring

/-- The complementary stationary population is also exact under scalar extension. -/
theorem spinBathUpper_rational (r : ℚ) : spinBathUpper (r : ℝ) = ((1 - spinRationalPopulation r : ℚ) : ℝ) := by
  have h := spinBathLower_rational r
  unfold spinBathLower at h
  push_cast
  linarith

/-- The existing rational positive-input probability is a literal measurement of a four-Kraus channel. -/
theorem spinThermalPositiveProbability_gadc (s : ℝ) (q r : ℚ) :
    spinThermalPositiveProbability (Real.exp s) (r : ℝ) (spinThermalCalibrationTime s q) =
      (gadcPositiveOutputProbability (spinRationalPopulation q) (spinRationalPopulation r) : ℝ) := by
  rw [spinThermalPositiveProbability_eq, spinThermalCalibration_survival, spinBathLower_rational]
  unfold gadcPositiveOutputProbability
  push_cast
  ring

/-- The rational negative-input probability is measured in that same quantum channel. -/
theorem spinThermalNegativeProbability_gadc (s : ℝ) (q r : ℚ) :
    spinThermalNegativeProbability (Real.exp s) (r : ℝ) (spinThermalCalibrationTime s q) =
      (gadcNegativeOutputProbability (spinRationalPopulation q) (spinRationalPopulation r) : ℝ) := by
  rw [spinThermalNegativeProbability_eq, spinThermalCalibration_survival, spinBathUpper_rational]
  unfold gadcNegativeOutputProbability
  push_cast
  ring

/-- Exact scalar-extension bridge from the old rational tree model to measured quantum dynamics. -/
theorem spinThermalTreeBP_gadc (p : ℕ) (s : ℝ) (q r y : ℚ) :
    spinThermalTreeBP p (Real.exp s) (r : ℝ) (spinThermalCalibrationTime s q) (y : ℝ) =
      (gadcHomogeneousPopulationBP p (spinRationalPopulation q) (spinRationalPopulation r) y : ℝ) := by
  rw [spinThermalTreeBP, spinThermalPositiveProbability_gadc, spinThermalNegativeProbability_gadc,
    gadcHomogeneousPopulationBP_eq, gadcPositiveSignal_eq_probability, gadcNegativeSignal_eq_probability]
  push_cast
  rfl

/-- The old polynomial multiplier is the derivative of the physically realized real recursion. -/
theorem spinThermalTree_deriv_gadc (p : ℕ) (s : ℝ) (q r : ℚ) :
    deriv (spinThermalTreeBP p (Real.exp s) (r : ℝ) (spinThermalCalibrationTime s q)) 0 =
      (((Polynomial.derivative (asymmetricBinaryTreeNumerator p
          (gadcPositiveSignal (spinRationalPopulation q) (spinRationalPopulation r))
          (gadcNegativeSignal (spinRationalPopulation q) (spinRationalPopulation r)))).eval 0 /
        (asymmetricBinaryTreeDenominator p
          (gadcPositiveSignal (spinRationalPopulation q) (spinRationalPopulation r))
          (gadcNegativeSignal (spinRationalPopulation q) (spinRationalPopulation r))).eval 0 : ℚ) : ℝ) := by
  rw [deriv_spinThermalTreeBP, spinThermalCalibration_survival, gadcTreePopulation_linearMultiplier]
  push_cast
  rfl

/-- The corpus's rational damping threshold governs the measured channel's analytic derivative. -/
theorem spinThermalTree_gadc_lt_one_iff (n : ℕ) (s : ℝ) (q r : ℚ) :
    deriv (spinThermalTreeBP (n + 1) (Real.exp s) (r : ℝ) (spinThermalCalibrationTime s q)) 0 < 1 ↔
      1 - 1 / ((n + 1 : ℕ) : ℚ) < spinRationalPopulation q := by
  rw [deriv_spinThermalTreeBP, spinThermalCalibration_survival]
  have h := gadcMultiplier_lt_one_iff (Nat.zero_lt_succ n) (spinRationalPopulation q)
  exact_mod_cast h

/-- Neutral response also matches the exact rational threshold, with positive branching constructed. -/
theorem spinThermalTree_gadc_eq_one_iff (n : ℕ) (s : ℝ) (q r : ℚ) :
    deriv (spinThermalTreeBP (n + 1) (Real.exp s) (r : ℝ) (spinThermalCalibrationTime s q)) 0 = 1 ↔
      spinRationalPopulation q = 1 - 1 / ((n + 1 : ℕ) : ℚ) := by
  rw [deriv_spinThermalTreeBP, spinThermalCalibration_survival]
  have h := gadcMultiplier_eq_one_iff (Nat.zero_lt_succ n) (spinRationalPopulation q)
  exact_mod_cast h

/-- A rational symmetric bath identifies the physically realized algebraic model with the Ising tree family. -/
theorem spinThermalTree_gadc_balancedBath (p : ℕ) (q : ℚ) :
    gadcTreePopulationRG p (spinRationalPopulation q) (spinRationalPopulation 1) =
      betheHolographicIsingRG p (1 - spinRationalPopulation q) := by
  have h : spinRationalPopulation 1 = 1 / 2 := by unfold spinRationalPopulation; ring
  rw [h, gadcTreePopulationRG_balancedBath]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
