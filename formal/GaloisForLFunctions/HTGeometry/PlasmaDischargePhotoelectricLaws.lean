import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Closed electrostatic, gas-discharge, and photoelectric scale laws

This module records unconditional algebraic forms of five physical laws. Positive dimensional
parameters use logarithmic coordinates, so positivity and nonvanishing are built into definitions
rather than carried as theorem hypotheses. Constants such as `4π`, permittivity, Boltzmann's
constant, and charge magnitudes are absorbed into named logarithmic scales.

The statements are structural identities only. They do not assign units or empirical constants.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Bjerrum and Debye lengths -/

/-- Bjerrum length in logarithmic coordinates, with electrostatic and thermal constants absorbed
into two positive scales. -/
def bjerrumLength (coulombLog thermalLog : ℝ) : ℝ :=
  Real.exp (coulombLog - thermalLog)

/-- Bjerrum length for two possibly different charge magnitudes, dielectric scale, and thermal
scale, all in logarithmic coordinates. -/
def bjerrumPairLength
    (charge₁Log charge₂Log dielectricLog thermalLog : ℝ) : ℝ :=
  Real.exp (charge₁Log + charge₂Log - dielectricLog - thermalLog)

/-- Coulomb energy at logarithmic separation, with geometric constants absorbed. -/
def coulombEnergyAtLogSeparation (coulombLog separationLog : ℝ) : ℝ :=
  Real.exp (coulombLog - separationLog)

theorem bjerrumLength_pos (coulombLog thermalLog : ℝ) :
    0 < bjerrumLength coulombLog thermalLog := Real.exp_pos _

theorem bjerrumPairLength_swap
    (charge₁Log charge₂Log dielectricLog thermalLog : ℝ) :
    bjerrumPairLength charge₁Log charge₂Log dielectricLog thermalLog =
      bjerrumPairLength charge₂Log charge₁Log dielectricLog thermalLog := by
  unfold bjerrumPairLength
  exact congrArg Real.exp (by ring)

theorem bjerrumPairLength_equalCharge
    (chargeLog dielectricLog thermalLog : ℝ) :
    bjerrumPairLength chargeLog chargeLog dielectricLog thermalLog =
      bjerrumLength (2 * chargeLog - dielectricLog) thermalLog := by
  unfold bjerrumPairLength bjerrumLength
  exact congrArg Real.exp (by ring)

theorem bjerrumPairLength_mul_dielectricThermalScale
    (charge₁Log charge₂Log dielectricLog thermalLog : ℝ) :
    bjerrumPairLength charge₁Log charge₂Log dielectricLog thermalLog *
        Real.exp (dielectricLog + thermalLog) =
      Real.exp (charge₁Log + charge₂Log) := by
  rw [bjerrumPairLength, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- At Bjerrum separation, normalized Coulomb energy equals thermal energy. -/
theorem coulombEnergy_at_bjerrumLength (coulombLog thermalLog : ℝ) :
    coulombEnergyAtLogSeparation coulombLog
        (Real.log (bjerrumLength coulombLog thermalLog)) =
      Real.exp thermalLog := by
  rw [coulombEnergyAtLogSeparation, bjerrumLength, Real.log_exp]
  exact congrArg Real.exp (by ring)

/-- Bjerrum length times thermal scale recovers electrostatic coupling scale. -/
theorem bjerrumLength_mul_thermalScale (coulombLog thermalLog : ℝ) :
    bjerrumLength coulombLog thermalLog * Real.exp thermalLog =
      Real.exp coulombLog := by
  rw [bjerrumLength, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- Heating by a logarithmic shift contracts Bjerrum length by reciprocal shift. -/
theorem bjerrumLength_thermal_shift (coulombLog thermalLog shift : ℝ) :
    bjerrumLength coulombLog (thermalLog + shift) =
      Real.exp (-shift) * bjerrumLength coulombLog thermalLog := by
  rw [bjerrumLength, bjerrumLength, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- Strengthening electrostatic coupling dilates Bjerrum length by same factor. -/
theorem bjerrumLength_coupling_shift (coulombLog thermalLog shift : ℝ) :
    bjerrumLength (coulombLog + shift) thermalLog =
      Real.exp shift * bjerrumLength coulombLog thermalLog := by
  rw [bjerrumLength, bjerrumLength, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- Debye length in logarithmic medium/stiffness coordinates. -/
def debyeLength (mediumLog chargeDensityLog : ℝ) : ℝ :=
  Real.sqrt (Real.exp (mediumLog - chargeDensityLog))

/-- Reciprocal Debye length. -/
def debyeWaveNumber (mediumLog chargeDensityLog : ℝ) : ℝ :=
  (debyeLength mediumLog chargeDensityLog)⁻¹

/-- Total `Σ nᵢqᵢ²` stiffness for a nonempty finite species family in logarithmic density and
charge coordinates. -/
def multispeciesChargeStiffness {n : ℕ}
    (densityLog chargeLog : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i, Real.exp (densityLog i + 2 * chargeLog i)

/-- Multi-species Debye length `sqrt (medium / Σ nᵢqᵢ²)`. -/
def multispeciesDebyeLength {n : ℕ} (mediumLog : ℝ)
    (densityLog chargeLog : Fin (n + 1) → ℝ) : ℝ :=
  Real.sqrt
    (Real.exp mediumLog / multispeciesChargeStiffness densityLog chargeLog)

theorem multispeciesChargeStiffness_pos {n : ℕ}
    (densityLog chargeLog : Fin (n + 1) → ℝ) :
    0 < multispeciesChargeStiffness densityLog chargeLog := by
  unfold multispeciesChargeStiffness
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem multispeciesDebyeLength_sq {n : ℕ} (mediumLog : ℝ)
    (densityLog chargeLog : Fin (n + 1) → ℝ) :
    multispeciesDebyeLength mediumLog densityLog chargeLog ^ 2 =
      Real.exp mediumLog / multispeciesChargeStiffness densityLog chargeLog := by
  exact Real.sq_sqrt
    (div_nonneg (Real.exp_pos _).le (multispeciesChargeStiffness_pos _ _).le)

/-- Multi-species formula is effective-stiffness instance of scalar Debye length. -/
theorem multispeciesDebyeLength_eq_debyeLength {n : ℕ} (mediumLog : ℝ)
    (densityLog chargeLog : Fin (n + 1) → ℝ) :
    multispeciesDebyeLength mediumLog densityLog chargeLog =
      debyeLength mediumLog
        (Real.log (multispeciesChargeStiffness densityLog chargeLog)) := by
  unfold multispeciesDebyeLength debyeLength
  congr 1
  rw [Real.exp_sub, Real.exp_log (multispeciesChargeStiffness_pos _ _)]

/-- Squared Debye length is medium scale divided by charge-density stiffness. -/
theorem debyeLength_sq (mediumLog chargeDensityLog : ℝ) :
    debyeLength mediumLog chargeDensityLog ^ 2 =
      Real.exp (mediumLog - chargeDensityLog) := by
  exact Real.sq_sqrt (Real.exp_pos _).le

theorem debyeLength_pos (mediumLog chargeDensityLog : ℝ) :
    0 < debyeLength mediumLog chargeDensityLog := by
  exact Real.sqrt_pos.2 (Real.exp_pos _)

/-- Debye length and Debye wave number cancel exactly. -/
theorem debyeLength_mul_waveNumber (mediumLog chargeDensityLog : ℝ) :
    debyeLength mediumLog chargeDensityLog *
      debyeWaveNumber mediumLog chargeDensityLog = 1 := by
  exact mul_inv_cancel₀ (debyeLength_pos _ _).ne'

/-- Shared thermal scale cancels from `Bjerrum length × Debye length²`. -/
theorem bjerrum_debye_temperature_cancellation
    (coulombLog thermalLog chargeDensityLog : ℝ) :
    bjerrumLength coulombLog thermalLog *
        debyeLength thermalLog chargeDensityLog ^ 2 =
      Real.exp (coulombLog - chargeDensityLog) := by
  rw [debyeLength_sq, bjerrumLength, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-! ## Townsend discharge and Paschen law -/

/-- First-Townsend avalanche gain. -/
def townsendGain (ionization distance : ℝ) : ℝ :=
  Real.exp (ionization * distance)

/-- Avalanche population from a positive logarithmic seed. -/
def townsendPopulation (seedLog ionization distance : ℝ) : ℝ :=
  Real.exp seedLog * townsendGain ionization distance

/-- Product gain through finitely many segments with independently constant ionization
coefficients. -/
def townsendSegmentedGain {n : ℕ}
    (ionization distance : Fin n → ℝ) : ℝ :=
  ∏ i, townsendGain (ionization i) (distance i)

/-- Secondary-emission feedback after an avalanche with integrated exponent `exponent`. -/
def townsendFeedback (secondaryLog exponent : ℝ) : ℝ :=
  Real.exp secondaryLog * (Real.exp exponent - 1)

theorem townsendGain_zero (ionization : ℝ) : townsendGain ionization 0 = 1 := by
  simp [townsendGain]

/-- Townsend gain is a multiplicative semigroup in discharge distance. -/
theorem townsendGain_distance_add (ionization x y : ℝ) :
    townsendGain ionization (x + y) =
      townsendGain ionization x * townsendGain ionization y := by
  rw [townsendGain, townsendGain, townsendGain, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- Population propagation factors through consecutive discharge segments. -/
theorem townsendPopulation_distance_add (seedLog ionization x y : ℝ) :
    townsendPopulation seedLog ionization (x + y) =
      townsendPopulation seedLog ionization x * townsendGain ionization y := by
  rw [townsendPopulation, townsendPopulation, townsendGain_distance_add]
  ring

/-- Segmented Townsend gain depends only on integrated ionization exponent. -/
theorem townsendSegmentedGain_eq_exp_sum {n : ℕ}
    (ionization distance : Fin n → ℝ) :
    townsendSegmentedGain ionization distance =
      Real.exp (∑ i, ionization i * distance i) := by
  classical
  unfold townsendSegmentedGain
  have hsegments : ∀ s : Finset (Fin n),
      (∏ i ∈ s, townsendGain (ionization i) (distance i)) =
        Real.exp (∑ i ∈ s, ionization i * distance i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [townsendGain]
    | @insert i s hi ih =>
        simp only [Finset.prod_insert hi, Finset.sum_insert hi, ih]
        rw [townsendGain, Real.exp_add]
  simpa using hsegments Finset.univ

/-- Reciprocal rescaling of coefficient and distance leaves avalanche gain unchanged. -/
theorem townsendGain_logGauge_invariant (ionizationLog distanceLog shift : ℝ) :
    townsendGain (Real.exp (ionizationLog + shift))
        (Real.exp (distanceLog - shift)) =
      townsendGain (Real.exp ionizationLog) (Real.exp distanceLog) := by
  unfold townsendGain
  exact congrArg Real.exp (by
    rw [← Real.exp_add, ← Real.exp_add]
    exact congrArg Real.exp (by ring))

/-- Local avalanche growth rate is ionization coefficient times current population. -/
theorem hasDerivAt_townsendGain (ionization distance : ℝ) :
    HasDerivAt (townsendGain ionization)
      (ionization * townsendGain ionization distance) distance := by
  change HasDerivAt (fun x : ℝ => Real.exp (ionization * x))
    (ionization * Real.exp (ionization * distance)) distance
  simpa only [Function.comp_def, mul_one, mul_comm] using
    (Real.hasDerivAt_exp (ionization * distance)).comp distance
      ((hasDerivAt_id distance).const_mul ionization)

/-- Paschen secondary-emission correction `log (log (1 + 1/γ))`, with `γ = exp γLog`. -/
def paschenSecondaryCorrection (secondaryLog : ℝ) : ℝ :=
  Real.log (Real.log (1 + Real.exp (-secondaryLog)))

/-- Logarithm of pressure-gap product on physical Paschen branch. -/
def paschenProductLog (aLog secondaryLog branchLog : ℝ) : ℝ :=
  paschenSecondaryCorrection secondaryLog - aLog + Real.exp branchLog

/-- Paschen voltage on physical branch. `A = exp aLog`, `B = exp bLog`; `branchLog`
parametrizes positive denominator. -/
def paschenVoltage (aLog bLog secondaryLog branchLog : ℝ) : ℝ :=
  Real.exp (bLog + paschenProductLog aLog secondaryLog branchLog - branchLog)

/-- Paschen voltage before restricting to physical branch, expressed through pressure and gap
logs separately. -/
def paschenVoltageAtPressureGap
    (aLog bLog secondaryLog pressureLog gapLog : ℝ) : ℝ :=
  Real.exp bLog * Real.exp (pressureLog + gapLog) /
    (aLog + pressureLog + gapLog - paschenSecondaryCorrection secondaryLog)

/-- Integrated first-Townsend coefficient `α d = A p d exp (-B p d / V)`. -/
def townsendReducedExponent
    (aLog bLog productLog voltage : ℝ) : ℝ :=
  Real.exp (aLog + productLog) *
    Real.exp (-(Real.exp (bLog + productLog) / voltage))

/-- Physical-branch Paschen denominator is positive coordinate `exp branchLog`. -/
theorem paschen_denominator_eq_exp (aLog secondaryLog branchLog : ℝ) :
    aLog + paschenProductLog aLog secondaryLog branchLog -
        paschenSecondaryCorrection secondaryLog = Real.exp branchLog := by
  unfold paschenProductLog
  ring

/-- Paschen voltage depends only on pressure-gap product. -/
theorem paschen_pressure_gap_logGauge_invariant
    (aLog bLog secondaryLog pressureLog gapLog shift : ℝ) :
    paschenVoltageAtPressureGap aLog bLog secondaryLog
        (pressureLog + shift) (gapLog - shift) =
      paschenVoltageAtPressureGap aLog bLog secondaryLog pressureLog gapLog := by
  unfold paschenVoltageAtPressureGap
  have hsum : (pressureLog + shift) + (gapLog - shift) = pressureLog + gapLog := by
    ring
  have hden :
      aLog + (pressureLog + shift) + (gapLog - shift) -
          paschenSecondaryCorrection secondaryLog =
        aLog + pressureLog + gapLog - paschenSecondaryCorrection secondaryLog := by
    ring
  rw [hsum, hden]

theorem paschen_pressure_gap_swap
    (aLog bLog secondaryLog pressureLog gapLog : ℝ) :
    paschenVoltageAtPressureGap aLog bLog secondaryLog pressureLog gapLog =
      paschenVoltageAtPressureGap aLog bLog secondaryLog gapLog pressureLog := by
  unfold paschenVoltageAtPressureGap
  have hsum : pressureLog + gapLog = gapLog + pressureLog := by ring
  have hden :
      aLog + pressureLog + gapLog - paschenSecondaryCorrection secondaryLog =
        aLog + gapLog + pressureLog - paschenSecondaryCorrection secondaryLog := by
    ring
  rw [hsum, hden]

/-- Branch parametrization reproduces standard Paschen quotient. -/
theorem paschenVoltage_eq_standard_formula
    (aLog bLog secondaryLog branchLog : ℝ) :
    paschenVoltage aLog bLog secondaryLog branchLog =
      Real.exp bLog * Real.exp (paschenProductLog aLog secondaryLog branchLog) /
        (aLog + paschenProductLog aLog secondaryLog branchLog -
          paschenSecondaryCorrection secondaryLog) := by
  rw [paschen_denominator_eq_exp]
  rw [paschenVoltage]
  apply (eq_div_iff (Real.exp_ne_zero branchLog)).2
  rw [← Real.exp_add, ← Real.exp_add]
  exact congrArg Real.exp (by ring)

/-- Paschen curve has unconditional physical-branch minimum at `branchLog = 0`. -/
theorem paschenVoltage_minimum (aLog bLog secondaryLog branchLog : ℝ) :
    paschenVoltage aLog bLog secondaryLog 0 ≤
      paschenVoltage aLog bLog secondaryLog branchLog := by
  unfold paschenVoltage paschenProductLog
  apply Real.exp_le_exp.mpr
  simp only [Real.exp_zero, sub_zero]
  nlinarith [Real.add_one_le_exp branchLog]

/-- Paschen voltage makes integrated Townsend coefficient equal critical secondary-emission log. -/
theorem paschen_townsend_exponent
    (aLog bLog secondaryLog branchLog : ℝ) :
    townsendReducedExponent aLog bLog
        (paschenProductLog aLog secondaryLog branchLog)
        (paschenVoltage aLog bLog secondaryLog branchLog) =
      Real.log (1 + Real.exp (-secondaryLog)) := by
  have hlogpos : 0 < Real.log (1 + Real.exp (-secondaryLog)) := by
    exact Real.log_pos (by linarith [Real.exp_pos (-secondaryLog)])
  rw [townsendReducedExponent, paschenVoltage, paschenProductLog,
    paschenSecondaryCorrection]
  have hquot :
      Real.exp
          (bLog +
            (Real.log (Real.log (1 + Real.exp (-secondaryLog))) - aLog +
              Real.exp branchLog)) /
        Real.exp
          (bLog +
              (Real.log (Real.log (1 + Real.exp (-secondaryLog))) - aLog +
                Real.exp branchLog) -
            branchLog) = Real.exp branchLog := by
    rw [div_eq_iff (Real.exp_ne_zero _)]
    rw [← Real.exp_add]
    exact congrArg Real.exp (by ring)
  rw [hquot]
  rw [← Real.exp_add]
  have hcollapse :
      aLog +
          (Real.log (Real.log (1 + Real.exp (-secondaryLog))) - aLog +
            Real.exp branchLog) +
        -Real.exp branchLog =
        Real.log (Real.log (1 + Real.exp (-secondaryLog))) := by ring
  rw [hcollapse, Real.exp_log hlogpos]

/-- Paschen voltage satisfies Townsend self-sustaining-discharge condition exactly. -/
theorem paschen_townsend_breakdown
    (aLog bLog secondaryLog branchLog : ℝ) :
    townsendFeedback secondaryLog
        (townsendReducedExponent aLog bLog
          (paschenProductLog aLog secondaryLog branchLog)
          (paschenVoltage aLog bLog secondaryLog branchLog)) = 1 := by
  rw [paschen_townsend_exponent]
  unfold townsendFeedback
  have harg : 0 < 1 + Real.exp (-secondaryLog) := by positivity
  rw [Real.exp_log harg]
  rw [show 1 + Real.exp (-secondaryLog) - 1 = Real.exp (-secondaryLog) by ring]
  rw [← Real.exp_add]
  simp

/-- Townsend feedback is exactly critical at integrated exponent `log (1 + 1/γ)`. -/
theorem townsendFeedback_at_criticalExponent (secondaryLog : ℝ) :
    townsendFeedback secondaryLog
        (Real.log (1 + Real.exp (-secondaryLog))) = 1 := by
  unfold townsendFeedback
  rw [Real.exp_log (by positivity : 0 < 1 + Real.exp (-secondaryLog))]
  rw [show 1 + Real.exp (-secondaryLog) - 1 = Real.exp (-secondaryLog) by ring]
  rw [← Real.exp_add]
  simp

/-! ## Photoelectric effect -/

/-- Einstein photoelectric kinetic energy `hν - φ`. -/
def photoelectricKineticEnergy (planck workFunction frequency : ℝ) : ℝ :=
  planck * frequency - workFunction

/-- Threshold frequency in positive logarithmic coordinates for `h` and `φ`. -/
def photoelectricThresholdFrequency (planckLog workLog : ℝ) : ℝ :=
  Real.exp (workLog - planckLog)

/-- Stopping potential: kinetic energy divided by positive charge magnitude. -/
def photoelectricStoppingPotential
    (chargeLog planck workFunction frequency : ℝ) : ℝ :=
  photoelectricKineticEnergy planck workFunction frequency / Real.exp chargeLog

/-- Multiphoton photoelectric kinetic energy `N hν - φ`, with positive photon count `N = n+1`. -/
def multiphotonKineticEnergy
    (n : ℕ) (planck workFunction frequency : ℝ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) * planck * frequency - workFunction

/-- Multiphoton threshold frequency for positive log-coordinate `h` and `φ`. -/
def multiphotonThresholdFrequency (n : ℕ) (planckLog workLog : ℝ) : ℝ :=
  Real.exp workLog / (((n + 1 : ℕ) : ℝ) * Real.exp planckLog)

theorem multiphotonKineticEnergy_eq_photoelectricKineticEnergy
    (n : ℕ) (planck workFunction frequency : ℝ) :
    multiphotonKineticEnergy n planck workFunction frequency =
      photoelectricKineticEnergy (((n + 1 : ℕ) : ℝ) * planck)
        workFunction frequency := by
  unfold multiphotonKineticEnergy photoelectricKineticEnergy
  ring

theorem multiphoton_at_threshold (n : ℕ) (planckLog workLog : ℝ) :
    multiphotonKineticEnergy n (Real.exp planckLog) (Real.exp workLog)
        (multiphotonThresholdFrequency n planckLog workLog) = 0 := by
  unfold multiphotonKineticEnergy multiphotonThresholdFrequency
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hn, Real.exp_ne_zero]
  ring

/-- Photoelectron kinetic energy vanishes at threshold frequency. -/
theorem photoelectric_at_threshold (planckLog workLog : ℝ) :
    photoelectricKineticEnergy (Real.exp planckLog) (Real.exp workLog)
      (photoelectricThresholdFrequency planckLog workLog) = 0 := by
  rw [photoelectricKineticEnergy, photoelectricThresholdFrequency]
  rw [← Real.exp_add]
  rw [show planckLog + (workLog - planckLog) = workLog by ring]
  ring

/-- Above threshold, frequency excess converts linearly to positive kinetic energy. -/
theorem photoelectric_above_threshold
    (planckLog workLog excessLog : ℝ) :
    photoelectricKineticEnergy (Real.exp planckLog) (Real.exp workLog)
        (photoelectricThresholdFrequency planckLog workLog + Real.exp excessLog) =
      Real.exp (planckLog + excessLog) := by
  rw [photoelectricKineticEnergy, photoelectricThresholdFrequency]
  rw [mul_add, ← Real.exp_add, ← Real.exp_add]
  rw [show planckLog + (workLog - planckLog) = workLog by ring]
  ring

/-- Below threshold, formal kinetic energy is exactly negative threshold deficit. -/
theorem photoelectric_below_threshold
    (planckLog workLog deficitLog : ℝ) :
    photoelectricKineticEnergy (Real.exp planckLog) (Real.exp workLog)
        (photoelectricThresholdFrequency planckLog workLog - Real.exp deficitLog) =
      -Real.exp (planckLog + deficitLog) := by
  rw [photoelectricKineticEnergy, photoelectricThresholdFrequency]
  rw [mul_sub, ← Real.exp_add, ← Real.exp_add]
  rw [show planckLog + (workLog - planckLog) = workLog by ring]
  ring

/-- Charge times stopping potential recovers photoelectron kinetic energy. -/
theorem photoelectric_charge_mul_stoppingPotential
    (chargeLog planck workFunction frequency : ℝ) :
    Real.exp chargeLog *
        photoelectricStoppingPotential chargeLog planck workFunction frequency =
      photoelectricKineticEnergy planck workFunction frequency := by
  unfold photoelectricStoppingPotential
  field_simp

/-- Photoelectric energy responds affinely to frequency increments. -/
theorem photoelectric_frequency_add
    (planck workFunction frequency increment : ℝ) :
    photoelectricKineticEnergy planck workFunction (frequency + increment) =
      photoelectricKineticEnergy planck workFunction frequency + planck * increment := by
  unfold photoelectricKineticEnergy
  ring

/-- Photoelectric energy-frequency slope is Planck factor. -/
theorem hasDerivAt_photoelectricKineticEnergy
    (planck workFunction frequency : ℝ) :
    HasDerivAt (photoelectricKineticEnergy planck workFunction)
      planck frequency := by
  change HasDerivAt (fun x : ℝ => planck * x - workFunction) planck frequency
  simpa using
    ((hasDerivAt_id frequency).const_mul planck).sub_const workFunction

end GaloisForLFunctions.HTGeometry
