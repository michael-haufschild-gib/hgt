import GaloisForLFunctions.HTGeometry.CPVThermalRadiation
import Mathlib

/-!
# Positive frequency, compatible Hawking mass, and microstate degeneracy

Equations (26)--(31) of arXiv:2601.07437 on the full punctured coherent-state
disk. The coupling is `exp j` and the pair count is `N+1`; every denominator
is therefore proved nonzero. Hawking mass is a compatible assignment in units
`G=c=ℏ=1`, not an assertion that a spacetime is produced by the quantum state.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Radius of a nonvacuum coherent-state label. -/
def coherentRadius (tau : ℝ) : ℝ := Real.sqrt (thermalRatio tau)

theorem coherentRadius_pos (tau : ℝ) : 0 < coherentRadius tau :=
  Real.sqrt_pos.mpr (thermalRatio_pos tau)
theorem coherentRadius_lt_one (tau : ℝ) : coherentRadius tau < 1 := by
  unfold coherentRadius
  rw [Real.sqrt_lt' zero_lt_one]
  simpa using thermalRatio_lt_one tau
@[simp] theorem coherentRadius_sq (tau : ℝ) : coherentRadius tau ^ 2 = thermalRatio tau :=
  Real.sq_sqrt (thermalRatio_pos tau).le

/-- Polar coherent-state coordinate with no vacuum or boundary points. -/
def coherentLabel (tau phi : ℝ) : ℂ :=
  (coherentRadius tau : ℂ) * ((Real.cos phi : ℂ) + (Real.sin phi : ℂ) * Complex.I)

/-- Its modulus is exactly the thermal occupation ratio. -/
theorem coherentLabel_normSq (tau phi : ℝ) :
    Complex.normSq (coherentLabel tau phi) = thermalRatio tau := by
  rw [coherentLabel, Complex.normSq_mul]
  simp only [Complex.normSq_ofReal, Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq phi, coherentRadius_sq tau]

/-- The phase-dependent positive numerator shared by energy and frequency. -/
def radiationNumerator (tau phi : ℝ) : ℝ :=
  1 + thermalRatio tau - 2 * coherentRadius tau * Real.sin phi

/-- Exact positive decomposition, uniformly over coherent-state phase. -/
theorem radiationNumerator_decomposition (tau phi : ℝ) :
    radiationNumerator tau phi = (1 - coherentRadius tau) ^ 2 +
      2 * coherentRadius tau * (1 - Real.sin phi) := by
  unfold radiationNumerator
  nlinarith [coherentRadius_sq tau]

/-- No nonvacuum interior microstate has zero or negative frequency. -/
theorem radiationNumerator_pos (tau phi : ℝ) : 0 < radiationNumerator tau phi := by
  rw [radiationNumerator_decomposition]
  have h1 : 0 < (1 - coherentRadius tau) ^ 2 :=
    sq_pos_of_pos (sub_pos.mpr (coherentRadius_lt_one tau))
  have h2 : 0 ≤ 2 * coherentRadius tau * (1 - Real.sin phi) :=
    mul_nonneg (by linarith [coherentRadius_pos tau]) (sub_nonneg.mpr (Real.sin_le_one phi))
  linarith

/-- Frequency from equation (29). -/
def radiationFrequency (N : ℕ) (j tau phi : ℝ) : ℝ :=
  Real.exp j / ((N : ℝ) + 1) * radiationNumerator tau phi / (1 + thermalRatio tau)

/-- Temperature from equation (30), with the logarithm evaluated exactly. -/
def radiationTemperature (N : ℕ) (j tau phi : ℝ) : ℝ :=
  radiationFrequency N j tau phi / Real.exp tau

/-- Half-plane energy coordinate of the polar coherent label. -/
def coherentEnergyCoordinate (tau phi : ℝ) : ℝ :=
  radiationNumerator tau phi / (1 - thermalRatio tau)

theorem radiationFrequency_pos (N : ℕ) (j tau phi : ℝ) :
    0 < radiationFrequency N j tau phi := by
  unfold radiationFrequency
  exact div_pos (mul_pos (div_pos (Real.exp_pos j) (by positivity))
    (radiationNumerator_pos tau phi)) (by linarith [thermalRatio_pos tau])

theorem radiationTemperature_pos (N : ℕ) (j tau phi : ℝ) :
    0 < radiationTemperature N j tau phi :=
  div_pos (radiationFrequency_pos N j tau phi) (Real.exp_pos tau)

/-- The proposed thermodynamic parameters reproduce exactly the occupation ratio. -/
theorem radiationFrequency_div_temperature (N : ℕ) (j tau phi : ℝ) :
    radiationFrequency N j tau phi / radiationTemperature N j tau phi = Real.exp tau := by
  unfold radiationTemperature
  field_simp [(radiationFrequency_pos N j tau phi).ne']

/-- Literal Boltzmann-factor identity from equation (26). -/
theorem radiationFrequency_boltzmann (N : ℕ) (j tau phi : ℝ) :
    Real.exp (-radiationFrequency N j tau phi / radiationTemperature N j tau phi) =
      thermalRatio tau := by
  rw [neg_div, radiationFrequency_div_temperature]
  rfl

/-- The logarithmic effective inverse scale in equation (30) is not a premise. -/
theorem coherentLabel_log_inverse_normSq (tau phi : ℝ) :
    Real.log ((Complex.normSq (coherentLabel tau phi))⁻¹) = Real.exp tau := by
  rw [coherentLabel_normSq, Real.log_inv]
  simp [thermalRatio]

/-- The expectation energy of one emitted oscillator, including its vacuum half. -/
def radiationMeanEnergy (N : ℕ) (j tau phi : ℝ) : ℝ :=
  radiationFrequency N j tau phi * ((thermalRatio tau / (1 - thermalRatio tau)) + 1 / 2)

/-- The mean energy is an actual convergent infinite expectation. -/
theorem radiationMeanEnergy_hasSum (N : ℕ) (j tau phi : ℝ) :
    HasSum (fun n : ℕ => radiationFrequency N j tau phi * ((n : ℝ) + 1 / 2) *
      radiationMass tau n) (radiationMeanEnergy N j tau phi) := by
  have h := ((radiationMass_mean tau).add ((radiationMass_hasSum tau).mul_left (1 / 2))).mul_left
    (radiationFrequency N j tau phi)
  convert! h using 1
  · funext n
    ring
  · unfold radiationMeanEnergy
    ring

/-- Equation (28): paired outgoing energy equals the coherent Hamiltonian. -/
theorem radiationMeanEnergy_balance (N : ℕ) (j tau phi : ℝ) :
    2 * ((N : ℝ) + 1) * radiationMeanEnergy N j tau phi =
      Real.exp j * coherentEnergyCoordinate tau phi := by
  unfold radiationMeanEnergy radiationFrequency coherentEnergyCoordinate
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  have hp : 1 + thermalRatio tau ≠ 0 := by linarith [thermalRatio_pos tau]
  have hm : 1 - thermalRatio tau ≠ 0 := ne_of_gt (sub_pos.mpr (thermalRatio_lt_one tau))
  field_simp
  ring

/-- Phase reflection preserves the outgoing temperature. -/
theorem radiationTemperature_phase_reflection (N : ℕ) (j tau phi : ℝ) :
    radiationTemperature N j tau (Real.pi - phi) = radiationTemperature N j tau phi := by
  simp [radiationTemperature, radiationFrequency, radiationNumerator, Real.sin_pi_sub]

/-- Opposite real coherent labels are different microstates. -/
theorem coherentLabel_zero_ne_pi (tau : ℝ) : coherentLabel tau 0 ≠ coherentLabel tau Real.pi := by
  simp only [coherentLabel, Real.cos_zero, Real.sin_zero, Complex.ofReal_one,
    Complex.ofReal_zero, zero_mul, add_zero, mul_one, Real.cos_pi, Real.sin_pi,
    Complex.ofReal_neg, mul_neg]
  intro h
  have hr : (coherentRadius tau : ℂ) = 0 := by linear_combination h / 2
  exact (coherentRadius_pos tau).ne' (Complex.ofReal_eq_zero.mp hr)

/-- Explicit distinct microstates with identical radiation temperature. -/
theorem distinct_microstates_same_temperature (N : ℕ) (j tau : ℝ) :
    coherentLabel tau 0 ≠ coherentLabel tau Real.pi ∧
      radiationTemperature N j tau 0 = radiationTemperature N j tau Real.pi := by
  constructor
  · exact coherentLabel_zero_ne_pi tau
  · simpa using (radiationTemperature_phase_reflection N j tau 0).symm

/-- Positive mass compatible with the Hawking-temperature matching condition. -/
def compatibleHawkingMass (N : ℕ) (j tau phi : ℝ) : ℝ :=
  1 / (8 * Real.pi * radiationTemperature N j tau phi)

theorem compatibleHawkingMass_pos (N : ℕ) (j tau phi : ℝ) :
    0 < compatibleHawkingMass N j tau phi := by
  unfold compatibleHawkingMass
  exact div_pos zero_lt_one (mul_pos (mul_pos (by positivity) Real.pi_pos)
    (radiationTemperature_pos N j tau phi))

/-- Exact matching of microscopic and Hawking temperatures in natural units. -/
theorem compatibleHawkingMass_temperature (N : ℕ) (j tau phi : ℝ) :
    1 / (8 * Real.pi * compatibleHawkingMass N j tau phi) =
      radiationTemperature N j tau phi := by
  unfold compatibleHawkingMass
  field_simp

/-- At fixed coherent label and coupling, temperature scales inversely with pair count. -/
theorem radiationTemperature_pair_count (N : ℕ) (j tau phi : ℝ) :
    radiationTemperature N j tau phi = radiationTemperature 0 j tau phi / ((N : ℝ) + 1) := by
  unfold radiationTemperature radiationFrequency
  simp only [Nat.cast_zero, zero_add, div_one]
  ring

/-- The compatible source mass grows linearly with the pair count. -/
theorem compatibleHawkingMass_pair_count (N : ℕ) (j tau phi : ℝ) :
    compatibleHawkingMass N j tau phi = ((N : ℝ) + 1) * compatibleHawkingMass 0 j tau phi := by
  unfold compatibleHawkingMass
  rw [radiationTemperature_pair_count]
  field_simp

end GaloisForLFunctions.HTGeometry.CPV
