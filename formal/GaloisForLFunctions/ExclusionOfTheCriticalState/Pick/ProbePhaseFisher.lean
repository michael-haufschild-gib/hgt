import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorMassPairings
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbePhaseDynamics
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity
import GaloisForLFunctions.HTGeometry.ProjectiveQuantumFisherValue

/-!
# Quantum Fisher geometry of the actual Weil phase flow

The actual real-time derivative has projective Gram energy equal to the
product of the two reflection-sector masses. Normalization gives a
conserved quantum Fisher value between zero and one. It vanishes exactly
on pure reflection sectors and is maximal exactly at nonzero vectors of
zero signed Weil energy. Individual off-line zero coordinates attain one.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

private theorem generator_projective_energy (x : ZeroSpace) :
    _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) x (Complex.I • negativePart x) =
      positiveMass x * negativeMass x := by
  simp only [_root_.HTGeometry.projectiveGramTangentEnergy, norm_smul, Complex.norm_I,
    one_mul, inner_smul_right, norm_mul, inner_negativePart_eq_mass,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  change ‖x‖ ^ 2 * negativeMass x - negativeMass x ^ 2 = positiveMass x * negativeMass x
  rw [← sector_mass_sum x]
  ring

/-- The projective energy of the actual derivative is conserved sector mixing. -/
theorem timePhase_projective_energy (t : ℝ) (x : ZeroSpace) :
    _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (timePhase t x)
      (deriv (fun s : ℝ => timePhase s x) t) = positiveMass x * negativeMass x := by
  rw [(timePhase_hasDerivAt t x).deriv, generator_projective_energy]
  simp only [positiveMass, negativeMass, timePhase, positivePart_phaseRotate,
    negativePart_phaseRotate, norm_smul, Circle.norm_coe, one_mul]

/-- The conventional pure-state quantum Fisher value of the actual phase derivative. -/
def phaseQuantumFisher (t : ℝ) (x : ZeroSpace) : ℝ :=
  4 * _root_.HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) (timePhase t x)
    (deriv (fun s : ℝ => timePhase s x) t) / ‖timePhase t x‖ ^ 4

/-- The Fisher value is time independent and depends only on the two sector masses. -/
theorem phaseQuantumFisher_value (t : ℝ) (x : ZeroSpace) :
    phaseQuantumFisher t x = 4 * (positiveMass x * negativeMass x) / ‖x‖ ^ 4 := by
  rw [phaseQuantumFisher, timePhase_projective_energy]
  have hn : ‖timePhase t x‖ = ‖x‖ := (phaseRotationEquiv (Circle.exp t)).norm_map x
  rw [hn]

/-- Every zero-coordinate vector has a Fisher value in the closed unit interval. -/
theorem phaseQuantumFisher_bounds (t : ℝ) (x : ZeroSpace) :
    0 ≤ phaseQuantumFisher t x ∧ phaseQuantumFisher t x ≤ 1 := by
  rw [phaseQuantumFisher_value]
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (pow_nonneg (norm_nonneg _) _)
  · by_cases hx : x = 0
    · simp [hx]
    · apply (div_le_iff₀ (pow_pos (norm_pos_iff.mpr hx) 4)).mpr
      simpa only [one_mul] using sector_mass_product_le x

/-- Projectively stationary flows are exactly the two pure reflection sectors. -/
theorem phaseQuantumFisher_zero_iff (t : ℝ) (x : ZeroSpace) :
    phaseQuantumFisher t x = 0 ↔ zeroReflection x = x ∨ zeroReflection x = -x := by
  by_cases hx : x = 0
  · simp [phaseQuantumFisher_value, hx]
  · rw [phaseQuantumFisher_value, div_eq_zero_iff]
    simp only [(pow_pos (norm_pos_iff.mpr hx) 4).ne', or_false, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, sector_mass_product_zero_iff]

/-- Maximal Fisher information is exactly nonzero balanced-sector mass. -/
theorem phaseQuantumFisher_eq_one_iff (t : ℝ) (x : ZeroSpace) :
    phaseQuantumFisher t x = 1 ↔ x ≠ 0 ∧ reflectionEnergy x = 0 := by
  by_cases hx : x = 0
  · simp [phaseQuantumFisher_value, hx]
  · rw [phaseQuantumFisher_value, div_eq_iff (pow_pos (norm_pos_iff.mpr hx) 4).ne', one_mul]
    simp only [hx, not_false_eq_true, true_and]
    exact sector_mass_product_max_iff x

/-- A single zero has zero Fisher information on the critical line and maximal information off it. -/
theorem phaseQuantumFisher_zeroBasis (t : ℝ) (z : zetaZeroConfig.carrier) :
    phaseQuantumFisher t (zeroBasis z) = if (z : ℂ).re = 1 / 2 then 0 else 1 := by
  classical
  rw [phaseQuantumFisher_value, norm_zeroBasis, (sector_masses_zeroBasis z).1,
    (sector_masses_zeroBasis z).2]
  by_cases hz : (z : ℂ).re = 1 / 2 <;> norm_num [hz]

#print axioms timePhase_projective_energy
#print axioms phaseQuantumFisher_value
#print axioms phaseQuantumFisher_bounds
#print axioms phaseQuantumFisher_zero_iff
#print axioms phaseQuantumFisher_eq_one_iff
#print axioms phaseQuantumFisher_zeroBasis
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
