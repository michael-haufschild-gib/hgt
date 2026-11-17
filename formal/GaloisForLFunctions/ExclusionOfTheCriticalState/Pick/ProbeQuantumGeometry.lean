import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeSectorMassPairings
import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeZeroPhaseSensitivity
import GaloisForLFunctions.HTGeometry.QuantumGeometricTensorGram

/-!
# Quantum metric and Berry curvature of the Weil reflection pair

The tangent pair `x, i R x` has metric area equal to the fourth power of its
Hilbert norm. Its Berry curvature is minus twice its signed Weil energy.
The excess of metric area over curvature is exactly four times the product
of the two reflection-sector masses. Thus strict quantum-geometric excess
is precisely genuine mixing of the positive and negative sectors.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open ArithmeticCastelnuovoSeveri Zeta23

/-- Berry curvature of the reflection tangent pair is the signed Weil energy. -/
theorem reflectionPair_berry (x : ZeroSpace) :
    _root_.HTGeometry.berryCurvatureValue x (Complex.I • zeroReflection x) =
      -2 * reflectionEnergy x := by
  rw [_root_.HTGeometry.berryCurvatureValue, inner_smul_right, inner_reflection_eq_energy]
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add]

/-- The real quantum metric area is independent of the reflection-sector split. -/
theorem reflectionPair_metricArea (x : ZeroSpace) :
    _root_.HTGeometry.quantumMetricAreaValue x (Complex.I • zeroReflection x) = ‖x‖ ^ 4 := by
  rw [_root_.HTGeometry.quantumMetricAreaValue, norm_smul, Complex.norm_I,
    one_mul, norm_zeroReflection, inner_smul_right, inner_reflection_eq_energy]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_self, zero_pow (by decide : 2 ≠ 0), sub_zero]
  ring

/-- The exact metric–Berry excess is the mixing energy of the two Weil sectors. -/
theorem reflectionPair_quantum_gap (x : ZeroSpace) :
    _root_.HTGeometry.quantumMetricAreaValue x (Complex.I • zeroReflection x) -
      _root_.HTGeometry.berryCurvatureValue x (Complex.I • zeroReflection x) ^ 2 / 4 =
      4 * (positiveMass x * negativeMass x) := by
  rw [reflectionPair_metricArea, reflectionPair_berry, sector_mass_product]
  ring

/-- Saturating the quantum-geometric bound is exactly concentration in one reflection sector. -/
theorem reflectionPair_quantum_gap_zero_iff (x : ZeroSpace) :
    _root_.HTGeometry.quantumMetricAreaValue x (Complex.I • zeroReflection x) =
      _root_.HTGeometry.berryCurvatureValue x (Complex.I • zeroReflection x) ^ 2 / 4 ↔
      zeroReflection x = x ∨ zeroReflection x = -x := by
  rw [← sub_eq_zero, reflectionPair_quantum_gap, mul_eq_zero]
  simp only [OfNat.ofNat_ne_zero, false_or, sector_mass_product_zero_iff]

/-- The reflection pair is complex independent exactly when both sector masses are positive. -/
theorem reflectionPair_independent_iff (x : ZeroSpace) :
    LinearIndependent ℂ ![x, Complex.I • zeroReflection x] ↔
      0 < positiveMass x * negativeMass x := by
  rw [← _root_.HTGeometry.quantumMetricArea_strict_iff_linearIndependent_pair,
    ← sub_pos, reflectionPair_quantum_gap]
  constructor <;> intro h <;> linarith only [h]

/-- The single-zero reflection pair is independent precisely off the critical line. -/
theorem zeroBasis_reflectionPair_independent_iff (z : zetaZeroConfig.carrier) :
    LinearIndependent ℂ ![zeroBasis z, Complex.I • zeroReflection (zeroBasis z)] ↔
      (z : ℂ).re ≠ 1 / 2 := by
  classical
  rw [reflectionPair_independent_iff, (sector_masses_zeroBasis z).1,
    (sector_masses_zeroBasis z).2]
  by_cases hz : (z : ℂ).re = 1 / 2 <;> norm_num [hz]

#print axioms inner_reflection_eq_energy
#print axioms reflectionPair_berry
#print axioms reflectionPair_metricArea
#print axioms reflectionPair_quantum_gap
#print axioms reflectionPair_quantum_gap_zero_iff
#print axioms reflectionPair_independent_iff
#print axioms zeroBasis_reflectionPair_independent_iff

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
