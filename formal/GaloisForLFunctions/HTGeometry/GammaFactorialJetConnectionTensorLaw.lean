import GaloisForLFunctions.HTGeometry.GammaFactorialAsymptoticConnection
import GaloisForLFunctions.HTGeometry.GammaPoleWeightedCovariantAsymptotic

/-!
# Factorial connection tensor law for intrinsic Gamma jets

The pole-index connection and the intrinsic differential-jet grading were introduced separately.
The covariant top-residue frame contains the missing bridge: its grade-`j` coordinate is the
`j`th tensor power of the inverse factorial connection, multiplied by the universal fiber norm
`j!`.  Advancing from pole `-m` to pole `-(m+1)` therefore multiplies the grade-`j` residue norm
by `(m+1)^j`.
-/

namespace GaloisForLFunctions

noncomputable section

/-- **Factorial-connection tensor law.**  Intrinsic jet grade `j` sees the inverse pole-index
transport in its `j`th tensor power, with universal fiber factor `j!`. -/
theorem norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower
    (branch n : ℕ) (j : Fin (n + 1)) :
    ‖gammaPoleCovariantTopResidueValue branch n j‖ =
      (HTGeometry.gammaFactorialConnectionTransport branch)⁻¹ ^ (j : ℕ) *
        ((j : ℕ).factorial : ℝ) := by
  simp [gammaPoleCovariantTopResidueValue,
    ← HTGeometry.norm_reciprocalGammaFactorialScale_eq_connectionTransport]

/-- Adjacent pole transport acts on grade `j` by the inverse `j`th power of the connection
link. -/
theorem norm_gammaPoleCovariantTopResidueValue_succ_eq_connectionLinkTensorPower
    (branch n : ℕ) (j : Fin (n + 1)) :
    ‖gammaPoleCovariantTopResidueValue (branch + 1) n j‖ =
      (HTGeometry.gammaFactorialConnectionLink branch)⁻¹ ^ (j : ℕ) *
        ‖gammaPoleCovariantTopResidueValue branch n j‖ := by
  rw [norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower,
    norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower,
    HTGeometry.gammaFactorialConnectionTransport_succ]
  field_simp
  ring

/-- Closed form of the tensor law: the grade-`j` top-residue norm at pole `-branch` is
`(branch!)^j j!`. -/
theorem norm_gammaPoleCovariantTopResidueValue_eq_factorial_pow_mul_factorial
    (branch n : ℕ) (j : Fin (n + 1)) :
    ‖gammaPoleCovariantTopResidueValue branch n j‖ =
      (branch.factorial : ℝ) ^ (j : ℕ) * ((j : ℕ).factorial : ℝ) := by
  rw [norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower]
  simp [HTGeometry.gammaFactorialConnectionTransport]

/-- **Pole-index/jet-grade bridge.**  Moving one Gamma pole deeper multiplies the intrinsic
grade-`j` top-residue norm by the `j`th power of the new pole index. -/
theorem norm_gammaPoleCovariantTopResidueValue_succ_eq_indexPow_mul
    (branch n : ℕ) (j : Fin (n + 1)) :
    ‖gammaPoleCovariantTopResidueValue (branch + 1) n j‖ =
      ((branch + 1 : ℕ) : ℝ) ^ (j : ℕ) *
        ‖gammaPoleCovariantTopResidueValue branch n j‖ := by
  rw [norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower,
    norm_gammaPoleCovariantTopResidueValue_eq_factorialConnectionTensorPower,
    HTGeometry.gammaFactorialConnectionTransport_succ]
  simp [HTGeometry.gammaFactorialConnectionLink]
  field_simp
  rw [← mul_pow]
  congr 1
  ring

end

end GaloisForLFunctions
