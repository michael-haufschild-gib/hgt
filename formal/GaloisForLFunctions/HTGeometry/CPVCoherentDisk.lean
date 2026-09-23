import GaloisForLFunctions.HTGeometry.CayleySchur
import Mathlib

/-!
# Pseudo-spin disk geometry and radiation frequency

The disk coordinate in arXiv:2601.07437, equation (6), is the corpus
Cayley transform followed by a quarter turn. All upper-half-plane points
are constructed with positive height `exp s`; no disk-membership hypothesis
is needed. The frequency law (29) becomes an explicit positive rational function.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV

/-- Upper-half-plane coordinate with unrestricted real parameters. -/
def upperPoint (v s : ℝ) : ℂ := (v : ℂ) + (Real.exp s : ℂ) * Complex.I

/-- Rotated corpus Cayley transform used by the pseudo-spin coherent states. -/
def diskPoint (v s : ℝ) : ℂ :=
  Complex.I * ((upperPoint v s - Complex.I) / (upperPoint v s + Complex.I))

/-- Every point of this family lies strictly inside the coherent-state disk. -/
theorem diskPoint_norm_lt_one (v s : ℝ) : ‖diskPoint v s‖ < 1 := by
  unfold diskPoint
  rw [norm_mul, Complex.norm_I, one_mul]
  apply GaloisForLFunctions.cayley_upperHalfPlane_to_disk
  simpa only [upperPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    using Real.exp_pos s

/-- Positive common denominator of the disk coordinates. -/
def diskDenominator (v s : ℝ) : ℝ := v ^ (2 : ℕ) + (Real.exp s + 1) ^ (2 : ℕ)

theorem diskDenominator_pos (v s : ℝ) : 0 < diskDenominator v s := by
  unfold diskDenominator
  positivity

/-- Cartesian formula for the real disk coordinate. -/
theorem diskPoint_re (v s : ℝ) : (diskPoint v s).re = 2 * v / diskDenominator v s := by
  simp [diskPoint, upperPoint, Complex.div_re, Complex.div_im, Complex.normSq_apply,
    diskDenominator, -Complex.ofReal_exp]
  ring

/-- Cartesian formula for the imaginary disk coordinate. -/
theorem diskPoint_im (v s : ℝ) :
    (diskPoint v s).im = (v ^ (2 : ℕ) + Real.exp s ^ (2 : ℕ) - 1) / diskDenominator v s := by
  simp [diskPoint, upperPoint, Complex.div_re, Complex.div_im, Complex.normSq_apply,
    diskDenominator, -Complex.ofReal_exp]
  ring

/-- Squared coherent-state radius in the half-plane variables. -/
theorem diskPoint_normSq (v s : ℝ) :
    Complex.normSq (diskPoint v s) =
      (v ^ (2 : ℕ) + (Real.exp s - 1) ^ (2 : ℕ)) / diskDenominator v s := by
  rw [diskPoint, Complex.normSq_mul, Complex.normSq_I, one_mul, Complex.normSq_div]
  simp [upperPoint, Complex.normSq_apply, diskDenominator, -Complex.ofReal_exp]
  ring

/-- Exact disk defect measuring finite quantum occupation. -/
theorem diskPoint_defect (v s : ℝ) :
    1 - Complex.normSq (diskPoint v s) = 4 * Real.exp s / diskDenominator v s := by
  rw [diskPoint_normSq]
  unfold diskDenominator
  have hd := ne_of_gt (diskDenominator_pos v s)
  unfold diskDenominator at hd
  field_simp
  ring

/-- The Cayley image never reaches the singular boundary point `i`. -/
theorem diskPoint_ne_I (v s : ℝ) : diskPoint v s ≠ Complex.I := by
  intro h
  have hh := diskPoint_norm_lt_one v s
  rw [h, Complex.norm_I] at hh
  exact lt_irrefl _ hh

/-- Literal conformal-coordinate identity from equation (6). -/
theorem diskPoint_cayley_inverse (v s : ℝ) :
    (Complex.I + diskPoint v s) / (Complex.I - diskPoint v s) =
      (Real.exp s : ℂ) - Complex.I * (v : ℂ) := by
  have hd : upperPoint v s + Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [upperPoint, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero,
      Complex.zero_im] at hh
    linarith [Real.exp_pos s]
  have hi : Complex.I - diskPoint v s ≠ 0 := sub_ne_zero.mpr (Ne.symm (diskPoint_ne_I v s))
  apply (div_eq_iff hi).mpr
  unfold diskPoint
  field_simp
  simp [upperPoint]
  linear_combination 2 * (v : ℂ) * Complex.I_sq

/-- The positive frequency multiplier in equation (29). -/
def frequencyFactor (v s : ℝ) : ℝ :=
  1 - 2 * (diskPoint v s).im / (1 + Complex.normSq (diskPoint v s))

/-- Radiation frequency is a simple half-plane radial function. -/
theorem frequencyFactor_eq (v s : ℝ) :
    frequencyFactor v s = 2 / (v ^ (2 : ℕ) + Real.exp s ^ (2 : ℕ) + 1) := by
  unfold frequencyFactor
  rw [diskPoint_im, diskPoint_normSq]
  have hd := ne_of_gt (diskDenominator_pos v s)
  have hn : v ^ (2 : ℕ) + Real.exp s ^ (2 : ℕ) + 1 ≠ 0 := by positivity
  have hs : 1 + (v ^ (2 : ℕ) + (Real.exp s - 1) ^ (2 : ℕ)) / diskDenominator v s =
      2 * (v ^ (2 : ℕ) + Real.exp s ^ (2 : ℕ) + 1) / diskDenominator v s := by
    field_simp
    unfold diskDenominator
    ring
  rw [hs]
  field_simp
  ring

/-- Every finite coherent-state coordinate has positive emitted frequency. -/
theorem frequencyFactor_pos (v s : ℝ) : 0 < frequencyFactor v s := by
  rw [frequencyFactor_eq]
  positivity

/-- Frequency stays strictly below twice the microscopic coupling per mode. -/
theorem frequencyFactor_lt_two (v s : ℝ) : frequencyFactor v s < 2 := by
  rw [frequencyFactor_eq]
  apply (div_lt_iff₀ (by positivity : 0 < v ^ (2 : ℕ) + Real.exp s ^ (2 : ℕ) + 1)).mpr
  nlinarith [sq_nonneg v, sq_pos_of_pos (Real.exp_pos s)]

/-- Clock-time reversal leaves the single-mode radiation frequency unchanged. -/
theorem frequencyFactor_time_reversal (v s : ℝ) : frequencyFactor (-v) s = frequencyFactor v s := by
  rw [frequencyFactor_eq, frequencyFactor_eq]
  simp

/-- Energy balance (28) after eliminating the thermal hyperbolic function. -/
theorem frequencyFactor_energy_balance (v s : ℝ) :
    frequencyFactor v s *
      ((1 + Complex.normSq (diskPoint v s)) / (1 - Complex.normSq (diskPoint v s))) =
        (Real.exp s)⁻¹ := by
  rw [frequencyFactor_eq, diskPoint_defect, diskPoint_normSq]
  have hd := ne_of_gt (diskDenominator_pos v s)
  have hn : v ^ (2 : ℕ) + Real.exp s ^ (2 : ℕ) + 1 ≠ 0 := by positivity
  field_simp
  unfold diskDenominator
  ring

end GaloisForLFunctions.HTGeometry.CPV
