import GaloisForLFunctions.HTGeometry.GaussianWeightedVerticalSlope

/-!
# An all-radius exponential envelope for the full Gaussian phase slope

The strip slope is bounded by one explicit exponential times a linear radius
factor. The estimate uses the norm of the complete polynomial throughout.
-/

open scoped Real NNReal
noncomputable section

namespace GaloisForLFunctions

/-- An explicit whole-polynomial slope envelope, valid at every nonnegative radius. -/
def gaussianGlobalVerticalSlopeEnvelope (d : ℕ) (R : ℝ) : ℝ :=
  gaussianStripSamplingFactor (d + 1) 1 *
    Real.exp (π * R ^ 2 + R * Real.sqrt (4 * π * ((d : ℝ) + 2))) *
      (4 * (d : ℝ) + 9 + 3 / 2 * R * Real.sqrt (4 * π * ((d : ℝ) + 2)))

theorem gaussianGlobalVerticalSlopeEnvelope_nonneg (d : ℕ) (R : ℝ≥0) :
    0 ≤ gaussianGlobalVerticalSlopeEnvelope d R := by
  unfold gaussianGlobalVerticalSlopeEnvelope
  have hC := gaussianStripSamplingFactor_nonneg (d + 1) 1
  positivity

/-- A single degree ceiling controls every coefficient direction below it. -/
theorem gaussianGlobalVerticalSlopeEnvelope_mono (R : ℝ≥0) :
    Monotone (fun d : ℕ => gaussianGlobalVerticalSlopeEnvelope d R) := by
  intro d e hde
  have hc : (d : ℝ) ≤ (e : ℝ) := by exact_mod_cast hde
  have hB := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
    (add_le_add hc (le_refl 2)) (by positivity : (0 : ℝ) ≤ 4 * π))
  have hC := gaussianStripSamplingFactor_nonneg (e + 1) 1
  unfold gaussianGlobalVerticalSlopeEnvelope
  apply mul_le_mul
  · exact mul_le_mul (gaussianStripSamplingFactor_mono 1 (Nat.add_le_add_right hde 1))
      (Real.exp_le_exp.mpr (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hB R.coe_nonneg)))
      (Real.exp_pos _).le hC
  · exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hc (by positivity)) le_rfl)
      (mul_le_mul_of_nonneg_left hB (by positivity))
  · positivity
  · positivity

/-- The full coordinate slope has Gaussian exponential type, with explicit degree loss. -/
theorem gaussianCoordinateVerticalSlope_le_globalEnvelope (d : ℕ) (R : ℝ≥0) :
    gaussianCoordinateVerticalSlope d R ≤ gaussianGlobalVerticalSlopeEnvelope d R := by
  let B : ℝ := Real.sqrt (4 * π * ((d : ℝ) + 2))
  let E : ℝ := Real.exp (π * (R : ℝ) ^ 2 + (R : ℝ) * B)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hC := gaussianStripSamplingFactor_nonneg (d + 1) 1
  have hBsq : B ^ 2 = 4 * π * ((d : ℝ) + 2) := Real.sq_sqrt (by positivity)
  have hA : Real.sqrt (4 * π * ((d : ℝ) + 1)) ≤ B := by
    apply Real.sqrt_le_sqrt
    nlinarith only [Real.pi_pos]
  have hA0 : Real.sqrt (4 * π * (d : ℝ)) ≤ B := by
    apply Real.sqrt_le_sqrt
    nlinarith only [Real.pi_pos]
  have he : 1 ≤ Real.exp ((R : ℝ) * B) := Real.one_le_exp (mul_nonneg R.coe_nonneg hB)
  have he0 : Real.exp ((R : ℝ) * Real.sqrt (4 * π * (d : ℝ))) ≤
      Real.exp ((R : ℝ) * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA0 R.coe_nonneg)
  have he1 : Real.exp ((R : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 1))) ≤
      Real.exp ((R : ℝ) * B) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA R.coe_nonneg)
  have hL : gaussianVerticalDefectSlope (d + 1) R ≤ E * (2 * B + π * R) := by
    unfold gaussianVerticalDefectSlope
    simp only [Nat.cast_add, Nat.cast_one]
    have hprod := mul_le_mul hA he1 (Real.exp_pos _).le hB
    have htail := mul_le_mul_of_nonneg_right he
      (show 0 ≤ B + π * (R : ℝ) by positivity)
    have hbr : Real.sqrt (4 * π * ((d : ℝ) + 1)) *
          Real.exp ((R : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 1))) +
          Real.sqrt (4 * π * ((d : ℝ) + 1 + 1)) + π * (R : ℝ) ≤
        Real.exp ((R : ℝ) * B) * (2 * B + π * (R : ℝ)) := by
      have hbb : Real.sqrt (4 * π * ((d : ℝ) + 1 + 1)) = B := by
        congr 2; ring
      rw [hbb]
      nlinarith only [hprod, htail]
    calc
      _ ≤ Real.exp (π * (R : ℝ) ^ 2) *
          (Real.exp ((R : ℝ) * B) * (2 * B + π * (R : ℝ))) :=
        mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
      _ = E * (2 * B + π * (R : ℝ)) := by dsimp only [E]; rw [Real.exp_add]; ring
  have hV : verticalPolynomialGaussianDefect d R + 1 ≤ E * (1 + (R : ℝ) * B) := by
    have hRA := mul_le_mul_of_nonneg_left hA R.coe_nonneg
    have hRB := mul_le_mul_of_nonneg_right he (mul_nonneg R.coe_nonneg hB)
    have hbr : Real.exp ((R : ℝ) * Real.sqrt (4 * π * d)) +
        (R : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 1)) ≤
        Real.exp ((R : ℝ) * B) * (1 + (R : ℝ) * B) := by
      nlinarith only [he0, hRA, hRB]
    calc
      _ = Real.exp (π * (R : ℝ) ^ 2) *
          (Real.exp ((R : ℝ) * Real.sqrt (4 * π * d)) +
            (R : ℝ) * Real.sqrt (4 * π * ((d : ℝ) + 1))) := by
        rw [verticalPolynomialGaussianDefect, abs_of_nonneg R.coe_nonneg]; ring
      _ ≤ Real.exp (π * (R : ℝ) ^ 2) *
          (Real.exp ((R : ℝ) * B) * (1 + (R : ℝ) * B)) :=
        mul_le_mul_of_nonneg_left hbr (Real.exp_pos _).le
      _ = E * (1 + (R : ℝ) * B) := by dsimp only [E]; rw [Real.exp_add]; ring
  have hfirst := mul_le_mul
    (mul_le_mul_of_nonneg_left hL (gaussianStripSamplingFactor_nonneg (d + 1) 1))
    (div_le_div_of_nonneg_right hA (by positivity : (0 : ℝ) ≤ 2 * π))
    (by positivity : 0 ≤ Real.sqrt (4 * π * ((d : ℝ) + 1)) / (2 * π))
    (by positivity : 0 ≤ gaussianStripSamplingFactor (d + 1) 1 * (E * (2 * B + π * R)))
  have hsecond := mul_le_mul
    (gaussianStripSamplingFactor_mono 1 (Nat.le_succ d)) hV
    (add_nonneg (verticalPolynomialGaussianDefect_nonneg d R) (by positivity))
    (gaussianStripSamplingFactor_nonneg (d + 1) 1)
  have hbracket : (2 * B + π * (R : ℝ)) * (B / (2 * π)) + (1 + (R : ℝ) * B) =
      4 * (d : ℝ) + 9 + 3 / 2 * (R : ℝ) * B := by
    field_simp
    nlinarith only [hBsq]
  calc
    gaussianCoordinateVerticalSlope d R ≤
        gaussianStripSamplingFactor (d + 1) 1 * (E * (2 * B + π * R)) * (B / (2 * π)) +
        gaussianStripSamplingFactor (d + 1) 1 * (E * (1 + (R : ℝ) * B)) :=
      add_le_add hfirst hsecond
    _ = gaussianStripSamplingFactor (d + 1) 1 * E *
        ((2 * B + π * (R : ℝ)) * (B / (2 * π)) + (1 + (R : ℝ) * B)) := by ring
    _ = gaussianGlobalVerticalSlopeEnvelope d R := by
      rw [hbracket]
      rfl

end GaloisForLFunctions
