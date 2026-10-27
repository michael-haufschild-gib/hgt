import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialSourceScale
import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaSourceCurvature
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspStripAmplitudeBounds

/-!
# Potential stability for polynomial theta prefixes

The cutoff lies in a fixed vertical strip. Uniform strip amplitude bounds
therefore remove the ordinate from finite-source potential sensitivity.
The polynomial prefix pays both regulator sensitivity and cutoff derivatives.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower HTGeometry

/-- Finite amplitude error controls the regularized potential throughout every vertical strip. -/
theorem abs_finiteThetaSourcePotential_sub_xi_le_strip {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (N : ℕ) {z : ℂ} (hz : |z.re| ≤ R) :
    |finiteThetaSourcePotential η N z - xiLogPotential η z| ≤
      thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope R ^ 2 *
        Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) / η := by
  have ha := norm_finiteThetaAmplitude_le_strip N hR hz
  have hb := norm_fullThetaAmplitude_le_strip hR hz
  have hd := norm_finiteThetaAmplitude_sub_full_le_strip N hR hz
  rw [bilateral_fullTheta_eq_xi] at hb hd
  have hs := half_log_normSq_stability hη (finiteThetaAmplitude N z) (xi z)
  have he : |finiteThetaSourcePotential η N z - xiLogPotential η z| =
      |(1 / 2 : ℝ) * Real.log (Complex.normSq (finiteThetaAmplitude N z) + η) -
        (1 / 2 : ℝ) * Real.log (Complex.normSq (xi z) + η)| := by
    simp only [finiteThetaSourcePotential, xiLogPotential, radialLogPotential,
      Complex.normSq_apply, pow_two]
  rw [he]
  refine hs.trans ?_
  have hsum : ‖finiteThetaAmplitude N z‖ + ‖xi z‖ ≤ 2 * thetaAmplitudeEnvelope R := by
    linarith only [ha, hb]
  have hnum := mul_le_mul hsum hd (norm_nonneg _)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (thetaAmplitudeEnvelope_nonneg R))
  calc
    ((‖finiteThetaAmplitude N z‖ + ‖xi z‖) * ‖finiteThetaAmplitude N z - xi z‖) / (2 * η) ≤
        ((2 * thetaAmplitudeEnvelope R) *
          (thetaCuspIntegerTailConstant * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) *
            thetaAmplitudeEnvelope R)) / (2 * η) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = _ := by field_simp [hη.ne']

/-- Actual fixed-strip amplitude constant for the finite-source error. -/
def stripThetaPotentialConstant : ℝ := thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope 3 ^ 2

lemma stripThetaPotentialConstant_nonneg : 0 ≤ stripThetaPotentialConstant :=
  mul_nonneg thetaCuspIntegerTailConstant_nonneg (sq_nonneg _)

/-- Polynomial finite-prefix control holds throughout the source cutoff support. -/
theorem stripSourceControl_mul_finiteThetaPotential_error_le (n : ℕ)
    {z : ℂ} (hz : z ∈ tsupport (stripSourceCutoff n)) :
    stripSourceCutoffControl *
      |finiteThetaSourcePotential (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z -
        xiLogPotential (polynomialSourceRegulator n) z| ≤
      stripThetaPotentialConstant / ((n : ℝ) + 1) ^ 20 := by
  have hδ := stripSourceCutoff_support_re n hz
  have ht := abs_add_le (z.re - 1 / 2) (1 / 2 : ℝ)
  rw [sub_add_cancel, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at ht
  have hre : |z.re| ≤ (3 : ℝ) := by linarith only [hδ, ht]
  have h := abs_finiteThetaSourcePotential_sub_xi_le_strip (polynomialSourceRegulator_pos n)
    (by norm_num) (polynomialThetaIntegerCutoff n) hre
  have he : thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope 3 ^ 2 *
      Real.exp (-((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) /
        polynomialSourceRegulator n =
      stripThetaPotentialConstant *
        Real.exp (polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) := by
    unfold polynomialSourceRegulator stripThetaPotentialConstant
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he] at h
  have hM : 0 ≤ stripSourceCutoffControl := le_trans zero_le_one one_le_stripSourceCutoffControl
  refine (mul_le_mul_of_nonneg_left h hM).trans ?_
  calc
    stripSourceCutoffControl * (stripThetaPotentialConstant *
        Real.exp (polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2)) =
      stripThetaPotentialConstant * (stripSourceCutoffControl *
        Real.exp (polynomialSourceLogScale n - ((polynomialThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2)) := by ring
    _ ≤ stripThetaPotentialConstant * (1 / ((n : ℝ) + 1) ^ 20) :=
      mul_le_mul_of_nonneg_left (stripSourceControl_finite_tail_le n) stripThetaPotentialConstant_nonneg
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.stripSourceControl_mul_finiteThetaPotential_error_le
