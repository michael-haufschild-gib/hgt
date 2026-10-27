import GaloisForLFunctions.ConjugateDiagonalGeometry.XiExpRegulatorError
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFiniteAmplitudeBounds

/-!
# A prescribed integer cutoff for theta curvature readings

The squared integer cutoff dominates the regulator's logarithmic scale
and the amplitude's disc growth. The resulting Gaussian tail pays the
cutoff derivative control without any bound on that control's growth.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower HedenmalmThetaSource

/-- A prescribed finite integer cutoff; its prefix uses no divisor coordinate or error test. -/
def explicitThetaIntegerCutoff (n : ℕ) : ℕ :=
  ⌈explicitSourceLogScale n⌉₊ + n + 10

lemma explicitSourceLogScale_nonneg (n : ℕ) : 0 ≤ explicitSourceLogScale n := by
  unfold explicitSourceLogScale
  exact mul_nonneg (Real.exp_pos _).le (sourceCutoffControl_pos _).le

lemma sourceCutoffControl_le_explicitSourceLogScale (n : ℕ) :
    sourceCutoffControl n ≤ explicitSourceLogScale n := by
  have h : 1 ≤ Real.exp (((n : ℝ) + 1) ^ 4) := Real.one_le_exp (by positivity)
  have hm := mul_le_mul_of_nonneg_right h (sourceCutoffControl_pos n).le
  simpa only [one_mul, explicitSourceLogScale] using hm

lemma sourceCutoffControl_le_exp_logScale (n : ℕ) :
    sourceCutoffControl n ≤ Real.exp (explicitSourceLogScale n) := by
  have h := Real.log_le_sub_one_of_pos (Real.exp_pos (explicitSourceLogScale n))
  rw [Real.log_exp] at h
  exact (sourceCutoffControl_le_explicitSourceLogScale n).trans (by linarith only [h])

lemma radius_fourth_add_one_le_explicitSourceLogScale (n : ℕ) :
    ((n : ℝ) + 1) ^ 4 + 1 ≤ explicitSourceLogScale n := by
  have h := Real.log_le_sub_one_of_pos (Real.exp_pos (((n : ℝ) + 1) ^ 4))
  rw [Real.log_exp] at h
  have hm := le_mul_of_one_le_right (Real.exp_pos (((n : ℝ) + 1) ^ 4)).le
    (one_le_sourceCutoffControl n)
  unfold explicitSourceLogScale
  linarith only [h, hm]

lemma twice_logScale_sub_sq_le_neg_fourth {n : ℕ} (hn : 1 ≤ n) :
    2 * explicitSourceLogScale n - explicitSourceLogScale n ^ 2 ≤ -(((n : ℝ) + 1) ^ 4) := by
  have hx := source_radius_fourth_ge_sixteen hn
  have hK := radius_fourth_add_one_le_explicitSourceLogScale n
  have hp := mul_nonneg (explicitSourceLogScale_nonneg n)
    (show 0 ≤ explicitSourceLogScale n - 3 by linarith only [hx, hK])
  nlinarith only [hp, hK]

/-- Integer cutoff mass pays both the regulator scale and the amplitude growth radius. -/
lemma explicitThetaIntegerCutoff_sq_lower (n : ℕ) :
    explicitSourceLogScale n ^ 2 + ((n : ℝ) + 10) ^ 2 ≤
      ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2 := by
  have hceil := Nat.le_ceil (explicitSourceLogScale n)
  have he : ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) =
      (⌈explicitSourceLogScale n⌉₊ : ℝ) + (n : ℝ) + 11 := by
    simp only [explicitThetaIntegerCutoff, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    ring
  rw [he]
  have hsq := pow_le_pow_left₀
    (show 0 ≤ explicitSourceLogScale n + ((n : ℝ) + 10) by
      exact add_nonneg (explicitSourceLogScale_nonneg n) (by positivity))
    (show explicitSourceLogScale n + ((n : ℝ) + 10) ≤
      (⌈explicitSourceLogScale n⌉₊ : ℝ) + (n : ℝ) + 11 by linarith only [hceil]) 2
  have hp := mul_nonneg (explicitSourceLogScale_nonneg n)
    (show 0 ≤ (n : ℝ) + 10 by positivity)
  nlinarith only [hsq, hp]

lemma thetaAmplitudeEnvelope_sourceRadius_sq (n : ℕ) :
    thetaAmplitudeEnvelope ((n : ℝ) + 2) ^ 2 =
      (thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2 *
        Real.exp (((n : ℝ) + 19 / 2) ^ 2 / 12) := by
  have hm : 0 ≤ (n : ℝ) + 2 + 5 / 2 := by positivity
  unfold thetaAmplitudeEnvelope thetaCuspTiltDecayConstant
  rw [abs_of_nonneg hm]
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  rw [show 2 * (((n : ℝ) + 2 + 5 / 2 + 5) ^ 2 / 24) =
    ((n : ℝ) + 19 / 2) ^ 2 / 12 by ring]
  ring

lemma sourceRadius_amplitude_exponent_le (n : ℕ) :
    ((n : ℝ) + 19 / 2) ^ 2 / 12 ≤ ((n : ℝ) + 10) ^ 2 := by
  have h := pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ) + 19 / 2)
    (show (n : ℝ) + 19 / 2 ≤ (n : ℝ) + 10 by linarith) 2
  nlinarith only [h, sq_nonneg ((n : ℝ) + 10)]

/-- The finite integer tail absorbs the full logarithmic-potential regulator sensitivity. -/
theorem finiteTheta_potential_envelope_le {n : ℕ} (hn : 1 ≤ n) :
    sourceCutoffControl n *
      (thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope ((n : ℝ) + 2) ^ 2 *
        Real.exp (explicitSourceLogScale n - ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2)) ≤
    (thetaCuspIntegerTailConstant * (thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2) *
      Real.exp (-(((n : ℝ) + 1) ^ 4)) := by
  have htail := thetaCuspIntegerTailConstant_nonneg
  have hcoef : 0 ≤ thetaCuspIntegerTailConstant *
      (thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2 :=
    mul_nonneg thetaCuspIntegerTailConstant_nonneg (sq_nonneg _)
  rw [thetaAmplitudeEnvelope_sourceRadius_sq]
  calc
    sourceCutoffControl n *
        (thetaCuspIntegerTailConstant *
          ((thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2 *
            Real.exp (((n : ℝ) + 19 / 2) ^ 2 / 12)) *
          Real.exp (explicitSourceLogScale n - ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2)) ≤
        Real.exp (explicitSourceLogScale n) *
        (thetaCuspIntegerTailConstant *
          ((thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2 *
            Real.exp (((n : ℝ) + 19 / 2) ^ 2 / 12)) *
          Real.exp (explicitSourceLogScale n - ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_right (sourceCutoffControl_le_exp_logScale n) (by positivity)
    _ = (thetaCuspIntegerTailConstant * (thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2) *
        Real.exp (((n : ℝ) + 19 / 2) ^ 2 / 12 + 2 * explicitSourceLogScale n -
          ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) := by
      rw [show ((n : ℝ) + 19 / 2) ^ 2 / 12 + 2 * explicitSourceLogScale n -
          ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2 =
        explicitSourceLogScale n + (((n : ℝ) + 19 / 2) ^ 2 / 12) +
          (explicitSourceLogScale n - ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) by ring,
        Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by
        have ha := sourceRadius_amplitude_exponent_le n
        have hc := explicitThetaIntegerCutoff_sq_lower n
        have hK := twice_logScale_sub_sq_le_neg_fourth hn
        linarith only [ha, hc, hK])) hcoef

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteTheta_potential_envelope_le
