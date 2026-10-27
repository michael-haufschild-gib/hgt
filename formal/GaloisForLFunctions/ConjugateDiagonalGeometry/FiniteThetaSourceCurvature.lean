import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaRegulatorScale
import GaloisForLFunctions.ConjugateDiagonalGeometry.ThetaSourceMetric
import GaloisForLFunctions.HTGeometry.RegularizedLogStability

/-!
# Positive curvature of finite arithmetic theta amplitudes

The entire finite amplitude has a literal first-moment derivative.
Regularized potential stability and the prescribed integer cutoff give
a uniform potential error after all spatial cutoff derivative losses.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open _root_.RHTower HTGeometry

/-- Regularized potential of a literal finite theta amplitude. -/
def finiteThetaSourcePotential (η : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  radialLogPotential η (finiteThetaAmplitude N z)

/-- Positive curvature using only finitely many integer theta summands. -/
def finiteThetaSourceCurvature (η : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  η * Complex.normSq (finiteThetaFirstMoment N z) /
    (Complex.normSq (finiteThetaAmplitude N z) + η) ^ 2

theorem finiteThetaSourceCurvature_nonneg {η : ℝ} (hη : 0 ≤ η) (N : ℕ) (z : ℂ) :
    0 ≤ finiteThetaSourceCurvature η N z :=
  div_nonneg (mul_nonneg hη (Complex.normSq_nonneg _)) (sq_nonneg _)

theorem contDiff_finiteThetaSourcePotential {η : ℝ} (hη : 0 < η) (N : ℕ) :
    ContDiff ℝ 2 (finiteThetaSourcePotential η N) :=
  (contDiff_radialLogPotential hη).comp
    ((differentiable_finiteThetaAmplitude N).contDiff.restrict_scalars ℝ)

/-- The finite physical source may have a cusp; its entire amplitude still has positive curvature. -/
theorem laplacian_finiteThetaSourcePotential {η : ℝ} (hη : 0 < η) (N : ℕ) (z : ℂ) :
    Δ (finiteThetaSourcePotential η N) z = 2 * finiteThetaSourceCurvature η N z := by
  rw [show finiteThetaSourcePotential η N = radialLogPotential η ∘ finiteThetaAmplitude N from rfl,
    laplacian_real_holomorphic_comp _ _ (contDiff_radialLogPotential hη)
      (differentiable_finiteThetaAmplitude N), laplacian_radialLogPotential hη,
    deriv_finiteThetaAmplitude, Complex.normSq_neg]
  unfold finiteThetaSourceCurvature
  ring

lemma bilateral_fullTheta_eq_xi (z : ℂ) :
    bilateralLaplace thetaCuspTiltSource ((1 / 2 : ℂ) - z) = xi z :=
  thetaSourceAmplitude_eq_xi z

/-- Finite amplitude error controls the regularized potential throughout every disc. -/
theorem abs_finiteThetaSourcePotential_sub_xi_le {η R : ℝ} (hη : 0 < η) (hR : 0 ≤ R)
    (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ R) :
    |finiteThetaSourcePotential η N z - xiLogPotential η z| ≤
      thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope R ^ 2 *
        Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) / η := by
  have ha := norm_finiteThetaAmplitude_le N hR hz
  have hb := norm_fullThetaAmplitude_le hR hz
  have hd := norm_finiteThetaAmplitude_sub_full_le N hR hz
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

/-- Fixed arithmetic constant in the finite-source potential estimate. -/
def finiteThetaPotentialConstant : ℝ :=
  thetaCuspIntegerTailConstant *
    (HedenmalmThetaSource.thetaEnvelopeUpper * thetaAmplitudeProfileMass) ^ 2

lemma finiteThetaPotentialConstant_nonneg : 0 ≤ finiteThetaPotentialConstant :=
  mul_nonneg thetaCuspIntegerTailConstant_nonneg (sq_nonneg _)

/-- The prescribed integer cutoff controls the potential error after every cutoff derivative loss. -/
theorem sourceControl_mul_finiteThetaPotential_error_le {n : ℕ} (hn : 1 ≤ n)
    {z : ℂ} (hz : ‖z‖ ≤ (n : ℝ) + 2) :
    sourceCutoffControl n *
      |finiteThetaSourcePotential (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z -
        xiLogPotential (explicitSourceRegulator n) z| ≤
      finiteThetaPotentialConstant * Real.exp (-(((n : ℝ) + 1) ^ 4)) := by
  have h := abs_finiteThetaSourcePotential_sub_xi_le (explicitSourceRegulator_pos n)
    (by positivity) (explicitThetaIntegerCutoff n) hz
  have he : thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope ((n : ℝ) + 2) ^ 2 *
      Real.exp (-((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) /
        explicitSourceRegulator n =
      thetaCuspIntegerTailConstant * thetaAmplitudeEnvelope ((n : ℝ) + 2) ^ 2 *
        Real.exp (explicitSourceLogScale n - ((explicitThetaIntegerCutoff n + 1 : ℕ) : ℝ) ^ 2) := by
    unfold explicitSourceRegulator
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he] at h
  exact (mul_le_mul_of_nonneg_left h (sourceCutoffControl_pos n).le).trans
    (finiteTheta_potential_envelope_le hn)

/-- Compact Green testing of the finite positive arithmetic curvature. -/
theorem twice_integral_finiteThetaSourceCurvature (φ : ℂ → ℝ)
    (hp : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    2 * (∫ z, φ z * finiteThetaSourceCurvature η N z) =
      ∫ z, finiteThetaSourcePotential η N z * Δ φ z := by
  calc
    2 * (∫ z, φ z * finiteThetaSourceCurvature η N z) =
        ∫ z, φ z * (2 * finiteThetaSourceCurvature η N z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = ∫ z, φ z * Δ (finiteThetaSourcePotential η N) z := by
      simp_rw [laplacian_finiteThetaSourcePotential hη]
    _ = ∫ z, Δ φ z * finiteThetaSourcePotential η N z :=
      source_green_identity _ φ (contDiff_finiteThetaSourcePotential hη N) hp hc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      exact mul_comm _ _

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.sourceControl_mul_finiteThetaPotential_error_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.twice_integral_finiteThetaSourceCurvature
