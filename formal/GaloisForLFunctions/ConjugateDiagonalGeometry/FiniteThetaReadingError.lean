import GaloisForLFunctions.ConjugateDiagonalGeometry.FiniteThetaSourceCurvature
import GaloisForLFunctions.ConjugateDiagonalGeometry.ExplicitSourceMetric
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Uniform finite-theta reading error

Compact Green testing transfers the weighted potential error to positive
curvature readings. The moving moment Laplacian and disc area are absorbed
by one quartic exponential throughout the joint arithmetic window.
-/

open Complex MeasureTheory Filter Set Metric Laplacian InnerProductSpace
open scoped Laplacian Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- A compact positive reading from a prescribed finite integer theta prefix. -/
def finiteThetaSourceReading (φ : ℂ → ℝ) (n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z, sourceCutoff n z * φ z *
    finiteThetaSourceCurvature (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z

/-- Compact Green testing transfers the finite-source potential estimate to every smooth test. -/
lemma abs_finiteThetaSourceReading_sub_explicit_le (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    {n : ℕ} (hn : 1 ≤ n) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * φ w) z| ≤ sourceCutoffControl n * B) :
    |finiteThetaSourceReading φ n - explicitSourceReading φ n| ≤
      (2 * Real.pi)⁻¹ * B * finiteThetaPotentialConstant *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) * (Real.pi * ((n : ℝ) + 2) ^ 2) := by
  let ψ : ℂ → ℝ := fun z => sourceCutoff n z * φ z
  let V : ℂ → ℝ := fun z =>
    finiteThetaSourcePotential (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z -
      xiLogPotential (explicitSourceRegulator n) z
  have hpψ : ContDiff ℝ 2 ψ := (sourceCutoff n).contDiff.mul hp
  have hcψ : HasCompactSupport ψ := (sourceCutoff n).hasCompactSupport.mul_right
  have hη := explicitSourceRegulator_pos n
  have hΔ := continuous_test_laplacian hpψ
  have hV : Continuous V :=
    (contDiff_finiteThetaSourcePotential hη _).continuous.sub (contDiff_xiLogPotential hη).continuous
  have hu : IntegrableOn (fun z =>
      finiteThetaSourcePotential (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z * Δ ψ z)
      (closedBall (0 : ℂ) |(n : ℝ) + 2|) :=
    (((contDiff_finiteThetaSourcePotential hη _).continuous.mul hΔ).continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  have hv : IntegrableOn (fun z => xiLogPotential (explicitSourceRegulator n) z * Δ ψ z)
      (closedBall (0 : ℂ) |(n : ℝ) + 2|) :=
    (((contDiff_xiLogPotential hη).continuous.mul hΔ).continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  have heq (g : ℂ → ℝ) :
      (∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, g z * Δ ψ z) = ∫ z, g z * Δ ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [sourceCutoff_laplacian_eq_zero_outside n φ hp z hz, mul_zero]
  have hgreenF := twice_integral_finiteThetaSourceCurvature ψ hpψ hcψ hη (explicitThetaIntegerCutoff n)
  have hgreenX := twice_integral_xiCurvatureDensity_of_pos ψ hpψ hcψ hη
  have herr : finiteThetaSourceReading φ n - explicitSourceReading φ n =
      (2 * Real.pi)⁻¹ * ∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, V z * Δ ψ z := by
    have hdiff : (∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, V z * Δ ψ z) =
        (∫ z, finiteThetaSourcePotential (explicitSourceRegulator n) (explicitThetaIntegerCutoff n) z * Δ ψ z) -
          ∫ z, xiLogPotential (explicitSourceRegulator n) z * Δ ψ z := by
      dsimp only [V]
      simp_rw [sub_mul]
      rw [integral_sub hu hv, heq, heq]
    rw [hdiff, ← hgreenF, ← hgreenX]
    unfold finiteThetaSourceReading explicitSourceReading
    dsimp only [ψ]
    rw [mul_inv_rev]
    ring
  have hbound : |∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, V z * Δ ψ z| ≤
      (B * finiteThetaPotentialConstant * Real.exp (-(((n : ℝ) + 1) ^ 4))) *
        (Real.pi * ((n : ℝ) + 2) ^ 2) := by
    calc
      |∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, V z * Δ ψ z| ≤
          ∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, |V z * Δ ψ z| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (closedBall (0 : ℂ) |(n : ℝ) + 2|)) (fun z => V z * Δ ψ z)
      _ ≤ ∫ _z in closedBall (0 : ℂ) |(n : ℝ) + 2|,
          B * finiteThetaPotentialConstant * Real.exp (-(((n : ℝ) + 1) ^ 4)) := by
        apply setIntegral_mono_on
          (((hV.mul hΔ).abs.continuousOn).integrableOn_compact (isCompact_closedBall _ _))
          (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
          measurableSet_closedBall
        intro z hz
        have hz' : ‖z‖ ≤ (n : ℝ) + 2 := by
          simpa only [mem_closedBall, dist_zero_right,
            abs_of_pos (by positivity : 0 < (n : ℝ) + 2)] using hz
        have hpv := sourceControl_mul_finiteThetaPotential_error_le hn hz'
        dsimp only [Pi.mul_apply]
        rw [abs_mul]
        calc
          |V z| * |Δ ψ z| ≤ |V z| * (sourceCutoffControl n * B) :=
            mul_le_mul_of_nonneg_left (hb z hz) (abs_nonneg _)
          _ = B * (sourceCutoffControl n * |V z|) := by ring
          _ ≤ B * (finiteThetaPotentialConstant * Real.exp (-(((n : ℝ) + 1) ^ 4))) :=
            mul_le_mul_of_nonneg_left hpv hB
          _ = _ := by ring
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul]
        have harea : volume.real (closedBall (0 : ℂ) |(n : ℝ) + 2|) =
            Real.pi * ((n : ℝ) + 2) ^ 2 := by
          rw [measureReal_def, Complex.volume_closedBall]
          simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.coe_toReal,
            NNReal.coe_real_pi, sq_abs]
          ring
        rw [harea]
        ring
  rw [herr, abs_mul, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  calc
    (2 * Real.pi)⁻¹ * |∫ z in closedBall (0 : ℂ) |(n : ℝ) + 2|, V z * Δ ψ z| ≤
      (2 * Real.pi)⁻¹ * ((B * finiteThetaPotentialConstant *
        Real.exp (-(((n : ℝ) + 1) ^ 4))) * (Real.pi * ((n : ℝ) + 2) ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring

/-- Finite arithmetic truncation remains controlled throughout the moving C² window. -/
theorem finiteThetaSourceReading_error_le_window (f : CompactTest) {A : ℝ}
    (hA0 : 0 ≤ A) (hA : ∀ z : ℂ, ‖tr f.1 z‖ ≤ A * Real.exp (‖z‖ ^ 2))
    (j : ℕ) {n : ℕ} (hn : 1 ≤ n) (L τ : ℝ) (hτ : |τ| ≤ (n : ℝ))
    (hL : (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    |finiteThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      explicitSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n| ≤
      (((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2) * (4 * Real.pi * finiteThetaPotentialConstant)) *
        Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62) := by
  let E : ℝ := 2 * (((n : ℝ) + 3 + |τ|) ^ 2 + (j : ℝ) * |L| * ((n : ℝ) + 7 / 2))
  have hb : ∀ z ∈ closedBall (0 : ℂ) |(n : ℝ) + 2|,
      |Δ (fun w => sourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
        sourceCutoffControl n * (4 ^ (j + 1) * A ^ 2 * Real.exp E) := by
    intro z hz
    have hz' : ‖z‖ ≤ (n : ℝ) + 2 := by
      simpa only [mem_closedBall, dist_zero_right,
        abs_of_pos (by positivity : 0 < (n : ℝ) + 2)] using hz
    have h := abs_laplacian_cutoff_moving_moment_le f hA0 hA L j n 0 τ hz'
    simp only [sourceTranslate_zero, abs_zero, zero_add] at h
    refine h.trans_eq ?_
    unfold sourceSquareEnvelope
    dsimp only [E]
    rw [pow_succ (4 : ℝ) j]
    ring
  have h := abs_finiteThetaSourceReading_sub_explicit_le _
    (contDiff_sourceDepthKernel (sourceTwist τ f) L j) hn (by positivity) hb
  have he := source_poly_exp_window_le (C := 0) (by norm_num) j n L τ hτ hL
  simp only [mul_zero, zero_mul, add_zero] at he
  have hcoef : 0 ≤ (2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2 *
      (2 * finiteThetaPotentialConstant) := by
    exact mul_nonneg (by positivity) (mul_nonneg (by norm_num) finiteThetaPotentialConstant_nonneg)
  refine h.trans ?_
  calc
    (2 * Real.pi)⁻¹ * (4 ^ (j + 1) * A ^ 2 * Real.exp E) * finiteThetaPotentialConstant *
        Real.exp (-(((n : ℝ) + 1) ^ 4)) * (Real.pi * ((n : ℝ) + 2) ^ 2) =
      ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2 * (2 * finiteThetaPotentialConstant)) *
        (Real.pi * ((n : ℝ) + 2) ^ 2 / 2 * Real.exp (-(((n : ℝ) + 1) ^ 4) + E)) := by
      rw [Real.exp_add]
      ring
    _ ≤ ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * A ^ 2 * (2 * finiteThetaPotentialConstant)) *
        (2 * Real.pi * Real.exp (-((n : ℝ) ^ 4) + 56 * (n : ℝ) ^ 2 + 62)) :=
      mul_le_mul_of_nonneg_left he hcoef
    _ = _ := by ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaSourceReading_error_le_window
