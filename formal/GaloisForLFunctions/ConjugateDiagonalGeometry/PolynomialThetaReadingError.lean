import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialThetaPotential
import GaloisForLFunctions.ConjugateDiagonalGeometry.PolynomialSourceError
import GaloisForLFunctions.ConjugateDiagonalGeometry.StripSourceMomentBounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Polynomial finite-source reading errors

Compact Green testing separates integer truncation from logarithmic
regularization. The fixed-strip derivative bounds turn both local errors
into polynomially decaying errors for every test in the shared aperture.
-/

open Complex MeasureTheory Set Metric Laplacian InnerProductSpace
open scoped Laplacian
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Full theta curvature reading with a fixed-strip cutoff and polynomial logarithmic scale. -/
def polynomialSourceReading (φ : ℂ → ℝ) (n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z, stripSourceCutoff n z * φ z * xiCurvatureDensity (polynomialSourceRegulator n) z

/-- Finite arithmetic curvature reading with a polynomial integer prefix. -/
def polynomialThetaSourceReading (φ : ℂ → ℝ) (n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z, stripSourceCutoff n z * φ z *
    finiteThetaSourceCurvature (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z

/-- Compact Green testing transfers the finite-source potential estimate to every smooth test. -/
lemma abs_polynomialThetaSourceReading_sub_full_le (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ z : ℂ,
      |Δ (fun w => stripSourceCutoff n w * φ w) z| ≤ stripSourceCutoffControl * B) :
    |polynomialThetaSourceReading φ n - polynomialSourceReading φ n| ≤
      (2 * Real.pi)⁻¹ * B * stripThetaPotentialConstant *
        (1 / ((n : ℝ) + 1) ^ 20) * (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2) := by
  let ψ : ℂ → ℝ := fun z => stripSourceCutoff n z * φ z
  let V : ℂ → ℝ := fun z =>
    finiteThetaSourcePotential (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z -
      xiLogPotential (polynomialSourceRegulator n) z
  have hpψ : ContDiff ℝ 2 ψ := (contDiff_stripSourceCutoff n).mul hp
  have hcψ : HasCompactSupport ψ := (hasCompactSupport_stripSourceCutoff n).mul_right
  have hη := polynomialSourceRegulator_pos n
  have hΔ := continuous_test_laplacian hpψ
  have hV : Continuous V :=
    (contDiff_finiteThetaSourcePotential hη _).continuous.sub (contDiff_xiLogPotential hη).continuous
  have hu : IntegrableOn (fun z =>
      finiteThetaSourcePotential (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z * Δ ψ z)
      (closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|) :=
    (((contDiff_finiteThetaSourcePotential hη _).continuous.mul hΔ).continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  have hv : IntegrableOn (fun z => xiLogPotential (polynomialSourceRegulator n) z * Δ ψ z)
      (closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|) :=
    (((contDiff_xiLogPotential hη).continuous.mul hΔ).continuousOn).integrableOn_compact
      (isCompact_closedBall _ _)
  have heq (g : ℂ → ℝ) :
      (∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, g z * Δ ψ z) = ∫ z, g z * Δ ψ z := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    rw [stripSourceCutoff_laplacian_eq_zero_outside n φ hp z hz, mul_zero]
  have hgreenF := twice_integral_finiteThetaSourceCurvature ψ hpψ hcψ hη (polynomialThetaIntegerCutoff n)
  have hgreenX := twice_integral_xiCurvatureDensity_of_pos ψ hpψ hcψ hη
  have herr : polynomialThetaSourceReading φ n - polynomialSourceReading φ n =
      (2 * Real.pi)⁻¹ * ∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, V z * Δ ψ z := by
    have hdiff : (∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, V z * Δ ψ z) =
        (∫ z, finiteThetaSourcePotential (polynomialSourceRegulator n) (polynomialThetaIntegerCutoff n) z * Δ ψ z) -
          ∫ z, xiLogPotential (polynomialSourceRegulator n) z * Δ ψ z := by
      dsimp only [V]
      simp_rw [sub_mul]
      rw [integral_sub hu hv, heq, heq]
    rw [hdiff, ← hgreenF, ← hgreenX]
    unfold polynomialThetaSourceReading polynomialSourceReading
    dsimp only [ψ]
    rw [mul_inv_rev]
    ring
  have hbound : |∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, V z * Δ ψ z| ≤
      (B * stripThetaPotentialConstant * (1 / ((n : ℝ) + 1) ^ 20)) *
        (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2) := by
    calc
      |∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, V z * Δ ψ z| ≤
          ∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, |V z * Δ ψ z| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := volume.restrict (closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|)) (fun z => V z * Δ ψ z)
      _ ≤ ∫ _z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|,
          B * stripThetaPotentialConstant * (1 / ((n : ℝ) + 1) ^ 20) := by
        apply setIntegral_mono_on
          (((hV.mul hΔ).abs.continuousOn).integrableOn_compact (isCompact_closedBall _ _))
          (continuous_const.continuousOn.integrableOn_compact (isCompact_closedBall _ _))
          measurableSet_closedBall
        intro z hz
        by_cases hzS : z ∈ tsupport (stripSourceCutoff n)
        · have hpv := stripSourceControl_mul_finiteThetaPotential_error_le n hzS
          dsimp only [Pi.mul_apply]
          rw [abs_mul]
          calc
            |V z| * |Δ ψ z| ≤ |V z| * (stripSourceCutoffControl * B) :=
              mul_le_mul_of_nonneg_left (hb z) (abs_nonneg _)
            _ = B * (stripSourceCutoffControl * |V z|) := by ring
            _ ≤ B * (stripThetaPotentialConstant / ((n : ℝ) + 1) ^ 20) :=
              mul_le_mul_of_nonneg_left hpv hB
            _ = _ := by ring
        · have hz0 := stripSourceCutoff_laplacian_eq_zero_off_support n φ hp hzS
          dsimp only [Pi.mul_apply]
          change |V z * Δ (fun w => stripSourceCutoff n w * φ w) z| ≤ _
          rw [hz0, mul_zero, abs_zero]
          have hC := stripThetaPotentialConstant_nonneg
          positivity
      _ = _ := by
        rw [setIntegral_const, smul_eq_mul]
        have harea : volume.real (closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|) =
            Real.pi * (11 * ((n : ℝ) + 1)) ^ 2 := by
          rw [measureReal_def, Complex.volume_closedBall]
          simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
            ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.coe_toReal,
            NNReal.coe_real_pi, sq_abs]
          ring
        rw [harea]
        ring
  rw [herr, abs_mul, abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]
  calc
    (2 * Real.pi)⁻¹ * |∫ z in closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|, V z * Δ ψ z| ≤
      (2 * Real.pi)⁻¹ * ((B * stripThetaPotentialConstant *
        (1 / ((n : ℝ) + 1) ^ 20)) * (Real.pi * (11 * ((n : ℝ) + 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by ring


lemma abs_polynomialSourceReading_sub_current_le (φ : ℂ → ℝ) (hp : ContDiff ℝ 2 φ)
    (n : ℕ) {B : ℝ}
    (hb : ∀ z ∈ closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|,
      |Δ (fun w => stripSourceCutoff n w * φ w) z| ≤ B) :
    |polynomialSourceReading φ n - xiCurrentPairing (fun z => stripSourceCutoff n z * φ z)| ≤
      (2 * Real.pi)⁻¹ * B * xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1)) := by
  have h := abs_xiCurvatureReading_sub_current_le_of_pos
    (fun z => stripSourceCutoff n z * φ z) ((contDiff_stripSourceCutoff n).mul hp)
    (hasCompactSupport_stripSourceCutoff n).mul_right 0 (11 * ((n : ℝ) + 1)) B
    (stripSourceCutoff_laplacian_eq_zero_outside n φ hp) hb (polynomialSourceRegulator_pos n)
  have he : polynomialSourceReading φ n - xiCurrentPairing (fun z => stripSourceCutoff n z * φ z) =
      Real.pi⁻¹ * ((∫ z, (stripSourceCutoff n z * φ z) * xiCurvatureDensity (polynomialSourceRegulator n) z) -
        (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ (fun w => stripSourceCutoff n w * φ w) z) := by
    unfold polynomialSourceReading xiCurrentPairing
    ring
  rw [he, abs_mul, abs_of_pos (inv_pos.mpr Real.pi_pos)]
  calc
    Real.pi⁻¹ * |(∫ z, (stripSourceCutoff n z * φ z) * xiCurvatureDensity (polynomialSourceRegulator n) z) -
        (1 / 2 : ℝ) * ∫ z, Real.log ‖xi z‖ * Δ (fun w => stripSourceCutoff n w * φ w) z| ≤
        Real.pi⁻¹ * ((1 / 2 : ℝ) * B *
          xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left h (inv_nonneg.mpr Real.pi_pos.le)
    _ = _ := by ring

/-- Finite theta truncation has sixth-degree decay on the full growing test aperture. -/
theorem polynomialThetaSourceReading_error_le (f : CompactTest) {a : ℝ}
    (ha : 0 ≤ a) (hsupp : ∀ x, f.1 x ≠ 0 → |x| ≤ a)
    (L τ : ℝ) (j n : ℕ)
    (hwindow : a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1)) :
    |polynomialThetaSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
      polynomialSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 *
        (242 * stripThetaPotentialConstant / ((n : ℝ) + 1) ^ 6) := by
  have hb (z : ℂ) :
      |Δ (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
        stripSourceCutoffControl * (4 ^ (j + 1) * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12) := by
    convert abs_laplacian_stripCutoff_aperture_moment_le_global f ha hsupp L τ j n hwindow z
      using 1
    ring
  refine (abs_polynomialThetaSourceReading_sub_full_le _
    (contDiff_sourceDepthKernel (sourceTwist τ f) L j) n (by positivity) hb).trans_eq ?_
  rw [pow_succ (4 : ℝ) j]
  field_simp [Real.pi_ne_zero, (show (n : ℝ) + 1 ≠ 0 by positivity)]
  ring

/-- The actual logarithmic-square mass yields a universal second-degree current error. -/
theorem exists_polynomialSourceMomentCurrentError_bound :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ n : ℕ, 1 ≤ n → ∀ (f : CompactTest) (a : ℝ),
      0 ≤ a → (∀ x, f.1 x ≠ 0 → |x| ≤ a) → ∀ (j : ℕ) (L τ : ℝ),
      a + (j : ℝ) * |L| ≤ 2 * Real.log ((n : ℝ) + 1) →
      |polynomialSourceReading (sourceDepthKernel (sourceTwist τ f) L j) n -
        xiCurrentPairing (fun z => stripSourceCutoff n z * sourceDepthKernel (sourceTwist τ f) L j z)| ≤
      (4 : ℝ) ^ j * sourceTestSize f ^ 2 * (E / ((n : ℝ) + 1) ^ 2) := by
  obtain ⟨D, hD, hlocal⟩ := exists_polynomialSourceLocalError_bound
  refine ⟨(2 / Real.pi) * D, by positivity, fun n hn f a ha hsupp j L τ hwindow => ?_⟩
  have hb : ∀ z ∈ closedBall (0 : ℂ) |11 * ((n : ℝ) + 1)|,
      |Δ (fun w => stripSourceCutoff n w * sourceDepthKernel (sourceTwist τ f) L j w) z| ≤
        4 ^ (j + 1) * stripSourceCutoffControl * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12 :=
    fun z _ => abs_laplacian_stripCutoff_aperture_moment_le_global f ha hsupp L τ j n hwindow z
  refine (abs_polynomialSourceReading_sub_current_le _
    (contDiff_sourceDepthKernel (sourceTwist τ f) L j) n hb).trans ?_
  calc
    (2 * Real.pi)⁻¹ *
        (4 ^ (j + 1) * stripSourceCutoffControl * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12) *
        xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1)) =
      ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12) *
        (stripSourceCutoffControl *
          xiLocalPotentialError (polynomialSourceRegulator n) 0 (11 * ((n : ℝ) + 1))) := by ring
    _ ≤ ((2 * Real.pi)⁻¹ * 4 ^ (j + 1) * sourceTestSize f ^ 2 * ((n : ℝ) + 1) ^ 12) *
        (D / ((n : ℝ) + 1) ^ 14) :=
      mul_le_mul_of_nonneg_left (hlocal n hn) (by positivity)
    _ = _ := by
      rw [pow_succ (4 : ℝ) j]
      field_simp [Real.pi_ne_zero, (show (n : ℝ) + 1 ≠ 0 by positivity)]
      ring

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.polynomialThetaSourceReading_error_le
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_polynomialSourceMomentCurrentError_bound
