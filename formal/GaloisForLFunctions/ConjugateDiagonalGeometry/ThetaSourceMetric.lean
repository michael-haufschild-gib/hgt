import GaloisForLFunctions.ConjugateDiagonalGeometry.CommonSourceMetric
import GaloisForLFunctions.RHTower.ThetaTailFirstMomentKreinTransform

/-!
# The collided metric from literal theta source integrals

The positive planar density is a ratio of squared bilateral theta amplitudes
and their first moments. One common regulator schedule recovers every compact
source norm and all finite depth moments from these literal arithmetic integrals.
-/

open Complex MeasureTheory Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.ConjugateDiagonalGeometry
open Zeta23 ArithmeticPolarization _root_.RHTower

/-- Literal bilateral amplitude of the arithmetic completed theta source. -/
def thetaSourceAmplitude (z : ℂ) : ℂ :=
  ∫ x : ℝ, (thetaCuspFullSource x : ℂ) * Complex.exp (((1 / 2 : ℂ) - z) * x)

/-- The first source moment, before identifying it with a derivative of xi. -/
def thetaSourceFirstMoment (z : ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * (thetaCuspFullSource x : ℂ) *
    Complex.exp (((1 / 2 : ℂ) - z) * x)

private theorem thetaBilateralLaplace_eq_reflected_xi (w : ℂ) :
    thetaBilateralLaplace w = xi ((1 / 2 : ℂ) - w) := by
  rw [thetaBilateralLaplace_eq_XiC, XiC]
  congr 1
  rw [mul_assoc, mul_comm w Complex.I, ← mul_assoc, Complex.I_mul_I]
  ring

theorem thetaSourceAmplitude_eq_xi (z : ℂ) : thetaSourceAmplitude z = xi z := by
  rw [thetaSourceAmplitude, ← thetaBilateralLaplace_eq_integral,
    thetaBilateralLaplace_eq_reflected_xi]
  congr 1
  ring

theorem thetaSourceFirstMoment_eq_neg_deriv_xi (z : ℂ) :
    thetaSourceFirstMoment z = -deriv xi z := by
  have he : thetaBilateralLaplace = fun w => xi ((1 / 2 : ℂ) - w) :=
    funext thetaBilateralLaplace_eq_reflected_xi
  have hd := (xi_differentiable ((1 / 2 : ℂ) - ((1 / 2 : ℂ) - z))).hasDerivAt.comp
    ((1 / 2 : ℂ) - z) ((hasDerivAt_id ((1 / 2 : ℂ) - z)).const_sub (1 / 2 : ℂ))
  change HasDerivAt (fun w : ℂ => xi ((1 / 2 : ℂ) - w))
    (deriv xi ((1 / 2 : ℂ) - ((1 / 2 : ℂ) - z)) * -1) ((1 / 2 : ℂ) - z) at hd
  change thetaBilateralLaplaceMoment ((1 / 2 : ℂ) - z) = _
  rw [← deriv_thetaBilateralLaplace, he, hd.deriv]
  rw [show (1 / 2 : ℂ) - (1 / 2 - z) = z by ring]
  simp only [mul_neg, mul_one]

/-- A nonnegative density defined entirely from two literal arithmetic source integrals. -/
def thetaSourceCurvature (η : ℝ) (z : ℂ) : ℝ :=
  η * Complex.normSq (thetaSourceFirstMoment z) /
    (Complex.normSq (thetaSourceAmplitude z) + η) ^ 2

theorem thetaSourceCurvature_eq_xiCurvatureDensity (η : ℝ) (z : ℂ) :
    thetaSourceCurvature η z = xiCurvatureDensity η z := by
  simp only [thetaSourceCurvature, thetaSourceFirstMoment_eq_neg_deriv_xi,
    thetaSourceAmplitude_eq_xi, Complex.normSq_neg, xiCurvatureDensity]

theorem thetaSourceCurvature_nonneg {η : ℝ} (hη : 0 ≤ η) (z : ℂ) :
    0 ≤ thetaSourceCurvature η z :=
  div_nonneg (mul_nonneg hη (Complex.normSq_nonneg _)) (sq_nonneg _)

/-- A single positive arithmetic reading for every test, scale and finite moment order. -/
def thetaSourceMomentReading (f : CompactTest) (L : ℝ) (j n : ℕ) : ℝ :=
  Real.pi⁻¹ * ∫ z, sourceCutoff n z * sourceDepthKernel f L j z *
    thetaSourceCurvature (sourceRegulator (commonSourceIndex n)) z

theorem thetaSourceMomentReading_nonneg (f : CompactTest) (L : ℝ) (j n : ℕ) :
    0 ≤ thetaSourceMomentReading f L j n := by
  apply mul_nonneg (inv_nonneg.mpr Real.pi_pos.le)
  apply integral_nonneg
  intro z
  exact mul_nonneg (mul_nonneg (sourceCutoff n).nonneg
    (mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg (depthKernel_nonneg _ _) j)))
    (thetaSourceCurvature_nonneg (sourceRegulator_pos _).le z)

theorem thetaSourceMomentReading_eq_common (f : CompactTest) (L : ℝ) (j n : ℕ) :
    thetaSourceMomentReading f L j n = commonSourceReading (sourceDepthKernel f L j) n := by
  simp only [thetaSourceMomentReading, commonSourceReading, xiCompactSourceReading,
    thetaSourceCurvature_eq_xiCurvatureDensity]

/-- Literal theta integrals recover all collided depth moments along the same source-only schedule. -/
theorem tendsto_thetaSourceMomentReading (f : CompactTest) (L : ℝ) (j : ℕ) :
    Tendsto (thetaSourceMomentReading f L j) atTop
      (𝓝 (∑' ρ : zetaZeroConfig.carrier,
        zetaWeight f ρ * depthKernel L (zetaDepth ρ) ^ j)) := by
  have he : thetaSourceMomentReading f L j = commonSourceReading (sourceDepthKernel f L j) :=
    funext (thetaSourceMomentReading_eq_common f L j)
  rw [he]
  exact tendsto_commonSourceReading_depth_moment f L j

/-- Literal positive theta-source integrals converge to the full collided form. -/
theorem tendsto_thetaSourceMomentReading_collided (f : CompactTest) :
    Tendsto (thetaSourceMomentReading f 0 0) atTop (𝓝 (collidedForm zetaZeroConfig f.1)) := by
  simpa only [pow_zero, mul_one, zetaWeight, collidedForm] using
    tendsto_thetaSourceMomentReading f 0 0

/-- The same arithmetic sequence computes the full Hecke defect. -/
theorem tendsto_thetaSourceMomentReading_heckeDefect (f : CompactTest) (L : ℝ) :
    Tendsto (thetaSourceMomentReading f L 1) atTop (𝓝 (heckeDefect f L)) := by
  simpa only [pow_one, heckeDefect] using tendsto_thetaSourceMomentReading f L 1

end GaloisForLFunctions.ConjugateDiagonalGeometry
