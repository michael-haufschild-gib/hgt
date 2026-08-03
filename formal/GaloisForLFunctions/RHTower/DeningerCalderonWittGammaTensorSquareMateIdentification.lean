import GaloisForLFunctions.RHTower.DeningerCalderonWittAllCrossPrimeGammaAdmissionOperator
import GaloisForLFunctions.RHTower.BilateralPrimeAngleModeration

/-!
# Deninger tensor-square mate identification of the actual Gamma boundary

The associated-grade Deninger half-density character has a radial
source-inverse/analytic-dagger mate curvature: inverse squared norm minus
squared norm.  This file identifies the actual ordered `(2,3)`
Gamma/co-Poisson Calderon--Witt boundary coefficient with that curvature at
the forced composite degree `6 = 2 * 3`, up to a strictly positive constant.

Neither the scalar curvature nor the hyperbolic-sine Gamma formula is new in
isolation.  The content is their exact comparison, including composite
degree, orientation sign, and positive calibration.  No Xi-zero location or
source-null-homotopy assumption enters any theorem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Tensor-square radial source-inverse/analytic-dagger mate curvature of
the Deninger half-density character at degree `n`. -/
def deningerTensorSquareRadialMateCurvature (n : ℕ) (s : ℂ) : ℝ :=
  ‖bilateralHalfDensityCharacter n s‖⁻¹ ^ 2 -
    ‖bilateralHalfDensityCharacter n s‖ ^ 2

/-- Exact hyperbolic-sine formula for the tensor-square radial mate
curvature. -/
theorem deningerTensorSquareRadialMateCurvature_eq_sinh
    (n : ℕ) (s : ℂ) (hn : 0 < n) :
    deningerTensorSquareRadialMateCurvature n s =
      2 * Real.sinh ((2 * s.re - 1) * Real.log n) := by
  rw [deningerTensorSquareRadialMateCurvature,
    norm_bilateralHalfDensityCharacter hn]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnR, Real.sinh_eq]
  rw [← Real.exp_neg]
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
  ring_nf

/-- For a nontrivial degree, tensor-square radial mate curvature detects
exactly the critical half-density section. -/
theorem deningerTensorSquareRadialMateCurvature_eq_zero_iff
    (n : ℕ) (s : ℂ) (hn : 2 ≤ n) :
    deningerTensorSquareRadialMateCurvature n s = 0 ↔
      s.re = 1 / 2 := by
  rw [deningerTensorSquareRadialMateCurvature_eq_sinh n s
    (lt_of_lt_of_le Nat.zero_lt_two hn)]
  have hnR : (1 : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le one_lt_two hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  constructor
  · intro h
    have hsinh : Real.sinh ((2 * s.re - 1) * Real.log n) = 0 := by
      linarith
    rw [Real.sinh_eq_zero] at hsinh
    rcases mul_eq_zero.mp hsinh with hre | hnlog
    · linarith
    · exact False.elim (ne_of_gt hlog hnlog)
  · intro h
    rw [h]
    norm_num

/-- The two depth-zero modular rates at the ordered `(2,3)` witness sum to
the negative logarithm of the forced composite degree `6`. -/
theorem deningerCalderonWittBaseGammaTotalModularRate_eq_neg_log_six :
    deningerCalderonWittBaseGammaTotalModularRate = -Real.log 6 := by
  rw [deningerCalderonWittBaseGammaTotalModularRate,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight,
    xiGammaEulerPrimitiveModularRate_eq_neg_two_halfHeight]
  simp only [xiGammaEulerBoundaryHalfHeight]
  norm_num
  rw [show (6 : ℝ) = 2 * 3 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  ring

/-- Positive orientation calibration converting Deninger tensor-square mate
curvature to the actual ordered `(2,3)` Gamma boundary coefficient. -/
def deningerCalderonWittBaseGammaMateCalibration : ℝ :=
  -deningerCalderonWittBaseGammaUndeformedExteriorAmplitude / 2

/-- The actual Gamma-to-Deninger mate calibration is strictly positive. -/
theorem deningerCalderonWittBaseGammaMateCalibration_pos :
    0 < deningerCalderonWittBaseGammaMateCalibration := by
  rw [deningerCalderonWittBaseGammaMateCalibration]
  have h := deningerCalderonWittBaseGammaUndeformedExteriorAmplitude_neg
  linarith

/-- **Actual Gamma/Deninger mate identification.**  The canonical
Gamma/co-Poisson boundary defect is exactly a positive calibration of the
tensor-square radial source-inverse/analytic-dagger mate curvature at the
forced composite degree `6 = 2 * 3`. -/
theorem
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r =
      ((deningerCalderonWittBaseGammaMateCalibration *
        deningerTensorSquareRadialMateCurvature 6 (r.1 : ℂ) : ℝ) : ℂ) := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq,
    deningerCalderonWittTwoThreePacketIndex]
  change
    (xiGammaEulerPrimitiveReflectionOddExterior
      (xiNearbyPoleDualityAdjunctionFracture (r.1 : ℂ)).re
      (⟨2, Nat.prime_two⟩, 0) (⟨3, Nat.prime_three⟩, 0) : ℂ) = _
  rw [deningerCalderonWittBaseGammaReflectionOddExterior_eq_sinh,
    deningerCalderonWittBaseGammaTotalModularRate_eq_neg_log_six,
    deningerTensorSquareRadialMateCurvature_eq_sinh
      6 (r.1 : ℂ) (by norm_num)]
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [Complex.ofReal_re,
    deningerCalderonWittBaseGammaMateCalibration]
  norm_cast
  rw [show
    (2 * ((r.1 : ℂ).re - 1 / 2)) * -Real.log 6 =
      -((2 * (r.1 : ℂ).re - 1) * Real.log 6) by ring,
    Real.sinh_neg]
  ring

/-- The exact comparison preserves the critical zero set: no hidden
normalization creates or erases a fibre. -/
theorem
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff_tensorSquareMateCurvature_eq_zero
    (r : XiZeroCopy) :
    deningerCalderonWittBaseGammaBoundaryDefectCoefficient r = 0 ↔
      deningerTensorSquareRadialMateCurvature 6 (r.1 : ℂ) = 0 := by
  rw [deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_zero_iff,
    deningerTensorSquareRadialMateCurvature_eq_zero_iff
      6 (r.1 : ℂ) (by norm_num)]

end

end RHTower
