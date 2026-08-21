/-
# Chen--Gupta--Li Class-I Mellin normalization

This identifies the common canonical vertical-line limit with the existing
`mellinInv` convention.  The factor is exactly `1 / (2π)` after parametrizing
the vertical line by its imaginary coordinate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassISafeLine

open Complex Filter Topology MeasureTheory

noncomputable section

namespace RHTower

/-- At CGL's positive smoothing scale, the inverse-Mellin power factor is the
literal source smoothing factor on the safe vertical line. -/
theorem cglMellin_smoothingFactor_eq
    (Y : ℕ) (t : ℝ) :
    Complex.ofReal (((Y + 1 : ℕ) : ℝ)⁻¹) ^ (-((2 : ℂ) + (t : ℂ) * I)) =
      ((Y + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I) := by
  have hpos : (0 : ℝ) < (Y + 1 : ℕ) := by positivity
  have harg : (((Y + 1 : ℕ) : ℂ)).arg ≠ Real.pi := by
    rw [show ((Y + 1 : ℕ) : ℂ) = (((Y + 1 : ℕ) : ℝ) : ℂ) by norm_num,
      Complex.arg_ofReal_of_nonneg hpos.le]
    exact Real.pi_ne_zero.symm
  have hcast : Complex.ofReal (((Y + 1 : ℕ) : ℝ)⁻¹) = ((Y + 1 : ℕ) : ℂ)⁻¹ := by
    norm_num
  rw [hcast, Complex.cpow_neg, Complex.inv_cpow _ _ harg, inv_inv]

/-- **CGL Section 12.1 normalization.**  At every certified primitive
Class-I zero, `mellinInv` is exactly `1/(2π)` times the common canonical
vertical-line limit. -/
theorem cglPrimitiveClassI_mellinInv_eq_safeLineIntegral
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    mellinInv 2 (fun w => Complex.Gamma w *
      (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1 (z.1.1 + w) *
        DirichletCharacter.LFunction χ.1.1 (z.1.1 + w))) ((Y + 1 : ℕ) : ℝ)⁻¹ =
      (1 / (2 * Real.pi) : ℝ) • (∫ t : ℝ,
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((2 : ℂ) + (t : ℂ) * I)) := by
  unfold mellinInv
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp
    have hchar :
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).character = χ.1.1 := rfl
    have hpoint :
        (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).point = z.1.1 := rfl
    unfold cglSmoothedNonprincipalDetectorMellinIntegrand cglDetectorMellinIntegrand
    rw [hchar, hpoint]
    congr 1
    change Complex.ofReal (((Y + 1 : ℕ) : ℝ)⁻¹) ^ (-((2 : ℂ) + (t : ℂ) * I)) =
      ((Y + 1 : ℕ) : ℂ) ^ ((2 : ℂ) + (t : ℂ) * I)
    exact cglMellin_smoothingFactor_eq Y t

end RHTower
