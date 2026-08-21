/-
# Chen--Gupta--Li Class-II left critical-line integrand

This module rewrites the literal CGL left contour integrand as its
Gamma/smoothing/mollifier weight times a critical-line Dirichlet L-value. On
a finite local interval, that L-value is dominated by the canonical local
maximizer row. This is the pointwise analytic core needed before integrating
a compact Class-II envelope.

No RH, GRH, zero-density, zero-detection, large-value, or moment premise is
supplied by callers.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiClassIILocalMaximizer
import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassIIRows

open Complex

noncomputable section

namespace RHTower

/-- The left CGL contour point translated from a primitive Class-I zero. -/
def cglPrimitiveClassILeftLinePoint
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (t : ℝ) : ℂ :=
  (((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + (t : ℂ) * I

/-- Translating a left-line point by the zero lands exactly on the critical
line at the source ordinate plus the local offset. -/
theorem cglPrimitiveClassI_leftLine_argument_eq_criticalLine
    (n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (t : ℝ) :
    z.1.1 + cglPrimitiveClassILeftLinePoint n χ τ H z t =
      (cglCriticalLinePoint (z.1.1.im + t)).1 := by
  apply Complex.ext <;> simp [cglPrimitiveClassILeftLinePoint, cglCriticalLinePoint]

/-- The Gamma/smoothing/mollifier factor in the literal CGL left-line
integrand, separated from the critical-line L-value. -/
def cglPrimitiveClassILeftLineWeight
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (t : ℝ) : ℂ :=
  ((Y + 1 : ℕ) : ℂ) ^ (cglPrimitiveClassILeftLinePoint n χ τ H z t) *
    Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t) *
      zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
        (cglCriticalLinePoint (z.1.1.im + t)).1

/-- The actual CGL left-line integrand is exactly its weight times the
critical-line Dirichlet L-value. -/
theorem cglPrimitiveClassI_leftLineIntegrand_eq_weight_mul_LValue
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (t : ℝ) :
    cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      (cglPrimitiveClassILeftLinePoint n χ τ H z t) =
      cglPrimitiveClassILeftLineWeight X n Y χ τ H z t *
        DirichletCharacter.LFunction χ.1.1
          (cglCriticalLinePoint (z.1.1.im + t)).1 := by
  have harg := cglPrimitiveClassI_leftLine_argument_eq_criticalLine n χ τ H z t
  unfold cglSmoothedNonprincipalDetectorMellinIntegrand cglDetectorMellinIntegrand
    cglPrimitiveClassILeftLineWeight
  change ((Y + 1 : ℕ) : ℂ) ^ cglPrimitiveClassILeftLinePoint n χ τ H z t *
      (Complex.Gamma (cglPrimitiveClassILeftLinePoint n χ τ H z t) *
        (zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
          (z.1.1 + cglPrimitiveClassILeftLinePoint n χ τ H z t) *
          DirichletCharacter.LFunction χ.1.1
            (z.1.1 + cglPrimitiveClassILeftLinePoint n χ τ H z t))) = _
  rw [harg]
  ring

/-- The finite CGL Möbius detector has its closed cutoff bound at every left
critical-line point. -/
theorem norm_cglPrimitiveClassILeftLine_mollifier_le
    (X n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (t : ℝ) :
    ‖zeroDetectionMobiusPolynomial X (n + 1) χ.1.1
      (cglCriticalLinePoint (z.1.1.im + t)).1‖ ≤ (X + 1 : ℕ) :=
  norm_zeroDetectionMobiusPolynomial_criticalLine_le_cutoff X (n + 1) χ.1.1
    (z.1.1.im + t)

/-- On a closed local offset interval, the literal CGL left-line integrand is
pointwise dominated by its weight times the selected critical-line L-value
maximum. -/
theorem norm_cglPrimitiveClassI_leftLineIntegrand_le_localMax
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) (B : NNReal)
    (u : CGLClassIICriticalLineLocalOffset B) :
    ‖cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
      (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
      (cglPrimitiveClassILeftLinePoint n χ τ H z u.1)‖ ≤
      ‖cglPrimitiveClassILeftLineWeight X n Y χ τ H z u.1‖ *
        ‖DirichletCharacter.LFunction χ.1.1
          (cglCriticalLinePoint
            (cglClassIICriticalLineLocalMaximizerRow n χ.1.1 z.1.1.im B).time).1‖ := by
  rw [cglPrimitiveClassI_leftLineIntegrand_eq_weight_mul_LValue, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (cglClassIICriticalLineLocalMaximizerRow_maximal n χ.1.1 z.1.1.im B u)
    (norm_nonneg _)

end RHTower
