/-
# Canonical source-weighted Class-I vertical balance for Chen--Gupta--Li

The two genuine CGL horizontal edges vanish, so the difference between the
two finite canonical vertical edges tends to zero.  This does not assert
separate convergence of either vertical integral.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassISmoothedEdges
import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothedNonprincipalContourBalance

open Complex Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- For every actual primitive Class-I zero, the difference of the two
canonical finite vertical edges of CGL's genuinely smoothed detector tends to
zero.  This is a finite-contour boundary statement, not an assertion that
either vertical edge has an infinite limit. -/
theorem tendsto_cglPrimitiveClassISmoothedCanonicalVerticalGap
    (X n Y : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLPrimitiveClassIWindowZero n χ τ H) :
    Tendsto (fun K : ℕ =>
      (I • (∫ y in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((2 : ℂ) + y * I))) -
      (I • (∫ y in (-((K + 1 : ℕ) : ℝ))..((K + 1 : ℕ) : ℝ),
        cglSmoothedNonprincipalDetectorMellinIntegrand X n Y
          (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
          ((((1 / 2 : ℝ) - z.1.1.re : ℝ) : ℂ) + y * I)))) atTop (𝓝 0) := by
  have htop := tendsto_cglPrimitiveClassISmoothedUpperHorizontalEdge X n Y χ τ H z
  have hbottom := tendsto_cglPrimitiveClassISmoothedLowerHorizontalEdge X n Y χ τ H z
  have hdiff := htop.sub hbottom
  rw [sub_zero] at hdiff
  refine hdiff.congr fun K => ?_
  convert (cglSmoothedNonprincipalDetectorMellin_verticalBalance X n Y
    (cglPrimitiveNonprincipalCriticalStripLZeroOfClassIWindowZero n χ τ H z).toCGLNonprincipalCriticalStripLZero
    (cglPrimitiveClassICanonicalRectangle n χ τ H z K)).symm using 1 <;>
    simp [cglPrimitiveClassICanonicalRectangle]
  all_goals try ring
  apply intervalIntegral.integral_congr
  intro x _
  ring

end RHTower
