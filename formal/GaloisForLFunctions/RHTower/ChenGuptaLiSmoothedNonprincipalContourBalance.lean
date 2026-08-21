/-
# Chen--Gupta--Li source-weighted finite Mellin contour balance

This exposes the finite boundary identity for the genuinely smoothed CGL
detector in the vertical-edge form used by the Class-I argument.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothedNonprincipalContour

open Complex MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- Exact finite source-weighted nonprincipal Mellin contour shift at a
certified critical-strip zero: vertical-edge change equals horizontal error. -/
theorem cglSmoothedNonprincipalDetectorMellin_verticalBalance
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q)
    (r : CGLNonprincipalDetectorRectangle) :
    (I • (∫ y in r.lower.im..r.upper.im,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((r.upper.re : ℂ) + y * I))) -
      (I • (∫ y in r.lower.im..r.upper.im,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((r.lower.re : ℂ) + y * I))) =
      (∫ x in r.lower.re..r.upper.re,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((x : ℂ) + r.upper.im * I)) -
      ∫ x in r.lower.re..r.upper.re,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((x : ℂ) + r.lower.im * I) := by
  have h := rectIntegral_cglSmoothedNonprincipalDetectorMellinIntegrand_eq_zero X q Y z r
  unfold rectIntegral at h
  linear_combination h

/-- The finite source-weighted vertical-edge difference is bounded by the two
source-weighted horizontal edge integrals. -/
theorem norm_cglSmoothedNonprincipalDetectorMellin_verticalBalance_le
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q)
    (r : CGLNonprincipalDetectorRectangle) :
    ‖(I • (∫ y in r.lower.im..r.upper.im,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((r.upper.re : ℂ) + y * I))) -
      (I • (∫ y in r.lower.im..r.upper.im,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((r.lower.re : ℂ) + y * I)))‖ ≤
      ‖∫ x in r.lower.re..r.upper.re,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((x : ℂ) + r.upper.im * I)‖ +
      ‖∫ x in r.lower.re..r.upper.re,
        cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z ((x : ℂ) + r.lower.im * I)‖ := by
  rw [cglSmoothedNonprincipalDetectorMellin_verticalBalance]
  exact norm_sub_le _ _

end RHTower
