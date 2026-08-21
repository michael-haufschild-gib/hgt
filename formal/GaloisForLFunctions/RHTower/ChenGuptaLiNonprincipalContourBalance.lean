/-
# Chen--Gupta--Li non-principal finite Mellin contour balance

At a certified non-principal critical-strip Dirichlet-L zero, the apparent
Gamma pole of the detector integrand is removable.  The existing contour
theorem then gives a vanishing rectangular boundary integral.  This module
puts that fact in the source-useful form: the difference of the two vertical
Mellin edges equals the difference of the horizontal edges, with a closed
norm error bound.

No RH, GRH, zero-density, contour-decay, or zero-detection premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiNonprincipalAnalytic

open Complex MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

/-- Exact finite non-principal Mellin contour shift at a certified critical
strip zero: vertical-edge change equals horizontal-edge error. -/
theorem cglNonprincipalDetectorMellin_verticalBalance
    (X q : ℕ) (z : CGLNonprincipalCriticalStripLZero q)
    (r : CGLNonprincipalDetectorRectangle) :
    (I • (∫ y in r.lower.im..r.upper.im,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((r.upper.re : ℂ) + y * I))) -
      (I • (∫ y in r.lower.im..r.upper.im,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((r.lower.re : ℂ) + y * I))) =
      (∫ x in r.lower.re..r.upper.re,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((x : ℂ) + r.upper.im * I)) -
      ∫ x in r.lower.re..r.upper.re,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((x : ℂ) + r.lower.im * I) := by
  have h := rectIntegral_cglNonprincipalDetectorMellinIntegrand_eq_zero X q z r
  unfold rectIntegral at h
  linear_combination h

/-- The vertical finite contour-shift error is bounded by the two horizontal
edge integrals. -/
theorem norm_cglNonprincipalDetectorMellin_verticalBalance_le
    (X q : ℕ) (z : CGLNonprincipalCriticalStripLZero q)
    (r : CGLNonprincipalDetectorRectangle) :
    ‖(I • (∫ y in r.lower.im..r.upper.im,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((r.upper.re : ℂ) + y * I))) -
      (I • (∫ y in r.lower.im..r.upper.im,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((r.lower.re : ℂ) + y * I)))‖ ≤
      ‖∫ x in r.lower.re..r.upper.re,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((x : ℂ) + r.upper.im * I)‖ +
      ‖∫ x in r.lower.re..r.upper.re,
        cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero ((x : ℂ) + r.lower.im * I)‖ := by
  rw [cglNonprincipalDetectorMellin_verticalBalance]
  exact norm_sub_le _ _

end RHTower
