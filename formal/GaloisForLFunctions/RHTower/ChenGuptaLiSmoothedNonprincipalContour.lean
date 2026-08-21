/-
# Smoothed nonprincipal Chen--Gupta--Li Mellin contour

The exact CGL safe-line Mellin identity carries the smoothing factor
`(Y+1)^w`.  This module transports the nonprincipal zero cancellation and
finite-rectangle contour identity to that genuine weighted integrand.

No RH, GRH, zero-density estimate, large-value estimate, or caller-supplied
analytic premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiNonprincipalAnalytic

open Complex MeasureTheory

noncomputable section

namespace RHTower

/-- The source CGL detector integrand carrying its literal Mellin smoothing
factor. -/
def cglSmoothedNonprincipalDetectorMellinIntegrand
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  ((Y + 1 : ℕ) : ℂ) ^ w *
    cglDetectorMellinIntegrand X q z.toCGLCriticalStripLZero w

/-- The analytic replacement of the weighted nonprincipal detector after the
zero-cancelled Gamma pole is removed. -/
def cglSmoothedNonprincipalRegularizedMellinIntegrand
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) : ℂ :=
  ((Y + 1 : ℕ) : ℂ) ^ w * cglNonprincipalRegularizedMellinIntegrand X q z w

/-- The positive integral smoothing base raised to a complex variable is
entire. -/
theorem cglSmoothingWeight_analyticAt (Y : ℕ) (w : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => ((Y + 1 : ℕ) : ℂ) ^ z) w := by
  have hbase : ((Y + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero Y)
  exact (differentiable_id.const_cpow (Or.inl hbase)).analyticAt w

/-- Off the cancelled pole, the source-weighted detector is exactly its
analytic regularization. -/
theorem cglSmoothedNonprincipalMellinIntegrand_eq_regularized_off_zero
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q) (w : ℂ) (hw : w ≠ 0) :
    cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z w =
      cglSmoothedNonprincipalRegularizedMellinIntegrand X q Y z w := by
  unfold cglSmoothedNonprincipalDetectorMellinIntegrand
    cglSmoothedNonprincipalRegularizedMellinIntegrand
  rw [cglNonprincipalMellinIntegrand_eq_regularized_off_zero X q z w hw]

/-- The weighted regularized detector is analytic on the same safe Gamma
half-plane as the unweighted one. -/
theorem cglSmoothedNonprincipalRegularizedMellinIntegrand_analyticOnGammaSafe
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q) :
    AnalyticOnNhd ℂ (cglSmoothedNonprincipalRegularizedMellinIntegrand X q Y z)
      cglGammaSafeHalfPlane := by
  intro w hw
  unfold cglSmoothedNonprincipalRegularizedMellinIntegrand
  exact (cglSmoothingWeight_analyticAt Y w).mul
    (cglNonprincipalRegularizedMellinIntegrand_analyticOnGammaSafe X q z w hw)

/-- **Finite weighted nonprincipal contour shift.**  The actual CGL smoothed
integrand has zero boundary integral on every certified safe rectangle around
a nonprincipal critical-strip zero. -/
theorem rectIntegral_cglSmoothedNonprincipalDetectorMellinIntegrand_eq_zero
    (X q Y : ℕ) (z : CGLNonprincipalCriticalStripLZero q)
    (r : CGLNonprincipalDetectorRectangle) :
    rectIntegral (cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z)
      r.lower r.upper = 0 := by
  calc
    rectIntegral (cglSmoothedNonprincipalDetectorMellinIntegrand X q Y z)
        r.lower r.upper =
      rectIntegral (cglSmoothedNonprincipalRegularizedMellinIntegrand X q Y z)
        r.lower r.upper := by
      apply rectIntegral_congr (S := ({0}ᶜ : Set ℂ))
      · intro w hw
        exact cglSmoothedNonprincipalMellinIntegrand_eq_regularized_off_zero X q Y z w hw
      · exact cglNonprincipalDetectorRectangle_bottom_ne_zero r
      · exact cglNonprincipalDetectorRectangle_top_ne_zero r
      · exact cglNonprincipalDetectorRectangle_right_ne_zero r
      · exact cglNonprincipalDetectorRectangle_left_ne_zero r
    _ = 0 := rectIntegral_eq_zero_of_analyticOnNhd
      (cglNonprincipalDetectorRectangle_subset_gammaSafe r)
      (cglSmoothedNonprincipalRegularizedMellinIntegrand_analyticOnGammaSafe X q Y z)

end RHTower
