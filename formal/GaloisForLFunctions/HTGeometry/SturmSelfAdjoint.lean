import Mathlib

/-!
# Self-adjointness of a Sturm operator with vanishing weight

For a weight vanishing at both endpoints, the Sturm operator `u -> (w u')'` is symmetric on the
interval: integrating by parts once sends both sides to `- int w u' v'`, and every boundary term
carries the factor `w`, which vanishes there.

This is Lagrange's identity in the degenerate case that makes the finite Fourier transform commute
with the prolate differential operator: the prolate weight `1 - t^2` vanishes exactly at the ends of
the band.
-/

open intervalIntegral MeasureTheory

namespace HTGeometry

variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- One integration by parts against a weight vanishing at both endpoints. -/
theorem integral_mul_sturm_eq_neg {w u u' v' wv' : ℝ → A} {a b : ℝ}
    (hwa : w a * v' a = 0) (hwb : w b * v' b = 0)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hwv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun s => w s * v' s) (wv' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hwv' : IntervalIntegrable wv' volume a b) :
    ∫ x in a..b, u x * wv' x = -∫ x in a..b, u' x * (w x * v' x) := by
  rw [integral_mul_deriv_eq_deriv_mul hu hwv hu' hwv', hwa, hwb]
  ring

/-- **Lagrange's identity with vanishing weight.**  The Sturm operator is symmetric when the weight
vanishes at both endpoints. -/
theorem integral_mul_sturm_symm {w u v u' v' wu' wv' : ℝ → A} {a b : ℝ}
    (hwa : w a * v' a = 0) (hwb : w b * v' b = 0)
    (hwa' : w a * u' a = 0) (hwb' : w b * u' b = 0)
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hwu : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun s => w s * u' s) (wu' x) x)
    (hwv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun s => w s * v' s) (wv' x) x)
    (hu' : IntervalIntegrable u' volume a b)
    (hv' : IntervalIntegrable v' volume a b)
    (hwu' : IntervalIntegrable wu' volume a b)
    (hwv' : IntervalIntegrable wv' volume a b) :
    ∫ x in a..b, u x * wv' x = ∫ x in a..b, wu' x * v x := by
  have h1 : ∫ x in a..b, u x * wv' x = -∫ x in a..b, u' x * (w x * v' x) :=
    integral_mul_sturm_eq_neg hwa hwb hu hwv hu' hwv'
  have h2 : ∫ x in a..b, v x * wu' x = -∫ x in a..b, v' x * (w x * u' x) :=
    integral_mul_sturm_eq_neg hwa' hwb' hv hwu hv' hwu'
  have h3 : ∫ x in a..b, u' x * (w x * v' x) = ∫ x in a..b, v' x * (w x * u' x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  have h4 : ∫ x in a..b, wu' x * v x = ∫ x in a..b, v x * wu' x := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  rw [h1, h4, h2, h3]

end HTGeometry
