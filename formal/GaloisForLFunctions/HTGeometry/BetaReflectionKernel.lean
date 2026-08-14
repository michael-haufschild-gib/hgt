import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The reflection value of the Beta integral

On the critical strip the Beta integral at complementary arguments is the reflection kernel
`π / sin (π w)`.  The two ingredients are in mathlib separately — the Beta integral computes a
quotient of gamma values, and the gamma reflection formula evaluates the product at complementary
arguments — but their combination is not recorded.

This is the algebraic half of the Mellin kernel of `1 / (1 + y)`: the remaining half is the
substitution carrying the unit-interval Beta integral to the half line.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **The Beta integral at complementary arguments is the reflection kernel.** -/
theorem betaIntegral_one_sub {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1) :
    Complex.betaIntegral w (1 - w) = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w) := by
  have hone : (0 : ℝ) < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hprod := Complex.Gamma_mul_Gamma_eq_betaIntegral hw hone
  have hsum : w + (1 - w) = 1 := by ring
  rw [hsum, Complex.Gamma_one, one_mul] at hprod
  rw [← hprod]
  exact Complex.Gamma_mul_Gamma_one_sub w

/-- The reflection kernel is the Beta integral, in the explicit integral form. -/
theorem integral_unitInterval_reflection {w : ℂ} (hw : 0 < w.re) (hw1 : w.re < 1) :
    (∫ x in (0 : ℝ)..1, (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w))
      = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w) := by
  have hshape : (∫ x in (0 : ℝ)..1, (x : ℂ) ^ (w - 1) * (1 - (x : ℂ)) ^ (-w))
      = Complex.betaIntegral w (1 - w) := by
    rw [Complex.betaIntegral]
    refine intervalIntegral.integral_congr fun x _ => ?_
    congr 2
    ring
  rw [hshape]
  exact betaIntegral_one_sub hw hw1

end GaloisForLFunctions.HTGeometry
