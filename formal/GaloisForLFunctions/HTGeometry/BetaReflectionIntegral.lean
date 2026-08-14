import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# The Beta integral at complementary arguments

At complementary arguments the Beta integral collapses to the reflection formula: the Gamma
factors in the numerator are complementary and the denominator is `Γ(1) = 1`.

* `GaloisForLFunctions.HTGeometry.betaIntegral_self_one_sub`.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **The Beta integral at complementary arguments is `π / sin (π w)`.** -/
theorem betaIntegral_self_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    Complex.betaIntegral w (1 - w) = (Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w) := by
  have hv : 0 < (1 - w).re := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  rw [Complex.betaIntegral_eq_Gamma_mul_div w (1 - w) h0 hv, show w + (1 - w) = 1 by ring,
    Complex.Gamma_one, div_one, Complex.Gamma_mul_Gamma_one_sub]

end GaloisForLFunctions.HTGeometry
