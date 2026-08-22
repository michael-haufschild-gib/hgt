import GaloisForLFunctions.HTGeometry.BesselK1SectorialPoincare

/-!
# Complex powers along the imaginary axis

The fact about `cpow` needed to evaluate the `χ`-kernel `(-2πui)^{s-1}` on the two half-lines:
`i^w + (-i)^w = 2 cos(πw/2)`.  (Splitting a positive real factor out of a complex power is already
owned by `BesselK1SectorialPoincare.ofReal_mul_cpow`.)

Together they turn the even pairing against `(-2πui)^{s-1}` into `2cos(π(s-1)/2)` times the Mellin
transform at the reflected point — the `χ`-factor of the functional equation
(Burnol, arXiv:math/0203120).

## Main results

* `I_cpow_add_neg_I_cpow`
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Real

noncomputable section

/-- `i^w + (-i)^w = 2 cos(πw/2)`. -/
theorem I_cpow_add_neg_I_cpow (w : ℂ) :
    Complex.I ^ w + (-Complex.I) ^ w = 2 * Complex.cos ((Real.pi : ℂ) * w / 2) := by
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hnI : (-Complex.I) ≠ 0 := neg_ne_zero.2 hI
  rw [Complex.cpow_def_of_ne_zero hI, Complex.cpow_def_of_ne_zero hnI,
    Complex.log_I, Complex.log_neg_I, Complex.cos]
  have h1 : Complex.log Complex.I * w = (Real.pi : ℂ) / 2 * Complex.I * w := by
    rw [Complex.log_I]
  have e1 : ((Real.pi : ℂ) / 2 * Complex.I) * w = (Real.pi : ℂ) * w / 2 * Complex.I := by ring
  have e2 : (-((Real.pi : ℂ) / 2) * Complex.I) * w = -((Real.pi : ℂ) * w / 2 * Complex.I) := by
    ring
  rw [e1, e2]
  field_simp

end

end GaloisForLFunctions.HTGeometry
