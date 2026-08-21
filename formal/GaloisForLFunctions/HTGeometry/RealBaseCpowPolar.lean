import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Polar form of a complex power with positive real base

For `x > 0` and `w : ℂ` the complex power `x ^ w` is `exp (log x · w)`, so its real and imaginary
parts are the real power `x ^ re w` times `cos (im w · log x)` and `sin (im w · log x)`.  This is
the elementary device that splits a Mellin-type integral with real kernel into its cosine and sine
halves.
-/

open Complex Real

namespace GaloisForLFunctions.HTGeometry

/-- A complex power with positive real base is an exponential of a real logarithm. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    ((x : ℝ) : ℂ) ^ w = Complex.exp ((Real.log x : ℂ) * w) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]

/-- Real part of a complex power with positive real base. -/
theorem ofReal_cpow_re {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (((x : ℝ) : ℂ) ^ w).re = x ^ w.re * Real.cos (w.im * Real.log x) := by
  rw [ofReal_cpow_eq_exp hx, Complex.exp_re]
  simp [Real.rpow_def_of_pos hx, mul_comm]

/-- Imaginary part of a complex power with positive real base. -/
theorem ofReal_cpow_im {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (((x : ℝ) : ℂ) ^ w).im = x ^ w.re * Real.sin (w.im * Real.log x) := by
  rw [ofReal_cpow_eq_exp hx, Complex.exp_im]
  simp [Real.rpow_def_of_pos hx, mul_comm]

end GaloisForLFunctions.HTGeometry
