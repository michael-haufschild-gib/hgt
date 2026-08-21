import GaloisForLFunctions.RHTower.ChenGuptaLiSmoothBump

noncomputable section

namespace RHTower

/-- Certified source form of CGL's cutoff: a real-valued, nonnegative smooth bump. -/
structure CGLRealSmoothBump extends CGLSmoothBump where
  imaginary_zero : ∀ x, (value x).im = 0
  nonnegative : ∀ x, 0 ≤ (value x).re

/-- The real scalar represented by CGL's certified complex-valued cutoff. -/
def CGLRealSmoothBump.realValue (w : CGLRealSmoothBump) (x : ℝ) : ℝ :=
  (w.toCGLSmoothBump.value x).re

/-- The source cutoff is literally the complexification of its real scalar value. -/
theorem CGLRealSmoothBump.value_eq_realValue (w : CGLRealSmoothBump) (x : ℝ) :
    w.toCGLSmoothBump.value x = (w.realValue x : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [CGLRealSmoothBump.realValue] using w.imaginary_zero x

/-- The Hilbert--Schmidt cutoff factor is exactly the square of CGL's real bump. -/
theorem CGLRealSmoothBump.normSq_value_eq_realValue_sq
    (w : CGLRealSmoothBump) (x : ℝ) :
    ‖w.toCGLSmoothBump.value x‖ ^ 2 = w.realValue x ^ 2 := by
  rw [w.value_eq_realValue]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using sq_abs (w.realValue x)

/-- CGL's Poisson kernel `w²` is the complexification of the real squared cutoff. -/
theorem CGLRealSmoothBump.value_mul_self_eq_realValue_sq
    (w : CGLRealSmoothBump) (x : ℝ) :
    w.toCGLSmoothBump.value x * w.toCGLSmoothBump.value x = (w.realValue x ^ 2 : ℂ) := by
  rw [w.value_eq_realValue]
  ring

end RHTower
