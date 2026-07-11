import GaloisForLFunctions.RHTower.ThetaCuspSchwartz
import GaloisForLFunctions.RHTower.XiThetaCriticalTrace
import GaloisForLFunctions.RHTower.XiEntireReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fourier identification of the theta-cusp Schwartz source

This file develops the remaining exact Fourier identity between the actual theta-cusp Schwartz
object and the centered completed function `XiC`.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped FourierTransform SchwartzMap

noncomputable section

namespace RHTower

/-- On the critical line, `XiC` is the elementary quadratic multiplier of the pole-subtracted
completed zeta trace, together with its exact constant term. -/
theorem XiC_ofReal_eq_completedRiemannZeta₀ (t : ℝ) :
    XiC (t : ℂ) =
      (1 / 2 : ℂ) - (((t : ℂ) ^ 2 + 1 / 4) / 2) *
        completedRiemannZeta₀ ((1 : ℂ) / 2 + (t : ℂ) * I) := by
  rw [XiC, xi]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- On the positive logarithmic half-line, the completed theta source at scale `2x` is twice the
raw positive Gaussian tail used by the cusp operator. -/
theorem xiThetaLogSource_two_mul_eq_tail {x : ℝ} (hx : 0 < x) :
    xiThetaLogSource (2 * x) =
      (2 * thetaCuspTailDerivative 0 x : ℝ) := by
  rw [xiThetaLogSource_eq_positiveFormula (by linarith)]
  rw [xiThetaPositiveFormula, thetaCuspTailDerivative_zero_eq_evenKernel]
  norm_cast
  ring

end RHTower
