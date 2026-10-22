import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedGammaForm

/-!
# The exponential conjugation of the Gamma transport

Conjugating by `e^{σL}` turns the translation-invariant Gamma jump into the shifted one: the weight
splits off the evaluation point and leaves `e^{∓σs}` on the two translates, which is exactly the
definition of `shiftedSecondDifference`.  So the shifted operator applied to `e^{σL}f` is `e^{σL}`
times the unshifted operator applied to `f`, with no hypothesis on `f` at all — the identity is
pointwise in the scale, and the integral inherits it.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- **The conjugated second difference.** -/
theorem shiftedSecondDifference_exp_mul (σ : ℝ) (f : ℝ → ℝ) (L s : ℝ) :
    shiftedSecondDifference σ (fun y => Real.exp (σ * y) * f y) L s
      = Real.exp (σ * L) * secondDifference f L s := by
  rw [shiftedSecondDifference, secondDifference]
  have h1 : Real.exp (-(σ * s)) * (Real.exp (σ * (L + s)) * f (L + s))
      = Real.exp (σ * L) * f (L + s) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h2 : Real.exp (σ * s) * (Real.exp (σ * (L - s)) * f (L - s))
      = Real.exp (σ * L) * f (L - s) := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [h1, h2]
  ring

/-- **The conjugated Gamma jump.**  `R_σ(e^{σ·}f) = e^{σ·}R f`, with no hypothesis on `f`. -/
theorem shiftedGammaJump_exp_mul (σ : ℝ) (f : ℝ → ℝ) (L : ℝ) :
    shiftedGammaJump σ (fun y => Real.exp (σ * y) * f y) L
      = Real.exp (σ * L) * gammaTransport f L := by
  rw [shiftedGammaJump, gammaTransport, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  rw [shiftedSecondDifference_exp_mul]
  ring

end GaloisForLFunctions.RHTower
