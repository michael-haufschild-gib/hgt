import GaloisForLFunctions.HTGeometry.LiteralSourceHorizonLogCubicJet

/-!
Exact degree-two horizon jet of the source's original complex power.

The source profile uses `(1 + sqrt (1 - z)) ^ α` with `α = 2s - w`.
This file retains that literal `cpow` and proves its exact endpoint
coefficients. Those are the prescribed degree-zero through degree-two terms
of the source-pole counterterm, not fitted asymptotic parameters.
-/

namespace GaloisForLFunctions.HTGeometry
open Complex
noncomputable section
set_option autoImplicit false

/-- The literal source horizon power, presented through its positive real
logarithmic height. -/
def literalSourceHorizonPower (α : ℂ) (z : ℝ) : ℂ :=
  Complex.exp ((literalSourceHorizonLog z : ℂ) * α)

def literalSourceHorizonPowerFirst (α : ℂ) (z : ℝ) : ℂ :=
  (literalSourceHorizonLogFirst z : ℂ) * α * literalSourceHorizonPower α z

def literalSourceHorizonPowerSecond (α : ℂ) (z : ℝ) : ℂ :=
  ((literalSourceHorizonLogSecond z : ℂ) * α +
    ((literalSourceHorizonLogFirst z : ℂ) * α) ^ 2) * literalSourceHorizonPower α z

/-- The literal power has its actual first and second radial derivatives. -/
theorem literalSourceHorizonPower_derivatives (α : ℂ) {z : ℝ} (hz : z < 1) :
    HasDerivAt (literalSourceHorizonPower α) (literalSourceHorizonPowerFirst α z) z ∧
      HasDerivAt (literalSourceHorizonPowerFirst α) (literalSourceHorizonPowerSecond α z) z := by
  have hL := literalSourceHorizonLog_derivatives hz
  have hL0 : HasDerivAt (fun x : ℝ => (literalSourceHorizonLog x : ℂ))
      (literalSourceHorizonLogFirst z : ℂ) z := hL.1.ofReal_comp
  have hL1 : HasDerivAt (fun x : ℝ => (literalSourceHorizonLogFirst x : ℂ))
      (literalSourceHorizonLogSecond z : ℂ) z := hL.2.ofReal_comp
  have hinner := hL0.mul_const α
  have hp := hinner.cexp
  constructor
  · apply hp.congr_deriv
    dsimp [literalSourceHorizonPowerFirst, literalSourceHorizonPower]
    ring
  · have hg := hL1.mul_const α
    have hp' : HasDerivAt (literalSourceHorizonPower α)
        (literalSourceHorizonPowerFirst α z) z := by
      apply hp.congr_deriv
      dsimp [literalSourceHorizonPowerFirst, literalSourceHorizonPower]
      ring
    have hprod := hg.mul hp'
    apply hprod.congr_deriv
    dsimp [literalSourceHorizonPowerFirst, literalSourceHorizonPowerSecond]
    ring

/-- The exponential presentation is exactly the original `cpow` on the
positive source height. -/
theorem literalSourceHorizonPower_eq_cpow (α : ℂ) (z : ℝ) :
    literalSourceHorizonPower α z = ((literalSourceHorizonHeight z : ℂ) ^ α) := by
  have hpos : 0 < literalSourceHorizonHeight z := by
    dsimp [literalSourceHorizonHeight]
    positivity
  have hh : (literalSourceHorizonHeight z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpos.ne'
  unfold literalSourceHorizonPower literalSourceHorizonLog
  rw [Complex.cpow_def_of_ne_zero hh, Complex.ofReal_log hpos.le]

/-- The exact degree-two source-power endpoint coefficients. The final term is
the Taylor coefficient (half the second derivative), precisely the coefficient
needed by the cubic source-pole subtraction. -/
theorem literalSourceHorizonPower_zero_jets (α : ℂ) :
    literalSourceHorizonPower α 0 = (2 : ℂ) ^ α ∧
      literalSourceHorizonPowerFirst α 0 = -(α / 4) * literalSourceHorizonPower α 0 ∧
        literalSourceHorizonPowerSecond α 0 / 2 =
          α * (α - 3) / 32 * literalSourceHorizonPower α 0 := by
  have hz := literalSourceHorizonLog_zero_jets
  constructor
  · rw [literalSourceHorizonPower_eq_cpow]
    norm_num [literalSourceHorizonHeight]
  constructor
  · rw [literalSourceHorizonPowerFirst, hz.2.1]
    push_cast
    ring
  · have h2 : literalSourceHorizonLogSecond 0 = -(3 / 16 : ℝ) := by
      linarith [hz.2.2]
    rw [literalSourceHorizonPowerSecond, hz.2.1, h2]
    push_cast
    ring

end
end GaloisForLFunctions.HTGeometry
