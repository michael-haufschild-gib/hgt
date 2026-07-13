import GaloisForLFunctions.HTGeometry.EllipticGammaLogKernel
import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exponential-coordinate theta logarithmic kernel

The multiplicative theta boundary of the elliptic-gamma kernel is pulled back to the additive
coordinate used by mathlib's `jacobiTheta₂`.  The shifted coordinate

`x(τ,z) = -exp(π i τ) exp(2 π i z)`

aligns the multiplicative theta divisor with the odd half-period lattice.  Without using a Jacobi
triple-product identity, the constructed logarithmic kernel is proved to have exactly the same
period-one and period-`τ` quasiperiod laws as the analytic Jacobi-theta logarithmic derivative.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- The multiplicative nome attached to an additive upper-half-plane parameter. -/
def ellipticNome (τ : ℂ) : ℂ := Complex.exp (2 * Real.pi * I * τ)

/-- The multiplicative coordinate centered so that its `1`-level set is the odd half-period
lattice after nome translation. -/
def ellipticThetaCoordinate (τ z : ℂ) : ℂ :=
  -Complex.exp (Real.pi * I * τ) * Complex.exp (2 * Real.pi * I * z)

/-- Additive normalization of the theta-product logarithmic kernel. -/
def ellipticThetaAdditiveLogKernel (τ z : ℂ) : ℂ :=
  2 * Real.pi * I *
    ellipticThetaLogKernel (ellipticNome τ) (ellipticThetaCoordinate τ z)

theorem norm_ellipticNome_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖ellipticNome τ‖ < 1 := by
  exact UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨τ, hτ⟩

theorem ellipticNome_ne_zero (τ : ℂ) : ellipticNome τ ≠ 0 := by
  simp [ellipticNome]

theorem ellipticThetaCoordinate_ne_zero (τ z : ℂ) : ellipticThetaCoordinate τ z ≠ 0 := by
  simp [ellipticThetaCoordinate]

theorem analyticAt_ellipticThetaCoordinate (τ z : ℂ) :
    AnalyticAt ℂ (ellipticThetaCoordinate τ) z := by
  have hlin : AnalyticAt ℂ (fun w : ℂ => 2 * Real.pi * I * w) z :=
    analyticAt_const.mul analyticAt_id
  have hexp := analyticAt_cexp.comp hlin
  have hconst : AnalyticAt ℂ (fun _ : ℂ => -Complex.exp (Real.pi * I * τ)) z :=
    analyticAt_const
  have hmul := hconst.mul hexp
  simpa [ellipticThetaCoordinate, Function.comp_def] using hmul

theorem ellipticThetaCoordinate_add_one (τ z : ℂ) :
    ellipticThetaCoordinate τ (z + 1) = ellipticThetaCoordinate τ z := by
  rw [ellipticThetaCoordinate, ellipticThetaCoordinate]
  rw [mul_add, Complex.exp_add]
  norm_num [Complex.exp_two_pi_mul_I]

theorem ellipticThetaCoordinate_add_tau (τ z : ℂ) :
    ellipticThetaCoordinate τ (z + τ) = ellipticNome τ * ellipticThetaCoordinate τ z := by
  rw [ellipticThetaCoordinate, ellipticThetaCoordinate, ellipticNome]
  rw [mul_add, Complex.exp_add]
  ring

/-- Period-one law of the constructed additive theta logarithmic kernel. -/
theorem ellipticThetaAdditiveLogKernel_add_one (τ z : ℂ) :
    ellipticThetaAdditiveLogKernel τ (z + 1) = ellipticThetaAdditiveLogKernel τ z := by
  rw [ellipticThetaAdditiveLogKernel, ellipticThetaAdditiveLogKernel,
    ellipticThetaCoordinate_add_one]

/-- Period-`τ` quasiperiod law away from the theta pole. It agrees exactly with
`thetaLogDeriv(z+τ,τ)-thetaLogDeriv(z,τ) = -2πi`. -/
theorem ellipticThetaAdditiveLogKernel_add_tau_sub
    {τ z : ℂ} (hτ : 0 < τ.im) (hz : ellipticThetaCoordinate τ z ≠ 1) :
    ellipticThetaAdditiveLogKernel τ (z + τ) - ellipticThetaAdditiveLogKernel τ z =
      -(2 * Real.pi * I) := by
  rw [ellipticThetaAdditiveLogKernel, ellipticThetaAdditiveLogKernel,
    ellipticThetaCoordinate_add_tau]
  have hshift := ellipticThetaLogKernel_mul_q_sub (ellipticNome_ne_zero τ)
    (ellipticThetaCoordinate_ne_zero τ z) hz (norm_ellipticNome_lt_one hτ)
  rw [← mul_sub, hshift]
  ring

end

end GaloisForLFunctions
