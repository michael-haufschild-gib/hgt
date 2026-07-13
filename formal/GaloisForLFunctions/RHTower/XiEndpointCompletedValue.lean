import GaloisForLFunctions.RHTower.XiEndpointReflectionDefectEnergy
import GaloisForLFunctions.RHTower.HedenmalmLocalFrameObstruction

/-!
# The endpoint curvature as one completed-zeta value

The FE--Schwarz endpoint curvature is not an independent divisor constant.  It is twice the real
part of the entire modified completion `completedRiemannZeta₀` at zero:

`xiEndpointCompletedCurvature = 2 * re(completedRiemannZeta₀ 0)`.

Thus the source-only quantitative norm budget needs only the scalar completed-value estimate
`re(completedRiemannZeta₀ 0) < 1/2`.  The proof differentiates the entire definition of `xi` at
zero and transports that derivative to `XiC` at the endpoint `i/2`.
-/

open Complex

namespace RHTower

noncomputable section

theorem deriv_xi_zero_eq_completedRiemannZeta0 :
    deriv xi 0 = -completedRiemannZeta₀ 0 / 2 := by
  have hp : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) (-1 / 2) 0 := by
    simpa [id_eq] using (((hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).mul
      ((hasDerivAt_id (𝕜 := ℂ) (0 : ℂ)).sub_const 1)).div_const 2)
  have hL : HasDerivAt completedRiemannZeta₀
      (deriv completedRiemannZeta₀ 0) 0 :=
    (differentiable_completedZeta₀ 0).hasDerivAt
  have hprod := hp.mul hL
  have hsum := hprod.add_const (1 / 2)
  have hsum' : HasDerivAt (fun s : ℂ =>
      s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2)
      (-1 / 2 * completedRiemannZeta₀ 0 +
        0 * (0 - 1) / 2 * deriv completedRiemannZeta₀ 0) 0 := by
    simpa only [Pi.mul_apply] using hsum
  change deriv (fun s : ℂ =>
    s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2) 0 = _
  rw [hsum'.deriv]
  ring

theorem XiC_I_half_eq : XiC (I / 2) = 1 / 2 := by
  rw [XiC]
  have harg : (1 / 2 : ℂ) + (I / 2) * I = 0 := by
    field_simp
    rw [Complex.I_sq]
    ring
  rw [harg, xi]
  norm_num

/-- **Endpoint completed-value identity.** -/
theorem xiEndpointCompletedCurvature_eq_completedRiemannZeta0 :
    xiEndpointCompletedCurvature = 2 * (completedRiemannZeta₀ 0).re := by
  rw [xiEndpointCompletedCurvature, logDeriv_apply,
    deriv_XiC_eq_deriv_xi_mul_I, XiC_I_half_eq,
    show (1 / 2 : ℂ) + (I / 2) * I = 0 by
      field_simp
      rw [Complex.I_sq]
      ring,
    deriv_xi_zero_eq_completedRiemannZeta0]
  have hI : (I / 2 : ℂ) ≠ 0 := by exact div_ne_zero I_ne_zero (by norm_num)
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  field_simp [hI, hhalf]
  simp [mul_re, mul_comm]

theorem xiEndpointCompletedCurvature_lt_one_iff_completedRiemannZeta0_re_lt_half :
    xiEndpointCompletedCurvature < 1 ↔
      (completedRiemannZeta₀ 0).re < 1 / 2 := by
  rw [xiEndpointCompletedCurvature_eq_completedRiemannZeta0]
  constructor <;> intro h <;> linarith

end

end RHTower
