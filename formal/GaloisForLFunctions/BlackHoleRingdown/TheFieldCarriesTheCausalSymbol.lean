import GaloisForLFunctions.BlackHoleRingdown.TheReflectedSignalIsTheEchoTrain
import GaloisForLFunctions.BlackHoleRingdown.TheModesOfTheRingdown

/-!
# The full field carries the causal symbol

The horocycle mean of the Neumann field on the modular black hole splits exactly into three parts: the
incoming pulse, the response `g ∗ K` of the echo train, and a static mode `1/r`:

`∫₀¹ Φ dx = (e^{-τ/2}/r) √Y (g(τ + log Y) + (g ∗ K)(τ - log Y)) - 6 a(-i/2)/r`.

The retarded transform of the damped response is the transform of the pulse times the causal symbol:

`∫ e^{iωT} e^{-DT} (g ∗ K)(T) dT = 2π a(-iw) (s/(s-1)) 𝒞_D(ω)`,   `w = D - iω`, `s = w + ½`.

So the symbol is the transfer function of the full solution. Every pole `p` of the field's expansion lands
on a pole of the symbol at the mode frequency, for every overtone.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### The transform of the pulse -/

theorem cexp_mul_incomingPulse_eq {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) (w : ℂ) (S : ℝ) :
    Complex.exp (-w * (S : ℂ)) * incomingPulse ε ξ₀ S =
      ((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(1 / (4 * ε) : ℂ) * (S : ℂ) ^ 2 + (I * ξ₀ - w) * (S : ℂ) + 0) := by
  rw [incomingPulse_eq_closedForm hε, mul_left_comm, ← Complex.exp_add]
  congr 2
  ring

theorem integrable_cexp_mul_incomingPulse {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) (w : ℂ) :
    Integrable fun S : ℝ => Complex.exp (-w * (S : ℂ)) * incomingPulse ε ξ₀ S := by
  have h := (integrable_cexp_quadratic' (neg_quarter_inv_re_neg hε) (I * ξ₀ - w) 0).const_mul
    (((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ))
  exact h.congr (Eventually.of_forall fun S => (cexp_mul_incomingPulse_eq hε ξ₀ w S).symm)

/-- **The transform of the pulse is the amplitude**: `∫ e^{-wS} g(S) dS = 2π a(-iw)`. -/
theorem integral_cexp_mul_incomingPulse {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) (w : ℂ) :
    ∫ S : ℝ, Complex.exp (-w * (S : ℂ)) * incomingPulse ε ξ₀ S =
      2 * Real.pi * gaussianAmplitude ε ξ₀ (-I * w) := by
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hexp : Complex.exp (0 - (I * (ξ₀ : ℂ) - w) ^ 2 / (4 * -(1 / (4 * (ε : ℂ))))) =
      gaussianAmplitude ε ξ₀ (-I * w) := by
    have hsq : (I * (ξ₀ : ℂ) - w) ^ 2 / (4 * -(1 / (4 * (ε : ℂ)))) =
        -((ε : ℂ) * (I * (ξ₀ : ℂ) - w) ^ 2) := by
      field_simp
    rw [gaussianAmplitude, hsq]
    congr 1
    linear_combination ((ε : ℂ) * ((ξ₀ : ℂ) ^ 2 + w ^ 2)) * I_sq
  simp_rw [cexp_mul_incomingPulse_eq hε]
  rw [integral_const_mul, integral_cexp_quadratic (neg_quarter_inv_re_neg hε), neg_neg, hexp]
  linear_combination (gaussianAmplitude ε ξ₀ (-I * w)) * cpow_half_mul_cpow_half hε

/-! ### The response of the echo train -/

/-- The response `g ∗ K` of the echo train to the pulse. -/
def echoResponse (ε ξ₀ T : ℝ) : ℂ :=
  ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * ((echoKernel τ : ℝ) : ℂ)

theorem echoResponse_eq {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) :
    echoResponse ε ξ₀ T = reflectedSignal ε ξ₀ T +
      6 * gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) :=
  integral_pulse_mul_echoKernel hε ξ₀ T

/-- The damped response is a convolution of the damped pulse and the damped echo train. -/
theorem convolution_damped (ε ξ₀ : ℝ) (w : ℂ) (T : ℝ) :
    convolution (fun τ : ℝ => Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ))
        (fun S : ℝ => Complex.exp (-w * (S : ℂ)) * incomingPulse ε ξ₀ S)
        (ContinuousLinearMap.mul ℂ ℂ) volume T =
      Complex.exp (-w * (T : ℂ)) * echoResponse ε ξ₀ T := by
  rw [echoResponse, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  have he : Complex.exp (-w * ((T - τ : ℝ) : ℂ)) * Complex.exp (-w * (τ : ℂ)) =
      Complex.exp (-w * (T : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp only [ContinuousLinearMap.mul_apply']
  rw [← he]
  ring

/-- For `Re w > ½`, the kernel side of the transform. -/
theorem integral_cexp_mul_echoResponse_aux {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {w : ℂ}
    (hw : 1 / 2 < w.re) :
    ∫ T : ℝ, Complex.exp (-w * (T : ℂ)) * echoResponse ε ξ₀ T =
      (∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)) *
        (2 * Real.pi * gaussianAmplitude ε ξ₀ (-I * w)) := by
  have h := integral_convolution (μ := volume) (ν := volume) (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_cexp_mul_echoKernel hw) (integrable_cexp_mul_incomingPulse hε ξ₀ w)
  simp only [convolution_damped, ContinuousLinearMap.mul_apply'] at h
  rw [h, integral_cexp_mul_incomingPulse hε]

/-- **The transform of the response** is `2π a(-iw) φ(½ + w)` on `Re w > ½`. -/
theorem integral_cexp_mul_echoResponse {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {w : ℂ} (hw : 1 / 2 < w.re) :
    ∫ T : ℝ, Complex.exp (-w * (T : ℂ)) * echoResponse ε ξ₀ T =
      2 * Real.pi * gaussianAmplitude ε ξ₀ (-I * w) * scatteringPhase w := by
  rw [integral_cexp_mul_echoResponse_aux hε ξ₀ hw, integral_cexp_mul_echoKernel_eq_completed hw,
    completed_div_eq_scatteringPhase hw]
  ring

/-- **The full field carries the causal symbol.**  For `Im ω > ½ - D`, the retarded transform of the
damped response is the transform of the pulse times the causal symbol, up to the kinematic factor
`s/(s-1)`. -/
theorem retardedTransform_echoResponse {ε : ℝ} (hε : 0 < ε) (ξ₀ : ℝ) {D : ℝ} {ω : ℂ}
    (hω : 1 / 2 < D + ω.im) :
    ∫ T : ℝ, Complex.exp (I * ω * (T : ℂ)) * (((Real.exp (-D * T) : ℝ) : ℂ) * echoResponse ε ξ₀ T) =
      2 * Real.pi * gaussianAmplitude ε ξ₀ (-I * ((D : ℂ) - I * ω)) *
        ((D + 1 / 2 - I * ω) / (D + 1 / 2 - I * ω - 1) * causalSymbol D ω) := by
  set w : ℂ := (D : ℂ) - I * ω with hw
  have hre : 1 / 2 < w.re := by
    have : w.re = D + ω.im := by simp [hw]
    rw [this]
    exact hω
  have hpoint : ∀ T : ℝ, Complex.exp (I * ω * (T : ℂ)) * ((Real.exp (-D * T) : ℝ) : ℂ) =
      Complex.exp (-w * (T : ℂ)) := by
    intro T
    push_cast
    rw [← Complex.exp_add]
    congr 1
    rw [hw]
    ring
  have hkernel : ∫ τ : ℝ, Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ) =
      (D + 1 / 2 - I * ω) / (D + 1 / 2 - I * ω - 1) * causalSymbol D ω := by
    rw [← retardedTransform_dampedEchoKernel hω]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [Complex.ofReal_mul, ← mul_assoc, hpoint]
  have hint : ∫ T : ℝ, Complex.exp (I * ω * (T : ℂ)) *
      (((Real.exp (-D * T) : ℝ) : ℂ) * echoResponse ε ξ₀ T) =
      ∫ T : ℝ, Complex.exp (-w * (T : ℂ)) * echoResponse ε ξ₀ T := by
    refine integral_congr_ae (Eventually.of_forall fun T => ?_)
    simp only
    rw [← mul_assoc, hpoint]
  rw [hint, integral_cexp_mul_echoResponse_aux hε ξ₀ hre, hkernel]
  ring

/-! ### The field -/

/-- `√Y = e^{(log Y)/2}`. -/
theorem sqrt_eq_cexp {Y : ℝ} (hY : 0 < Y) :
    ((Real.sqrt Y : ℝ) : ℂ) = Complex.exp ((Real.log Y : ℂ) / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hY, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- **The horocycle mean of the Neumann field.**  It is the pulse and the echo response, damped by the
lift, together with the static mode `-6 a(-i/2)/r`. -/
theorem setIntegral_neumannField {ε : ℝ} (hε : 0 < ε) (ξ₀ t r : ℝ) {Y : ℝ} (hY : 0 < Y) :
    ∫ x in Ioc (0 : ℝ) 1, conformalScalar (neumannProfile ε ξ₀) t r x Y =
      Complex.exp (-(1 / 2 : ℂ) * (hyperboloidalTime t (tortoise r) : ℂ)) / (r : ℂ) *
          (((Real.sqrt Y : ℝ) : ℂ) *
            (incomingPulse ε ξ₀ (hyperboloidalTime t (tortoise r) + Real.log Y) +
              echoResponse ε ξ₀ (hyperboloidalTime t (tortoise r) - Real.log Y))) -
        6 * gaussianAmplitude ε ξ₀ (-I * (1 / 2)) / (r : ℂ) := by
  set τ := hyperboloidalTime t (tortoise r) with hτ
  have key : Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)) * ((Real.sqrt Y : ℝ) : ℂ) *
      Complex.exp (((τ - Real.log Y : ℝ) : ℂ) / 2) = 1 := by
    rw [sqrt_eq_cexp hY, ← Complex.exp_add, ← Complex.exp_add]
    have : -(1 / 2 : ℂ) * (τ : ℂ) + (Real.log Y : ℂ) / 2 + ((τ - Real.log Y : ℝ) : ℂ) / 2 = 0 := by
      push_cast
      ring
    rw [this, Complex.exp_zero]
  simp_rw [conformalScalar_neumannProfile, ← hτ]
  rw [integral_const_mul, setIntegral_wavePacket hε ξ₀ τ hY, echoResponse_eq hε]
  linear_combination (-(6 * gaussianAmplitude ε ξ₀ (-I * (1 / 2)) / (r : ℂ))) * key

/-! ### The poles of the field and of the symbol -/

/-- **Every mode rings at a pole of the causal symbol.**  For every overtone `n`, the frequency of the
mode of a pole `p` is a pole of the symbol at decay `2n + 3/2`. -/
theorem causalSymbol_modeFrequency_isPole (n : ℕ) {p : ℂ} (hp : xi (1 + 2 * p) = 0) :
    meromorphicOrderAt (causalSymbol (thetaCuspHawkingTopologicalBlackHoleConformalDecay n))
      (modeFrequency (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) p) < 0 := by
  have hXi : XiC (poleCoordinate p) = 0 := by
    have e : (1 / 2 : ℂ) + poleCoordinate p * I = 1 + 2 * p := by
      rw [poleCoordinate]
      linear_combination (-(2 * p + 1 / 2)) * I_sq
    rw [XiC, e, hp]
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hXi
  rw [modeFrequency_eq_qnmMinus, ← hq]
  exact causalSymbol_qnmMinus_isPole n q

end GaloisForLFunctions.BlackHoleRingdown

end
