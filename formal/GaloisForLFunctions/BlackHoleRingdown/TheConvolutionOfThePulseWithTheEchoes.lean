import GaloisForLFunctions.BlackHoleRingdown.TheRingdownExpansion
import GaloisForLFunctions.BlackHoleRingdown.TheEchoSpikesAndTheirGaussianObservation

/-!
# The convolution of the pulse with the echo train

The incoming pulse is Gaussian in time: `g(S) = √(π/ε) exp(iξ₀S - S²/(4ε))`. Its frequency integral can be
taken on any line `Re w = c`, so for `c > ½` the convolution `g ∗ K` with the echo train is computed by
Fubini. The Laplace transform of the echo train then gives

`(g ∗ K)(T) = ∫ a(-iw) e^{wT} φ(½+w) dy`,   `w = c + iy`.

The convolution of `g` with the mean growth `e^{τ/2}` is `2π a(-i/2) e^{T/2}`.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower HTGeometry

/-! ### Measurability of the echo train -/

theorem measurable_bounceKernel : Measurable bounceKernel := by
  unfold bounceKernel
  exact (measurable_const.sub (Real.measurable_exp.comp measurable_neg)).pow_const _

theorem measurable_echoTerm (c : ℕ) : Measurable (echoTerm c) := by
  unfold echoTerm
  exact Measurable.ite measurableSet_Ioi
    ((measurable_bounceKernel.comp (measurable_id.sub_const _)).const_mul _) measurable_const

theorem measurable_echoKernel : Measurable echoKernel :=
  Measurable.tsum (f := fun c τ => echoTerm c τ) measurable_echoTerm

/-- On `Re w > ½` the quotient of completed zeta values is the scattering coefficient. -/
theorem completed_div_eq_scatteringPhase {w : ℂ} (hw : 1 / 2 < w.re) :
    completedRiemannZeta (2 * w) / completedRiemannZeta (2 * w + 1) = scatteringPhase w := by
  have hre1 : (2 * w).re = 2 * w.re := by simp
  have hre2 : (1 + 2 * w).re = 1 + 2 * w.re := by simp
  have h1 : (2 : ℂ) * w ≠ 0 := fun h => by
    rw [h] at hre1
    simp at hre1
    linarith
  have h2 : (2 : ℂ) * w ≠ 1 := fun h => by
    rw [h] at hre1
    simp at hre1
    linarith
  have h3 : (1 : ℂ) + 2 * w ≠ 0 := fun h => by
    rw [h] at hre2
    simp at hre2
    linarith
  have h4 : (1 : ℂ) + 2 * w ≠ 1 := fun h => by
    rw [h] at hre2
    simp at hre2
    linarith
  have h2' : (2 : ℂ) * w - 1 ≠ 0 := sub_ne_zero.mpr h2
  have hw0 : w ≠ 0 := right_ne_zero_of_mul h1
  have hx1 := xi_eq_half_mul h1 h2
  have hx2 := xi_eq_half_mul h3 h4
  have hne : xi (1 + 2 * w) ≠ 0 := xi_ne_zero_of_one_le_re (by rw [hre2]; linarith)
  have hsub : (1 : ℂ) + 2 * w - 1 = 2 * w := by ring
  rw [hsub] at hx2
  have hb : completedRiemannZeta (1 + 2 * w) ≠ 0 := fun h => hne (by rw [hx2, h, mul_zero])
  rw [show (2 : ℂ) * w + 1 = 1 + 2 * w by ring, scatteringPhase, hx1, hx2]
  field_simp

/-! ### The pulse on any line -/

/-- The amplitude times an exponential, on the line `Re w = c`, is a Gaussian in `y`. -/
theorem gaussianAmplitude_line_eq (ε ξ₀ c S y : ℝ) :
    gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) *
        Complex.exp (((c : ℂ) + (y : ℂ) * I) * (S : ℂ)) =
      Complex.exp (-(ε : ℂ) * (y : ℂ) ^ 2 + (2 * ε * (ξ₀ + I * c) + I * S) * (y : ℂ) +
        (-(ε : ℂ) * ((ξ₀ : ℂ) + I * c) ^ 2 + c * S)) := by
  have h : -I * ((c : ℂ) + (y : ℂ) * I) - (ξ₀ : ℂ) = (y : ℂ) - ((ξ₀ : ℂ) + I * c) := by
    linear_combination (-(y : ℂ)) * I_sq
  rw [gaussianAmplitude, ← Complex.exp_add, h]
  congr 1
  ring

/-- **The pulse on the line `Re w = c`.**  The value does not depend on `c`. -/
theorem integral_gaussian_line {ε : ℝ} (hε : 0 < ε) (ξ₀ c S : ℝ) :
    ∫ y : ℝ, gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) *
        Complex.exp (((c : ℂ) + (y : ℂ) * I) * (S : ℂ)) =
      ((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (I * ξ₀ * S - (S : ℂ) ^ 2 / (4 * ε)) := by
  simp_rw [gaussianAmplitude_line_eq]
  have hb : (-(ε : ℂ)).re < 0 := by simpa using hε
  rw [integral_cexp_quadratic hb, neg_neg]
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hsq : (2 * (ε : ℂ) * ((ξ₀ : ℂ) + I * c) + I * S) ^ 2 / (4 * -(ε : ℂ)) =
      -((ε : ℂ) * ((ξ₀ : ℂ) + I * c) ^ 2) - ((ξ₀ : ℂ) + I * c) * I * S -
        I ^ 2 * (S : ℂ) ^ 2 / (4 * ε) := by
    field_simp
    first | done | ring
  rw [hsq]
  congr 2
  linear_combination ((c : ℂ) * S + (S : ℂ) ^ 2 / (4 * ε)) * I_sq

/-- The pulse in closed form. -/
theorem incomingPulse_eq_closedForm {ε : ℝ} (hε : 0 < ε) (ξ₀ S : ℝ) :
    incomingPulse ε ξ₀ S = ((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ) *
      Complex.exp (I * ξ₀ * S - (S : ℂ) ^ 2 / (4 * ε)) := by
  rw [← integral_gaussian_line hε ξ₀ 0 S, incomingPulse, packet]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [Complex.ofReal_zero, zero_add, mul_one]
  have h : -I * ((y : ℂ) * I) = y := by linear_combination (-(y : ℂ)) * I_sq
  have he : Complex.exp ((y : ℂ) * I * (S : ℂ)) = Complex.exp (I * (y : ℂ) * (S : ℂ)) := by
    congr 1
    ring
  rw [h, he]

theorem incomingPulse_eq_line {ε : ℝ} (hε : 0 < ε) (ξ₀ c S : ℝ) :
    ∫ y : ℝ, gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) *
        Complex.exp (((c : ℂ) + (y : ℂ) * I) * (S : ℂ)) = incomingPulse ε ξ₀ S := by
  rw [integral_gaussian_line hε, incomingPulse_eq_closedForm hε]

/-- The amplitude on a vertical line is integrable. -/
theorem integrable_gaussianAmplitude_line {ε : ℝ} (hε : 0 < ε) (ξ₀ c : ℝ) :
    Integrable fun y : ℝ => gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) := by
  have hcont : Continuous fun y : ℝ => gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) := by
    unfold gaussianAmplitude
    fun_prop
  refine integrable_of_continuous_of_gaussian_tail hcont (R := 0)
    (C := Real.exp (ε * c ^ 2 + ε * ξ₀ ^ 2)) (c := ε / 2) (by positivity) fun y _ => ?_
  rw [norm_gaussianAmplitude_rotated, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hre : ((c : ℂ) + (y : ℂ) * I).re = c := by simp
  have him : ((c : ℂ) + (y : ℂ) * I).im = y := by simp
  rw [hre, him]
  nlinarith [mul_nonneg hε.le (sq_nonneg (y - 2 * ξ₀))]

/-! ### Fubini -/

/-- The integrand of the double integral. -/
def echoDouble (ε ξ₀ c T τ y : ℝ) : ℂ :=
  gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) *
    Complex.exp (((c : ℂ) + (y : ℂ) * I) * ((T - τ : ℝ) : ℂ)) * ((echoKernel τ : ℝ) : ℂ)

theorem norm_echoDouble (ε ξ₀ c T τ y : ℝ) :
    ‖echoDouble ε ξ₀ c T τ y‖ =
      ‖Complex.exp (-(c : ℂ) * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)‖ *
        (Real.exp (c * T) * ‖gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I))‖) := by
  have h1 : ‖Complex.exp (((c : ℂ) + (y : ℂ) * I) * ((T - τ : ℝ) : ℂ))‖ =
      Real.exp (c * T) * Real.exp (-c * τ) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have : (((c : ℂ) + (y : ℂ) * I) * ((T - τ : ℝ) : ℂ)).re = c * (T - τ) := by simp
    rw [this]
    ring
  have h2 : ‖Complex.exp (-(c : ℂ) * (τ : ℂ))‖ = Real.exp (-c * τ) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [echoDouble]
  simp only [norm_mul]
  rw [h1, h2]
  ring

/-- The double integral converges absolutely for `c > ½`. -/
theorem integrable_echoDouble {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    Integrable (Function.uncurry (echoDouble ε ξ₀ c T)) (volume.prod volume) := by
  have hw : 1 / 2 < ((c : ℂ)).re := by simpa using hc
  have h1 := (integrable_cexp_mul_echoKernel hw).norm
  have h2 := ((integrable_gaussianAmplitude_line hε ξ₀ c).norm).const_mul (Real.exp (c * T))
  have hG := h1.mul_prod h2
  have hcontA : Continuous fun p : ℝ × ℝ =>
      gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + ((p.2 : ℝ) : ℂ) * I)) := by
    unfold gaussianAmplitude
    fun_prop
  have hcontE : Continuous fun p : ℝ × ℝ =>
      Complex.exp (((c : ℂ) + ((p.2 : ℝ) : ℂ) * I) * ((T - p.1 : ℝ) : ℂ)) := by
    fun_prop
  have hK : Measurable fun p : ℝ × ℝ => ((echoKernel p.1 : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_echoKernel.comp measurable_fst)
  have hmeas : Measurable (Function.uncurry (echoDouble ε ξ₀ c T)) :=
    (hcontA.measurable.mul hcontE.measurable).mul hK
  refine hG.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  exact le_of_eq (norm_echoDouble ε ξ₀ c T p.1 p.2)

/-- The inner integral in `y` is the pulse. -/
theorem integral_echoDouble_y {ε : ℝ} (hε : 0 < ε) (ξ₀ c T τ : ℝ) :
    ∫ y : ℝ, echoDouble ε ξ₀ c T τ y = incomingPulse ε ξ₀ (T - τ) * ((echoKernel τ : ℝ) : ℂ) := by
  simp only [echoDouble]
  rw [integral_mul_const, incomingPulse_eq_line hε]

/-- The inner integral in `τ` is the Laplace transform of the echo train. -/
theorem integral_echoDouble_τ (ε ξ₀ T y : ℝ) {c : ℝ} (hc : 1 / 2 < c) :
    ∫ τ : ℝ, echoDouble ε ξ₀ c T τ y =
      gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) *
        Complex.exp (((c : ℂ) + (y : ℂ) * I) * (T : ℂ)) *
          scatteringPhase ((c : ℂ) + (y : ℂ) * I) := by
  set w : ℂ := (c : ℂ) + (y : ℂ) * I with hw
  have hre : 1 / 2 < w.re := by
    have : w.re = c := by simp [hw]
    rw [this]
    exact hc
  have hpoint : ∀ τ : ℝ, echoDouble ε ξ₀ c T τ y =
      gaussianAmplitude ε ξ₀ (-I * w) * Complex.exp (w * (T : ℂ)) *
        (Complex.exp (-w * (τ : ℂ)) * ((echoKernel τ : ℝ) : ℂ)) := by
    intro τ
    have he : Complex.exp (w * ((T - τ : ℝ) : ℂ)) =
        Complex.exp (w * (T : ℂ)) * Complex.exp (-w * (τ : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [echoDouble, ← hw, he]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul, integral_cexp_mul_echoKernel_eq_completed hre,
    completed_div_eq_scatteringPhase hre]

/-- The convolution of the pulse with the echo train converges. -/
theorem integrable_pulse_mul_echoKernel {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) :
    Integrable fun τ : ℝ => incomingPulse ε ξ₀ (T - τ) * ((echoKernel τ : ℝ) : ℂ) := by
  have h := (integrable_echoDouble hε ξ₀ T (c := 1) (by norm_num)).integral_prod_left
  refine h.congr (Eventually.of_forall fun τ => ?_)
  exact integral_echoDouble_y hε ξ₀ 1 T τ

/-- **The convolution on the line `Re w = c`**, for any `c > ½`. -/
theorem integral_pulse_mul_echoKernel_eq_line {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) {c : ℝ}
    (hc : 1 / 2 < c) :
    ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * ((echoKernel τ : ℝ) : ℂ) =
      ∫ y : ℝ, gaussianAmplitude ε ξ₀ (-I * ((c : ℂ) + (y : ℂ) * I)) *
        Complex.exp (((c : ℂ) + (y : ℂ) * I) * (T : ℂ)) *
          scatteringPhase ((c : ℂ) + (y : ℂ) * I) := by
  have hswap := integral_integral_swap (f := echoDouble ε ξ₀ c T) (integrable_echoDouble hε ξ₀ T hc)
  simp_rw [integral_echoDouble_y hε, integral_echoDouble_τ ε ξ₀ T _ hc] at hswap
  exact hswap

/-! ### The mean growth -/

theorem cpow_half_mul_cpow_half {ε : ℝ} (hε : 0 < ε) :
    ((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ) * ((Real.pi : ℂ) / (1 / (4 * ε) : ℂ)) ^ (1 / 2 : ℂ) =
      2 * Real.pi := by
  have hpi := Real.pi_pos
  have h1 : (Real.pi : ℂ) / (ε : ℂ) = ((Real.pi / ε : ℝ) : ℂ) := (Complex.ofReal_div _ _).symm
  have h2 : (Real.pi : ℂ) / (1 / (4 * ε) : ℂ) = ((Real.pi / (1 / (4 * ε)) : ℝ) : ℂ) := by
    push_cast
    rfl
  have hprod : Real.pi / ε * (Real.pi / (1 / (4 * ε))) = (2 * Real.pi) ^ 2 := by
    field_simp
    first | done | ring
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h1, h2, ← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity), ← Complex.ofReal_mul,
    hprod, hhalf, ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by positivity)]
  push_cast
  rfl

/-- The pulse against `e^{(T-S)/2}` as a Gaussian in `S`. -/
theorem incomingPulse_mul_exp_eq {ε : ℝ} (hε : 0 < ε) (ξ₀ T S : ℝ) :
    incomingPulse ε ξ₀ S * Complex.exp (((T - S : ℝ) : ℂ) / 2) =
      ((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(1 / (4 * ε) : ℂ) * (S : ℂ) ^ 2 + (I * ξ₀ - 1 / 2) * (S : ℂ) + (T : ℂ) / 2) := by
  rw [incomingPulse_eq_closedForm hε, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem neg_quarter_inv_re_neg {ε : ℝ} (hε : 0 < ε) : (-(1 / (4 * ε) : ℂ)).re < 0 := by
  have h : (-(1 / (4 * ε) : ℂ)) = ((-(1 / (4 * ε)) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h, Complex.ofReal_re]
  have : 0 < 1 / (4 * ε) := by positivity
  linarith

/-- The convolution with the mean growth converges. -/
theorem integrable_pulse_mul_exp {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) :
    Integrable fun τ : ℝ => incomingPulse ε ξ₀ (T - τ) * Complex.exp ((τ : ℂ) / 2) := by
  have hint := ((integrable_cexp_quadratic' (neg_quarter_inv_re_neg hε) (I * ξ₀ - 1 / 2)
    ((T : ℂ) / 2)).const_mul (((Real.pi : ℂ) / (ε : ℂ)) ^ (1 / 2 : ℂ))).comp_sub_left T
  refine hint.congr (Eventually.of_forall fun τ => ?_)
  simp only
  rw [← incomingPulse_mul_exp_eq hε, sub_sub_cancel]

/-- **The convolution with the mean growth.** -/
theorem integral_pulse_mul_exp {ε : ℝ} (hε : 0 < ε) (ξ₀ T : ℝ) :
    ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * Complex.exp ((τ : ℂ) / 2) =
      2 * Real.pi * gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) := by
  have hb : (-(1 / (4 * ε) : ℂ)).re < 0 := neg_quarter_inv_re_neg hε
  have hsub : ∫ τ : ℝ, incomingPulse ε ξ₀ (T - τ) * Complex.exp ((τ : ℂ) / 2) =
      ∫ S : ℝ, incomingPulse ε ξ₀ S * Complex.exp (((T - S : ℝ) : ℂ) / 2) := by
    rw [← integral_sub_left_eq_self
      (fun S : ℝ => incomingPulse ε ξ₀ S * Complex.exp (((T - S : ℝ) : ℂ) / 2)) volume T]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [sub_sub_cancel]
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hexp : Complex.exp ((T : ℂ) / 2 - (I * (ξ₀ : ℂ) - 1 / 2) ^ 2 / (4 * -(1 / (4 * (ε : ℂ))))) =
      gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2) := by
    have hsq : (I * (ξ₀ : ℂ) - 1 / 2) ^ 2 / (4 * -(1 / (4 * (ε : ℂ)))) =
        -((ε : ℂ) * (I * (ξ₀ : ℂ) - 1 / 2) ^ 2) := by
      field_simp
    rw [gaussianAmplitude, ← Complex.exp_add, hsq]
    congr 1
    linear_combination ((ε : ℂ) * ((ξ₀ : ℂ) ^ 2 + 1 / 4)) * I_sq
  have key := cpow_half_mul_cpow_half hε
  rw [hsub]
  simp_rw [incomingPulse_mul_exp_eq hε]
  rw [integral_const_mul, integral_cexp_quadratic hb, neg_neg, hexp]
  linear_combination (gaussianAmplitude ε ξ₀ (-I * (1 / 2)) * Complex.exp ((T : ℂ) / 2)) * key

end GaloisForLFunctions.BlackHoleRingdown

end
