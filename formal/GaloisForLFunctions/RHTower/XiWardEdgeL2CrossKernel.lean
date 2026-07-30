import GaloisForLFunctions.RHTower.XiWardEdgeMassQuantization

/-!
# The edge cross-kernel integral

For right-half-plane abscissas `x₁, x₂ > 0` and real heights `β₁, β₂`, the
two Cauchy kernels `u(t) = x₁ + i(t+β₁)` and `v(t) = x₂ − i(t+β₂)` have
constant sum `K = (x₁+x₂) + i(β₁−β₂)`, so `1/(uv) = (1/K)(1/u + 1/v)`
exactly, and the combined integrand decays quadratically although neither
summand is integrable alone.  The real parts integrate to `π` each and the
imaginary parts cancel in the symmetric limit, giving the master identity

`∫ dt / (u v) = 2π / K`.

Every edge `L²` pairing of anti-causal Schwarz pair responses is a sum of
four such integrals; in particular all cross-pair pairings have strictly
positive real part and each pair deposits edge energy `2π·4(1/x + x/(x²+b²))`
with `x = Re λ + 1/2 < 1`, hence strictly more than `8π`.
-/

open Complex Filter MeasureTheory Real intervalIntegral

namespace RHTower

noncomputable section

/-- The two-kernel product integrand. -/
def edgeCrossKernel (x₁ x₂ β₁ β₂ t : ℝ) : ℂ :=
  ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ *
    ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹

theorem edgeCrossKernel_denom_ne_zero₁ {x₁ : ℝ} (hx₁ : 0 < x₁)
    (β₁ t : ℝ) : ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.zero_re] at hre
  nlinarith

theorem edgeCrossKernel_denom_ne_zero₂ {x₂ : ℝ} (hx₂ : 0 < x₂)
    (β₂ t : ℝ) : ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ)) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.zero_re] at hre
  nlinarith

/-- Constant-sum splitting: the two kernels sum to a `t`-free constant. -/
theorem edgeCrossKernel_sum_const (x₁ x₂ β₁ β₂ t : ℝ) :
    ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ)) +
      ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ)) =
      ((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ) := by
  push_cast
  ring

/-- Partial fractions with constant denominator sum. -/
theorem inv_mul_eq_sum_inv {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : u + v ≠ 0) :
    u⁻¹ * v⁻¹ = (u + v)⁻¹ * (u⁻¹ + v⁻¹) := by
  field_simp
  ring

/-- Exact partial-fraction form of the cross kernel. -/
theorem edgeCrossKernel_eq_split {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (β₁ β₂ t : ℝ) :
    edgeCrossKernel x₁ x₂ β₁ β₂ t =
      (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ))⁻¹ *
        (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
          ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹) := by
  have h₁ := edgeCrossKernel_denom_ne_zero₁ hx₁ β₁ t
  have h₂ := edgeCrossKernel_denom_ne_zero₂ hx₂ β₂ t
  have hK : (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.zero_re] at hre
    nlinarith
  have huv : ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ)) +
      ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ)) ≠ 0 := by
    rw [edgeCrossKernel_sum_const]
    exact hK
  rw [edgeCrossKernel, inv_mul_eq_sum_inv h₁ h₂ huv,
    edgeCrossKernel_sum_const]

/-- Real part of a single right-kernel inverse: a Lorentzian. -/
theorem re_rightKernel_inv (x β t : ℝ) :
    (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹).re =
      x / (x ^ 2 + (t + β) ^ 2) := by
  rw [Complex.inv_re]
  have hre : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).re = x := by
    norm_num [Complex.add_re, Complex.mul_re]
  have him : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).im = t + β := by
    norm_num [Complex.add_im, Complex.mul_im]
  rw [hre, Complex.normSq_apply, hre, him]
  ring

/-- Imaginary part of a single right-kernel inverse. -/
theorem im_rightKernel_inv (x β t : ℝ) :
    (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹).im =
      -(t + β) / (x ^ 2 + (t + β) ^ 2) := by
  rw [Complex.inv_im]
  have hre : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).re = x := by
    norm_num [Complex.add_re, Complex.mul_re]
  have him : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).im = t + β := by
    norm_num [Complex.add_im, Complex.mul_im]
  rw [him, Complex.normSq_apply, hre, him]
  ring

/-- Real part of a single left-kernel inverse. -/
theorem re_leftKernel_inv (x β t : ℝ) :
    (((x : ℂ) - I * ((t + β : ℝ) : ℂ))⁻¹).re =
      x / (x ^ 2 + (t + β) ^ 2) := by
  rw [Complex.inv_re]
  have hre : ((x : ℂ) - I * ((t + β : ℝ) : ℂ)).re = x := by
    norm_num [Complex.sub_re, Complex.mul_re]
  have him : ((x : ℂ) - I * ((t + β : ℝ) : ℂ)).im = -(t + β) := by
    norm_num [Complex.sub_im, Complex.mul_im]
  rw [hre, Complex.normSq_apply, hre, him]
  ring

/-- Imaginary part of a single left-kernel inverse. -/
theorem im_leftKernel_inv (x β t : ℝ) :
    (((x : ℂ) - I * ((t + β : ℝ) : ℂ))⁻¹).im =
      (t + β) / (x ^ 2 + (t + β) ^ 2) := by
  rw [Complex.inv_im]
  have hre : ((x : ℂ) - I * ((t + β : ℝ) : ℂ)).re = x := by
    norm_num [Complex.sub_re, Complex.mul_re]
  have him : ((x : ℂ) - I * ((t + β : ℝ) : ℂ)).im = -(t + β) := by
    norm_num [Complex.sub_im, Complex.mul_im]
  rw [him, Complex.normSq_apply, hre, him]
  ring

end

end RHTower

namespace RHTower

noncomputable section

/-- Quadratic domination of a shifted abscissa. -/
theorem one_add_sq_le_shifted {x β : ℝ} (hx : 0 < x) (t : ℝ) :
    1 + t ^ 2 ≤
      ((3 + 2 * β ^ 2) * (1 + x ^ 2) / x ^ 2) * (x ^ 2 + (t + β) ^ 2) := by
  have hx2 : 0 < x ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hx2]
  nlinarith [sq_nonneg (t + β), sq_nonneg t, sq_nonneg β, sq_nonneg x,
    sq_nonneg (t + 2 * β), sq_nonneg (x * t + x * β), sq_nonneg (x * x),
    mul_pos hx2 hx2, sq_nonneg (t * x), sq_nonneg (β * x),
    sq_nonneg (x * (t + β)), mul_pos hx hx]

/-- Norm of the cross kernel is dominated by an explicit multiple of the
Cauchy weight; hence the cross kernel is integrable. -/
theorem norm_edgeCrossKernel_le {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (β₁ β₂ t : ℝ) :
    ‖edgeCrossKernel x₁ x₂ β₁ β₂ t‖ ≤
      Real.sqrt (((3 + 2 * β₁ ^ 2) * (1 + x₁ ^ 2) / x₁ ^ 2) *
        ((3 + 2 * β₂ ^ 2) * (1 + x₂ ^ 2) / x₂ ^ 2)) * (1 + t ^ 2)⁻¹ := by
  have h₁ := one_add_sq_le_shifted (x := x₁) (β := β₁) hx₁ t
  have h₂ := one_add_sq_le_shifted (x := x₂) (β := β₂) hx₂ t
  have hpos1 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  set C₁ : ℝ := (3 + 2 * β₁ ^ 2) * (1 + x₁ ^ 2) / x₁ ^ 2 with hC₁
  set C₂ : ℝ := (3 + 2 * β₂ ^ 2) * (1 + x₂ ^ 2) / x₂ ^ 2 with hC₂
  have hC₁0 : 0 < C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  have hD₁ : (0 : ℝ) < x₁ ^ 2 + (t + β₁) ^ 2 := by positivity
  have hD₂ : (0 : ℝ) < x₂ ^ 2 + (t + β₂) ^ 2 := by positivity
  have hnorm : ‖edgeCrossKernel x₁ x₂ β₁ β₂ t‖ =
      (Real.sqrt (x₁ ^ 2 + (t + β₁) ^ 2))⁻¹ *
        (Real.sqrt (x₂ ^ 2 + (t + β₂) ^ 2))⁻¹ := by
    rw [edgeCrossKernel, norm_mul, norm_inv, norm_inv]
    congr 1
    · rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      have hre : ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ)).re = x₁ := by
        norm_num [Complex.add_re, Complex.mul_re]
      have him : ((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ)).im = t + β₁ := by
        norm_num [Complex.add_im, Complex.mul_im]
      rw [hre, him]
      ring
    · rw [Complex.norm_def, Complex.normSq_apply]
      congr 1
      have hre : ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ)).re = x₂ := by
        norm_num [Complex.sub_re, Complex.mul_re]
      have him : ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ)).im = -(t + β₂) := by
        norm_num [Complex.sub_im, Complex.mul_im]
      rw [hre, him]
      ring
  rw [hnorm]
  have hsqrt : (1 + t ^ 2) ≤
      Real.sqrt (C₁ * C₂) *
        (Real.sqrt (x₁ ^ 2 + (t + β₁) ^ 2) *
          Real.sqrt (x₂ ^ 2 + (t + β₂) ^ 2)) := by
    have hRHS : Real.sqrt (C₁ * C₂) *
        (Real.sqrt (x₁ ^ 2 + (t + β₁) ^ 2) *
          Real.sqrt (x₂ ^ 2 + (t + β₂) ^ 2)) =
        Real.sqrt ((C₁ * C₂) *
          ((x₁ ^ 2 + (t + β₁) ^ 2) * (x₂ ^ 2 + (t + β₂) ^ 2))) := by
      rw [Real.sqrt_mul (mul_pos hC₁0 hC₂0).le,
        Real.sqrt_mul hD₁.le]
    rw [hRHS, show (1 + t ^ 2 : ℝ) = Real.sqrt ((1 + t ^ 2) ^ 2) from
      (Real.sqrt_sq hpos1.le).symm]
    apply Real.sqrt_le_sqrt
    nlinarith [mul_le_mul h₁ h₂ hpos1.le
      (by positivity : (0 : ℝ) ≤ C₁ * (x₁ ^ 2 + (t + β₁) ^ 2))]
  have hs₁ : 0 < Real.sqrt (x₁ ^ 2 + (t + β₁) ^ 2) := Real.sqrt_pos.mpr hD₁
  have hs₂ : 0 < Real.sqrt (x₂ ^ 2 + (t + β₂) ^ 2) := Real.sqrt_pos.mpr hD₂
  have hprod : 0 < Real.sqrt (x₁ ^ 2 + (t + β₁) ^ 2) *
      Real.sqrt (x₂ ^ 2 + (t + β₂) ^ 2) := mul_pos hs₁ hs₂
  rw [← mul_inv, ← one_div,
    show Real.sqrt (C₁ * C₂) * (1 + t ^ 2)⁻¹ =
      Real.sqrt (C₁ * C₂) / (1 + t ^ 2) from by ring,
    div_le_div_iff₀ hprod hpos1]
  calc 1 * (1 + t ^ 2) = 1 + t ^ 2 := one_mul _
    _ ≤ Real.sqrt (C₁ * C₂) *
        (Real.sqrt (x₁ ^ 2 + (t + β₁) ^ 2) *
          Real.sqrt (x₂ ^ 2 + (t + β₂) ^ 2)) := hsqrt

/-- The cross kernel is integrable on the line. -/
theorem integrable_edgeCrossKernel {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (β₁ β₂ : ℝ) :
    MeasureTheory.Integrable (edgeCrossKernel x₁ x₂ β₁ β₂) := by
  have hcont : Continuous (edgeCrossKernel x₁ x₂ β₁ β₂) := by
    apply Continuous.mul
    · apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)))
      · exact fun t => edgeCrossKernel_denom_ne_zero₁ hx₁ β₁ t
    · apply Continuous.inv₀
      · exact continuous_const.sub (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)))
      · exact fun t => edgeCrossKernel_denom_ne_zero₂ hx₂ β₂ t
  apply MeasureTheory.Integrable.mono'
    (g := fun t : ℝ =>
      Real.sqrt (((3 + 2 * β₁ ^ 2) * (1 + x₁ ^ 2) / x₁ ^ 2) *
        ((3 + 2 * β₂ ^ 2) * (1 + x₂ ^ 2) / x₂ ^ 2)) * (1 + t ^ 2)⁻¹)
  · exact (integrable_inv_one_add_sq.const_mul _)
  · exact hcont.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t =>
      norm_edgeCrossKernel_le hx₁ hx₂ β₁ β₂ t

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory intervalIntegral

/-- Shifted Lorentzian half: integrable. -/
theorem lorentzianHalf_integrable {x : ℝ} (hx : 0 < x) (β : ℝ) :
    Integrable fun t : ℝ => x / (x ^ 2 + (t + β) ^ 2) := by
  have h := ((lorentzian_integrable0 hx).comp_add_right β).const_mul (1 / 2 : ℝ)
  apply h.congr
  filter_upwards with t
  have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
  field_simp

/-- Shifted Lorentzian half: total mass `π`. -/
theorem integral_lorentzianHalf {x : ℝ} (hx : 0 < x) (β : ℝ) :
    ∫ t : ℝ, x / (x ^ 2 + (t + β) ^ 2) = π := by
  have hshift : (∫ t : ℝ, x / (x ^ 2 + (t + β) ^ 2)) =
      ∫ u : ℝ, x / (x ^ 2 + u ^ 2) :=
    integral_add_right_eq_self (fun u : ℝ => x / (x ^ 2 + u ^ 2)) β
  rw [hshift, show (fun u : ℝ => x / (x ^ 2 + u ^ 2)) =
      fun u : ℝ => (1 / 2 : ℝ) * (2 * x / (x ^ 2 + u ^ 2)) from
    funext fun u => by
      have hD : (0 : ℝ) < x ^ 2 + u ^ 2 := by positivity
      field_simp]
  rw [MeasureTheory.integral_const_mul, lorentzian_integral hx]
  ring

/-- The centered odd width-difference has vanishing integral. -/
theorem integral_oddWidthPiece_zero (x₁ x₂ : ℝ) :
    ∫ s : ℝ, (s / (x₂ ^ 2 + s ^ 2) - s / (x₁ ^ 2 + s ^ 2)) = 0 := by
  have hodd : ∀ s : ℝ,
      (-s) / (x₂ ^ 2 + (-s) ^ 2) - (-s) / (x₁ ^ 2 + (-s) ^ 2) =
        -(s / (x₂ ^ 2 + s ^ 2) - s / (x₁ ^ 2 + s ^ 2)) := by
    intro s
    ring_nf
  have hneg := MeasureTheory.integral_neg_eq_self
    (fun s : ℝ => s / (x₂ ^ 2 + s ^ 2) - s / (x₁ ^ 2 + s ^ 2)) volume
  rw [show (fun s : ℝ =>
      (-s) / (x₂ ^ 2 + (-s) ^ 2) - (-s) / (x₁ ^ 2 + (-s) ^ 2)) =
    fun s : ℝ => -(s / (x₂ ^ 2 + s ^ 2) - s / (x₁ ^ 2 + s ^ 2)) from
    funext hodd, MeasureTheory.integral_neg] at hneg
  linarith

/-- Log-ratio antiderivative of the Lorentzian tilt. -/
theorem hasDerivAt_halfLogShift {x : ℝ} (hx : 0 < x) (s : ℝ) :
    HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * Real.log (x ^ 2 + s ^ 2))
      (s / (x ^ 2 + s ^ 2)) s := by
  have h1 : HasDerivAt (fun s : ℝ => x ^ 2 + s ^ 2) (2 * s) s := by
    simpa using ((hasDerivAt_pow 2 s).const_add (x ^ 2))
  have hD : (0 : ℝ) < x ^ 2 + s ^ 2 := by positivity
  have h2 := (Real.hasDerivAt_log hD.ne').comp s h1
  have h3 := h2.const_mul (1 / 2 : ℝ)
  exact h3.congr_deriv (by ring)

/-- Vanishing of the shift-difference integral by the log-limit. -/
theorem integral_shiftDiffPiece_zero {x : ℝ} (hx : 0 < x) (β₁ β₂ : ℝ)
    (hint : Integrable fun t : ℝ =>
      (t + β₂) / (x ^ 2 + (t + β₂) ^ 2) -
        (t + β₁) / (x ^ 2 + (t + β₁) ^ 2)) :
    ∫ t : ℝ, ((t + β₂) / (x ^ 2 + (t + β₂) ^ 2) -
      (t + β₁) / (x ^ 2 + (t + β₁) ^ 2)) = 0 := by
  have hlim := intervalIntegral_tendsto_integral hint
    tendsto_neg_atTop_atBot tendsto_id
  set h : ℝ → ℝ := fun s => s / (x ^ 2 + s ^ 2) with hh
  have hcont : Continuous h := by
    apply Continuous.div continuous_id
    · exact continuous_const.add (continuous_pow 2)
    · intro s
      have : (0 : ℝ) < x ^ 2 + s ^ 2 := by positivity
      exact this.ne'
  have hinterval : ∀ T : ℝ,
      (∫ t in (-T)..T, ((t + β₂) / (x ^ 2 + (t + β₂) ^ 2) -
        (t + β₁) / (x ^ 2 + (t + β₁) ^ 2))) =
      ((1 / 2 : ℝ) * Real.log (x ^ 2 + (T + β₂) ^ 2) -
        (1 / 2) * Real.log (x ^ 2 + (-T + β₂) ^ 2)) -
      ((1 / 2) * Real.log (x ^ 2 + (T + β₁) ^ 2) -
        (1 / 2) * Real.log (x ^ 2 + (-T + β₁) ^ 2)) := by
    intro T
    have hi₂ : IntervalIntegrable (fun t : ℝ => h (t + β₂)) volume (-T) T :=
      ((hcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
    have hi₁ : IntervalIntegrable (fun t : ℝ => h (t + β₁)) volume (-T) T :=
      ((hcont.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_sub hi₂ hi₁]
    congr 1
    · rw [intervalIntegral.integral_comp_add_right h β₂]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hasDerivAt_halfLogShift hx s)
        ((hcont.intervalIntegrable _ _))
    · rw [intervalIntegral.integral_comp_add_right h β₁]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s _ => hasDerivAt_halfLogShift hx s)
        ((hcont.intervalIntegrable _ _))
  have hratio : ∀ (γ δ : ℝ), Tendsto
      (fun T : ℝ => (1 / 2 : ℝ) * Real.log (x ^ 2 + (T + γ) ^ 2) -
        (1 / 2) * Real.log (x ^ 2 + (T + δ) ^ 2)) atTop (nhds 0) := by
    intro γ δ
    have hpos : ∀ T s : ℝ, (0 : ℝ) < x ^ 2 + (T + s) ^ 2 := by
      intro T s
      positivity
    have hlogdiff : ∀ T : ℝ,
        (1 / 2 : ℝ) * Real.log (x ^ 2 + (T + γ) ^ 2) -
          (1 / 2) * Real.log (x ^ 2 + (T + δ) ^ 2) =
        (1 / 2) * Real.log ((x ^ 2 + (T + γ) ^ 2) / (x ^ 2 + (T + δ) ^ 2)) := by
      intro T
      rw [Real.log_div (hpos T γ).ne' (hpos T δ).ne']
      ring
    simp only [hlogdiff]
    have hq : Tendsto
        (fun T : ℝ => (x ^ 2 + (T + γ) ^ 2) / (x ^ 2 + (T + δ) ^ 2))
        atTop (nhds 1) := by
      have hev : ∀ᶠ T : ℝ in atTop,
          (x ^ 2 + (T + γ) ^ 2) / (x ^ 2 + (T + δ) ^ 2) =
          ((x / T) ^ 2 + (1 + γ / T) ^ 2) / ((x / T) ^ 2 + (1 + δ / T) ^ 2) := by
        filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with T hT
        rw [div_eq_div_iff (hpos T δ).ne' (by positivity)]
        field_simp
      have hx0 : Tendsto (fun T : ℝ => x / T) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have hγ0 : Tendsto (fun T : ℝ => γ / T) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have hδ0 : Tendsto (fun T : ℝ => δ / T) atTop (nhds 0) :=
        Filter.Tendsto.div_atTop tendsto_const_nhds tendsto_id
      have hnum : Tendsto
          (fun T : ℝ => (x / T) ^ 2 + (1 + γ / T) ^ 2) atTop (nhds 1) := by
        have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
          tendsto_const_nhds
        have := (hx0.pow 2).add ((hone.add hγ0).pow 2)
        simpa using this
      have hden : Tendsto
          (fun T : ℝ => (x / T) ^ 2 + (1 + δ / T) ^ 2) atTop (nhds 1) := by
        have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
          tendsto_const_nhds
        have := (hx0.pow 2).add ((hone.add hδ0).pow 2)
        simpa using this
      have hdiv := hnum.div hden one_ne_zero
      rw [div_one] at hdiv
      have hev' : (fun T : ℝ =>
          (x ^ 2 + (T + γ) ^ 2) / (x ^ 2 + (T + δ) ^ 2)) =ᶠ[atTop]
          fun T : ℝ =>
            ((x / T) ^ 2 + (1 + γ / T) ^ 2) /
              ((x / T) ^ 2 + (1 + δ / T) ^ 2) := hev
      exact hdiv.congr' hev'.symm
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hq
    rw [Real.log_one] at hlog
    have := hlog.const_mul (1 / 2 : ℝ)
    simpa using this
  have hD : Tendsto (fun T : ℝ =>
      ((1 / 2 : ℝ) * Real.log (x ^ 2 + (T + β₂) ^ 2) -
        (1 / 2) * Real.log (x ^ 2 + (-T + β₂) ^ 2)) -
      ((1 / 2) * Real.log (x ^ 2 + (T + β₁) ^ 2) -
        (1 / 2) * Real.log (x ^ 2 + (-T + β₁) ^ 2))) atTop (nhds 0) := by
    have h1 := hratio β₂ β₁
    have h2 : Tendsto
        (fun T : ℝ => (1 / 2 : ℝ) * Real.log (x ^ 2 + (-T + β₁) ^ 2) -
          (1 / 2) * Real.log (x ^ 2 + (-T + β₂) ^ 2)) atTop (nhds 0) := by
      have h3 := hratio (-β₁) (-β₂)
      have h4 : Tendsto (fun T : ℝ => T) atTop atTop := tendsto_id
      apply h3.congr
      intro T
      congr 2 <;> ring
    have := h1.add h2
    rw [add_zero] at this
    apply this.congr
    intro T
    ring
  have hlim' := hlim.congr hinterval
  exact tendsto_nhds_unique hlim' hD

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory

/-- The shifted odd width piece is integrable, by conjugation-symmetric
domination through the cross kernel. -/
theorem integrable_oddPieceShifted {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β : ℝ) :
    Integrable fun t : ℝ =>
      (t + β) / (x₂ ^ 2 + (t + β) ^ 2) -
        (t + β) / (x₁ ^ 2 + (t + β) ^ 2) := by
  apply Integrable.mono'
    (((integrable_edgeCrossKernel hx₁ hx₂ β β).norm).const_mul |x₂ - x₁|)
  · apply Continuous.aestronglyMeasurable
    have hden : ∀ (x : ℝ), 0 < x → Continuous
        (fun t : ℝ => (t + β) / (x ^ 2 + (t + β) ^ 2)) := by
      intro x hx
      apply Continuous.div (continuous_id.add continuous_const)
      · exact continuous_const.add
          ((continuous_id.add continuous_const).pow 2)
      · intro t
        have : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
        exact this.ne'
    exact (hden x₂ hx₂).sub (hden x₁ hx₁)
  · filter_upwards with t
    have h₂conj : ‖((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹‖ =
        ‖((x₂ : ℂ) - I * ((t + β : ℝ) : ℂ))⁻¹‖ := by
      rw [norm_inv, norm_inv]
      congr 1
      rw [show ((x₂ : ℂ) - I * ((t + β : ℝ) : ℂ)) =
        (starRingEnd ℂ) ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ)) from by
          apply Complex.ext
          · simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
          · simp [Complex.sub_im, Complex.add_im, Complex.mul_im]]
      exact (RCLike.norm_conj _).symm
    have hdiffnorm :
        ‖((x₁ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ -
          ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹‖ ≤
        |x₂ - x₁| * ‖edgeCrossKernel x₁ x₂ β β t‖ := by
      have hd₁ := edgeCrossKernel_denom_ne_zero₁ hx₁ β t
      have hd₂ : ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ)) ≠ 0 := by
        intro h
        have hre := congrArg Complex.re h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, Complex.ofReal_im,
          Complex.zero_re] at hre
        nlinarith
      have hfactor :
          ((x₁ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ -
            ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ =
          (((x₂ : ℝ) : ℂ) - ((x₁ : ℝ) : ℂ)) *
            (((x₁ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ *
              ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) := by
        field_simp
        ring
      rw [hfactor, norm_mul, norm_mul]
      have hc : ‖((x₂ : ℝ) : ℂ) - ((x₁ : ℝ) : ℂ)‖ = |x₂ - x₁| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [hc, edgeCrossKernel, norm_mul, ← h₂conj]
    have him : ((t + β) / (x₂ ^ 2 + (t + β) ^ 2) -
        (t + β) / (x₁ ^ 2 + (t + β) ^ 2)) =
        (((x₁ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ -
          ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹).im := by
      rw [Complex.sub_im, im_rightKernel_inv, im_rightKernel_inv]
      ring
    rw [Real.norm_eq_abs, him]
    calc |(((x₁ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ -
          ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹).im|
        ≤ ‖((x₁ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹ -
          ((x₂ : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹‖ :=
          Complex.abs_im_le_norm _
      _ ≤ |x₂ - x₁| * ‖edgeCrossKernel x₁ x₂ β β t‖ := hdiffnorm

/-- The shifted odd width piece has vanishing integral. -/
theorem integral_oddPieceShifted_zero (x₁ x₂ β : ℝ) :
    ∫ t : ℝ, ((t + β) / (x₂ ^ 2 + (t + β) ^ 2) -
      (t + β) / (x₁ ^ 2 + (t + β) ^ 2)) = 0 := by
  have hshift : (∫ t : ℝ, ((t + β) / (x₂ ^ 2 + (t + β) ^ 2) -
      (t + β) / (x₁ ^ 2 + (t + β) ^ 2))) =
      ∫ s : ℝ, (s / (x₂ ^ 2 + s ^ 2) - s / (x₁ ^ 2 + s ^ 2)) :=
    integral_add_right_eq_self
      (fun s : ℝ => s / (x₂ ^ 2 + s ^ 2) - s / (x₁ ^ 2 + s ^ 2)) β
  rw [hshift]
  exact integral_oddWidthPiece_zero x₁ x₂

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory

/-- The kernel sum is integrable: it is the constant `K` times the cross
kernel. -/
theorem integrable_kernelSum {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (β₁ β₂ : ℝ) :
    Integrable fun t : ℝ =>
      (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
        ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹) := by
  have hK : (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.zero_re] at hre
    nlinarith
  have h := (integrable_edgeCrossKernel hx₁ hx₂ β₁ β₂).const_mul
    (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ))
  apply h.congr
  filter_upwards with t
  rw [edgeCrossKernel_eq_split hx₁ hx₂ β₁ β₂ t, ← mul_assoc,
    mul_inv_cancel₀ hK, one_mul]

/-- **Kernel-sum evaluation**: the combined single-kernel integral is `2π`. -/
theorem integral_kernelSum {x₁ x₂ : ℝ} (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (β₁ β₂ : ℝ) :
    (∫ t : ℝ, (((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
      ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹)) =
      ((2 * π : ℝ) : ℂ) := by
  have hint := integrable_kernelSum hx₁ hx₂ β₁ β₂
  have hreval : (∫ t : ℝ,
      ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
        ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) = 2 * π := by
    rw [show (fun t : ℝ =>
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
          ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹)).re) =
        fun t : ℝ => x₁ / (x₁ ^ 2 + (t + β₁) ^ 2) +
          x₂ / (x₂ ^ 2 + (t + β₂) ^ 2) from funext fun t => by
      rw [Complex.add_re, re_rightKernel_inv, re_leftKernel_inv]]
    rw [MeasureTheory.integral_add (lorentzianHalf_integrable hx₁ β₁)
      (lorentzianHalf_integrable hx₂ β₂),
      integral_lorentzianHalf hx₁ β₁, integral_lorentzianHalf hx₂ β₂]
    ring
  have hoddInt := integrable_oddPieceShifted hx₁ hx₂ β₁
  have hsdInt : Integrable (fun t : ℝ =>
      (t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2) -
        (t + β₁) / (x₂ ^ 2 + (t + β₁) ^ 2)) := by
    have h1 := hint.im.sub hoddInt
    apply h1.congr
    filter_upwards with t
    simp only [Pi.sub_apply, RCLike.im_to_complex]
    rw [Complex.add_im, im_rightKernel_inv, im_leftKernel_inv]
    ring
  have himval : (∫ t : ℝ,
      ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
        ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹)).im) = 0 := by
    rw [show (fun t : ℝ =>
        ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
          ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹)).im) =
        fun t : ℝ =>
          ((t + β₂) / (x₂ ^ 2 + (t + β₂) ^ 2) -
            (t + β₁) / (x₂ ^ 2 + (t + β₁) ^ 2)) +
          ((t + β₁) / (x₂ ^ 2 + (t + β₁) ^ 2) -
            (t + β₁) / (x₁ ^ 2 + (t + β₁) ^ 2)) from funext fun t => by
      rw [Complex.add_im, im_rightKernel_inv, im_leftKernel_inv]
      ring]
    rw [MeasureTheory.integral_add hsdInt hoddInt,
      integral_shiftDiffPiece_zero hx₂ β₁ β₂ hsdInt,
      integral_oddPieceShifted_zero x₁ x₂ β₁]
    ring
  rw [← integral_re_add_im hint]
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex]
  rw [hreval, himval]
  simp

/-- **Master cross-kernel integral**: `∫ dt/(uv) = 2π/K` with
`K = (x₁+x₂) + i(β₁−β₂)` the constant kernel sum. -/
theorem integral_edgeCrossKernel_eq {x₁ x₂ : ℝ} (hx₁ : 0 < x₁)
    (hx₂ : 0 < x₂) (β₁ β₂ : ℝ) :
    (∫ t : ℝ, edgeCrossKernel x₁ x₂ β₁ β₂ t) =
      ((2 * π : ℝ) : ℂ) *
        (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ))⁻¹ := by
  have hsplit : (fun t : ℝ => edgeCrossKernel x₁ x₂ β₁ β₂ t) =
      fun t : ℝ =>
        (((x₁ + x₂ : ℝ) : ℂ) + I * ((β₁ - β₂ : ℝ) : ℂ))⁻¹ *
          ((((x₁ : ℂ) + I * ((t + β₁ : ℝ) : ℂ))⁻¹ +
            ((x₂ : ℂ) - I * ((t + β₂ : ℝ) : ℂ))⁻¹)) :=
    funext fun t => edgeCrossKernel_eq_split hx₁ hx₂ β₁ β₂ t
  rw [hsplit, MeasureTheory.integral_const_mul,
    integral_kernelSum hx₁ hx₂ β₁ β₂]
  ring

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory

/-- The Euler-edge pair response as two right kernels with common abscissa
`Re λ + 1/2` and heights `± Im λ`. -/
theorem xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq_kernels
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    xiAntiCausalWardSchwarzPairResponse q ((1 / 2 : ℂ) + I * (t : ℂ)) =
      2 * (((((xiRightCenteredZero q.1).re + 1 / 2 : ℝ) : ℂ) +
          I * ((t + (xiRightCenteredZero q.1).im : ℝ) : ℂ))⁻¹ +
        ((((xiRightCenteredZero q.1).re + 1 / 2 : ℝ) : ℂ) +
          I * ((t + -(xiRightCenteredZero q.1).im : ℝ) : ℂ))⁻¹) := by
  have hconj :
      xiRightCenteredZero (xiRightZeroCopyConjEquiv q.1) =
        (starRingEnd ℂ) (xiRightCenteredZero q.1) :=
    xiRightCenteredZero_conj q.1
  have h1 : (1 / 2 : ℂ) + I * (t : ℂ) + xiRightCenteredZero q.1 =
      ((((xiRightCenteredZero q.1).re + 1 / 2 : ℝ) : ℂ) +
        I * ((t + (xiRightCenteredZero q.1).im : ℝ) : ℂ)) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
      norm_num
  have h2 : (1 / 2 : ℂ) + I * (t : ℂ) +
      (starRingEnd ℂ) (xiRightCenteredZero q.1) =
      ((((xiRightCenteredZero q.1).re + 1 / 2 : ℝ) : ℂ) +
        I * ((t + -(xiRightCenteredZero q.1).im : ℝ) : ℂ)) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
      norm_num
      ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]
      norm_num
  rw [xiAntiCausalWardSchwarzPairResponse, hconj, h1, h2]

/-- Pointwise expansion of the squared edge modulus of one pair into four
cross kernels. -/
theorem normSq_xiPairEdge_eq_four_sum (q : XiRightUpperZeroCopy) (t : ℝ) :
    Complex.normSq
        (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))) =
      4 * ((edgeCrossKernel ((xiRightCenteredZero q.1).re + 1 / 2)
          ((xiRightCenteredZero q.1).re + 1 / 2)
          (xiRightCenteredZero q.1).im (xiRightCenteredZero q.1).im t).re +
        (edgeCrossKernel ((xiRightCenteredZero q.1).re + 1 / 2)
          ((xiRightCenteredZero q.1).re + 1 / 2)
          (xiRightCenteredZero q.1).im (-(xiRightCenteredZero q.1).im) t).re +
        (edgeCrossKernel ((xiRightCenteredZero q.1).re + 1 / 2)
          ((xiRightCenteredZero q.1).re + 1 / 2)
          (-(xiRightCenteredZero q.1).im) (xiRightCenteredZero q.1).im t).re +
        (edgeCrossKernel ((xiRightCenteredZero q.1).re + 1 / 2)
          ((xiRightCenteredZero q.1).re + 1 / 2)
          (-(xiRightCenteredZero q.1).im)
          (-(xiRightCenteredZero q.1).im) t).re) := by
  set x : ℝ := (xiRightCenteredZero q.1).re + 1 / 2
  set b : ℝ := (xiRightCenteredZero q.1).im
  have hker := xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq_kernels q t
  set u : ℂ := ((x : ℝ) : ℂ) + I * ((t + b : ℝ) : ℂ) with hu
  set v : ℂ := ((x : ℝ) : ℂ) + I * ((t + -b : ℝ) : ℂ) with hv
  have hnormSq : Complex.normSq
      (xiAntiCausalWardSchwarzPairResponse q ((1 / 2 : ℂ) + I * (t : ℂ))) =
      ((2 * (u⁻¹ + v⁻¹)) * (starRingEnd ℂ) (2 * (u⁻¹ + v⁻¹))).re := by
    rw [← hker, Complex.mul_conj]
    simp
  rw [hnormSq]
  have hstaru : (starRingEnd ℂ) u⁻¹ =
      (((x : ℝ) : ℂ) - I * ((t + b : ℝ) : ℂ))⁻¹ := by
    rw [map_inv₀, hu]
    congr 1
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
      norm_num
    · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]
      norm_num
  have hstarv : (starRingEnd ℂ) v⁻¹ =
      (((x : ℝ) : ℂ) - I * ((t + -b : ℝ) : ℂ))⁻¹ := by
    rw [map_inv₀, hv]
    congr 1
    apply Complex.ext
    · simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
      norm_num
    · simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_im]
      norm_num
  have hexpand : (2 * (u⁻¹ + v⁻¹)) * (starRingEnd ℂ) (2 * (u⁻¹ + v⁻¹)) =
      4 * (edgeCrossKernel x x b b t + edgeCrossKernel x x b (-b) t +
        edgeCrossKernel x x (-b) b t + edgeCrossKernel x x (-b) (-b) t) := by
    rw [map_mul, map_add, hstaru, hstarv]
    simp only [edgeCrossKernel, map_ofNat]
    ring
  rw [hexpand]
  have h4 : ((4 : ℂ) * (edgeCrossKernel x x b b t +
      edgeCrossKernel x x b (-b) t + edgeCrossKernel x x (-b) b t +
      edgeCrossKernel x x (-b) (-b) t)).re =
      4 * (edgeCrossKernel x x b b t + edgeCrossKernel x x b (-b) t +
        edgeCrossKernel x x (-b) b t +
        edgeCrossKernel x x (-b) (-b) t).re := by
    norm_num [Complex.mul_re]
  rw [h4, Complex.add_re, Complex.add_re, Complex.add_re]

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory

/-- Closed form of the integrated cross-kernel real part at common
abscissa. -/
theorem integral_re_edgeCrossKernel {x : ℝ} (hx : 0 < x) (β β' : ℝ) :
    (∫ t : ℝ, (edgeCrossKernel x x β β' t).re) =
      2 * π * (2 * x) / ((2 * x) ^ 2 + (β - β') ^ 2) := by
  have hint := integrable_edgeCrossKernel hx hx β β'
  have hcomm := (Complex.reCLM.integral_comp_comm hint).symm
  have hre : (∫ t : ℝ, (edgeCrossKernel x x β β' t).re) =
      (∫ t : ℝ, edgeCrossKernel x x β β' t).re := by
    exact hcomm.symm
  rw [hre, integral_edgeCrossKernel_eq hx hx β β']
  have hKre : (((x + x : ℝ) : ℂ) + I * ((β - β' : ℝ) : ℂ)).re = 2 * x := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hKim : (((x + x : ℝ) : ℂ) + I * ((β - β' : ℝ) : ℂ)).im = β - β' := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.inv_re,
    Complex.inv_im, Complex.normSq_apply, hKre, hKim]
  have hD : (0 : ℝ) < 2 * x * (2 * x) + (β - β') * (β - β') := by
    nlinarith [sq_nonneg (β - β')]
  field_simp
  ring

/-- **Per-pair edge deposit**: one strict-right pair deposits exactly
`2π·4(1/x + x/(x²+b²))` of edge `L²` mass, `x = Re λ + 1/2`, `b = Im λ`. -/
theorem integral_normSq_xiPairEdge (q : XiRightUpperZeroCopy) :
    (∫ t : ℝ, Complex.normSq
        (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ)))) =
      2 * π * (4 * (1 / ((xiRightCenteredZero q.1).re + 1 / 2) +
        ((xiRightCenteredZero q.1).re + 1 / 2) /
          (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
            (xiRightCenteredZero q.1).im ^ 2))) := by
  set x : ℝ := (xiRightCenteredZero q.1).re + 1 / 2 with hxdef
  set b : ℝ := (xiRightCenteredZero q.1).im with hbdef
  have ha : 0 < (xiRightCenteredZero q.1).re := xiRightCenteredZero_re_pos q.1
  have hx : 0 < x := by rw [hxdef]; linarith
  have hI : ∀ β β' : ℝ,
      Integrable (fun t : ℝ => (edgeCrossKernel x x β β' t).re) := by
    intro β β'
    exact (integrable_edgeCrossKernel hx hx β β').re
  rw [show (fun t : ℝ => Complex.normSq
      (xiAntiCausalWardSchwarzPairResponse q ((1 / 2 : ℂ) + I * (t : ℂ)))) =
      fun t : ℝ => (4 : ℝ) * ((edgeCrossKernel x x b b t).re +
        (edgeCrossKernel x x b (-b) t).re +
        (edgeCrossKernel x x (-b) b t).re +
        (edgeCrossKernel x x (-b) (-b) t).re) from
    funext fun t => normSq_xiPairEdge_eq_four_sum q t]
  have h12 : Integrable (fun t : ℝ =>
      (edgeCrossKernel x x b b t).re + (edgeCrossKernel x x b (-b) t).re) :=
    (hI b b).add (hI b (-b))
  have h123 : Integrable (fun t : ℝ =>
      (edgeCrossKernel x x b b t).re + (edgeCrossKernel x x b (-b) t).re +
        (edgeCrossKernel x x (-b) b t).re) :=
    h12.add (hI (-b) b)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add h123 (hI (-b) (-b)),
    MeasureTheory.integral_add h12 (hI (-b) b),
    MeasureTheory.integral_add (hI b b) (hI b (-b)),
    integral_re_edgeCrossKernel hx b b,
    integral_re_edgeCrossKernel hx b (-b),
    integral_re_edgeCrossKernel hx (-b) b,
    integral_re_edgeCrossKernel hx (-b) (-b)]
  have hD1 : (0 : ℝ) < (2 * x) ^ 2 := by positivity
  have hD2 : (0 : ℝ) < (2 * x) ^ 2 + (b - -b) ^ 2 := by positivity
  have hD3 : (0 : ℝ) < (2 * x) ^ 2 + (-b - b) ^ 2 := by positivity
  have hD4 : (0 : ℝ) < x ^ 2 + b ^ 2 := by positivity
  field_simp
  ring

/-- **Deposit floor**: every pair deposits strictly more than `8π`. -/
theorem eightPi_lt_integral_normSq_xiPairEdge (q : XiRightUpperZeroCopy) :
    8 * π < ∫ t : ℝ, Complex.normSq
        (xiAntiCausalWardSchwarzPairResponse q
          ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  rw [integral_normSq_xiPairEdge q]
  have ha : 0 < (xiRightCenteredZero q.1).re := xiRightCenteredZero_re_pos q.1
  have hahalf : (xiRightCenteredZero q.1).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  set x : ℝ := (xiRightCenteredZero q.1).re + 1 / 2 with hxdef
  set b : ℝ := (xiRightCenteredZero q.1).im with hbdef
  have hx0 : 0 < x := by rw [hxdef]; linarith
  have hx1 : x < 1 := by rw [hxdef]; linarith
  have h1x : 1 < 1 / x := by
    rw [lt_div_iff₀ hx0]
    linarith
  have hpos : 0 < x / (x ^ 2 + b ^ 2) := by positivity
  have hπ := Real.pi_pos
  nlinarith [mul_pos hπ hpos]

end

end RHTower

namespace RHTower

noncomputable section

open MeasureTheory intervalIntegral

/-- The squared right kernel integrates to zero: complex FTC with boundary
decay. -/
theorem integral_sq_rightKernel_inv {x : ℝ} (hx : 0 < x) (β : ℝ) :
    (∫ t : ℝ, (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2) = 0 := by
  have hne : ∀ t : ℝ, ((x : ℂ) + I * ((t + β : ℝ) : ℂ)) ≠ 0 :=
    edgeCrossKernel_denom_ne_zero₁ hx β
  have hint : Integrable fun t : ℝ =>
      (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2 := by
    apply Integrable.mono' ((lorentzianHalf_integrable hx β).const_mul (1 / x))
    · apply Continuous.aestronglyMeasurable
      apply Continuous.pow
      apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)))
      · exact hne
    · filter_upwards with t
      have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
      have hnorm : ‖(((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2‖ =
          (x ^ 2 + (t + β) ^ 2)⁻¹ := by
        rw [norm_pow, norm_inv]
        have habs : ‖(x : ℂ) + I * ((t + β : ℝ) : ℂ)‖ =
            Real.sqrt (x ^ 2 + (t + β) ^ 2) := by
          rw [Complex.norm_def, Complex.normSq_apply]
          congr 1
          have hre : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).re = x := by
            norm_num [Complex.add_re, Complex.mul_re]
          have him : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).im = t + β := by
            norm_num [Complex.add_im, Complex.mul_im]
          rw [hre, him]
          ring
        rw [habs, ← Real.sqrt_inv, Real.sq_sqrt (by positivity)]
      rw [hnorm]
      rw [show (1 / x) * (x / (x ^ 2 + (t + β) ^ 2)) =
        (x ^ 2 + (t + β) ^ 2)⁻¹ from by field_simp]
  have hlim := intervalIntegral_tendsto_integral hint
    tendsto_neg_atTop_atBot tendsto_id
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun t : ℝ => I * (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹))
      ((((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2) t := by
    intro t
    have hinner : HasDerivAt
        (fun t : ℝ => ((x : ℂ) + I * ((t + β : ℝ) : ℂ))) I t := by
      have hfun : (fun t : ℝ => ((x : ℂ) + I * ((t + β : ℝ) : ℂ))) =
          fun t : ℝ => I * ((t : ℝ) : ℂ) +
            (((x : ℝ) : ℂ) + I * ((β : ℝ) : ℂ)) := by
        funext s
        push_cast
        ring
      rw [hfun]
      have hr : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := by
        simpa using! Complex.ofRealCLM.hasDerivAt (x := t)
      simpa using (hr.const_mul I).add_const
        (((x : ℝ) : ℂ) + I * ((β : ℝ) : ℂ))
    have hz := hasDerivAt_inv (hne t)
    have hcomp := hz.scomp t hinner
    have := hcomp.const_mul I
    simpa using! this.congr_deriv (by
      simp only [smul_eq_mul]
      rw [← mul_assoc, Complex.I_mul_I]
      simp only [neg_mul, one_mul, neg_neg]
      push_cast
      rfl)
  have hFTC : ∀ T : ℝ, (∫ t in (-T)..T,
      (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2) =
      I * (((x : ℂ) + I * ((T + β : ℝ) : ℂ))⁻¹) -
        I * (((x : ℂ) + I * ((-T + β : ℝ) : ℂ))⁻¹) := by
    intro T
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv t)
      ((Continuous.intervalIntegrable (by
        apply Continuous.pow
        apply Continuous.inv₀
        · exact continuous_const.add (continuous_const.mul
            (Complex.continuous_ofReal.comp
              (continuous_id.add continuous_const)))
        · exact hne) _ _))
  have hdecay : Tendsto (fun T : ℝ =>
      I * (((x : ℂ) + I * ((T + β : ℝ) : ℂ))⁻¹) -
        I * (((x : ℂ) + I * ((-T + β : ℝ) : ℂ))⁻¹)) atTop (nhds 0) := by
    have hnorm : ∀ T : ℝ, ∀ s : ℝ, ‖((x : ℂ) + I * ((s : ℝ) : ℂ))⁻¹‖ ≤
        (Real.sqrt (x ^ 2 + s ^ 2))⁻¹ := by
      intro T s
      rw [norm_inv]
      apply (inv_le_inv₀ (by
        rw [Complex.norm_def]
        exact Real.sqrt_pos.mpr (by
          rw [Complex.normSq_apply]
          have hre : ((x : ℂ) + I * ((s : ℝ) : ℂ)).re = x := by
            norm_num [Complex.add_re, Complex.mul_re]
          have him : ((x : ℂ) + I * ((s : ℝ) : ℂ)).im = s := by
            norm_num [Complex.add_im, Complex.mul_im]
          rw [hre, him]
          nlinarith))
        (Real.sqrt_pos.mpr (by positivity))).mpr
      rw [Complex.norm_def, Complex.normSq_apply]
      apply Real.sqrt_le_sqrt
      have hre : ((x : ℂ) + I * ((s : ℝ) : ℂ)).re = x := by
        norm_num [Complex.add_re, Complex.mul_re]
      have him : ((x : ℂ) + I * ((s : ℝ) : ℂ)).im = s := by
        norm_num [Complex.add_im, Complex.mul_im]
      rw [hre, him]
      ring_nf
      exact le_refl _
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun T => norm_nonneg _)
      (g := fun T : ℝ => (Real.sqrt (x ^ 2 + (T + β) ^ 2))⁻¹ +
        (Real.sqrt (x ^ 2 + (-T + β) ^ 2))⁻¹)
    · intro T
      calc ‖I * (((x : ℂ) + I * ((T + β : ℝ) : ℂ))⁻¹) -
            I * (((x : ℂ) + I * ((-T + β : ℝ) : ℂ))⁻¹)‖
          ≤ ‖I * (((x : ℂ) + I * ((T + β : ℝ) : ℂ))⁻¹)‖ +
            ‖I * (((x : ℂ) + I * ((-T + β : ℝ) : ℂ))⁻¹)‖ :=
            norm_sub_le _ _
        _ = ‖((x : ℂ) + I * ((T + β : ℝ) : ℂ))⁻¹‖ +
            ‖((x : ℂ) + I * ((-T + β : ℝ) : ℂ))⁻¹‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
        _ ≤ (Real.sqrt (x ^ 2 + (T + β) ^ 2))⁻¹ +
            (Real.sqrt (x ^ 2 + (-T + β) ^ 2))⁻¹ := by
            exact add_le_add (hnorm T (T + β)) (hnorm T (-T + β))
    · have h1 : Tendsto (fun T : ℝ =>
          (Real.sqrt (x ^ 2 + (T + β) ^ 2))⁻¹) atTop (nhds 0) := by
        apply Tendsto.inv_tendsto_atTop
        apply Real.tendsto_sqrt_atTop.comp
        have : Tendsto (fun T : ℝ => (T + β) ^ 2) atTop atTop :=
          (tendsto_pow_atTop (n := 2) (by norm_num)).comp
            (tendsto_atTop_add_const_right atTop β tendsto_id)
        exact tendsto_atTop_add_const_left atTop (x ^ 2) this
      have h2 : Tendsto (fun T : ℝ =>
          (Real.sqrt (x ^ 2 + (-T + β) ^ 2))⁻¹) atTop (nhds 0) := by
        apply Tendsto.inv_tendsto_atTop
        apply Real.tendsto_sqrt_atTop.comp
        have : Tendsto (fun T : ℝ => (-T + β) ^ 2) atTop atTop := by
          have h0 : Tendsto (fun T : ℝ => (T - β) ^ 2) atTop atTop :=
            (tendsto_pow_atTop (n := 2) (by norm_num)).comp
              (tendsto_atTop_add_const_right atTop (-β) tendsto_id)
          apply h0.congr
          intro T
          ring
        exact tendsto_atTop_add_const_left atTop (x ^ 2) this
      simpa using h1.add h2
  have hFTC' := hlim.congr hFTC
  exact tendsto_nhds_unique hFTC' hdecay

/-- Squared Lorentzian-half mass: `∫ (x/(x²+(t+β)²))² dt = π/(2x)`.
Mechanism: with `w = (x + i(t+β))⁻¹` the pointwise identity
`(Re w)² = (Re (w²) + |w|²)/2` splits the square into the vanishing
holomorphic square integral and half the Lorentzian mass. -/
theorem integral_sq_lorentzianHalf {x : ℝ} (hx : 0 < x) (β : ℝ) :
    ∫ t : ℝ, (x / (x ^ 2 + (t + β) ^ 2)) ^ 2 = π / (2 * x) := by
  have hne : ∀ t : ℝ, ((x : ℂ) + I * ((t + β : ℝ) : ℂ)) ≠ 0 :=
    edgeCrossKernel_denom_ne_zero₁ hx β
  have hint : Integrable fun t : ℝ =>
      (((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2 := by
    apply Integrable.mono' ((lorentzianHalf_integrable hx β).const_mul (1 / x))
    · apply Continuous.aestronglyMeasurable
      apply Continuous.pow
      apply Continuous.inv₀
      · exact continuous_const.add (continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)))
      · exact hne
    · filter_upwards with t
      have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
      have hnorm : ‖((x : ℂ) + I * ((t + β : ℝ) : ℂ))‖ ^ 2
          = x ^ 2 + (t + β) ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im]
        ring
      rw [norm_pow, norm_inv]
      rw [show ‖((x : ℂ) + I * ((t + β : ℝ) : ℂ))‖⁻¹ ^ 2
          = (‖((x : ℂ) + I * ((t + β : ℝ) : ℂ))‖ ^ 2)⁻¹ from by
        rw [inv_pow]]
      rw [hnorm]
      rw [show (1 / x) * (x / (x ^ 2 + (t + β) ^ 2))
          = (x ^ 2 + (t + β) ^ 2)⁻¹ from by field_simp]
  have hlorInv : Integrable fun t : ℝ => (x ^ 2 + (t + β) ^ 2)⁻¹ := by
    have h := (lorentzianHalf_integrable hx β).const_mul (1 / x)
    apply h.congr
    filter_upwards with t
    have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
    field_simp
  have hpt : ∀ t : ℝ, (x / (x ^ 2 + (t + β) ^ 2)) ^ 2
      = (1 / 2 : ℝ) * ((((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2).re
        + (1 / 2 : ℝ) * (x ^ 2 + (t + β) ^ 2)⁻¹ := by
    intro t
    have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
    have hure : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).re = x := by
      simp
    have huim : ((x : ℂ) + I * ((t + β : ℝ) : ℂ)).im = t + β := by
      simp
    have hres : ((((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2).re
        = (x ^ 2 - (t + β) ^ 2) / (x ^ 2 + (t + β) ^ 2) ^ 2 := by
      rw [inv_pow, Complex.inv_re, map_pow,
        pow_two ((x : ℂ) + I * ((t + β : ℝ) : ℂ)), Complex.mul_re,
        hure, huim, Complex.normSq_apply, hure, huim]
      ring
    rw [hres]
    field_simp
    ring
  have hfun : (fun t : ℝ => (x / (x ^ 2 + (t + β) ^ 2)) ^ 2)
      = fun t : ℝ =>
        (1 / 2 : ℝ) * ((((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2).re
          + (1 / 2 : ℝ) * (x ^ 2 + (t + β) ^ 2)⁻¹ := funext hpt
  have h1 : Integrable (fun t : ℝ =>
      (1 / 2 : ℝ) * ((((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2).re)
      volume := hint.re.const_mul (1 / 2 : ℝ)
  have h2 : Integrable (fun t : ℝ =>
      (1 / 2 : ℝ) * (x ^ 2 + (t + β) ^ 2)⁻¹) volume :=
    hlorInv.const_mul (1 / 2 : ℝ)
  have hre0 : (∫ t : ℝ, ((((x : ℂ) + I * ((t + β : ℝ) : ℂ))⁻¹) ^ 2).re)
      = 0 := by
    have hcomm := Complex.reCLM.integral_comp_comm hint
    rw [integral_sq_rightKernel_inv hx β] at hcomm
    simpa using hcomm
  have hlorint : (∫ t : ℝ, (x ^ 2 + (t + β) ^ 2)⁻¹) = π / x := by
    have hcongr : (∫ t : ℝ, (x ^ 2 + (t + β) ^ 2)⁻¹)
        = ∫ t : ℝ, (1 / x) * (x / (x ^ 2 + (t + β) ^ 2)) := by
      congr 1
      funext t
      have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
      field_simp
    rw [hcongr, MeasureTheory.integral_const_mul,
      integral_lorentzianHalf hx β]
    field_simp
  rw [hfun, MeasureTheory.integral_add h1 h2,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hre0, hlorint]
  ring

/-- The squared Lorentzian half is integrable: it is dominated by `x⁻¹`
times the Lorentzian half. -/
theorem integrable_sq_lorentzianHalf {x : ℝ} (hx : 0 < x) (β : ℝ) :
    Integrable fun t : ℝ => (x / (x ^ 2 + (t + β) ^ 2)) ^ 2 := by
  apply Integrable.mono' ((lorentzianHalf_integrable hx β).const_mul (1 / x))
  · apply Continuous.aestronglyMeasurable
    apply Continuous.pow
    exact continuous_const.div
      (continuous_const.add ((continuous_id.add continuous_const).pow 2))
      (fun t => by positivity)
  · filter_upwards with t
    have hD : (0 : ℝ) < x ^ 2 + (t + β) ^ 2 := by positivity
    have hL : 0 ≤ x / (x ^ 2 + (t + β) ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : x / (x ^ 2 + (t + β) ^ 2) ≤ 1 / x := by
      rw [div_le_div_iff₀ hD hx]
      nlinarith [sq_nonneg (t + β)]
    calc (x / (x ^ 2 + (t + β) ^ 2)) ^ 2
        = (x / (x ^ 2 + (t + β) ^ 2)) * (x / (x ^ 2 + (t + β) ^ 2)) := by
          ring
      _ ≤ (1 / x) * (x / (x ^ 2 + (t + β) ^ 2)) :=
          mul_le_mul_of_nonneg_right hle hL

/-- Dropping the positive cross term: the squared edge real part of one
Schwarz pair dominates four times the sum of its two squared Lorentzian
halves. -/
theorem sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_ge
    (q : XiRightUpperZeroCopy) (t : ℝ) :
    4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2 ≤
    ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 := by
  rw [re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_eq]
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have hD1 : 0 < ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
      (t + (xiRightCenteredZero q.1).im) ^ 2 := by positivity
  have hD2 : 0 < ((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
      (t + -(xiRightCenteredZero q.1).im) ^ 2 := by positivity
  have hL1 : 0 ≤ ((xiRightCenteredZero q.1).re + 1 / 2) /
      (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
        (t + (xiRightCenteredZero q.1).im) ^ 2) := by positivity
  have hL2 : 0 ≤ ((xiRightCenteredZero q.1).re + 1 / 2) /
      (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
        (t + -(xiRightCenteredZero q.1).im) ^ 2) := by positivity
  have hkey : (2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + (xiRightCenteredZero q.1).im) ^ 2) +
      2 * ((xiRightCenteredZero q.1).re + 1 / 2) /
        (((xiRightCenteredZero q.1).re + 1 / 2) ^ 2 +
          (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2
      = 4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
          4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
          8 * ((((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + (xiRightCenteredZero q.1).im) ^ 2)) *
            (((xiRightCenteredZero q.1).re + 1 / 2) /
            ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
              (t + -(xiRightCenteredZero q.1).im) ^ 2))) := by
    ring
  rw [hkey]
  linarith [mul_nonneg hL1 hL2]

/-- Each strict-right pair forces edge quadratic energy at least
`4π/(Re λ + 1/2) > 4π` on the continued Ward response. -/
theorem lintegral_normSq_continuedXiAntiCausalWardResponse_edge_lower
    (q : XiRightUpperZeroCopy) :
    ENNReal.ofReal (4 * π / ((xiRightCenteredZero q.1).re + 1 / 2)) ≤
      ∫⁻ t : ℝ, ENNReal.ofReal (Complex.normSq
        (continuedXiAntiCausalWardResponse
          ((1 / 2 : ℂ) + I * (t : ℂ)))) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have h4a : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      ((xiRightCenteredZero q.1).im)).const_mul 4
  have h4b : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      (-(xiRightCenteredZero q.1).im)).const_mul 4
  have hint : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
        4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    h4a.add h4b
  have hgint : (∫ t : ℝ,
      (4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
        4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2)) =
      4 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
    rw [MeasureTheory.integral_add h4a h4b,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_sq_lorentzianHalf hx ((xiRightCenteredZero q.1).im),
      integral_sq_lorentzianHalf hx (-(xiRightCenteredZero q.1).im)]
    field_simp
    ring
  calc ENNReal.ofReal (4 * π / ((xiRightCenteredZero q.1).re + 1 / 2))
      = ∫⁻ t : ℝ, ENNReal.ofReal
          (4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
              ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
                (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
            4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
              ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
                (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) := by
        rw [← hgint]
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
          (Filter.Eventually.of_forall fun t => by positivity)
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal (Complex.normSq
          (continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ)))) := by
        apply MeasureTheory.lintegral_mono
        intro t
        apply ENNReal.ofReal_le_ofReal
        have hw : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
          norm_num [Complex.add_re, Complex.mul_re]
        have h1 := sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_ge q t
        have h2 := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hw
        have h2' : ((xiAntiCausalWardSchwarzPairResponse q
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
            ((continuedXiAntiCausalWardResponse
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 :=
          pow_le_pow_left₀
            (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le h2 2
        have h3 : ((continuedXiAntiCausalWardResponse
              ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
            Complex.normSq (continuedXiAntiCausalWardResponse
              ((1 / 2 : ℂ) + I * (t : ℂ))) := by
          rw [Complex.normSq_apply]
          nlinarith [sq_nonneg (continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))).im]
        linarith

/-- Edge quadratic-energy law at budget `c`: the total squared edge modulus
of the continued Ward response is at most `c`. -/
def ContinuedXiWardEdgeQuadEnergyLaw (c : ℝ) : Prop :=
  ∫⁻ t : ℝ, ENNReal.ofReal (Complex.normSq
      (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))) ≤
    ENNReal.ofReal c

/-- **Four-pi edge completeness law, closed budget.**  For any fixed budget
`0 ≤ c ≤ 4π` the Riemann Hypothesis is equivalent to the edge
quadratic-energy law at budget `c`: under RH the response vanishes
identically, while a single off-critical pair already deposits edge energy
`4π/(Re λ + 1/2)` strictly above `4π` because `Re λ + 1/2 < 1` strictly. -/
theorem riemannHypothesis_iff_continuedXiWardEdgeQuadEnergyLaw
    {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 4 * π) :
    RiemannHypothesis ↔ ContinuedXiWardEdgeQuadEnergyLaw c := by
  constructor
  · intro hRH
    letI : IsEmpty XiRightZeroCopy := by
      constructor
      intro p
      obtain ⟨s, hs⟩ := xiSpectralPoint_real_of_rh hRH p.1
      have hpos := p.2
      rw [hs] at hpos
      simp at hpos
    letI : IsEmpty XiRightUpperZeroCopy := ⟨fun p => isEmptyElim p.1⟩
    have hzero : ∀ t : ℝ,
        continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)) =
          0 := by
      intro t
      have hw : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
        norm_num [Complex.add_re, Complex.mul_re]
      rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
        tsum_empty]
    unfold ContinuedXiWardEdgeQuadEnergyLaw
    rw [show (fun t : ℝ => ENNReal.ofReal (Complex.normSq
        (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ)))))
        = fun _ : ℝ => (0 : ENNReal) from funext fun t => by
      rw [hzero t]; simp]
    rw [lintegral_zero]
    exact zero_le

  · intro hlaw
    by_contra hRH
    obtain ⟨q⟩ := nonempty_xiRightUpperZeroCopy_for_boundaryLift hRH
    have hre := xiRightCenteredZero_re_pos q.1
    have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
    have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
    have hx1 : (xiRightCenteredZero q.1).re + 1 / 2 < 1 := by linarith
    have hchain :=
      (lintegral_normSq_continuedXiAntiCausalWardResponse_edge_lower q).trans
        hlaw
    rw [ENNReal.ofReal_le_ofReal_iff hc0] at hchain
    have hgt : 4 * π < 4 * π /
        ((xiRightCenteredZero q.1).re + 1 / 2) := by
      rw [lt_div_iff₀ hx]
      nlinarith [pi_pos]
    linarith

/-- Diagonal quadratic edge minorant of one Schwarz pair: four times the sum
of its two squared Lorentzian halves. -/
def xiWardPairEdgeQuadMinorant (q : XiRightUpperZeroCopy) (t : ℝ) : ℝ :=
  4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
      ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
        (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2 +
    4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
      ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
        (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2

theorem xiWardPairEdgeQuadMinorant_nonneg (q : XiRightUpperZeroCopy)
    (t : ℝ) : 0 ≤ xiWardPairEdgeQuadMinorant q t := by
  have hre := xiRightCenteredZero_re_pos q.1
  unfold xiWardPairEdgeQuadMinorant
  positivity

theorem xiWardPairEdgeQuadMinorant_le_sq_re (q : XiRightUpperZeroCopy)
    (t : ℝ) :
    xiWardPairEdgeQuadMinorant q t ≤
      ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 := by
  unfold xiWardPairEdgeQuadMinorant
  exact sq_re_xiAntiCausalWardSchwarzPairResponse_eulerEdge_ge q t

theorem integrable_xiWardPairEdgeQuadMinorant (q : XiRightUpperZeroCopy) :
    Integrable (fun t : ℝ => xiWardPairEdgeQuadMinorant q t) volume := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have h4a : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      ((xiRightCenteredZero q.1).im)).const_mul 4
  have h4b : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      (-(xiRightCenteredZero q.1).im)).const_mul 4
  have h := h4a.add h4b
  apply h.congr
  filter_upwards with t
  simp [xiWardPairEdgeQuadMinorant, Pi.add_apply]

/-- Each pair minorant carries total mass `4π/(Re λ + 1/2)`. -/
theorem integral_xiWardPairEdgeQuadMinorant (q : XiRightUpperZeroCopy) :
    ∫ t : ℝ, xiWardPairEdgeQuadMinorant q t =
      4 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
  have hre := xiRightCenteredZero_re_pos q.1
  have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
  have h4a : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + (xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      ((xiRightCenteredZero q.1).im)).const_mul 4
  have h4b : Integrable (fun t : ℝ =>
      4 * (((xiRightCenteredZero q.1).re + 1 / 2) /
          ((((xiRightCenteredZero q.1).re + 1 / 2)) ^ 2 +
            (t + -(xiRightCenteredZero q.1).im) ^ 2)) ^ 2) volume :=
    (integrable_sq_lorentzianHalf hx
      (-(xiRightCenteredZero q.1).im)).const_mul 4
  unfold xiWardPairEdgeQuadMinorant
  rw [MeasureTheory.integral_add h4a h4b,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    integral_sq_lorentzianHalf hx ((xiRightCenteredZero q.1).im),
    integral_sq_lorentzianHalf hx (-(xiRightCenteredZero q.1).im)]
  field_simp
  ring

/-- Over any finite family of strict-right pairs the sum of squared edge
real parts is dominated by the squared edge modulus of the continued
response. -/
theorem sum_sq_re_xiAntiCausalWardSchwarzPairResponse_le_normSq
    (F : Finset XiRightUpperZeroCopy) (t : ℝ) :
    ∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      Complex.normSq (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  have hw : (0 : ℝ) < ((1 / 2 : ℂ) + I * (t : ℂ)).re := by
    norm_num [Complex.add_re, Complex.mul_re]
  have hsum := summable_xiAntiCausalWardSchwarzPairResponse hw
  have hsumre : Summable fun p : XiRightUpperZeroCopy =>
      (xiAntiCausalWardSchwarzPairResponse p
        ((1 / 2 : ℂ) + I * (t : ℂ))).re :=
    (Complex.hasSum_re hsum.hasSum).summable
  have h2 : ∑ q ∈ F, ((xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      (∑ q ∈ F, (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun q _ =>
      (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le
  have h3 : (∑ q ∈ F, (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ≤
      (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re := by
    rw [continuedXiAntiCausalWardResponse_eq_tsum_schwarzPairs hw,
      Complex.re_tsum hsum]
    exact hsumre.sum_le_tsum F fun q _ =>
      (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le
  have h3' : (∑ q ∈ F, (xiAntiCausalWardSchwarzPairResponse q
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      ((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 :=
    pow_le_pow_left₀
      (Finset.sum_nonneg fun q _ =>
        (re_xiAntiCausalWardSchwarzPairResponse_pos q hw).le) h3 2
  have h4 : ((continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))).re) ^ 2 ≤
      Complex.normSq (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))) := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg (continuedXiAntiCausalWardResponse
      ((1 / 2 : ℂ) + I * (t : ℂ))).im]
  linarith

/-- Superadditive pointwise floor: over any finite family of strict-right
pairs, the sum of the pair minorants is dominated by the squared edge
modulus of the continued Ward response.  Cross terms are dropped, not
interchanged: no double-series rearrangement enters. -/
theorem sum_xiWardPairEdgeQuadMinorant_le_normSq
    (F : Finset XiRightUpperZeroCopy) (t : ℝ) :
    ∑ q ∈ F, xiWardPairEdgeQuadMinorant q t ≤
      Complex.normSq (continuedXiAntiCausalWardResponse
        ((1 / 2 : ℂ) + I * (t : ℂ))) := by
  refine le_trans (Finset.sum_le_sum fun q _ =>
    xiWardPairEdgeQuadMinorant_le_sq_re q t) ?_
  exact sum_sq_re_xiAntiCausalWardSchwarzPairResponse_le_normSq F t

/-- Total edge quadratic energy of the continued Ward response. -/
def xiWardEdgeQuadEnergy : ENNReal :=
  ∫⁻ t : ℝ, ENNReal.ofReal (Complex.normSq
    (continuedXiAntiCausalWardResponse ((1 / 2 : ℂ) + I * (t : ℂ))))

/-- **Edge energy counts the divisor**: any `N` distinct strict-right pairs
force edge quadratic energy at least `N·4π`. -/
theorem card_nsmul_le_xiWardEdgeQuadEnergy
    (F : Finset XiRightUpperZeroCopy) :
    ENNReal.ofReal (4 * π * F.card) ≤ xiWardEdgeQuadEnergy := by
  have hintF : Integrable (fun t : ℝ =>
      ∑ q ∈ F, xiWardPairEdgeQuadMinorant q t) volume :=
    integrable_finsetSum F fun q _ => integrable_xiWardPairEdgeQuadMinorant q
  have hval : (∫ t : ℝ, ∑ q ∈ F, xiWardPairEdgeQuadMinorant q t)
      = ∑ q ∈ F, 4 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
    rw [MeasureTheory.integral_finsetSum F fun q _ =>
      integrable_xiWardPairEdgeQuadMinorant q]
    exact Finset.sum_congr rfl fun q _ =>
      integral_xiWardPairEdgeQuadMinorant q
  have hper : ∀ q ∈ F, (4 * π : ℝ) ≤
      4 * π / ((xiRightCenteredZero q.1).re + 1 / 2) := by
    intro q _
    have hre := xiRightCenteredZero_re_pos q.1
    have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
    have hx : 0 < (xiRightCenteredZero q.1).re + 1 / 2 := by linarith
    rw [le_div_iff₀ hx]
    nlinarith [pi_pos]
  have hcard := Finset.card_nsmul_le_sum F _ _ hper
  rw [nsmul_eq_mul] at hcard
  unfold xiWardEdgeQuadEnergy
  calc ENNReal.ofReal (4 * π * F.card)
      ≤ ENNReal.ofReal (∑ q ∈ F,
          4 * π / ((xiRightCenteredZero q.1).re + 1 / 2)) := by
        apply ENNReal.ofReal_le_ofReal
        calc (4 * π * F.card : ℝ) = F.card * (4 * π) := by ring
          _ ≤ _ := hcard
    _ = (∫⁻ t : ℝ, ENNReal.ofReal
          (∑ q ∈ F, xiWardPairEdgeQuadMinorant q t)) := by
        rw [← hval]
        exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hintF
          (Filter.Eventually.of_forall fun t =>
            Finset.sum_nonneg fun q _ =>
              xiWardPairEdgeQuadMinorant_nonneg q t)
    _ ≤ (∫⁻ t : ℝ, ENNReal.ofReal (Complex.normSq
          (continuedXiAntiCausalWardResponse
            ((1 / 2 : ℂ) + I * (t : ℂ))))) := by
        apply MeasureTheory.lintegral_mono
        intro t
        exact ENNReal.ofReal_le_ofReal
          (sum_xiWardPairEdgeQuadMinorant_le_normSq F t)

/-- Zero-counting bound: an edge energy budget `c` caps every finite family
of strict-right pairs at `c/(4π)` members. -/
theorem card_le_of_xiWardEdgeQuadEnergy_le {c : ℝ} (hc0 : 0 ≤ c)
    (hlaw : xiWardEdgeQuadEnergy ≤ ENNReal.ofReal c)
    (F : Finset XiRightUpperZeroCopy) :
    4 * π * F.card ≤ c := by
  have h := (card_nsmul_le_xiWardEdgeQuadEnergy F).trans hlaw
  rwa [ENNReal.ofReal_le_ofReal_iff hc0] at h

/-- **Finiteness law**: finite edge quadratic energy forces a finite
strict-right divisor. -/
theorem finite_xiRightUpperZeroCopy_of_xiWardEdgeQuadEnergy_ne_top
    (h : xiWardEdgeQuadEnergy ≠ ⊤) : Finite XiRightUpperZeroCopy := by
  by_contra hinf
  rw [not_finite_iff_infinite] at hinf
  obtain ⟨n, hn⟩ := exists_nat_gt (xiWardEdgeQuadEnergy.toReal / (4 * π))
  obtain ⟨F, hF⟩ := Infinite.exists_subset_card_eq XiRightUpperZeroCopy n
  have hlow := card_nsmul_le_xiWardEdgeQuadEnergy F
  rw [hF] at hlow
  have hle := (ENNReal.ofReal_le_iff_le_toReal h).mp hlow
  have h4 : (0 : ℝ) < 4 * π := by positivity
  have hgt : xiWardEdgeQuadEnergy.toReal < 4 * π * n := by
    calc xiWardEdgeQuadEnergy.toReal
        = xiWardEdgeQuadEnergy.toReal / (4 * π) * (4 * π) := by
          field_simp
      _ < n * (4 * π) := mul_lt_mul_of_pos_right hn h4
      _ = 4 * π * n := by ring
  linarith


/-- **Bilinear expansion of a mirrored kernel pair.**  Let `k x β` be a kernel family whose
cross products are integrable with the universal mass `π(x+x′)/((x+x′)² + (β−β′)²)`.  If two
functions are constant multiples of the sum of that kernel at a height and at its reflection,
their product integrates to
`2cc′π(x+x′)(1/((x+x′)²+(b−b′)²) + 1/((x+x′)²+(b+b′)²))`.
The four cross terms pair up: the mixed heights `b−(−b′)` and `(−b)−b′` share the denominator
`(b+b′)²`, the aligned ones the denominator `(b−b′)²`. -/
theorem integral_mul_mirroredKernelPair {k : ℝ → ℝ → ℝ → ℝ} {x x' : ℝ}
    (hx : 0 < x) (hx' : 0 < x')
    (hint : ∀ β β' : ℝ, Integrable (fun t : ℝ => k x β t * k x' β' t) volume)
    (hval : ∀ β β' : ℝ, ∫ t : ℝ, k x β t * k x' β' t
      = π * (x + x') / ((x + x') ^ 2 + (β - β') ^ 2))
    (c c' b b' : ℝ) {f f' : ℝ → ℝ}
    (hf : ∀ t, f t = c * (k x b t + k x (-b) t))
    (hf' : ∀ t, f' t = c' * (k x' b' t + k x' (-b') t)) :
    ∫ t : ℝ, f t * f' t =
      2 * (c * c') * π * (x + x') *
        (1 / ((x + x') ^ 2 + (b - b') ^ 2) + 1 / ((x + x') ^ 2 + (b + b') ^ 2)) := by
  have hxx : (0 : ℝ) < x + x' := by linarith
  have hD1 : (0 : ℝ) < (x + x') ^ 2 + (b - b') ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hxx 2) (sq_nonneg _)
  have hD2 : (0 : ℝ) < (x + x') ^ 2 + (b + b') ^ 2 :=
    add_pos_of_pos_of_nonneg (pow_pos hxx 2) (sq_nonneg _)
  have h11 := (hint b b').const_mul (c * c')
  have h12 := (hint b (-b')).const_mul (c * c')
  have h21 := (hint (-b) b').const_mul (c * c')
  have h22 := (hint (-b) (-b')).const_mul (c * c')
  have hfun : (fun t : ℝ => f t * f' t) = fun t : ℝ =>
      ((c * c') * (k x b t * k x' b' t) + (c * c') * (k x b t * k x' (-b') t)) +
      ((c * c') * (k x (-b) t * k x' b' t) + (c * c') * (k x (-b) t * k x' (-b') t)) := by
    funext t
    rw [hf, hf']
    ring
  have hA : Integrable (fun t : ℝ =>
      (c * c') * (k x b t * k x' b' t) + (c * c') * (k x b t * k x' (-b') t)) volume :=
    h11.add h12
  have hB : Integrable (fun t : ℝ =>
      (c * c') * (k x (-b) t * k x' b' t) + (c * c') * (k x (-b) t * k x' (-b') t)) volume :=
    h21.add h22
  rw [hfun, integral_add hA hB, integral_add h11 h12,
    integral_add h21 h22, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hval, hval, hval, hval]
  have e2 : (x + x') ^ 2 + (b - -b') ^ 2 = (x + x') ^ 2 + (b + b') ^ 2 := by ring
  have e3 : (x + x') ^ 2 + (-b - b') ^ 2 = (x + x') ^ 2 + (b + b') ^ 2 := by ring
  have e4 : (x + x') ^ 2 + (-b - -b') ^ 2 = (x + x') ^ 2 + (b - b') ^ 2 := by ring
  rw [e2, e3, e4]
  field_simp
  ring

end

end RHTower
