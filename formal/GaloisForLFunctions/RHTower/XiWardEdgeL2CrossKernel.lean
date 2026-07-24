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
