import Mathlib
import GaloisForLFunctions.RHTower.SuzukiGammaWeightedTailCoercivity

/-!
# Finiteness of the shifted Gamma jump constant

The negative majorant of the vertically shifted Gamma jump integrand is integrable on the positive
ray for every shift below one, so the constant

`kappa_sigma = ∫_0^∞ 2 (cosh (sigma s) − 1)/(exp s − 1) ds`

is finite.  Two elementary bounds do it.  For `sigma ≤ 1` monotonicity of `cosh` and the identity
`2(cosh s − 1) = e^{-s}(e^s − 1)^2` give the uniform bound `1 − e^{-s} ≤ 1`.  For `s ≥ 1` the
denominator is at least `e^s/2` and `cosh (sigma s) ≤ e^{sigma s}`, giving `4 e^{-(1-sigma)s}`.
The exact integrand is dominated by that majorant plus a term coming from `1 − cos (xs) ≤ x^2s^2/2`,
so the integrated numerical-range bound `-kappa_sigma ≤ ∫ Re r_sigma` holds for every real
frequency.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

private theorem exp_sub_one_pos {s : ℝ} (hs : 0 < s) : 0 < Real.exp s - 1 :=
  sub_pos.mpr (Real.one_lt_exp_iff.mpr hs)

private theorem half_exp_le_exp_sub_one {s : ℝ} (hs : 1 ≤ s) :
    Real.exp s / 2 ≤ Real.exp s - 1 := by
  have h2 : (2 : ℝ) ≤ Real.exp s := by
    have h1 : Real.exp 1 ≤ Real.exp s := Real.exp_le_exp.mpr hs
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    linarith
  linarith

/-- Two times `cosh s − 1` factors through the denominator. -/
private theorem two_cosh_sub_one_eq (s : ℝ) :
    2 * (Real.cosh s - 1) = Real.exp (-s) * (Real.exp s - 1) ^ 2 := by
  rw [Real.cosh_eq, Real.exp_neg]
  have hs : Real.exp s ≠ 0 := Real.exp_ne_zero s
  field_simp
  ring

/-- **Uniform bound.**  Below shift one the majorant never exceeds one. -/
theorem suzukiGammaShiftLowerKernel_le_one {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) {s : ℝ}
    (hs : 0 < s) : suzukiGammaShiftLowerKernel σ s ≤ 1 := by
  have hden := exp_sub_one_pos hs
  have hmono : Real.cosh (σ * s) ≤ Real.cosh s := by
    refine Real.cosh_le_cosh.mpr ?_
    rw [abs_of_nonneg (mul_nonneg hσ0 hs.le), abs_of_nonneg hs.le]
    nlinarith
  have hkey : 2 * (Real.cosh s - 1) / (Real.exp s - 1) = 1 - Real.exp (-s) := by
    rw [two_cosh_sub_one_eq, Real.exp_neg]
    have hs0 : Real.exp s ≠ 0 := Real.exp_ne_zero s
    field_simp
  have hstep : suzukiGammaShiftLowerKernel σ s ≤ 2 * (Real.cosh s - 1) / (Real.exp s - 1) := by
    rw [suzukiGammaShiftLowerKernel]
    exact (div_le_div_iff_of_pos_right hden).mpr (by linarith)
  rw [hkey] at hstep
  have : 0 < Real.exp (-s) := Real.exp_pos _
  linarith

/-- **Tail bound.**  Beyond `s = 1` the majorant decays at rate `1 − sigma`. -/
theorem suzukiGammaShiftLowerKernel_le_exp {σ : ℝ} (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 1 ≤ s) :
    suzukiGammaShiftLowerKernel σ s ≤ 4 * Real.exp (-(1 - σ) * s) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs
  have hden := exp_sub_one_pos hs0
  have hhalf := half_exp_le_exp_sub_one hs
  have hcosh : Real.cosh (σ * s) ≤ Real.exp (σ * s) := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-(σ * s)) ≤ Real.exp (σ * s) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  have hnum : 2 * (Real.cosh (σ * s) - 1) ≤ 2 * Real.exp (σ * s) := by
    have := Real.one_le_cosh (σ * s)
    linarith
  have hexppos : (0 : ℝ) < Real.exp s := Real.exp_pos s
  have hquot : suzukiGammaShiftLowerKernel σ s ≤ 2 * Real.exp (σ * s) / (Real.exp s / 2) := by
    rw [suzukiGammaShiftLowerKernel]
    have hnn : 0 ≤ 2 * (Real.cosh (σ * s) - 1) := by
      have := Real.one_le_cosh (σ * s)
      linarith
    have hpos : (0 : ℝ) < Real.exp s / 2 := by positivity
    calc 2 * (Real.cosh (σ * s) - 1) / (Real.exp s - 1)
        ≤ 2 * (Real.cosh (σ * s) - 1) / (Real.exp s / 2) :=
          div_le_div_of_nonneg_left hnn hpos hhalf
      _ ≤ 2 * Real.exp (σ * s) / (Real.exp s / 2) :=
          (div_le_div_iff_of_pos_right hpos).mpr hnum
  have hfinal : 2 * Real.exp (σ * s) / (Real.exp s / 2) = 4 * Real.exp (-(1 - σ) * s) := by
    rw [show -(1 - σ) * s = σ * s - s by ring, Real.exp_sub]
    field_simp
    ring
  rw [hfinal] at hquot
  exact hquot

private theorem continuousOn_lowerKernel (σ : ℝ) :
    ContinuousOn (suzukiGammaShiftLowerKernel σ) (Ioi 0) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  unfold suzukiGammaShiftLowerKernel
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (exp_sub_one_pos hs).ne'

private theorem continuousOn_realIntegrand (σ x : ℝ) :
    ContinuousOn (suzukiGammaShiftRealIntegrand σ x) (Ioi 0) := by
  intro s hs
  refine ContinuousAt.continuousWithinAt ?_
  unfold suzukiGammaShiftRealIntegrand
  exact ContinuousAt.div (by fun_prop) (by fun_prop) (exp_sub_one_pos hs).ne'

/-- **Finiteness of the shift constant.**  For every shift strictly below one the negative majorant
is integrable on the positive ray. -/
theorem integrableOn_suzukiGammaShiftLowerKernel {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    IntegrableOn (suzukiGammaShiftLowerKernel σ) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  have hnear : IntegrableOn (suzukiGammaShiftLowerKernel σ) (Ioc 0 1) := by
    have hmeas : AEStronglyMeasurable (suzukiGammaShiftLowerKernel σ)
        (volume.restrict (Ioc 0 1)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact (continuousOn_lowerKernel σ).mono (fun s hs => hs.1)
    refine Integrable.mono' (g := fun _ : ℝ => (1 : ℝ)) ?_ hmeas ?_
    · exact integrableOn_const (by simp)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_eq_abs, abs_of_nonneg (suzukiGammaShiftLowerKernel_nonneg σ hs.1)]
      exact suzukiGammaShiftLowerKernel_le_one hσ0 hσ1.le hs.1
  have hfar : IntegrableOn (suzukiGammaShiftLowerKernel σ) (Ioi 1) := by
    have hmeas : AEStronglyMeasurable (suzukiGammaShiftLowerKernel σ)
        (volume.restrict (Ioi 1)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      exact (continuousOn_lowerKernel σ).mono
        (fun s hs => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hs)))
    refine Integrable.mono' (g := fun s : ℝ => 4 * Real.exp (-(1 - σ) * s)) ?_ hmeas ?_
    · exact (exp_neg_integrableOn_Ioi 1 (by linarith : (0 : ℝ) < 1 - σ)).const_mul 4
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
      rw [Real.norm_eq_abs,
        abs_of_nonneg (suzukiGammaShiftLowerKernel_nonneg σ (lt_trans zero_lt_one hs))]
      exact suzukiGammaShiftLowerKernel_le_exp hσ0 hs1
  rw [hsplit]
  exact hnear.union hfar

/-- The finite shifted Gamma jump constant `kappa_sigma`. -/
def suzukiGammaShiftKappa (σ : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), suzukiGammaShiftLowerKernel σ s

theorem suzukiGammaShiftKappa_nonneg (σ : ℝ) : 0 ≤ suzukiGammaShiftKappa σ := by
  refine setIntegral_nonneg measurableSet_Ioi fun s hs => ?_
  exact suzukiGammaShiftLowerKernel_nonneg σ hs

/-- The exact integrand is dominated by the majorant plus the cosine defect. -/
theorem abs_suzukiGammaShiftRealIntegrand_le (σ x : ℝ) {s : ℝ} (hs : 0 < s) :
    |suzukiGammaShiftRealIntegrand σ x s| ≤
      suzukiGammaShiftLowerKernel σ s + x ^ 2 * s ^ 2 / (Real.exp s - 1) := by
  have hden := exp_sub_one_pos hs
  have hq : 1 - (x * s) ^ 2 / 2 ≤ Real.cos (x * s) := Real.one_sub_sq_div_two_le_cos
  have hcosh := Real.one_le_cosh (σ * s)
  have hcosle := Real.cos_le_one (x * s)
  have hcosge := Real.neg_one_le_cos (x * s)
  have hprod : 0 ≤ (Real.cosh (σ * s) - 1) * (1 + Real.cos (x * s)) :=
    mul_nonneg (by linarith) (by linarith)
  have hnum : |2 * (1 - Real.cosh (σ * s) * Real.cos (x * s))| ≤
      2 * (Real.cosh (σ * s) - 1) + x ^ 2 * s ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x * s), hprod]
  rw [suzukiGammaShiftRealIntegrand, suzukiGammaShiftLowerKernel, abs_div,
    abs_of_pos hden, ← add_div]
  exact (div_le_div_iff_of_pos_right hden).mpr hnum

/-! ## The cosine defect and the integrated bound -/

private theorem sq_le_exp_half (s : ℝ) (hs : 0 ≤ s) : s ^ 2 ≤ 16 * Real.exp (s / 2) := by
  have h1 : 1 + s / 4 ≤ Real.exp (s / 4) := by
    have := Real.add_one_le_exp (s / 4)
    linarith
  have hpos : (0 : ℝ) ≤ 1 + s / 4 := by linarith
  have hsq : (1 + s / 4) ^ 2 ≤ Real.exp (s / 4) ^ 2 := by
    nlinarith [Real.exp_pos (s / 4)]
  have hexp : Real.exp (s / 4) ^ 2 = Real.exp (s / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp] at hsq
  nlinarith

/-- The cosine defect term is integrable on the positive ray. -/
theorem integrableOn_cosineDefect (x : ℝ) :
    IntegrableOn (fun s : ℝ => x ^ 2 * s ^ 2 / (Real.exp s - 1)) (Ioi 0) := by
  have hcont : ContinuousOn (fun s : ℝ => x ^ 2 * s ^ 2 / (Real.exp s - 1)) (Ioi 0) := by
    intro s hs
    refine ContinuousAt.continuousWithinAt ?_
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (exp_sub_one_pos hs).ne'
  have hnn : ∀ {s : ℝ}, 0 < s → 0 ≤ x ^ 2 * s ^ 2 / (Real.exp s - 1) := by
    intro s hs
    exact div_nonneg (by positivity) (exp_sub_one_pos hs).le
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  have hnear : IntegrableOn (fun s : ℝ => x ^ 2 * s ^ 2 / (Real.exp s - 1)) (Ioc 0 1) := by
    have hmeas : AEStronglyMeasurable (fun s : ℝ => x ^ 2 * s ^ 2 / (Real.exp s - 1))
        (volume.restrict (Ioc 0 1)) :=
      (hcont.mono (fun s hs => hs.1)).aestronglyMeasurable measurableSet_Ioc
    refine Integrable.mono' (g := fun _ : ℝ => x ^ 2) ?_ hmeas ?_
    · exact integrableOn_const (by simp)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      have hs0 : 0 < s := hs.1
      have hlow : s ≤ Real.exp s - 1 := by
        have := Real.add_one_le_exp s
        linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn hs0)]
      have hquot : s ^ 2 / (Real.exp s - 1) ≤ 1 := by
        rw [div_le_one (exp_sub_one_pos hs0)]
        nlinarith [hs.2]
      calc x ^ 2 * s ^ 2 / (Real.exp s - 1) = x ^ 2 * (s ^ 2 / (Real.exp s - 1)) := by ring
        _ ≤ x ^ 2 * 1 := by nlinarith [sq_nonneg x, hnn hs0]
        _ = x ^ 2 := by ring
  have hfar : IntegrableOn (fun s : ℝ => x ^ 2 * s ^ 2 / (Real.exp s - 1)) (Ioi 1) := by
    have hmeas : AEStronglyMeasurable (fun s : ℝ => x ^ 2 * s ^ 2 / (Real.exp s - 1))
        (volume.restrict (Ioi 1)) :=
      (hcont.mono (fun s hs => mem_Ioi.mpr (lt_trans zero_lt_one (mem_Ioi.mp hs)))).aestronglyMeasurable
        measurableSet_Ioi
    refine Integrable.mono' (g := fun s : ℝ => (32 * x ^ 2) * Real.exp (-(1 / 2 : ℝ) * s)) ?_
      hmeas ?_
    · exact (exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      have hs1 : (1 : ℝ) ≤ s := le_of_lt hs
      have hs0 : (0 : ℝ) < s := lt_of_lt_of_le zero_lt_one hs1
      have hhalf := half_exp_le_exp_sub_one hs1
      have hexp : (0 : ℝ) < Real.exp s := Real.exp_pos s
      have hsq := sq_le_exp_half s hs0.le
      have hkey : s ^ 2 / (Real.exp s - 1) ≤ 32 * Real.exp (-(1 / 2 : ℝ) * s) := by
        have h1 : s ^ 2 / (Real.exp s - 1) ≤ s ^ 2 / (Real.exp s / 2) :=
          div_le_div_of_nonneg_left (sq_nonneg s) (by positivity) hhalf
        have h2 : s ^ 2 / (Real.exp s / 2) ≤ 16 * Real.exp (s / 2) / (Real.exp s / 2) :=
          (div_le_div_iff_of_pos_right (by positivity)).mpr hsq
        have h3 : 16 * Real.exp (s / 2) / (Real.exp s / 2) = 32 * Real.exp (-(1 / 2 : ℝ) * s) := by
          rw [show -(1 / 2 : ℝ) * s = s / 2 - s by ring, Real.exp_sub]
          field_simp
          ring
        linarith [h1, h2, h3.le, h3.ge]
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn hs0)]
      calc x ^ 2 * s ^ 2 / (Real.exp s - 1) = x ^ 2 * (s ^ 2 / (Real.exp s - 1)) := by ring
        _ ≤ x ^ 2 * (32 * Real.exp (-(1 / 2 : ℝ) * s)) := by nlinarith [sq_nonneg x]
        _ = 32 * x ^ 2 * Real.exp (-(1 / 2 : ℝ) * s) := by ring
  rw [hsplit]
  exact hnear.union hfar

/-- The exact shifted Gamma integrand is integrable on the positive ray. -/
theorem integrableOn_suzukiGammaShiftRealIntegrand {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (x : ℝ) :
    IntegrableOn (suzukiGammaShiftRealIntegrand σ x) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable (suzukiGammaShiftRealIntegrand σ x)
      (volume.restrict (Ioi 0)) :=
    (continuousOn_realIntegrand σ x).aestronglyMeasurable measurableSet_Ioi
  have hmaj : IntegrableOn
      (fun s : ℝ => suzukiGammaShiftLowerKernel σ s + x ^ 2 * s ^ 2 / (Real.exp s - 1))
      (Ioi 0) :=
    Integrable.add (integrableOn_suzukiGammaShiftLowerKernel hσ0 hσ1)
      (integrableOn_cosineDefect x)
  refine Integrable.mono'
    (g := fun s : ℝ => suzukiGammaShiftLowerKernel σ s + x ^ 2 * s ^ 2 / (Real.exp s - 1))
    hmaj hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs]
  exact abs_suzukiGammaShiftRealIntegrand_le σ x hs

/-- **Integrated numerical-range bound.**  For every real frequency the real part of the shifted
Gamma jump multiplier is at least `-kappa_sigma`. -/
theorem neg_suzukiGammaShiftKappa_le_integral {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (x : ℝ) :
    -suzukiGammaShiftKappa σ ≤ ∫ s in Ioi (0 : ℝ), suzukiGammaShiftRealIntegrand σ x s := by
  rw [suzukiGammaShiftKappa, ← integral_neg]
  refine setIntegral_mono_on
    ((integrableOn_suzukiGammaShiftLowerKernel hσ0 hσ1).neg)
    (integrableOn_suzukiGammaShiftRealIntegrand hσ0 hσ1 x) measurableSet_Ioi fun s hs => ?_
  exact neg_suzukiGammaShiftLowerKernel_le_realIntegrand σ x hs

/-! ## The multiplier numerical range -/

/-- **Numerical-range bound from a symbol bound.**  A multiplication operator whose symbol has real
part at least `-kappa` almost everywhere has quadratic form at least `-kappa` times the squared
norm.  This is the Plancherel step: once the shifted Gamma jump is realized as multiplication by
`r_sigma` on the Fourier side, `neg_suzukiGammaShiftKappa_le_integral` is exactly the hypothesis
`hsymbol` below. -/
theorem neg_mul_integral_normSq_le_integral_re_symbol
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {m f : α → ℂ} {κ : ℝ}
    (hsymbol : ∀ᵐ x ∂μ, -κ ≤ (m x).re)
    (hEnergy : Integrable (fun x => ‖f x‖ ^ 2) μ)
    (hForm : Integrable (fun x => (m x).re * ‖f x‖ ^ 2) μ) :
    -κ * ∫ x, ‖f x‖ ^ 2 ∂μ ≤ ∫ x, (m x).re * ‖f x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  refine integral_mono_ae (hEnergy.const_mul _) hForm ?_
  filter_upwards [hsymbol] with x hx
  exact mul_le_mul_of_nonneg_right hx (by positivity)

end GaloisForLFunctions.RHTower
