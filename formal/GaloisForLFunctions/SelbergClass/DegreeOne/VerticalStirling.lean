import GaloisForLFunctions.RHTower.GammaVerticalPhaseSecondOrder
import GaloisForLFunctions.HTGeometry.GammaShiftRatioAsymptotic
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Stirling's formula on vertical lines, with its constant

For every real `a`, as `τ → +∞`,

`Γ(a + iτ) ~ √(2π) · e^{iπ(a−½)/2} · τ^{a−½} · e^{−πτ/2} · e^{i(τ log τ − τ)}`.

The line `a = ½` is exact in modulus (`|Γ(½+iτ)|² = π/cosh πτ`) and second-order in phase.  Translates
to the right follow from the digamma ratio, and translates to the left from `Γ(w+1) = wΓ(w)`.
-/

set_option autoImplicit false

open Complex Filter Topology
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

noncomputable section

/-- The Stirling shape of `Γ(a + iτ)`, without the constant `√(2π)`. -/
def stirlingShape (a τ : ℝ) : ℂ :=
  cexp (I * ((π * (a - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) *
    ((τ ^ (a - 1 / 2) * Real.exp (-(π * τ / 2)) : ℝ) : ℂ)

theorem stirlingShape_ne_zero (a : ℝ) {τ : ℝ} (hτ : 0 < τ) : stirlingShape a τ ≠ 0 := by
  unfold stirlingShape
  refine mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.mpr ?_)
  exact (mul_pos (Real.rpow_pos_of_pos hτ _) (Real.exp_pos _)).ne'

/-- `‖Γ(½+iτ)‖ e^{πτ/2} → √(2π)`, from the exact modulus. -/
theorem tendsto_norm_Gamma_half_mul_exp :
    Tendsto (fun τ : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ * Real.exp (π * τ / 2))
      atTop (𝓝 (Real.sqrt (2 * π))) := by
  have hexp : Tendsto (fun τ : ℝ => Real.exp (-(2 * π * τ))) atTop (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (by positivity : (0 : ℝ) < 2 * π))
  have hq : Tendsto (fun τ : ℝ => 2 * π / (1 + Real.exp (-(2 * π * τ)))) atTop
      (𝓝 (2 * π / (1 + 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.add hexp) (by norm_num)
  rw [add_zero, div_one] at hq
  have hs := (Real.continuous_sqrt.tendsto (2 * π)).comp hq
  refine hs.congr fun τ => ?_
  have hsq := HTGeometry.norm_Gamma_half_add_I_sq τ
  have hcast : (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) = 1 / 2 + (τ : ℂ) * I := by
    push_cast
    rfl
  rw [hcast]
  simp only [Function.comp_apply]
  have hval : 2 * π / (1 + Real.exp (-(2 * π * τ))) =
      (‖Complex.Gamma (1 / 2 + (τ : ℂ) * I)‖ * Real.exp (π * τ / 2)) ^ 2 := by
    rw [mul_pow, hsq, ← Real.exp_nat_mul, Real.cosh_eq]
    have e1 : ((2 : ℕ) : ℝ) * (π * τ / 2) = π * τ := by
      push_cast
      ring
    have e2 : Real.exp (-(2 * π * τ)) = Real.exp (-(π * τ)) / Real.exp (π * τ) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [e1, e2]
    have hE := Real.exp_pos (π * τ)
    have hE' := Real.exp_pos (-(π * τ))
    field_simp
  rw [hval, Real.sqrt_sq (by positivity)]

/-- The line `a = ½`. -/
theorem tendsto_Gamma_half_div_stirlingShape :
    Tendsto (fun τ : ℝ => Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) / stirlingShape (1 / 2) τ)
      atTop (𝓝 (Real.sqrt (2 * π) : ℂ)) := by
  have hphase : Tendsto (fun τ : ℝ =>
      RHTower.gammaVerticalPhase (1 / 2) τ - (τ * Real.log τ - τ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (tendsto_const_nhds.div_atTop tendsto_id (a := (8 : ℝ)))
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with τ hτ
    exact RHTower.abs_gammaVerticalPhase_half_sub_main_le hτ
  have hexp : Tendsto (fun τ : ℝ =>
      cexp (I * ((RHTower.gammaVerticalPhase (1 / 2) τ - (τ * Real.log τ - τ) : ℝ) : ℂ))) atTop
      (𝓝 (cexp (I * ((0 : ℝ) : ℂ)))) := by
    refine (Complex.continuous_exp.tendsto _).comp ?_
    refine tendsto_const_nhds.mul ?_
    exact (Complex.continuous_ofReal.tendsto _).comp hphase
  have hnorm := (Complex.continuous_ofReal.tendsto _).comp tendsto_norm_Gamma_half_mul_exp
  have hmul := hnorm.mul hexp
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hpolar := RHTower.gammaVerticalValue_eq_norm_mul_exp_phase (σ := 1 / 2) (by norm_num) τ
  unfold RHTower.gammaVerticalValue at hpolar
  rw [hpolar]
  simp only [Function.comp_apply, stirlingShape]
  have hE : ((Real.exp (π * τ / 2) : ℝ) : ℂ) * ((Real.exp (-(π * τ / 2)) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
  have hP : τ ^ ((1 : ℝ) / 2 - 1 / 2) = 1 := by
    rw [sub_self, Real.rpow_zero]
  have hexp1 : cexp (I * ((π * ((1 : ℝ) / 2 - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) *
      cexp (I * ((RHTower.gammaVerticalPhase (1 / 2) τ - (τ * Real.log τ - τ) : ℝ) : ℂ)) =
      cexp (I * ((RHTower.gammaVerticalPhase (1 / 2) τ : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hne : cexp (I * ((π * ((1 : ℝ) / 2 - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have hne2 : ((Real.exp (-(π * τ / 2)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [hP, one_mul, Complex.ofReal_mul, eq_div_iff (mul_ne_zero hne hne2), ← hexp1]
  generalize cexp (I * ((π * ((1 : ℝ) / 2 - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) = X at *
  generalize cexp (I * ((RHTower.gammaVerticalPhase (1 / 2) τ - (τ * Real.log τ - τ) : ℝ) : ℂ)) = Y
  linear_combination
    ((‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ : ℂ) * Y * X) * hE

/-- `(½+iτ)^λ / (τ^λ e^{iπλ/2}) → 1`. -/
theorem tendsto_half_cpow_div (lam : ℝ) :
    Tendsto (fun τ : ℝ => (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) ^ (lam : ℂ) /
      ((τ ^ lam : ℝ) * cexp (I * ((π * lam / 2 : ℝ) : ℂ)))) atTop (𝓝 1) := by
  have h := HTGeometry.tendsto_log_vertical_sub_vertLog (1 / 2)
  have hexp : Tendsto (fun τ : ℝ =>
      cexp ((lam : ℂ) * (Complex.log (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) - vertLog τ)))
      atTop (𝓝 (cexp ((lam : ℂ) * 0))) :=
    (Complex.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul h)
  rw [mul_zero, Complex.exp_zero] at hexp
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hne : (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hτ.ne' this
  rw [Complex.cpow_def_of_ne_zero hne]
  have hd : ((τ ^ lam : ℝ) : ℂ) * cexp (I * ((π * lam / 2 : ℝ) : ℂ)) =
      cexp ((lam : ℂ) * vertLog τ) := by
    rw [Real.rpow_def_of_pos hτ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    unfold vertLog
    push_cast
    ring
  rw [hd, ← Complex.exp_sub]
  congr 1
  ring

/-- Translating the shape to the right. -/
theorem stirlingShape_add (a lam : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    stirlingShape (a + lam) τ =
      stirlingShape a τ * (((τ ^ lam : ℝ) : ℂ) * cexp (I * ((π * lam / 2 : ℝ) : ℂ))) := by
  unfold stirlingShape
  have e1 : cexp (I * ((π * (a + lam - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) =
      cexp (I * ((π * (a - 1 / 2) / 2 + (τ * Real.log τ - τ) : ℝ) : ℂ)) *
        cexp (I * ((π * lam / 2 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e2 : τ ^ (a + lam - 1 / 2) = τ ^ (a - 1 / 2) * τ ^ lam := by
    rw [← Real.rpow_add hτ]
    congr 1
    ring
  rw [e1, e2]
  push_cast
  ring

/-- Stirling's formula to the right of the critical line. -/
theorem tendsto_Gamma_div_stirlingShape_of_nonneg {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun τ : ℝ => Complex.Gamma (((1 / 2 + lam : ℝ) : ℂ) + (τ : ℂ) * I) /
      stirlingShape (1 / 2 + lam) τ) atTop (𝓝 (Real.sqrt (2 * π) : ℂ)) := by
  have h1 := HTGeometry.tendsto_gammaShift_ratio (σ := 1 / 2) (by norm_num) hlam
  have h := (h1.mul tendsto_Gamma_half_div_stirlingShape).mul (tendsto_half_cpow_div lam)
  simp only [one_mul, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hne : (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hτ.ne' this
  have hG0 : Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp)
  have hZ : (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I) ^ (lam : ℂ) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hne]
    exact Complex.exp_ne_zero _
  have hS := stirlingShape_ne_zero (1 / 2) hτ
  have hD : ((τ ^ lam : ℝ) : ℂ) * cexp (I * ((π * lam / 2 : ℝ) : ℂ)) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hτ _).ne') (Complex.exp_ne_zero _)
  rw [stirlingShape_add _ _ hτ]
  simp only [gammaLine]
  field_simp

/-- A limit for `Γ(a+1+iτ)` gives the same limit for `Γ(a+iτ)`. -/
theorem tendsto_Gamma_div_stirlingShape_step {a : ℝ} {C : ℂ}
    (h : Tendsto (fun τ : ℝ => Complex.Gamma (((a + 1 : ℝ) : ℂ) + (τ : ℂ) * I) /
      stirlingShape (a + 1) τ) atTop (𝓝 C)) :
    Tendsto (fun τ : ℝ => Complex.Gamma ((a : ℂ) + (τ : ℂ) * I) / stirlingShape a τ) atTop
      (𝓝 C) := by
  have hdiv : Tendsto (fun τ : ℝ => a / τ) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hq : Tendsto (fun τ : ℝ => (1 - ((a / τ : ℝ) : ℂ) * I)⁻¹) atTop (𝓝 1) := by
    have h0 : Tendsto (fun τ : ℝ => (1 : ℂ) - ((a / τ : ℝ) : ℂ) * I) atTop
        (𝓝 (1 - ((0 : ℝ) : ℂ) * I)) :=
      tendsto_const_nhds.sub (((Complex.continuous_ofReal.tendsto _).comp hdiv).mul_const I)
    simp only [Complex.ofReal_zero, zero_mul, sub_zero] at h0
    simpa using h0.inv₀ one_ne_zero
  have hmul := h.mul hq
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with τ hτ
  have hτc : (τ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ.ne'
  have hw : ((a : ℂ) + (τ : ℂ) * I) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact hτ.ne' this
  have hτI : (τ : ℂ) * I ≠ 0 := mul_ne_zero hτc Complex.I_ne_zero
  have hS := stirlingShape_ne_zero a hτ
  have hshape : stirlingShape (a + 1) τ = stirlingShape a τ * ((τ : ℂ) * I) := by
    rw [stirlingShape_add _ _ hτ, Real.rpow_one]
    have e : ((π * 1 / 2 : ℝ) : ℂ) = (π : ℂ) / 2 := by
      push_cast
      ring
    rw [e, mul_comm I, Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    simp
  have hG : Complex.Gamma (((a + 1 : ℝ) : ℂ) + (τ : ℂ) * I) =
      ((a : ℂ) + (τ : ℂ) * I) * Complex.Gamma ((a : ℂ) + (τ : ℂ) * I) := by
    rw [← Complex.Gamma_add_one _ hw]
    congr 1
    push_cast
    ring
  have hfrac : (1 : ℂ) - ((a / τ : ℝ) : ℂ) * I = ((a : ℂ) + (τ : ℂ) * I) / ((τ : ℂ) * I) := by
    rw [eq_div_iff hτI]
    have hc : (a : ℂ) / τ * τ = a := div_mul_cancel₀ _ hτc
    push_cast
    linear_combination (-(I * I)) * hc + (-(a : ℂ)) * Complex.I_mul_I
  rw [hshape, hG, hfrac]
  field_simp

/-- **Stirling's formula on the vertical line through any real `a`.** -/
theorem tendsto_Gamma_div_stirlingShape (a : ℝ) :
    Tendsto (fun τ : ℝ => Complex.Gamma ((a : ℂ) + (τ : ℂ) * I) / stirlingShape a τ) atTop
      (𝓝 (Real.sqrt (2 * π) : ℂ)) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / 2 ≤ a + n := by
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / 2 - a)
    exact ⟨n, by linarith⟩
  induction n generalizing a with
  | zero =>
    have h := tendsto_Gamma_div_stirlingShape_of_nonneg (lam := a - 1 / 2) (by
      push_cast at hn
      linarith)
    rwa [show (1 : ℝ) / 2 + (a - 1 / 2) = a by ring] at h
  | succ n ih =>
    refine tendsto_Gamma_div_stirlingShape_step (ih (a + 1) ?_)
    push_cast at hn ⊢
    linarith

end

end GaloisForLFunctions.SelbergClass.DegreeOne
