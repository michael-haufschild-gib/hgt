/-
# Chen--Gupta--Li `h_t`: first parameter-explicit Fourier decay

This module closes the `j = 1` instance of the first family of estimates in
CGL Lemma 4.3: the literal Fourier transform of `h_t` is bounded by a
cutoff-only constant times `(1 + |t|) / |ξ|`.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiHtFourierDerivative

open MeasureTheory
open scoped FourierTransform

noncomputable section

namespace RHTower

/-- The zeroth-order Fourier budget of the literal CGL kernel is independent of `t`. -/
theorem cglSmoothBumpHt_zeroOrderBudget (w : CGLSmoothBump) (t : ℝ) :
    cglSchwartzFourierDecayBudget (cglSmoothBumpHt w t) 0 =
      ∫ x : ℝ, ‖w.value x‖ ^ (2 : ℕ) := by
  rw [show cglSchwartzFourierDecayBudget (cglSmoothBumpHt w t) 0 =
      ∫ x : ℝ, ‖cglSmoothBumpHt w t x‖ by
        simp [cglSchwartzFourierDecayBudget]]
  simp_rw [norm_cglSmoothBumpHt_eq_normSq]

/-- The literal `j = 0` case shared by both families of CGL Lemma 4.3. -/
theorem cglSmoothBumpHt_zeroOrder_fourier_decay (w : CGLSmoothBump) (t ξ : ℝ) :
    ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖ ≤ ∫ x : ℝ, ‖w.value x‖ ^ (2 : ℕ) := by
  have h := cglSmoothBumpHt_abs_pow_mul_norm_fourier_le w t 0 ξ
  rw [pow_zero, one_mul, cglSmoothBumpHt_zeroOrderBudget] at h
  exact h

/-- The Schwartz derivative of the literal CGL cutoff. -/
noncomputable def cglSmoothBumpDerivative (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  SchwartzMap.derivCLM ℂ ℂ w.toSchwartz

theorem cglSmoothBumpDerivative_apply (w : CGLSmoothBump) (x : ℝ) :
    cglSmoothBumpDerivative w x = deriv w.value x := by
  rw [cglSmoothBumpDerivative, SchwartzMap.derivCLM_apply]
  rfl

/-- The Schwartz product `w' w` used in the first `h_t` derivative bound. -/
noncomputable def cglSmoothBumpDerivativeProduct (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (cglSmoothBumpDerivative w) w.toSchwartz

theorem cglSmoothBumpDerivativeProduct_apply (w : CGLSmoothBump) (x : ℝ) :
    cglSmoothBumpDerivativeProduct w x = deriv w.value x * w.value x := by
  rw [cglSmoothBumpDerivativeProduct,
    SchwartzMap.smulLeftCLM_apply_apply (cglSmoothBumpDerivative w).hasTemperateGrowth,
    cglSmoothBumpDerivative_apply]
  rfl

/-- The literal squared cutoff retained as a Schwartz product. -/
noncomputable def cglSmoothBumpSquare (w : CGLSmoothBump) : SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ w.toSchwartz w.toSchwartz

theorem cglSmoothBumpSquare_apply (w : CGLSmoothBump) (x : ℝ) :
    cglSmoothBumpSquare w x = w.value x * w.value x := by
  rw [cglSmoothBumpSquare,
    SchwartzMap.smulLeftCLM_apply_apply w.toSchwartz.hasTemperateGrowth]
  rfl

/-- The source support interval controls the inverse factor in the phase derivative. -/
theorem cglSmoothBump_norm_sq_mul_abs_inv_le (w : CGLSmoothBump) (x : ℝ) :
    ‖w.value x‖ ^ (2 : ℕ) * |x⁻¹| ≤ ‖w.value x‖ ^ (2 : ℕ) := by
  by_cases hx : x ∈ Set.Icc (1 : ℝ) 2
  · have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
    have hinv : |x⁻¹| ≤ 1 := by
      rw [abs_of_nonneg (inv_nonneg.mpr hxpos.le)]
      exact inv_le_one_of_one_le₀ hx.1
    simpa using mul_le_mul_of_nonneg_left hinv (sq_nonneg ‖w.value x‖)
  · rw [w.outside_support x hx]
    norm_num

/-- Pointwise first-derivative bound with two fixed cutoff Schwartz factors. -/
theorem norm_deriv_cglSmoothBumpHtValue_le_linear (w : CGLSmoothBump) (t x : ℝ) :
    ‖deriv (cglSmoothBumpHtValue w t) x‖ ≤
      2 * ‖cglSmoothBumpDerivativeProduct w x‖ + |t| * ‖cglSmoothBumpSquare w x‖ := by
  rw [cglSmoothBumpDerivativeProduct_apply, cglSmoothBumpSquare_apply]
  simp only [norm_mul]
  have hinv := cglSmoothBump_norm_sq_mul_abs_inv_le w x
  calc
    ‖deriv (cglSmoothBumpHtValue w t) x‖ ≤
        2 * ‖deriv w.value x‖ * ‖w.value x‖ +
          |t| * ‖w.value x‖ ^ (2 : ℕ) * |x⁻¹| :=
      norm_deriv_cglSmoothBumpHtValue_le w t x
    _ ≤ 2 * (‖deriv w.value x‖ * ‖w.value x‖) +
          |t| * (‖w.value x‖ * ‖w.value x‖) := by
      nlinarith [mul_le_mul_of_nonneg_left hinv (abs_nonneg t)]

/-- The first derivative has an integrable cutoff-only linear envelope in `|t|`. -/
theorem integral_norm_deriv_cglSmoothBumpHtValue_le_linear (w : CGLSmoothBump) (t : ℝ) :
    (∫ x : ℝ, ‖deriv (cglSmoothBumpHtValue w t) x‖) ≤
      2 * (∫ x : ℝ, ‖cglSmoothBumpDerivativeProduct w x‖) +
        |t| * (∫ x : ℝ, ‖cglSmoothBumpSquare w x‖) := by
  have hderiv : Integrable (fun x : ℝ => ‖deriv (cglSmoothBumpHtValue w t) x‖) := by
    simpa only [cglSmoothBumpHtDerivative_apply] using
      (cglSmoothBumpHtDerivative w t).integrable.norm
  have hproduct : Integrable (fun x : ℝ => ‖cglSmoothBumpDerivativeProduct w x‖) :=
    (cglSmoothBumpDerivativeProduct w).integrable.norm
  have hsquare : Integrable (fun x : ℝ => ‖cglSmoothBumpSquare w x‖) :=
    (cglSmoothBumpSquare w).integrable.norm
  have henvelope : Integrable (fun x : ℝ =>
      2 * ‖cglSmoothBumpDerivativeProduct w x‖ + |t| * ‖cglSmoothBumpSquare w x‖) := by
    exact (hproduct.const_mul 2).add (hsquare.const_mul |t|)
  calc
    (∫ x : ℝ, ‖deriv (cglSmoothBumpHtValue w t) x‖) ≤
        ∫ x : ℝ, 2 * ‖cglSmoothBumpDerivativeProduct w x‖ +
          |t| * ‖cglSmoothBumpSquare w x‖ :=
      integral_mono hderiv henvelope (norm_deriv_cglSmoothBumpHtValue_le_linear w t)
    _ = 2 * (∫ x : ℝ, ‖cglSmoothBumpDerivativeProduct w x‖) +
          |t| * (∫ x : ℝ, ‖cglSmoothBumpSquare w x‖) := by
      rw [integral_add (hproduct.const_mul 2) (hsquare.const_mul |t|),
        integral_const_mul, integral_const_mul]

/-- The generic zeroth-order Fourier budget of `deriv h_t` is its literal `L¹` norm. -/
theorem cglSmoothBumpHtDerivative_zeroOrderBudget (w : CGLSmoothBump) (t : ℝ) :
    cglSchwartzFourierDecayBudget (cglSmoothBumpHtDerivative w t) 0 =
      ∫ x : ℝ, ‖deriv (cglSmoothBumpHtValue w t) x‖ := by
  rw [show cglSchwartzFourierDecayBudget (cglSmoothBumpHtDerivative w t) 0 =
      ∫ x : ℝ, ‖cglSmoothBumpHtDerivative w t x‖ by
        simp [cglSchwartzFourierDecayBudget]]
  simp_rw [cglSmoothBumpHtDerivative_apply]

/-- Cutoff-only constant for the first parameter-explicit CGL Fourier-decay estimate. -/
noncomputable def cglSmoothBumpHtFirstDerivativeDecayBudget (w : CGLSmoothBump) : ℝ :=
  2 * (∫ x : ℝ, ‖cglSmoothBumpDerivativeProduct w x‖) +
    ∫ x : ℝ, ‖cglSmoothBumpSquare w x‖

/-- First Fourier integration by parts with the literal cutoff-only linear `|t|` budget. -/
theorem cglSmoothBumpHt_firstDerivative_fourier_decay_linear (w : CGLSmoothBump) (t ξ : ℝ) :
    (2 * Real.pi) * (|ξ| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) ≤
      cglSmoothBumpHtFirstDerivativeDecayBudget w * (1 + |t|) := by
  rw [cglSmoothBumpHtFirstDerivativeDecayBudget]
  calc
    (2 * Real.pi) * (|ξ| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) ≤
        cglSchwartzFourierDecayBudget (cglSmoothBumpHtDerivative w t) 0 :=
      cglSmoothBumpHt_firstDerivative_fourier_decay w t ξ
    _ = ∫ x : ℝ, ‖deriv (cglSmoothBumpHtValue w t) x‖ :=
      cglSmoothBumpHtDerivative_zeroOrderBudget w t
    _ ≤ 2 * (∫ x : ℝ, ‖cglSmoothBumpDerivativeProduct w x‖) +
          |t| * (∫ x : ℝ, ‖cglSmoothBumpSquare w x‖) :=
      integral_norm_deriv_cglSmoothBumpHtValue_le_linear w t
    _ ≤ (2 * (∫ x : ℝ, ‖cglSmoothBumpDerivativeProduct w x‖) +
          ∫ x : ℝ, ‖cglSmoothBumpSquare w x‖) * (1 + |t|) := by
      have hproduct_nonneg : 0 ≤ ∫ x : ℝ, ‖cglSmoothBumpDerivativeProduct w x‖ :=
        integral_nonneg fun _ => norm_nonneg _
      have hsquare_nonneg : 0 ≤ ∫ x : ℝ, ‖cglSmoothBumpSquare w x‖ :=
        integral_nonneg fun _ => norm_nonneg _
      nlinarith [abs_nonneg t]

/-- The literal `j = 1` case of CGL Lemma 4.3(1). -/
theorem cglSmoothBumpHt_firstOrder_fourier_decay (w : CGLSmoothBump) (t ξ : ℝ) :
    |ξ| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖ ≤
      (cglSmoothBumpHtFirstDerivativeDecayBudget w / (2 * Real.pi)) * (1 + |t|) := by
  have hpos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  refine le_of_mul_le_mul_left ?_ hpos
  calc
    (2 * Real.pi) * (|ξ| * ‖𝓕 (cglSmoothBumpHt w t : ℝ → ℂ) ξ‖) ≤
        cglSmoothBumpHtFirstDerivativeDecayBudget w * (1 + |t|) :=
      cglSmoothBumpHt_firstDerivative_fourier_decay_linear w t ξ
    _ = (2 * Real.pi) *
        ((cglSmoothBumpHtFirstDerivativeDecayBudget w / (2 * Real.pi)) * (1 + |t|)) := by
      field_simp [ne_of_gt hpos]

end RHTower
