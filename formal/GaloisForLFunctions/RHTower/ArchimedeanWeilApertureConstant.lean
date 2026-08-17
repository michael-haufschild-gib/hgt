import GaloisForLFunctions.RHTower.ArchimedeanWeilKernelSign

/-!
# The aperture constant of the archimedean Weil form

Continuing `ArchimedeanWeilKernelSign`.  Writing the archimedean Weil functional together with the
pole contribution in the autocorrelation variable, for an even correlation supported in `[-S, S]`,

```
  C S · g 0  +  ∫_0^S (g 0 - g u) · K u  du,
```

this module bounds the scalar `C S` from below and exhibits an explicit aperture below which it is
strictly positive.  Together with `weilKernel_pos_of_lt_threshold` — which makes the integral term
nonnegative — this gives an elementary positivity certificate for the archimedean part at small
aperture, with no explicit formula, no prolate analysis and no operator theory.

```
  C S = -γ - log π - log (1 - e^{-2S}) - J S + 8 sinh (S/2),
  J S = 2 ∫_0^S (e^{-u/2} - e^{-2u}) / (1 - e^{-2u}) du.
```

The deficit integrand is pinned between `0` and `3/4`; the bound `3/4` is the algebraic inequality
`y⁴ - 4y + 3 = (y-1)²(y²+2y+3) ≥ 0` at `y = e^{-u/2}`, and it is attained in the limit `u → 0`.
Since `-log (1 - e^{-2S}) ≥ -log (2S) → ∞` as `S → 0`, the constant is positive below the explicit
threshold `1 / (2π e^{γ + 3/4})`.
-/

namespace RHTower.ArchimedeanKernel

/-- Integrand of the deficit correction. -/
noncomputable def kernelDeficit (u : ℝ) : ℝ :=
  (Real.exp (-u / 2) - Real.exp (-2 * u)) / (1 - Real.exp (-2 * u))

/-- The deficit correction at aperture `S`. -/
noncomputable def deficitIntegral (S : ℝ) : ℝ := 2 * ∫ u in (0 : ℝ)..S, kernelDeficit u

/-- The scalar coefficient of `g 0` in the aperture-restricted archimedean Weil form. -/
noncomputable def apertureConstant (S : ℝ) : ℝ :=
  -Real.eulerMascheroniConstant - Real.log Real.pi - Real.log (1 - Real.exp (-2 * S)) -
    deficitIntegral S + 8 * Real.sinh (S / 2)

/-- The explicit aperture below which the constant is positive. -/
noncomputable def apertureThreshold : ℝ :=
  1 / (2 * Real.pi * Real.exp (Real.eulerMascheroniConstant + 3 / 4))

/-! ## The deficit integrand is pinned between `0` and `3/4` -/

theorem kernelDeficit_nonneg {u : ℝ} (hu : 0 < u) : 0 ≤ kernelDeficit u := by
  have hden := one_sub_exp_neg_two_mul_pos hu
  have hnum : Real.exp (-2 * u) ≤ Real.exp (-u / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  rw [kernelDeficit]
  apply div_nonneg _ hden.le
  linarith

theorem kernelDeficit_le {u : ℝ} (hu : 0 < u) : kernelDeficit u ≤ 3 / 4 := by
  have hden := one_sub_exp_neg_two_mul_pos hu
  have hy : (0 : ℝ) < Real.exp (-u / 2) := Real.exp_pos _
  have h4 := exp_neg_two_mul u
  rw [kernelDeficit, div_le_iff₀ hden]
  rw [h4]
  nlinarith [sq_nonneg (Real.exp (-u / 2) - 1), sq_nonneg (Real.exp (-u / 2) + 1),
    sq_nonneg (Real.exp (-u / 2)), hy]

theorem abs_kernelDeficit_le {u : ℝ} (hu : 0 < u) : |kernelDeficit u| ≤ 3 / 4 := by
  rw [abs_of_nonneg (kernelDeficit_nonneg hu)]
  exact kernelDeficit_le hu

/-! ## Bounds on the deficit correction -/

theorem deficitIntegral_nonneg {S : ℝ} (hS : 0 ≤ S) : 0 ≤ deficitIntegral S := by
  rw [deficitIntegral]
  have : 0 ≤ ∫ u in (0 : ℝ)..S, kernelDeficit u := by
    apply intervalIntegral.integral_nonneg hS
    intro u hu
    rcases lt_or_eq_of_le hu.1 with h | h
    · exact kernelDeficit_nonneg h
    · rw [← h, kernelDeficit]
      norm_num
  linarith

theorem deficitIntegral_le {S : ℝ} (hS : 0 ≤ S) : deficitIntegral S ≤ 3 / 2 * S := by
  have hbound : ‖∫ u in (0 : ℝ)..S, kernelDeficit u‖ ≤ 3 / 4 * |S - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro u hu
    rw [Set.uIoc_of_le hS] at hu
    exact abs_kernelDeficit_le hu.1
  rw [Real.norm_eq_abs] at hbound
  have habs : |S - 0| = S := by
    rw [sub_zero, abs_of_nonneg hS]
  rw [habs] at hbound
  have := le_of_abs_le hbound
  rw [deficitIntegral]
  linarith

/-! ## Positivity of the aperture constant -/

theorem one_sub_exp_le {S : ℝ} : 1 - Real.exp (-2 * S) ≤ 2 * S := by
  have := Real.add_one_le_exp (-2 * S)
  linarith

theorem apertureThreshold_pos : 0 < apertureThreshold := by
  rw [apertureThreshold]
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : (0 : ℝ) < Real.exp (Real.eulerMascheroniConstant + 3 / 4) := Real.exp_pos _
  positivity

theorem apertureThreshold_lt_half : apertureThreshold < 1 / 2 := by
  rw [apertureThreshold]
  have hπ : (3 : ℝ) < Real.pi := by
    have := Real.pi_gt_three
    linarith
  have he : (1 : ℝ) ≤ Real.exp (Real.eulerMascheroniConstant + 3 / 4) := by
    apply Real.one_le_exp
    have := Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hprod : (2 : ℝ) < 2 * Real.pi * Real.exp (Real.eulerMascheroniConstant + 3 / 4) := by
    nlinarith [Real.pi_pos]
  rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- **The aperture constant is positive below the explicit threshold.** -/
theorem apertureConstant_pos {S : ℝ} (hS : 0 < S) (hlt : S < apertureThreshold) :
    0 < apertureConstant S := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hE : (0 : ℝ) < Real.exp (Real.eulerMascheroniConstant + 3 / 4) := Real.exp_pos _
  have hden : 0 < 1 - Real.exp (-2 * S) := one_sub_exp_neg_two_mul_pos hS
  -- the logarithm of the denominator is bounded above by `log (2S)`
  have hlog : Real.log (1 - Real.exp (-2 * S)) ≤ Real.log (2 * S) :=
    Real.log_le_log hden one_sub_exp_le
  -- the threshold bound converts to a bound on `log (2S)`
  have hprod : (2 * S) * (Real.pi * Real.exp (Real.eulerMascheroniConstant + 3 / 4)) < 1 := by
    have h := hlt
    rw [apertureThreshold, lt_div_iff₀ (by positivity)] at h
    calc (2 * S) * (Real.pi * Real.exp (Real.eulerMascheroniConstant + 3 / 4))
        = S * (2 * Real.pi * Real.exp (Real.eulerMascheroniConstant + 3 / 4)) := by ring
      _ < 1 := h
  have h2S : 2 * S < 1 / (Real.pi * Real.exp (Real.eulerMascheroniConstant + 3 / 4)) := by
    rw [lt_div_iff₀ (by positivity)]
    exact hprod
  have h2Spos : (0 : ℝ) < 2 * S := by linarith
  have hlog2S : Real.log (2 * S) <
      -Real.log Real.pi - (Real.eulerMascheroniConstant + 3 / 4) := by
    have h := Real.log_lt_log h2Spos h2S
    rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (ne_of_gt hπ) (ne_of_gt hE), Real.log_exp] at h
    linarith
  -- the deficit correction is small
  have hJ : deficitIntegral S ≤ 3 / 2 * S := deficitIntegral_le hS.le
  have hShalf : S < 1 / 2 := lt_trans hlt apertureThreshold_lt_half
  have hJsmall : deficitIntegral S < 3 / 4 := by linarith
  -- the hyperbolic term is nonnegative
  have hsinh : 0 ≤ 8 * Real.sinh (S / 2) := by
    have : 0 ≤ Real.sinh (S / 2) := by
      rw [← Real.sinh_zero]
      exact Real.sinh_le_sinh.mpr (by linarith)
    linarith
  rw [apertureConstant]
  linarith

end RHTower.ArchimedeanKernel
