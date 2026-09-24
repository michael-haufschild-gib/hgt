import GaloisForLFunctions.RHTower.EstermannContourShift
import GaloisForLFunctions.RHTower.EstermannExponentialMellin

/-!
# The exponentially smoothed twisted divisor sum

Combining the Perron inversion at `Re s = 2` with the contour shift to `Re s = ½`:

```text
∑_{N ≥ 1} d(N) e(aN/q) e^{-Nx} = (γ - log x - 2 log q)/(q x) + E(x),
```

with `E(x)` the vertical integral on the half line, of size `O(x^{-1/2})` with a constant
depending only on `q` and `a`.  With `x = 1/X` the main term is `(X/q)(log(X/q²) + γ)`.
-/

open Complex Filter MeasureTheory

namespace RHTower

noncomputable section

/-- The inverse Mellin transform on a line, in the integrand's own notation. -/
theorem mellinInv_eq_verticalIntegral (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (x σ : ℝ) :
    mellinInv σ (fun s => Complex.Gamma s * estermannZeta q ((a : ZMod q)) s) x
      = (1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ,
          estermannMellinIntegrand q ((a : ZMod q)) x ((σ : ℂ) + (v : ℂ) * I) := by
  rw [mellinInv]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun v => ?_))
  simp only [estermannMellinIntegrand, smul_eq_mul, mul_assoc]

/-- **The smoothed twisted divisor sum.** -/
theorem estermann_smoothed_sum (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) {x : ℝ} (hx : 0 < x) :
    (∑' N : ℕ, estermannCoeff q ((a : ZMod q)) N * Complex.exp (-(((N : ℝ) * x : ℝ) : ℂ)))
      = ((q : ℂ) * (x : ℂ))⁻¹ *
          ((Real.eulerMascheroniConstant : ℂ) - (Real.log x : ℂ) - 2 * Complex.log (q : ℂ))
        + (1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ,
            estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I) := by
  have hperron := estermann_exponential_mellin q ((a : ZMod q)) (by norm_num : (1 : ℝ) < 2) hx
  have hshift := estermannMellin_vertical_difference q a hx
  have hres := deriv_estermannMellinNumerator_one q a hx
  rw [mellinInv_eq_verticalIntegral q a x 2] at hperron
  rw [← hperron, ← hres, Complex.real_smul, Complex.real_smul]
  have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * (Real.pi : ℂ)) = 1 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact Real.pi_ne_zero
    push_cast
    field_simp
  linear_combination ((1 / (2 * Real.pi) : ℝ) : ℂ) * hshift
    + deriv (estermannMellinNumerator q ((a : ZMod q)) x) 1 * hc

/-- **The error term is `O(x^{-1/2})`.** -/
theorem exists_bound_norm_estermann_smoothed_error (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(1 / (2 * Real.pi) : ℝ) • ∫ v : ℝ,
          estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ C * x ^ (-(1 / 2 : ℝ)) := by
  have hbase : Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) 1 (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    integrable_estermannMellinIntegrand_vertical q a one_pos (by norm_num) (by norm_num)
      (by norm_num)
  set C₀ : ℝ := ∫ v : ℝ,
    ‖estermannMellinIntegrand q ((a : ZMod q)) 1 (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ with hC₀
  have hC₀0 : 0 ≤ C₀ := integral_nonneg (fun v => norm_nonneg _)
  refine ⟨(1 / (2 * Real.pi)) * C₀, by positivity, fun x hx => ?_⟩
  have hxpow : (0 : ℝ) < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hscale : ∀ v : ℝ,
      ‖estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
        = x ^ (-(1 / 2 : ℝ)) *
          ‖estermannMellinIntegrand q ((a : ZMod q)) 1 (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ := by
    intro v
    have hre : (-(((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)).re = -(1 / 2 : ℝ) := by simp
    simp only [estermannMellinIntegrand, norm_mul, Complex.ofReal_one, Complex.one_cpow,
      one_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    ring
  have hint : Integrable (fun v : ℝ =>
      estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) :=
    integrable_estermannMellinIntegrand_vertical q a hx (by norm_num) (by norm_num) (by norm_num)
  have hnorm : ‖∫ v : ℝ,
      estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
        ≤ x ^ (-(1 / 2 : ℝ)) * C₀ := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [hC₀, ← integral_const_mul]
    exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall hscale))
  rw [Complex.real_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc (1 / (2 * Real.pi)) * ‖∫ v : ℝ,
        estermannMellinIntegrand q ((a : ZMod q)) x (((1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖
      ≤ (1 / (2 * Real.pi)) * (x ^ (-(1 / 2 : ℝ)) * C₀) := by
        exact mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 1 / (2 * Real.pi) * C₀ * x ^ (-(1 / 2 : ℝ)) := by ring

end

end RHTower
