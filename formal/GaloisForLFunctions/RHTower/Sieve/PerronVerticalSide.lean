import GaloisForLFunctions.RHTower.Sieve.VerticalLogWeight

/-!
# The shifted vertical side of the Perron contour

On the line `Re s = σ` the Perron integrand is the logarithmic derivative times `x^σ/‖s‖`, so its
vertical integral is `x^σ` times the logarithmic weight integral — `O(x^σ log²T)`, with the
`x`-dependence entirely in the abscissa.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- The pointwise size of the Perron integrand on a vertical line. -/
theorem norm_perron_integrand_line {x σ t K : ℝ} (hx : 0 < x)
    (hK : ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ K * (1 + Real.log (2 + |t|))) :
    ‖(-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (K * x ^ σ) * ((1 + Real.log (2 + |t|))
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) := by
  have hlog : (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
      / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
      = -logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [logDeriv_apply, neg_div]
  rw [hlog, norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (((σ : ℂ) + (t : ℂ) * Complex.I)).re = σ := by simp
  rw [hre]
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hden : (0 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := norm_nonneg _
  have hid : (K * x ^ σ) * ((1 + Real.log (2 + |t|)) / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖)
      = (K * (1 + Real.log (2 + |t|))) * (x ^ σ / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) := by
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- **The shifted vertical side.** -/
theorem norm_vIntegral_perron_le {x σ T K : ℝ} (hx : 0 < x) (hσ0 : 0 < σ) (hT : 1 ≤ T)
    (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ K * (1 + Real.log (2 + |t|)))
    (hcont : Continuous fun t : ℝ =>
      (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I))) :
    ‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
        σ (-T) T‖
      ≤ (K * x ^ σ)
        * (2 * (1 + Real.log 3) / σ + 2 * (1 + Real.log (2 + T)) * Real.log T) := by
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hcoef : (0 : ℝ) ≤ K * x ^ σ := by positivity
  have hnorm : ‖VIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s)
      * ((x : ℂ) ^ s / s)) σ (-T) T‖
      = ‖∫ t in (-T)..T, (-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
        * ((x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ := by
    rw [VIntegral, norm_smul, Complex.norm_I, one_mul]
  rw [hnorm]
  refine (intervalIntegral.norm_integral_le_integral_norm hTle).trans ?_
  have hmono : (∫ t in (-T)..T, ‖(-deriv riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))
      * ((x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) / ((σ : ℂ) + (t : ℂ) * Complex.I))‖)
      ≤ ∫ t in (-T)..T, (K * x ^ σ)
          * ((1 + Real.log (2 + |t|)) / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖) := by
    refine intervalIntegral.integral_mono_on (μ := volume) hTle
      (hcont.norm.intervalIntegrable _ _)
      (((continuous_logWeight hσ0).const_mul (K * x ^ σ)).intervalIntegrable _ _)
      fun t _ => norm_perron_integrand_line hx (hK t)
  refine hmono.trans ?_
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_log_weight_le hσ0 hT) hcoef

end

end RHTower.Sieve
