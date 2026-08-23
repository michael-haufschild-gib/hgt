import GaloisForLFunctions.RHTower.Sieve.PerronVerticalSide

/-!
# The horizontal sides of the Perron contour

At height `T` the Perron integrand is at most `C log T/(σ−1/2) · x^σ/T`, so each horizontal side of
the rectangle costs the width of the strip times that — a factor `1/T` smaller than the vertical
sides, which is why the truncation height may be taken as large as one likes.
-/

namespace RHTower.Sieve

open Complex MeasureTheory

noncomputable section

/-- **The horizontal side of the Perron contour.** -/
theorem norm_hIntegral_perron_le {x σ₁ σ₀ y C : ℝ} (hx : 1 ≤ x)
    (hσ₁ : 1 / 2 < σ₁) (hσ₁σ₀ : σ₁ ≤ σ₀) (hσ₀ : σ₀ ≤ 9 / 8) (hy : 7 ≤ |y|) (hC0 : 0 < C)
    (hC : ∀ σ γ : ℝ, 7 ≤ |γ| → 1 / 2 < σ → σ ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((σ : ℂ) + (γ : ℂ) * Complex.I)‖
        ≤ C * Real.log |γ| / (σ - 1 / 2)) :
    ‖HIntegral (fun s : ℂ => (-deriv riemannZeta s / riemannZeta s) * ((x : ℂ) ^ s / s))
        σ₁ σ₀ y‖
      ≤ (C * Real.log |y| / (σ₁ - 1 / 2)) * (x ^ σ₀ / |y|) * |σ₀ - σ₁| := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < |y| := by linarith
  have hlogy : (0 : ℝ) ≤ Real.log |y| := Real.log_nonneg (by linarith)
  have hσ₁0 : (0 : ℝ) < σ₁ - 1 / 2 := by linarith
  have hbound : ∀ σ ∈ Set.uIoc σ₁ σ₀,
      ‖(-deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
            / riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I))
          * ((x : ℂ) ^ ((σ : ℂ) + (y : ℂ) * Complex.I) / ((σ : ℂ) + (y : ℂ) * Complex.I))‖
        ≤ (C * Real.log |y| / (σ₁ - 1 / 2)) * (x ^ σ₀ / |y|) := by
    intro σ hσ
    rw [Set.uIoc_of_le hσ₁σ₀, Set.mem_Ioc] at hσ
    have hσlow : 1 / 2 < σ := by linarith [hσ.1]
    have hσhigh : σ ≤ 9 / 8 := by linarith [hσ.2]
    have hlogd := hC σ y hy hσlow hσhigh
    have hlog : (-deriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
        / riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I))
        = -logDeriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I) := by
      rw [logDeriv_apply, neg_div]
    rw [hlog, norm_mul, norm_neg, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (((σ : ℂ) + (y : ℂ) * Complex.I)).re = σ := by simp
    rw [hre]
    have hden : |y| ≤ ‖(σ : ℂ) + (y : ℂ) * Complex.I‖ :=
      abs_le_norm_sigma_add_mul_I (σ := σ) (t := y)
    have hden0 : (0 : ℝ) < ‖(σ : ℂ) + (y : ℂ) * Complex.I‖ := by linarith
    have hxσ : x ^ σ ≤ x ^ σ₀ := Real.rpow_le_rpow_of_exponent_le hx hσ.2
    have hxσ0 : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx0.le σ
    have hquot : x ^ σ / ‖(σ : ℂ) + (y : ℂ) * Complex.I‖ ≤ x ^ σ₀ / |y| := by
      rw [div_le_div_iff₀ hden0 hy0]
      nlinarith [hxσ, hden, hxσ0, Real.rpow_nonneg hx0.le σ₀]
    have hlogd' : ‖logDeriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)‖
        ≤ C * Real.log |y| / (σ₁ - 1 / 2) := by
      refine hlogd.trans ?_
      gcongr
      linarith [hσ.1]
    have hLnn : (0 : ℝ) ≤ ‖logDeriv riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)‖ :=
      norm_nonneg _
    have hQnn : (0 : ℝ) ≤ x ^ σ / ‖(σ : ℂ) + (y : ℂ) * Complex.I‖ := by positivity
    have hRnn : (0 : ℝ) ≤ C * Real.log |y| / (σ₁ - 1 / 2) := by positivity
    exact mul_le_mul hlogd' hquot hQnn hRnn
  rw [HIntegral]
  exact intervalIntegral.norm_integral_le_of_norm_le_const hbound

end

end RHTower.Sieve
