import GaloisForLFunctions.RHTower.BarnesMellinShift

/-!
# The Mellin representation of the canonical-product sum

On the strip `-1 < σ < -1/s` the term-by-term Mellin inversion of the Cauchy kernel sums to

```text
∑_{n ≥ 1} x / (n^s + x) = (1/2πi) ∫_{(σ)} x^{-w} ζ(-sw) (-π/sin πw) dw ,
```

the left side being the Euler logarithmic derivative of the canonical product with zeros `-n^s`
and the right side the normalized vertical integral of `barnesIntegrand`.  Every contour shift
then reads off a term of the Barnes expansion.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- The inner sum of the inverted Mellin integral is the zeta factor. -/
theorem integrand_eq_barnesIntegrand {s x σ : ℝ} (hx : 0 < x)
    (h1 : -1 < σ) (h2 : σ < 0) (hsσ : s * σ < -1) (y : ℝ) :
    (∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ)) : ℂ) ^ (-((σ : ℂ) + (y : ℂ) * I))
        * mellin GaloisForLFunctions.HTGeometry.cauchyKernel ((σ : ℂ) + (y : ℂ) * I))
      = barnesIntegrand s x ((σ : ℂ) + (y : ℂ) * I) := by
  have hre : ((σ : ℂ) + (y : ℂ) * I).re = σ := by simp
  have hzre : (-(s : ℂ) * ((σ : ℂ) + (y : ℂ) * I)).re = -(s * σ) := by
    simp [Complex.mul_re, hre]
  have hz : 1 < (-(s : ℂ) * ((σ : ℂ) + (y : ℂ) * I)).re := by
    rw [hzre]; linarith
  rw [tsum_mul_right,
    GaloisForLFunctions.HTGeometry.tsum_scaled_eq_zeta hx hz,
    GaloisForLFunctions.HTGeometry.mellin_cauchyKernel_eq (by rw [hre]; exact h1)
      (by rw [hre]; exact h2)]
  rw [barnesIntegrand]

/-- **The Mellin representation.**  The Euler sum of the canonical product is the normalized
vertical integral of the Mellin integrand. -/
theorem hasSum_barnes_verticalIntegral' {s x σ : ℝ} (hx : 0 < x)
    (h1 : -1 < σ) (h2 : σ < 0) (hsσ : s * σ < -1) :
    HasSum (fun n : ℕ => ((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ)))
      (VerticalIntegral' (barnesIntegrand s x) σ) := by
  have hbase := GaloisForLFunctions.HTGeometry.hasSum_eulerLogDerivTerms_mellin
    (s := s) (σ := σ) h1 h2 hsσ hx
  have hcongr : (∫ y : ℝ, ∑' n : ℕ, ((((x / ((n : ℝ) + 1) ^ s) : ℝ)) : ℂ)
        ^ (-((σ : ℂ) + (y : ℂ) * I))
      * mellin GaloisForLFunctions.HTGeometry.cauchyKernel ((σ : ℂ) + (y : ℂ) * I))
      = ∫ y : ℝ, barnesIntegrand s x ((σ : ℂ) + (y : ℂ) * I) :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun y => integrand_eq_barnesIntegrand hx h1 h2 hsσ y)
  rw [hcongr] at hbase
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hscaled := hbase.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  have hterm : ∀ n : ℕ, ((2 * Real.pi)⁻¹ : ℝ) • ((2 * Real.pi : ℝ) •
      (((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ))))
      = ((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ)) := by
    intro n
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hpi), one_smul]
  have hval : ((2 * Real.pi)⁻¹ : ℝ) • (∫ y : ℝ, barnesIntegrand s x ((σ : ℂ) + (y : ℂ) * I))
      = VerticalIntegral' (barnesIntegrand s x) σ := by
    rw [VerticalIntegral', VerticalIntegral, smul_smul, Complex.real_smul]
    have hpine : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))
    congr 1
    push_cast
    field_simp
  rw [← hval]
  exact hscaled.congr_fun fun n => (hterm n).symm

end

end RHTower
