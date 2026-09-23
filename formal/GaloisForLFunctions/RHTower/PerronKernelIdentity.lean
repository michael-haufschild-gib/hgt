import GaloisForLFunctions.RHTower.PerronTentTransform

/-!
# The smoothed Perron kernel identity

Fourier inversion of the tent transform:

`∫ e^{2πiwu}·(a+2πiw)⁻² dw = u·e^{-au}·1_{u>0}`,

the `2πξ`-normalized form of `(1/2πi)∫_{(a)} y^s/s² ds = (log y)⁺` at
`u = log y`.  The transform side is integrable by comparison with
`(1+w²)⁻¹`, the tent is integrable and continuous, and mathlib's
inversion theorem closes the identity pointwise.
-/

noncomputable section

namespace RHTower

open MeasureTheory Set Filter
open scoped FourierTransform

/-- Integrability of the tent transform. -/
theorem integrable_fourier_perronTent {a : ℝ} (ha : 0 < a) :
    Integrable (FourierTransform.fourier (perronTent a)) := by
  have heq : FourierTransform.fourier (perronTent a)
      = fun w : ℝ => 1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ) :=
    funext (fourier_perronTent ha)
  rw [heq]
  have hπ0 : (0 : ℝ) < Real.pi := Real.pi_pos
  set C : ℝ := 1 / a ^ (2 : ℕ) + 1 / (4 * Real.pi ^ (2 : ℕ)) with hC
  have hC0 : 0 < C := by positivity
  have hg : Integrable (fun w : ℝ => C * (1 + w ^ (2 : ℕ))⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  have hcne : ∀ w : ℝ, ((a : ℂ) + 2 * Real.pi * w * Complex.I) ≠ 0 := by
    intro w h
    have h2 := congrArg Complex.re h
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im] at h2
    linarith
  apply Integrable.mono hg
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div continuous_const
    · fun_prop
    · intro w
      exact pow_ne_zero 2 (hcne w)
  · filter_upwards with w
    have hnorm : ‖(1 : ℂ) / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ)‖
        = 1 / (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ)) := by
      rw [norm_div, norm_one, norm_pow]
      rw [show (a : ℂ) + 2 * Real.pi * w * Complex.I
          = ((a : ℝ) : ℂ) + ((2 * Real.pi * w : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      rw [Complex.norm_add_mul_I]
      rw [Real.sq_sqrt (by positivity)]
    rw [hnorm]
    have hgn : ‖C * (1 + w ^ (2 : ℕ))⁻¹‖ = C * (1 + w ^ (2 : ℕ))⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [hgn]
    rw [inv_eq_one_div, mul_one_div,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : C * a ^ (2 : ℕ) = 1 + a ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ)) := by
      rw [hC]
      field_simp
    have h2 : C * (2 * Real.pi * w) ^ (2 : ℕ)
        = (2 * Real.pi * w) ^ (2 : ℕ) / a ^ (2 : ℕ) + w ^ (2 : ℕ) := by
      rw [hC]
      field_simp
      ring
    have hdist : C * (a ^ (2 : ℕ) + (2 * Real.pi * w) ^ (2 : ℕ))
        = C * a ^ (2 : ℕ) + C * (2 * Real.pi * w) ^ (2 : ℕ) := by ring
    have h3 : (0 : ℝ) ≤ a ^ (2 : ℕ) / (4 * Real.pi ^ (2 : ℕ)) := by positivity
    have h4 : (0 : ℝ) ≤ (2 * Real.pi * w) ^ (2 : ℕ) / a ^ (2 : ℕ) := by positivity
    nlinarith [h1, h2, hdist, h3, h4]

/-- **The Perron kernel identity**: Fourier inversion evaluates
`∫ e^{2πiwu}·(a+2πiw)⁻² dw` to the tent `u·e^{-au}·1_{u>0}`. -/
theorem perron_kernel_identity {a : ℝ} (ha : 0 < a) (u : ℝ) :
    ∫ w : ℝ, Complex.exp (((2 * Real.pi * (w * u) : ℝ) : ℂ) * Complex.I)
      • (1 / ((a : ℂ) + 2 * Real.pi * w * Complex.I) ^ (2 : ℕ))
      = perronTent a u := by
  have hinv := (integrable_perronTent ha).fourierInv_fourier_eq
    (v := u) (integrable_fourier_perronTent ha)
    ((continuous_perronTent a).continuousAt)
  rw [Real.fourierInv_eq'] at hinv
  rw [← hinv]
  apply integral_congr_ae
  filter_upwards with w
  rw [fourier_perronTent ha w]
  congr 2
  simp [RCLike.inner_apply]
  ring

end RHTower
