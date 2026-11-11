import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthCenteredCameraPrimeCost
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthCenteredCameraSeesNearTopClusters

/-!
# The centered camera remainder

Depth centering also damps the gamma integral and the pole terms in the
explicit formula. The gain is measured using the original profile, so
the constants remain uniform in the centering depth and camera width.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

theorem contDiff_depthCenteredProfile {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v)
    (b δ : ℝ) : ContDiff ℝ 2 (depthCenteredProfile v b δ) :=
  (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id).neg).mul hv

theorem depthCenteredProfile_support {v : ℝ → ℝ}
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (b δ : ℝ) :
    ∀ u, depthCenteredProfile v b δ u ≠ 0 → |u| ≤ 1 := by
  intro u hu
  apply hsupp u
  intro hz
  exact hu (by simp only [depthCenteredProfile, hz, mul_zero])

/-- The real-axis transform keeps the full centering gain. -/
theorem norm_paperFT_depthCenteredCamera_real_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {b δ y : ℝ} (hb : 0 ≤ b) (hδ : 0 < δ) (hy : δ ≤ y) (r : ℝ) :
    ‖paperFT (depthCenteredCamera v b δ y) r‖ ≤
      profileMass v * Real.exp (-(b * (y - δ))) * (1 + (δ * r) ^ 2)⁻¹ := by
  have harg : gammaOf (1 / 2 : ℂ) - ((-r : ℝ) : ℂ) = r := by
    simp only [gammaOf, sub_self, zero_div, zero_sub, Complex.ofReal_neg, neg_neg]
  have h := norm_paperFT_depthCenteredCamera_le_of_shallow hv hsupp hδ hy hb
    (b := b) (d := b) (ρ := (1 / 2 : ℂ)) (t := -r) (by simp)
  rw [harg] at h
  simpa [lorentzKernel, mul_pow] using h

private theorem paperFT_centered_eq_profile (v : ℝ → ℝ) (b δ y : ℝ)
    (hδ : 0 < δ) (z : ℂ) :
    paperFT (depthCenteredCamera v b δ y) z = (Real.exp (-(b * y)) : ℂ) *
      paperFT (cameraTest (depthCenteredProfile v b δ) δ y) z := by
  rw [depthCenteredCamera_eq_profile v b δ y hδ]
  simp only [paperFT_def, mul_assoc, integral_const_mul]

/-- The centered explicit formula has exactly the same two poles and gamma
integral, evaluated against the centered test. -/
theorem widthCenteredZeroField_add_poly_eq
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {δ y : ℝ} (hδ : 0 < δ) (hy : δ < y) (t : ℝ) :
    widthCenteredZeroField v δ y t + depthCenteredCameraPoly v zetaZeroWidth δ y t =
      paperFT (depthCenteredCamera v zetaZeroWidth δ y) (I / 2 - t) +
      paperFT (depthCenteredCamera v zetaZeroWidth δ y) (-I / 2 - t) +
      ∫ r : ℝ, paperFT (depthCenteredCamera v zetaZeroWidth δ y) r * (mu (r + t) : ℂ) := by
  have he := zeroField_add_cameraPoly_eq (contDiff_depthCenteredProfile hv zetaZeroWidth δ)
    (depthCenteredProfile_support hsupp zetaZeroWidth δ) hδ hy t
  have hZ : widthCenteredZeroField v δ y t = (Real.exp (-(zetaZeroWidth * y)) : ℂ) *
      zeroField (depthCenteredProfile v zetaZeroWidth δ) δ y t := by
    unfold widthCenteredZeroField zeroField
    simp_rw [paperFT_centered_eq_profile v zetaZeroWidth δ y hδ]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro ρ
    ring
  rw [hZ, depthCenteredCameraPoly_eq_profile v zetaZeroWidth δ y t hδ, ← mul_add, he]
  simp only [paperFT_centered_eq_profile v zetaZeroWidth δ y hδ,
    mul_add, mul_assoc, integral_const_mul]

/-- A Lorentzian envelope controls the gamma integral uniformly over all
functions satisfying it. -/
theorem exists_norm_gamma_lorentz_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ t M : ℝ) (f : ℝ → ℂ), 1 ≤ δ → 0 ≤ M →
      (∀ r : ℝ, ‖f r‖ ≤ M * (1 + (δ * r) ^ 2)⁻¹) →
      ‖∫ r : ℝ, f r * (mu (r + t) : ℂ)‖ ≤
        C * M * (1 + Real.log (2 + |t|) / δ) := by
  obtain ⟨A, hA⟩ := exists_abs_mu_le
  have hJi : Integrable (fun r : ℝ => (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) :=
    integrable_one_add_norm (by norm_num)
  set J := ∫ r : ℝ, (1 + ‖r‖) ^ (-(7 / 4 : ℝ)) with hJdef
  have hJ : 0 ≤ J := integral_nonneg fun r => by positivity
  refine ⟨π * (|A| + 1) + 8 * J, by positivity, fun δ t M f hδ hM hf => ?_⟩
  have hX : 0 ≤ M * π := by positivity
  have hY : 0 ≤ 8 * M * J := by positivity
  have hδ0 : 0 < δ := by linarith
  set P := Real.log (2 + |t|) with hPdef
  have hP : 0 ≤ P := Real.log_nonneg (by linarith [abs_nonneg t])
  have hLi : Integrable (fun r : ℝ => (1 + (δ * r) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_mul_left' hδ0.ne'
  have hLint : ∫ r : ℝ, (1 + (δ * r) ^ 2)⁻¹ = π / δ := by
    rw [Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) δ,
      integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.2 hδ0), smul_eq_mul]
    field_simp
  have hbound : ∀ r : ℝ, ‖f r * (mu (r + t) : ℂ)‖ ≤
      M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ + 8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ)) := by
    intro r
    have hK := hf r
    have hmu : |mu (r + t)| ≤ |A| + P + Real.log (1 + |r|) := by
      have h1 := hA (r + t)
      have h2 := log_two_add_abs_add_le r t
      linarith [le_abs_self A]
    have hℓ0 : 0 ≤ Real.log (1 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
    have htail := inv_mul_log_le r hδ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖f r‖ * |mu (r + t)|
        ≤ (M * (1 + (δ * r) ^ 2)⁻¹) * (|A| + P + Real.log (1 + |r|)) :=
          mul_le_mul hK hmu (abs_nonneg _) (by positivity)
      _ = M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ +
            M * ((1 + (δ * r) ^ 2)⁻¹ * Real.log (1 + |r|)) := by ring
      _ ≤ M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ + M * (8 * (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) := by
          gcongr
      _ = _ := by ring
  have hLi' : Integrable (fun r : ℝ => M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹) := hLi.const_mul _
  have hJi' : Integrable (fun r : ℝ => 8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) := hJi.const_mul _
  have hgi : Integrable (fun r : ℝ => M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ +
      8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ))) := hLi'.add hJi'
  have h := norm_integral_le_of_norm_le hgi (Eventually.of_forall hbound)
  refine h.trans ?_
  have hsum : (∫ r : ℝ, (M * (|A| + P) * (1 + (δ * r) ^ 2)⁻¹ +
      8 * M * (1 + ‖r‖) ^ (-(7 / 4 : ℝ)))) = M * (|A| + P) * (π / δ) + 8 * M * J := by
    rw [integral_add hLi' hJi', integral_const_mul, integral_const_mul, hLint]
  rw [hsum]
  have hq0 : 0 ≤ δ⁻¹ := (inv_pos.2 hδ0).le
  have hq1 : δ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hδ
  have ha1 := abs_nonneg A
  rw [div_eq_mul_inv, div_eq_mul_inv]
  nlinarith [mul_nonneg (mul_nonneg hX ha1) (sub_nonneg.2 hq1),
    mul_nonneg (mul_nonneg hX ha1) (mul_nonneg hP hq0), mul_nonneg hY (mul_nonneg hP hq0)]

/-- The centered gamma remainder has the same exponential gain as the
prime polynomial, with a constant depending only on the original profile. -/
theorem exists_norm_gamma_depthCenteredCamera_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b δ y t : ℝ, 0 ≤ b → 1 ≤ δ → δ ≤ y →
      ‖∫ r : ℝ, paperFT (depthCenteredCamera v b δ y) r * (mu (r + t) : ℂ)‖ ≤
        C * Real.exp (-(b * (y - δ))) * (1 + Real.log (2 + |t|) / δ) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_gamma_lorentz_le
  refine ⟨C * profileMass v, mul_nonneg hC0 (profileMass_nonneg v),
    fun b δ y t hb hδ hy => ?_⟩
  have h := hC δ t (profileMass v * Real.exp (-(b * (y - δ))))
    (fun r => paperFT (depthCenteredCamera v b δ y) r) hδ
    (mul_nonneg (profileMass_nonneg v) (Real.exp_pos _).le)
    (norm_paperFT_depthCenteredCamera_real_le hv hsupp hb (one_pos.trans_le hδ) hy)
  simpa only [mul_assoc] using h

/-- The two pole terms retain the centering gain when the camera support
ends below `log t`. The estimate holds throughout the real unit interval. -/
theorem norm_paperFT_depthCenteredCamera_pole_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {b δ y t q : ℝ} (hb : 0 ≤ b) (hδ : 1 ≤ δ) (hy : δ ≤ y)
    (ht : 1 ≤ t) (hN : Real.exp (y + δ) ≤ t) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ‖paperFT (depthCenteredCamera v b δ y) (gammaOf (q : ℂ) - t)‖ ≤
      profileMass v * Real.exp (-(b * (y - δ))) := by
  rw [paperFT_depthCenteredCamera]
  have hδ0 : 0 < δ := one_pos.trans_le hδ
  have hy0 : 0 ≤ y := hδ0.le.trans hy
  have hp : |q - b - 1 / 2| ≤ b + 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith only [hq0, hq1, hb]
  have he : (q - b - 1 / 2) * y + |q - b - 1 / 2| * δ ≤
      -(b * (y - δ)) + (y + δ) := by
    have h1 := mul_le_mul_of_nonneg_right hp hδ0.le
    have h2 := mul_le_mul_of_nonneg_right hq1 hy0
    nlinarith only [h1, h2, hy0, hδ0.le]
  have hden : t ≤ 1 + δ ^ 2 * t ^ 2 := by
    have hd2 : 1 ≤ δ ^ 2 := by nlinarith only [hδ]
    have hm := mul_le_mul_of_nonneg_right hd2 (sq_nonneg t)
    nlinarith only [hm, ht]
  have hk : companionWeight δ y t ((q : ℂ) - (b : ℂ)) ≤
      Real.exp (-(b * (y - δ))) := by
    simp only [companionWeight, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_self, zero_sub, sq_neg]
    rw [div_le_iff₀ (by positivity)]
    calc
      _ ≤ Real.exp (-(b * (y - δ)) + (y + δ)) := Real.exp_le_exp.mpr he
      _ = Real.exp (-(b * (y - δ))) * Real.exp (y + δ) := Real.exp_add _ _
      _ ≤ Real.exp (-(b * (y - δ))) * t :=
        mul_le_mul_of_nonneg_left hN (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le
  exact (norm_paperFT_companion_le hv hsupp hδ0 y t ((q : ℂ) - (b : ℂ))).trans
    (mul_le_mul_of_nonneg_left hk (profileMass_nonneg v))

/-- The complete centered explicit-formula remainder decays with the same
factor as the centered prime coefficients. -/
theorem exists_norm_widthCenteredZeroField_add_poly_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ y t : ℝ, 1 ≤ δ → δ < y → 1 ≤ t →
      Real.exp (y + δ) ≤ t →
      ‖widthCenteredZeroField v δ y t + depthCenteredCameraPoly v zetaZeroWidth δ y t‖ ≤
        C * Real.exp (-(zetaZeroWidth * (y - δ))) * (1 + Real.log (2 + t) / δ) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_norm_gamma_depthCenteredCamera_le hv hsupp
  have hM := profileMass_nonneg v
  refine ⟨CG + 2 * profileMass v, by positivity, fun δ y t hδ hy ht hN => ?_⟩
  have hb := SquareRootThreshold.zetaZeroWidth_nonneg
  have h0 := norm_paperFT_depthCenteredCamera_pole_le hv hsupp hb hδ hy.le ht hN
    (q := 0) (by norm_num) (by norm_num)
  have h1 := norm_paperFT_depthCenteredCamera_pole_le hv hsupp hb hδ hy.le ht hN
    (q := 1) (by norm_num) (by norm_num)
  have he0 : gammaOf (0 : ℂ) = I / 2 := by
    simp only [gammaOf, Complex.div_I]
    ring
  have he1 : gammaOf (1 : ℂ) = -I / 2 := by
    simp only [gammaOf, Complex.div_I]
    ring
  rw [he0] at h0
  rw [he1] at h1
  have hG := hCG zetaZeroWidth δ y t hb hδ hy.le
  rw [abs_of_nonneg (one_pos.le.trans ht)] at hG
  rw [widthCenteredZeroField_add_poly_eq hv hsupp (one_pos.trans_le hδ) hy t]
  have htri := (norm_add_le
    (paperFT (depthCenteredCamera v zetaZeroWidth δ y) (I / 2 - t) +
      paperFT (depthCenteredCamera v zetaZeroWidth δ y) (-I / 2 - t))
    (∫ r : ℝ, paperFT (depthCenteredCamera v zetaZeroWidth δ y) r * (mu (r + t) : ℂ))).trans
      (add_le_add_right (norm_add_le _ _) _)
  have hP : 0 ≤ Real.log (2 + t) / δ :=
    div_nonneg (Real.log_nonneg (by linarith only [ht])) (one_pos.le.trans hδ)
  have hgain : 0 ≤ profileMass v * Real.exp (-(zetaZeroWidth * (y - δ))) :=
    mul_nonneg hM (Real.exp_pos _).le
  nlinarith only [htri, h0, h1, hG, mul_nonneg hgain hP]

end GaloisForLFunctions.MultiscaleMollifiedZetaField
