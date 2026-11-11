import GaloisForLFunctions.MultiscaleMollifiedZetaField.BoxCameraLorentzEnvelope
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDepthCenteredCameraPaysItsExteriorMass

/-!
# Box cameras pay exterior mass geometrically

Centering at the actual zero width places every transformed zero in the
upper half-plane. A fixed ordinate gap then gives one factor `1/(h g)`
per additional box, with the complete multiplicity-weighted exterior paid
by the known unit-scale Lorentzian mass.
-/

noncomputable section

open Complex MeasureTheory Set
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

/-- Actual zero width supplies the damping sign; no zero-free premise is needed. -/
theorem norm_paperFT_widthCenteredBoxCamera_le_of_gap
    {A h r y t g : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (hg : 0 < g)
    (n : ℕ) (hy : boxCameraRadius A h n r ≤ y) (ρ : zetaZeroConfig.carrier)
    (hgap : g ≤ |(ρ : ℂ).im - t|) :
    ‖paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)‖ ≤
      ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n) *
        (1 / (1 + ((ρ : ℂ).im - t) ^ 2)) := by
  have hzr : (gammaOf ρ - (t : ℂ) + I * (zetaZeroWidth : ℂ)).re = (ρ : ℂ).im - t := by
    simp [ZeroConfigurationGeometry.gammaOf_eq]
  have hzi : (gammaOf ρ - (t : ℂ) + I * (zetaZeroWidth : ℂ)).im =
      zetaZeroWidth - ((ρ : ℂ).re - 1 / 2) := by
    simp [ZeroConfigurationGeometry.gammaOf_eq, ZeroConfigurationGeometry.depth] <;> ring
  have hw : (ρ : ℂ).re - 1 / 2 ≤ zetaZeroWidth :=
    (le_abs_self _).trans (SquareRootThreshold.abs_re_sub_half_le_zetaZeroWidth ρ.2)
  rw [paperFT_boxCenteredCamera]
  have hb := norm_damped_boxPlateau_le_of_gap hA hh hr hg n hy
    (z := gammaOf ρ - (t : ℂ) + I * (zetaZeroWidth : ℂ))
    (by rw [hzi]; exact sub_nonneg.mpr hw) (by rw [hzr]; exact hgap)
  simpa only [hzr] using hb

/-- Full exterior multiplicity is charged to the existing Lorentzian mass.
When `h g>1`, the coefficient decreases geometrically with convolution order. -/
theorem sum_widthCenteredBoxCamera_exterior_le
    {A h r y t g : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (hg : 0 < g)
    (n : ℕ) (hy : boxCameraRadius A h n r ≤ y)
    (F : Finset zetaZeroConfig.carrier) (hgap : ∀ ρ ∈ F, g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)‖) ≤
      ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n) * lorentzMass t := by
  have hmass := sum_mult_unit_le_lorentzMass t (F.image Subtype.val)
    (fun ρ hρ => by obtain ⟨ρ', _, rfl⟩ := Finset.mem_image.mp hρ; exact ρ'.2)
  rw [Finset.sum_image Subtype.val_injective.injOn] at hmass
  have hterm (ρ : zetaZeroConfig.carrier) (hρ : ρ ∈ F) :
      (zetaZeroConfig.mult ρ : ℝ) *
        ‖paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)‖ ≤
      ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n) *
        ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) := by
    have hb := norm_paperFT_widthCenteredBoxCamera_le_of_gap hA hh hr hg n hy ρ (hgap ρ hρ)
    rw [show ((ρ : ℂ).im - t) ^ 2 = (t - (ρ : ℂ).im) ^ 2 by ring] at hb
    have hm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (zetaZeroConfig.mult ρ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  calc
    _ ≤ ∑ ρ ∈ F, ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n) *
        ((zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) :=
      Finset.sum_le_sum hterm
    _ = ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n) *
        ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-- Shallow zeros are damped even at the cluster ordinate. -/
theorem norm_paperFT_widthCenteredBoxCamera_le_of_shallow
    {A h r y t d : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (hy : boxCameraRadius A h n r ≤ y) (hd : 0 ≤ d)
    (ρ : zetaZeroConfig.carrier) (hdepth : (ρ : ℂ).re - 1 / 2 ≤ zetaZeroWidth - d) :
    ‖paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)‖ ≤
      (4 * A + 4 / h) * Real.exp (-(d * (y - boxCameraRadius A h n r))) *
        (1 / (1 + ((ρ : ℂ).im - t) ^ 2)) := by
  have hzr : (gammaOf ρ - (t : ℂ) + I * (zetaZeroWidth : ℂ)).re = (ρ : ℂ).im - t := by
    simp [ZeroConfigurationGeometry.gammaOf_eq]
  have hzi : (gammaOf ρ - (t : ℂ) + I * (zetaZeroWidth : ℂ)).im =
      zetaZeroWidth - ((ρ : ℂ).re - 1 / 2) := by
    simp [ZeroConfigurationGeometry.gammaOf_eq, ZeroConfigurationGeometry.depth] <;> ring
  rw [paperFT_boxCenteredCamera]
  have hb := norm_damped_boxPlateau_le_lorentz hA hh hr n hy hd
    (z := gammaOf ρ - (t : ℂ) + I * (zetaZeroWidth : ℂ))
    (by rw [hzi]; linarith only [hdepth])
  simpa only [hzr] using hb

/-- The complete box-camera zero field is absolutely summable. -/
theorem summable_widthCenteredBoxCamera
    {A h r y t : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (hy : boxCameraRadius A h n r ≤ y) :
    Summable (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.mult ρ : ℂ) *
      paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)) := by
  apply Summable.of_norm
  refine ((summable_mult_lorentzKernel (δ := 1) le_rfl t).mul_left
    (4 * A + 4 / h)).of_nonneg_of_le (fun _ => norm_nonneg _) fun ρ => ?_
  have hw : (ρ : ℂ).re - 1 / 2 ≤ zetaZeroWidth - 0 := by
    simpa only [sub_zero] using (le_abs_self _).trans
      (SquareRootThreshold.abs_re_sub_half_le_zetaZeroWidth ρ.2)
  have hb := norm_paperFT_widthCenteredBoxCamera_le_of_shallow hA hh hr n hy le_rfl ρ hw
    (t := t)
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at hb
  rw [norm_mul, Complex.norm_natCast]
  simpa only [lorentzKernel, one_pow, one_mul, mul_assoc, mul_left_comm, mul_comm] using
    mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (zetaZeroConfig.mult ρ))

/-- Only deep exterior zeros need a gap; all shallow multiplicities are
paid by the positive-lag damping. The constants do not grow with order. -/
theorem sum_widthCenteredBoxCamera_exterior_le_deep_gap
    {A h r y t g d : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (hg : 0 < g)
    (n : ℕ) (hy : boxCameraRadius A h n r ≤ y) (hd : 0 ≤ d)
    (F : Finset zetaZeroConfig.carrier)
    (hgap : ∀ ρ ∈ F, zetaZeroWidth - d ≤ (ρ : ℂ).re - 1 / 2 →
      g ≤ |(ρ : ℂ).im - t|) :
    (∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
      ‖paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)‖) ≤
      ((2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n +
        (4 * A + 4 / h) * Real.exp (-(d * (y - boxCameraRadius A h n r)))) *
        lorentzMass t := by
  let C := (2 / h) * ((1 + g ^ 2) / g ^ 2) * (1 / (h * g)) ^ n +
    (4 * A + 4 / h) * Real.exp (-(d * (y - boxCameraRadius A h n r)))
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hmass := sum_mult_unit_le_lorentzMass t (F.image Subtype.val)
    (fun ρ hρ => by obtain ⟨ρ', _, rfl⟩ := Finset.mem_image.mp hρ; exact ρ'.2)
  rw [Finset.sum_image Subtype.val_injective.injOn] at hmass
  have hterm (ρ : zetaZeroConfig.carrier) (hρ : ρ ∈ F) :
      ‖paperFT (boxCenteredCamera A h n r zetaZeroWidth y) (gammaOf ρ - t)‖ ≤
        C * (1 / (1 + ((ρ : ℂ).im - t) ^ 2)) := by
    by_cases hp : zetaZeroWidth - d ≤ (ρ : ℂ).re - 1 / 2
    · refine (norm_paperFT_widthCenteredBoxCamera_le_of_gap hA hh hr hg n hy ρ
        (hgap ρ hρ hp)).trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_add_of_nonneg_right (by positivity)
    · refine (norm_paperFT_widthCenteredBoxCamera_le_of_shallow hA hh hr n hy hd ρ
        (not_le.mp hp).le).trans ?_
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ ∑ ρ ∈ F, C * ((zetaZeroConfig.mult ρ : ℝ) *
        (1 / (1 + (t - (ρ : ℂ).im) ^ 2))) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hb := mul_le_mul_of_nonneg_left (hterm ρ hρ) (Nat.cast_nonneg (zetaZeroConfig.mult ρ))
      rw [show ((ρ : ℂ).im - t) ^ 2 = (t - (ρ : ℂ).im) ^ 2 by ring] at hb
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hb
    _ = C * ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) *
        (1 / (1 + (t - (ρ : ℂ).im) ^ 2)) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass hC

end GaloisForLFunctions.MultiscaleMollifiedZetaField
