import GaloisForLFunctions.MultiscaleMollifiedZetaField.BoxCameraProfileMass
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheWidthCenteredCameraSeesNearTopClusters

/-!
# Box cameras as normalized Turán profiles

Rescaling a box camera to unit support preserves its mass. This identifies
the actual box camera with the existing depth-centered camera, so the
finite-cluster Turán theorem applies without another power-sum argument.
-/

noncomputable section

open Complex MeasureTheory Set
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

open SquareRootThreshold (zetaZeroWidth)

def boxTuranProfile (A h : ℝ) (n : ℕ) (r : ℝ) : ℝ → ℝ :=
  fun u => boxCameraRadius A h n r *
    (boxPlateau A h (n + 1) r (boxCameraRadius A h n r * u)).re

/-- Averaging against positive unit-mass kernels preserves the unit bound. -/
theorem norm_boxPlateau_le_one {A h r : ℝ} (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (u : ℝ) : ‖boxPlateau A h n r u‖ ≤ 1 := by
  rw [boxPlateau_apply]
  have hi : Integrable (fun t => smoothUnitBump r (u - t)) :=
    (integrable_smoothUnitBump hr).comp_sub_left u
  calc
    _ ≤ ∫ t, ‖boxPower A h n t * smoothUnitBump r (u - t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖smoothUnitBump r (u - t)‖ := by
      refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hi.norm
        (ae_of_all _ fun t => ?_)
      simp only
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_boxPower_le hh n t)
    _ = 1 := by
      simp_rw [norm_smoothUnitBump hr]
      rw [integral_sub_left_eq_self, (radiusBump hr).integral_normed]

theorem boxCameraRadius_pos {A h r : ℝ} (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) : 0 < boxCameraRadius A h n r := by
  unfold boxCameraRadius
  positivity

theorem contDiff_boxTuranProfile {A h r : ℝ} (hr : 0 < r) (n : ℕ) :
    ContDiff ℝ 2 (boxTuranProfile A h n r) := by
  unfold boxTuranProfile
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp
    ((contDiff_boxPlateau hr (n + 1)).comp (contDiff_const.mul contDiff_id)))

theorem boxTuranProfile_nonneg {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) (u : ℝ) :
    0 ≤ boxTuranProfile A h n r u :=
  mul_nonneg (boxCameraRadius_pos hA hh hr n).le (positiveReal_boxPlateau hh hr (n + 1) _).1

theorem abs_boxTuranProfile_le {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) (u : ℝ) :
    |boxTuranProfile A h n r u| ≤ boxCameraRadius A h n r := by
  rw [boxTuranProfile, abs_mul, abs_of_pos (boxCameraRadius_pos hA hh hr n)]
  exact mul_le_of_le_one_right (boxCameraRadius_pos hA hh hr n).le
    ((Complex.abs_re_le_norm _).trans (norm_boxPlateau_le_one hh hr (n + 1) _))

theorem boxTuranProfile_support {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) :
    ∀ u, boxTuranProfile A h n r u ≠ 0 → |u| ≤ 1 := by
  intro u hu
  by_contra hn
  have hδ := boxCameraRadius_pos hA hh hr n
  have hx : boxCameraRadius A h n r ≤ |boxCameraRadius A h n r * u| := by
    rw [abs_mul, abs_of_pos hδ]
    exact le_mul_of_one_le_right hδ.le (lt_of_not_ge hn).le
  have hb := boxPlateau_eq_zero hh hr (n + 1) hx
  apply hu
  simp only [boxTuranProfile, hb, Complex.zero_re, mul_zero]

theorem integral_boxTuranProfile {A h r : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) :
    ∫ u, boxTuranProfile A h n r u = 2 * A := by
  have hδ := boxCameraRadius_pos hA hh hr n
  have he : (fun u => (boxPlateau A h (n + 1) r (boxCameraRadius A h n r * u)).re) =
      fun u => (boxPlateau A h (n + 1) r (u / (boxCameraRadius A h n r)⁻¹)).re := by
    funext u
    rw [div_inv_eq_mul, mul_comm]
  have hi := integral_re (integrable_boxPlateau (A := A) (h := h) hr (n + 1))
  simp only [RCLike.re_to_complex] at hi
  rw [boxTuranProfile, integral_const_mul, he, Measure.integral_comp_div,
    abs_of_pos (inv_pos.mpr hδ), smul_eq_mul, hi, integral_boxPlateau hA hh hr,
    Complex.ofReal_re]
  field_simp [hδ.ne']

/-- The physical camera is exactly the existing normalized camera. -/
theorem depthCenteredCamera_boxTuranProfile {A h r b y : ℝ}
    (hA : 0 ≤ A) (hh : 0 < h) (hr : 0 < r) (n : ℕ) :
    depthCenteredCamera (boxTuranProfile A h n r) b (boxCameraRadius A h n r) y =
      boxCenteredCamera A h n r b y := by
  have hδ := boxCameraRadius_pos hA hh hr n
  funext u
  have he : boxCameraRadius A h n r * ((u - y) / boxCameraRadius A h n r) = u - y := by
    field_simp [hδ.ne']
  simp only [depthCenteredCamera, ZeroConfigurationGeometry.tilt, cameraTest,
    boxTuranProfile, he, mul_div_cancel_left₀ _ hδ.ne',
    (positiveReal_boxPlateau hh hr (n + 1) (u - y)).2, boxCenteredCamera]
  rw [Complex.ofReal_exp]
  congr 2
  push_cast

/-- A near-top sector cluster keeps its Turán signal for the box camera. -/
theorem exists_nu_widthCenteredBox_cluster_signal
    {A h r ℓ t η : ℝ} (hA : 0 < A) (hh : 0 < h) (hr : 0 < r)
    (n : ℕ) (hℓ : 0 < ℓ) (hη : 0 ≤ η)
    {M N : ℕ} (hN : 1 ≤ N) {s : Finset zetaZeroConfig.carrier}
    (hcard : s.card ≤ N)
    (hsec : ∀ ρ ∈ s, |(ρ : ℂ).im - t| * boxCameraRadius A h n r ≤ 1 / 10)
    {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hnear : zetaZeroWidth - η ≤ (ρ : ℂ).re - 1 / 2) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      A * turanConstant N M *
        Real.exp (-(η * (((M : ℝ) + N) * ℓ + boxCameraRadius A h n r))) ≤
      ‖∑ q ∈ s, (zetaZeroConfig.mult q : ℂ) *
        paperFT (boxCenteredCamera A h n r zetaZeroWidth ((ν : ℝ) * ℓ))
          (gammaOf q - t)‖ := by
  have hI : 0 < ∫ u, boxTuranProfile A h n r u := by
    rw [integral_boxTuranProfile hA.le hh hr]
    positivity
  obtain ⟨ν, hν1, hνN, hs⟩ := exists_nu_widthCentered_cluster_signal
    (contDiff_boxTuranProfile hr n) (boxTuranProfile_support hA.le hh hr n)
    (boxTuranProfile_nonneg hA.le hh hr n) hI (boxCameraRadius_pos hA.le hh hr n)
    hℓ hη hN hcard hsec hρ hnear
  rw [integral_boxTuranProfile hA.le hh hr,
    show (1 / 2 : ℝ) * (2 * A) = A by ring] at hs
  simp_rw [depthCenteredCamera_boxTuranProfile hA.le hh hr n] at hs
  exact ⟨ν, hν1, hνN, hs⟩

end GaloisForLFunctions.MultiscaleMollifiedZetaField
