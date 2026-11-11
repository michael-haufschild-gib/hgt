import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDepthCenteredCameraPaysItsExteriorMass

/-!
# The prime cost of depth centering

Depth centering multiplies the camera at lag `u` by `exp(-bu)`.
Its prime coefficients are therefore damped. Writing the centered camera
as a scalar times an exponentially tilted profile lets the existing mean
value theorem retain this gain: the mean square acquires the factor
`exp(-2b(y-δ))`, with no uncontrolled profile-dependent constant.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

/-- The profile obtained by removing depth `b` on a camera of width `δ`. -/
def depthCenteredProfile (v : ℝ → ℝ) (b δ u : ℝ) : ℝ :=
  Real.exp (-(b * δ * u)) * v u

/-- Centering is a scalar factor and a tilt of the fixed profile. -/
theorem depthCenteredCamera_eq_profile (v : ℝ → ℝ) (b δ y : ℝ) (hδ : 0 < δ) :
    depthCenteredCamera v b δ y =
      fun u => (Real.exp (-(b * y)) : ℂ) * cameraTest (depthCenteredProfile v b δ) δ y u := by
  funext u
  have he : Real.exp (-(b * y)) * Real.exp (-(b * δ * ((u - y) / δ))) =
      Real.exp (-(b * u)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hδ.ne']
    ring
  have hr : (v ((u - y) / δ) / δ) * Real.exp (-(b * u)) =
      Real.exp (-(b * y)) *
        (Real.exp (-(b * δ * ((u - y) / δ))) * v ((u - y) / δ) / δ) := by
    rw [← he]
    ring
  simpa only [depthCenteredCamera, ZeroConfigurationGeometry.tilt, cameraTest,
    depthCenteredProfile, neg_mul, Complex.ofReal_mul, Complex.ofReal_div] using
      congrArg Complex.ofReal hr

/-- The tilted profile has an explicit supremum bound. -/
theorem abs_depthCenteredProfile_le {v : ℝ → ℝ} {S b δ : ℝ}
    (hS : ∀ u, |v u| ≤ S) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hb : 0 ≤ b) (hδ : 0 ≤ δ) (u : ℝ) :
    |depthCenteredProfile v b δ u| ≤ S * Real.exp (b * δ) := by
  have hS0 : 0 ≤ S := (abs_nonneg (v 0)).trans (hS 0)
  by_cases hu : v u = 0
  · simp only [depthCenteredProfile, hu, mul_zero, abs_zero]
    exact mul_nonneg hS0 (Real.exp_pos _).le
  have hu1 := (abs_le.mp (hsupp u hu)).1
  have hbd : 0 ≤ b * δ := mul_nonneg hb hδ
  have he : -(b * δ * u) ≤ b * δ := by nlinarith only [hbd, hu1]
  rw [depthCenteredProfile, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (b * δ) * S :=
      mul_le_mul (Real.exp_le_exp.mpr he) (hS u) (abs_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

/-- Prime coefficients of the centered camera. -/
def depthCenteredCameraCoeff (v : ℝ → ℝ) (b δ y : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℝ) * depthCenteredCamera v b δ y (Real.log n)

/-- The prime polynomial uses the same support and length after centering. -/
def depthCenteredCameraPoly (v : ℝ → ℝ) (b δ y t : ℝ) : ℂ :=
  edPoly (depthCenteredCameraCoeff v b δ y) (Finset.Icc 1 (cameraLength δ y))
    (displacedLinePt 0 t)

theorem depthCenteredCameraCoeff_eq_profile (v : ℝ → ℝ) (b δ y : ℝ)
    (hδ : 0 < δ) (n : ℕ) :
    depthCenteredCameraCoeff v b δ y n = (Real.exp (-(b * y)) : ℂ) *
      cameraCoeff (depthCenteredProfile v b δ) δ y n := by
  rw [depthCenteredCameraCoeff, depthCenteredCamera_eq_profile v b δ y hδ, cameraCoeff]
  ring

theorem depthCenteredCameraPoly_eq_profile (v : ℝ → ℝ) (b δ y t : ℝ)
    (hδ : 0 < δ) :
    depthCenteredCameraPoly v b δ y t = (Real.exp (-(b * y)) : ℂ) *
      cameraPoly (depthCenteredProfile v b δ) δ y t := by
  simp only [depthCenteredCameraPoly, cameraPoly, edPoly,
    depthCenteredCameraCoeff_eq_profile v b δ y hδ, Finset.mul_sum, mul_assoc]

/-- Centering at nonnegative depth reduces the prime mean square by an
explicit exponential factor. -/
theorem integral_depthCenteredCameraPoly_sq_le
    {v : ℝ → ℝ} {S CΛ b : ℝ} (hS : ∀ u, |v u| ≤ S)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hb : 0 ≤ b)
    (hCΛ : ∀ N : ℕ, 1 ≤ N → ∑ k ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt k) ^ (2 : ℕ) / (k : ℝ) ≤
        Real.log (N : ℝ) * (Real.log (N : ℝ) + CΛ))
    {c T y : ℝ} (hc0 : 0 < c) (hc : c < 1 / 3) (hT3 : 3 ≤ T)
    (hL2 : 2 ≤ Real.log T) (hLd : 64 / c ^ 2 ≤ Real.log T)
    (hLC : 1 + |CΛ| ≤ Real.log T)
    (hy0 : 0 ≤ y + c * Real.log T) (hy : y + c * Real.log T ≤ (1 - c) * Real.log T) :
    (∫ t in T..(2 * T), ‖depthCenteredCameraPoly v b (c * Real.log T) y t‖ ^ 2) ≤
      (8 * S ^ 2 / c ^ 2 * T) * Real.exp (-(2 * b * (y - c * Real.log T))) := by
  have hL0 : 0 < Real.log T := by linarith only [hL2]
  have hδ : 0 < c * Real.log T := mul_pos hc0 hL0
  have hm := integral_cameraPoly_sq_le
    (fun u => abs_depthCenteredProfile_le hS hsupp hb hδ.le u)
    hCΛ hc0 hc hT3 hL2 hLd hLC hy0 hy
  simp_rw [depthCenteredCameraPoly_eq_profile v b (c * Real.log T) y _ hδ,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [intervalIntegral.integral_const_mul]
  apply (mul_le_mul_of_nonneg_left hm (sq_nonneg _)).trans_eq
  have he : Real.exp (-(b * y)) ^ 2 * Real.exp (b * (c * Real.log T)) ^ 2 =
      Real.exp (-(2 * b * (y - c * Real.log T))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  calc
    _ = (8 * S ^ 2 / c ^ 2 * T) *
        (Real.exp (-(b * y)) ^ 2 * Real.exp (b * (c * Real.log T)) ^ 2) := by ring
    _ = _ := by rw [he]

/-- The centered prime mean-square estimate, with its arithmetic input
supplied by the proved von Mangoldt square-weight bound. The constant is
uniform in the centering depth and the camera centre. -/
theorem exists_integral_depthCenteredCameraPoly_sq_le
    {v : ℝ → ℝ} (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 3) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ b y : ℝ, 0 ≤ b →
      c * Real.log T ≤ y → y + c * Real.log T ≤ (1 - c) * Real.log T →
      (∫ t in T..(2 * T), ‖depthCenteredCameraPoly v b (c * Real.log T) y t‖ ^ 2) ≤
        C * T * Real.exp (-(2 * b * (y - c * Real.log T))) := by
  obtain ⟨S, hS0, hS⟩ := exists_abs_profile_le hv hsupp
  obtain ⟨CΛ, hCΛ⟩ := exists_sum_vonMangoldt_sq_div_le
  refine ⟨8 * S ^ 2 / c ^ 2, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop 3,
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop (64 / c ^ 2),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 + |CΛ|)]
    with T hT hL hLd hLC b y hb hyδ hy
  have hδ : 0 ≤ c * Real.log T := mul_nonneg hc0.le (by linarith only [hL])
  exact integral_depthCenteredCameraPoly_sq_le hS hsupp hb hCΛ hc0 hc hT hL hLd hLC
    (by linarith only [hyδ, hδ]) hy

end GaloisForLFunctions.MultiscaleMollifiedZetaField
