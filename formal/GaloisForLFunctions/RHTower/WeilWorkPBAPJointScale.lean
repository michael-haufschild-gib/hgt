import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity
import Mathlib.Analysis.Calculus.Deriv.CompMul

/-!
# Actual dilation of smooth cluster profiles

Support, physical mass, the full complex autocorrelation, both derivatives and
all complex Fourier arguments retain their exact width factors. Nonnegative
real source profiles supply the autocorrelation sign used by the modulation
kernel. These identities are the parameter construction for the width sector;
they assert no full-energy sign by themselves.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

def jointDilatedProfile (f : ℝ → ℂ) (W u : ℝ) : ℂ := f (W⁻¹*u)

theorem contDiff_jointDilatedProfile {f : ℝ → ℂ}
    (hf : ContDiff ℝ ∞ f) (W : ℝ) : ContDiff ℝ ∞ (jointDilatedProfile f W) :=
  hf.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_jointDilatedProfile {f : ℝ → ℂ}
    (hf : HasCompactSupport f) {W : ℝ} (hW : 0 < W) :
    HasCompactSupport (jointDilatedProfile f W) :=
  hf.comp_homeomorph (Homeomorph.mulLeft₀ W⁻¹ (inv_ne_zero hW.ne'))

def jointDilatedTest (f : JointSmoothTest) (W : ℝ) (hW : 0 < W) : JointSmoothTest :=
  ⟨⟨jointDilatedProfile f.1.1 W,
      (contDiff_jointDilatedProfile f.2 W).of_le (by norm_cast),
      hasCompactSupport_jointDilatedProfile f.1.2.2 hW⟩,
    contDiff_jointDilatedProfile f.2 W⟩

/-- The actual unit-interval profile has exactly the required dilated support bound. -/
theorem jointDilatedProfile_support {f : ℝ → ℂ} (hf : tsupport f ⊆ Icc 0 1)
    {W : ℝ} (hW : 0 < W) : tsupport (jointDilatedProfile f W) ⊆ Icc 0 W := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have hfu : f (W⁻¹*u) ≠ 0 := hu
  have hh := hf (subset_tsupport _ hfu)
  have he : W*(W⁻¹*u)=u := by rw [← mul_assoc, mul_inv_cancel₀ hW.ne', one_mul]
  have hp := mul_nonneg hW.le hh.1
  have hq := mul_le_mul_of_nonneg_left hh.2 hW.le
  rw [he] at hp hq
  exact ⟨hp, by simpa only [mul_one] using hq⟩

/-- Physical mass scales by the literal width. -/
theorem jointDilatedProfile_mass (f : ℝ → ℂ) {W : ℝ} (hW : 0 < W) :
    testMass (jointDilatedProfile f W)=W*testMass f := by
  unfold testMass jointDilatedProfile
  rw [Measure.integral_comp_inv_mul_left (fun u => ‖f u‖^2),
    abs_of_pos hW, smul_eq_mul]

/-- The full complex autocorrelation scales before taking its real part. -/
theorem jointDilatedProfile_corr (f : ℝ → ℂ) {W : ℝ} (hW : 0 < W) (y : ℝ) :
    EF.weilTest (jointDilatedProfile f W) (jointDilatedProfile f W) y =
      W • EF.weilTest f f (W⁻¹*y) := by
  rw [weilTest_apply, weilTest_apply]
  unfold jointDilatedProfile
  simp_rw [mul_sub]
  change (∫ u : ℝ, (fun v => f v*conj (f (v-W⁻¹*y))) (W⁻¹*u)) = _
  rw [Measure.integral_comp_inv_mul_left (fun v => f v*conj (f (v-W⁻¹*y))) W,
    abs_of_pos hW]

/-- First derivative under actual dilation; no differentiability premise is necessary. -/
theorem jointDilatedProfile_deriv (f : ℝ → ℂ) (W : ℝ) :
    deriv (jointDilatedProfile f W) = fun u => W⁻¹ • deriv f (W⁻¹*u) := by
  funext u
  exact deriv_comp_mul_left W⁻¹ f u

/-- The second derivative keeps both inverse-width factors. -/
theorem jointDilatedProfile_deriv_two (f : ℝ → ℂ) (W : ℝ) :
    deriv (deriv (jointDilatedProfile f W)) =
      fun u => (W⁻¹*W⁻¹) • deriv (deriv f) (W⁻¹*u) := by
  rw [jointDilatedProfile_deriv]
  funext u
  rw [deriv_fun_const_smul_field, deriv_comp_mul_left, smul_smul]

/-- The exact inverse-width derivative cost used in the high-frequency estimates. -/
theorem jointDilatedProfile_deriv_two_norm (f : ℝ → ℂ) {W : ℝ} (hW : 0 < W) :
    (∫ u : ℝ, ‖deriv (deriv (jointDilatedProfile f W)) u‖) =
      (∫ u : ℝ, ‖deriv (deriv f) u‖)/W := by
  rw [jointDilatedProfile_deriv_two]
  simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hW]
  rw [integral_const_mul,
    Measure.integral_comp_inv_mul_left (fun u => ‖deriv (deriv f) u‖) W,
    abs_of_pos hW, smul_eq_mul]
  field_simp [hW.ne']

/-- Autocorrelation of a real profile is its literal real product integral. -/
theorem joint_real_autocorr (f : ℝ → ℝ) (y : ℝ) :
    EF.weilTest (fun u => (f u:ℂ)) (fun u => (f u:ℂ)) y =
      ((∫ u : ℝ, f u*f (u-y):ℝ):ℂ) := by
  rw [weilTest_apply, ← integral_complex_ofReal]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by simp only [Complex.conj_ofReal, Complex.ofReal_mul]

/-- Nonnegative real profiles pay the sign requirement of the modulation kernel. -/
theorem joint_real_autocorr_nonneg (f : ℝ → ℝ) (hf : ∀ u, 0 ≤ f u) (y : ℝ) :
    0 ≤ (EF.weilTest (fun u => (f u:ℂ)) (fun u => (f u:ℂ)) y).re := by
  rw [joint_real_autocorr, Complex.ofReal_re]
  exact integral_nonneg fun u => mul_nonneg (hf u) (hf (u-y))

/-- Actual dilation also rescales every complex Fourier argument, including both poles. -/
theorem jointDilatedProfile_paperFT (f : ℝ → ℂ) {W : ℝ} (hW : 0 < W) (z : ℂ) :
    paperFT (jointDilatedProfile f W) z = W • paperFT f ((W:ℂ)*z) := by
  have hw : (W:ℂ) ≠ 0 := by exact_mod_cast hW.ne'
  have he (u : ℝ) : I*((W:ℂ)*z)*((W⁻¹*u:ℝ):ℂ)=I*z*u := by
    push_cast
    field_simp [hw]
  rw [paperFT_def, paperFT_def]
  change (∫ u : ℝ, f (W⁻¹*u)*Complex.exp (I*z*u)) = _
  calc
    _ = ∫ u : ℝ, (fun v => f v*Complex.exp (I*((W:ℂ)*z)*v)) (W⁻¹*u) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by dsimp only; rw [he]
    _ = _ := by
      rw [Measure.integral_comp_inv_mul_left
        (fun v => f v*Complex.exp (I*((W:ℂ)*z)*v)) W, abs_of_pos hW]

end RHTower.WeilWorkPBAP
