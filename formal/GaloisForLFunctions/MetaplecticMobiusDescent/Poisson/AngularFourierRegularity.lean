import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AngularFourierProfiles
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.DivisorBlocksAndKernelTransfer

/-! # Euler derivative bounds for angular Fourier profiles

Restricting the plane Fourier transform to a real ray gives a Schwartz function.
The logarithmic derivative of its square-root profile is the half-Euler operator.
This yields rapid decay for every fixed number of Euler derivatives with finite
control by seminorms of the original annular source.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical SchwartzMap ContDiff
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open Eisenstein
open GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson

/-- Angular Fourier transform restricted to the trace-frequency ray. -/
def angularFourierRayCLM (n : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ)
        (Units.mk0 ((ringComplex omega).im)⁻¹ (inv_ne_zero complex_omega_im_ne_zero)))).comp
      ((SchwartzMap.compCLMOfAntilipschitz ℝ (vertical_temperate 0)
        (vertical_isometry 0).antilipschitz).comp (annularFourierCLM n))

@[simp] theorem angularFourierRayCLM_apply (n : ℕ) (W : 𝓢(ℝ, ℂ)) (s : ℝ) :
    angularFourierRayCLM n W s =
      (2 / Real.sqrt 3 : ℝ) • annularFourierCLM n W (paperFrequency (s : ℂ)) := by
  change (2 / Real.sqrt 3 : ℝ) •
    annularFourierCLM n W (complexPoint 0 (((ringComplex omega).im)⁻¹ * s)) = _
  rw [paperFrequency_coordinates]
  simp only [Complex.ofReal_im, Complex.ofReal_re, div_eq_mul_inv, zero_mul, mul_comm]

/-- The angular profile is a square-root pullback of a Schwartz function on the ray. -/
theorem paperAngularFourier_eq_ray (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    paperAngularFourier n W = fun x : ℝ => angularFourierRayCLM n W (Real.sqrt x) := by
  funext x
  rw [paperAngularFourier_eq_plane n W hW, angularFourierRayCLM_apply]

/-- The ray Schwartz operator representing the `j`th Euler derivative. -/
def angularEulerCLM (n j : ℕ) : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (halfEulerIterateCLM j).comp (angularFourierRayCLM n)

theorem paperAngularFourier_eulerDeriv (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2)
    (j : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    LocalLogFourier.eulerDeriv (paperAngularFourier n W) j x =
      angularEulerCLM n j W (Real.sqrt x) := by
  rw [paperAngularFourier_eq_ray n W hW, eulerDeriv_sqrt_profile _ j x hx]
  simp only [angularEulerCLM, ContinuousLinearMap.comp_apply, halfEulerIterateCLM_apply]

theorem paperAngularFourier_contDiffOn (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) :
    ContDiffOn ℝ ∞ (paperAngularFourier n W) (Set.Ioi 0) := by
  rw [paperAngularFourier_eq_ray n W hW]
  exact contDiffOn_sqrt_profile _

theorem paperAngularFourier_log_contDiff (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (hW : Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2) (x : ℝ) (hx : 0 ≤ x) :
    ContDiff ℝ ∞ (fun t : ℝ => paperAngularFourier n W (x * Real.exp t)) := by
  rw [paperAngularFourier_eq_ray n W hW]
  exact contDiff_sqrt_profile_log _ x hx

/-- All Euler derivatives up to a prescribed order retain rapid Fourier decay. -/
theorem paperAngularFourier_euler_source_weighted_bound (n A K : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ j ≤ K, ∀ x : ℝ, 0 ≤ x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperAngularFourier n W) j x‖ ≤
          C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨S, C, hC, hb⟩ :=
    schwartzCLM_family_finite_seminorm_control (angularEulerCLM n) A K
  refine ⟨S, 2 ^ A * C, by positivity, ?_⟩
  intro W hW j hj x hx
  rw [paperAngularFourier_eulerDeriv n W hW j x hx]
  apply (sqrt_profile_rapid_bound (angularEulerCLM n j W) A x hx).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb W j hj)
    (show 0 ≤ (2 : ℝ) ^ A by positivity)

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
