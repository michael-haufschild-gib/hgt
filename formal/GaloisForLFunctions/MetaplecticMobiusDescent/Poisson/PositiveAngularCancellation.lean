import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.GaussianAffineAngularBound
import GaloisForLFunctions.HTGeometry.PositiveWolffMeasure

/-!
# Continuous rotation kills every positive angular zero mode

Rotation through `π/k` multiplies angular weight `k > 0` by minus one and
preserves planar measure. Thus every positive angular weight has zero integral,
including the weights divisible by four which survive Gaussian unit averaging.
The affine lattice estimate consequently applies to all positive angular weights.
-/

noncomputable section
open Complex MeasureTheory
open scoped Classical SchwartzMap FourierTransform

namespace GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
open CubicEisenstein.SchwartzPlanePoisson
open HTGeometry.PositiveWolffMeasure (halfTurnRoot halfTurnRoot_pow)

/-- Normalized angular powers transform by their character under every rotation. -/
theorem angularRadial_rotation (k : ℕ) (W : ℝ → ℂ) (u : Circle) (z : ℂ) :
    angularRadial k W ((u : ℂ) * z) = (u : ℂ) ^ k * angularRadial k W z := by
  simp only [angularRadial, norm_mul, Circle.norm_coe, one_mul, mul_div_assoc,
    mul_pow, mul_assoc]

/-- Every positive angular weight has zero planar Fourier mass at the origin. -/
theorem angular_positive_zero_mode (n : ℕ) (W : ℝ → ℂ) :
    paperFourier (angularRadial (n + 1) W) 0 = 0 := by
  have hu : (halfTurnRoot (n + 1) : ℂ) ≠ 0 := by
    intro h
    have hn := Circle.norm_coe (halfTurnRoot (n + 1))
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have h := paperFourier_comp_mul (angularRadial (n + 1) W)
    (halfTurnRoot (n + 1) : ℂ) hu 0
  simp only [Circle.norm_coe, one_pow, div_one, one_smul, zero_div] at h
  have hr : (fun z => angularRadial (n + 1) W ((halfTurnRoot (n + 1) : ℂ) * z)) =
      fun z => -angularRadial (n + 1) W z := by
    funext z
    rw [angularRadial_rotation, halfTurnRoot_pow (Nat.succ_pos n), neg_one_mul]
  rw [hr] at h
  have hn : paperFourier (fun z => -angularRadial (n + 1) W z) 0 =
      -paperFourier (angularRadial (n + 1) W) 0 := by
    simp only [paperFourier, mul_neg, integral_neg, smul_neg]
  rw [hn] at h
  linear_combination (-1 / 2 : ℂ) * h

/-- Standard Fourier normalization has the same positive angular cancellation. -/
theorem standard_angular_positive_zero_mode (n : ℕ) (W : ℝ → ℂ) :
    (𝓕 (angularRadial (n + 1) W)) 0 = 0 := by
  have h := angular_positive_zero_mode n W
  rw [paperFourier_eq_standard] at h
  simp only [paperFrequency, zero_div, map_zero, mul_zero] at h
  exact (smul_eq_zero.mp h).resolve_left (by positivity : (2 / Real.sqrt 3 : ℝ) ≠ 0)

/-- Every positive annular angular Schwartz kernel has zero Fourier value at the origin. -/
theorem annularFourier_positive_zero (n : ℕ) (W : 𝓢(ℝ, ℂ)) :
    annularFourierCLM (n + 1) W 0 = 0 := by
  change (𝓕 (annularAngularCLM (n + 1) W)) 0 = 0
  rw [SchwartzMap.fourier_coe,
    show (annularAngularCLM (n + 1) W : ℂ → ℂ) =
      angularRadial (n + 1) (fun t => (annularBump t : ℂ) * W t) from
        funext (annularAngularCLM_apply (n + 1) W)]
  exact standard_angular_positive_zero_mode n _

/-- Four physical derivatives control the complete dual mass in every positive weight. -/
theorem scaled_positive_annularFourier_mass_le (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (s : PositiveScale) (a : ℂ) :
    s.val ^ 2 * (∑' z : GaussianInt,
      ‖gaussianPhase a z * annularFourierCLM (n + 1) W ((s.val : ℂ) * (z : ℂ))‖) ≤
      1632 * derivativeMass 4 (annularAngularCLM (n + 1) W) := by
  have h := scaled_fourier_mass_sub_zero_le_derivativeMass
    (annularAngularCLM (n + 1) W) s a
  change s.val ^ 2 * ((∑' z : GaussianInt,
    ‖gaussianPhase a z * annularFourierCLM (n + 1) W ((s.val : ℂ) * (z : ℂ))‖) -
      ‖annularFourierCLM (n + 1) W 0‖) ≤ _ at h
  simpa only [annularFourier_positive_zero, norm_zero, sub_zero] using h

/-- All positive angular weights admit a bound uniform in affine dilation and translation. -/
theorem gaussian_affine_positive_annular_sum_le (n : ℕ) (W : 𝓢(ℝ, ℂ))
    (c : ℂˣ) (b : ℂ) :
    ‖gaussianAffineSum (annularAngularCLM (n + 1) W) c b‖ ≤
      1632 * derivativeMass 4 (annularAngularCLM (n + 1) W) := by
  have hz := annularFourier_positive_zero n W
  change (𝓕 (annularAngularCLM (n + 1) W)) 0 = 0 at hz
  have h := gaussian_affine_sum_sub_mean_le (annularAngularCLM (n + 1) W) c b
  simpa only [hz, smul_zero, sub_zero] using h

end GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
