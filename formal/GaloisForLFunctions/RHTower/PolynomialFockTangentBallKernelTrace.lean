import GaloisForLFunctions.RHTower.PolynomialFockSharpPhaseTransition
import GaloisForLFunctions.RHTower.Deninger.DeningerRadialIntegral

open MeasureTheory Set Metric

namespace RHTower

noncomputable section

theorem normSq_polynomialMomentFockKernel_radial
    {m : ℝ} (hm : 2 ≤ m) (z : ℂ) :
    ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 =
      ‖momentFockKernel (polynomialMomentFockData m hm) (‖z‖ : ℂ)‖ ^ 2 := by
  rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
  apply tsum_congr
  intro n
  simp only [momentFockKernel_apply]
  change ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ 2 =
    ‖momentFockKernelCoeff (polynomialFockMoment m) (‖z‖ : ℂ) n‖ ^ 2
  have hz := norm_momentFockKernelCoeff_polynomial_sq hm z n
  have hr := norm_momentFockKernelCoeff_polynomial_sq hm (‖z‖ : ℂ) n
  rw [Real.rpow_two] at hz hr
  rw [hz, hr]
  simp

theorem measurable_normSq_polynomialMomentFockKernel
    {m : ℝ} (hm : 2 ≤ m) :
    Measurable (fun z : ℂ =>
      ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2) := by
  have heq : (fun z : ℂ =>
      ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2) =
      fun z : ℂ => ∑' n : ℕ,
        ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ 2 := by
    funext z
    rw [HilbertSchmidt.lp_norm_sq_eq]
    apply tsum_congr
    intro n
    simp only [momentFockKernel_apply]
    change ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ 2 =
      ‖momentFockKernelCoeff (polynomialFockMoment m) z n‖ ^ 2
    rfl
  rw [heq]
  apply Measurable.tsum
  intro n
  apply Continuous.measurable
  unfold momentFockKernelCoeff
  exact ((continuous_star.comp continuous_id).pow n).div_const _ |>.norm.pow 2

/-- Weighted diagonal density of the polynomial moment-Fock reproducing kernel. -/
def polynomialMomentFockKernelDiagonalDensity (m : ℝ) (hm : 2 ≤ m) (z : ℂ) : ℝ :=
  ‖momentFockKernel (polynomialMomentFockData m hm) z‖ ^ 2 *
    Real.exp (-2 * polynomialFockPotential m ‖z‖)

theorem polynomialMomentFockKernelDiagonalDensity_nonneg
    (m : ℝ) (hm : 2 ≤ m) (z : ℂ) :
    0 ≤ polynomialMomentFockKernelDiagonalDensity m hm z := by
  unfold polynomialMomentFockKernelDiagonalDensity
  positivity

theorem measurable_polynomialMomentFockKernelDiagonalDensity
    (m : ℝ) (hm : 2 ≤ m) :
    Measurable (polynomialMomentFockKernelDiagonalDensity m hm) := by
  unfold polynomialMomentFockKernelDiagonalDensity
  exact (measurable_normSq_polynomialMomentFockKernel hm).mul
    (Real.continuous_exp.comp
      (continuous_const.mul
        ((continuous_polynomialFockPotential m).comp continuous_norm))).measurable

theorem polynomialMomentFockKernelDiagonalDensity_le_curvature
    {m : ℝ} (hm : 4 ≤ m) (z : ℂ) :
    polynomialMomentFockKernelDiagonalDensity m (by linarith) z ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
        Real.pi * (m * (1 + ‖z‖ ^ 2) ^ (m / 2 - 1)) := by
  have hk := normSq_polynomialMomentFockKernel_upper hm (norm_nonneg z)
  have hrad := normSq_polynomialMomentFockKernel_radial (by linarith : 2 ≤ m) z
  rw [← hrad] at hk
  have hweight : 0 ≤ Real.exp (-2 * polynomialFockPotential m ‖z‖) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hk hweight
  have hm0 : 0 < m := by linarith
  have hr2 := polynomialFockTangentRadius_sq (x := ‖z‖) hm0
  have hcurv : 0 < m * (1 + ‖z‖ ^ 2) ^ (m / 2 - 1) := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  calc
    polynomialMomentFockKernelDiagonalDensity m (by linarith) z =
      ‖momentFockKernel (polynomialMomentFockData m (by linarith)) z‖ ^ 2 *
        Real.exp (-2 * polynomialFockPotential m ‖z‖) := rfl
    _ ≤ (Real.exp (2 * polynomialFockPotential m ‖z‖ +
          2 * (polynomialFockLocalBregmanConstant m / m)) /
        (Real.pi * (m * (1 + ‖z‖ ^ 2) ^ (m / 2 - 1))⁻¹)) *
          Real.exp (-2 * polynomialFockPotential m ‖z‖) := by
            simpa [hr2] using hmul
    _ = Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
        Real.pi * (m * (1 + ‖z‖ ^ 2) ^ (m / 2 - 1)) := by
      rw [div_eq_mul_inv]
      field_simp [hm0.ne']
      rw [← Real.exp_add]
      congr 1
      field_simp [hm0.ne']
      ring

theorem polynomialFockKernelDiagonalDensity_le_anchorCurvature_of_mem_tangentBall
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) {z : ℂ}
    (hz : z ∈ ball (x : ℂ) (polynomialFockTangentRadius m x)) :
    polynomialMomentFockKernelDiagonalDensity m (by linarith) z ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
        Real.pi * 3 ^ (m / 2 - 1) *
          (m * (1 + x ^ 2) ^ (m / 2 - 1)) := by
  have habs : |‖z‖ - x| ≤ polynomialFockTangentRadius m x := by
    have hnorm := abs_norm_sub_norm_le z (x : ℂ)
    have hdist : ‖z - (x : ℂ)‖ < polynomialFockTangentRadius m x := by
      simpa [mem_ball, dist_eq_norm] using hz
    have hxnorm : ‖(x : ℂ)‖ = x := by simp [abs_of_nonneg (by linarith : 0 ≤ x)]
    rw [hxnorm] at hnorm
    exact hnorm.trans hdist.le
  have hcurv := polynomialFockTangentCurvature_local_le hm hx habs
  have hdiag := polynomialMomentFockKernelDiagonalDensity_le_curvature hm z
  calc
    polynomialMomentFockKernelDiagonalDensity m (by linarith) z ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
        Real.pi * (m * (1 + ‖z‖ ^ 2) ^ (m / 2 - 1)) := hdiag
    _ ≤ Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
        Real.pi * (3 ^ (m / 2 - 1) *
          (m * (1 + x ^ 2) ^ (m / 2 - 1))) := by
      gcongr
    _ = _ := by ring

theorem integral_tangentBall_polynomialFockKernelDiagonalDensity_le
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    (∫ z in ball (x : ℂ) (polynomialFockTangentRadius m x),
      polynomialMomentFockKernelDiagonalDensity m (by linarith) z) ≤
      Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        3 ^ (m / 2 - 1) := by
  let C : ℝ := Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) /
    Real.pi * 3 ^ (m / 2 - 1) * (m * (1 + x ^ 2) ^ (m / 2 - 1))
  have hle : (∫ z in ball (x : ℂ) (polynomialFockTangentRadius m x),
      polynomialMomentFockKernelDiagonalDensity m (by linarith) z) ≤
      ∫ _z in ball (x : ℂ) (polynomialFockTangentRadius m x), C := by
    have hg : Integrable (fun _ : ℂ => C)
        (volume.restrict (ball (x : ℂ) (polynomialFockTangentRadius m x))) := by
      exact integrableOn_const
    have hf : Integrable (polynomialMomentFockKernelDiagonalDensity m (by linarith))
        (volume.restrict (ball (x : ℂ) (polynomialFockTangentRadius m x))) := by
      apply MeasureTheory.Integrable.mono' hg
        (measurable_polynomialMomentFockKernelDiagonalDensity m (by linarith)).aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
      rw [Real.norm_of_nonneg
        (polynomialMomentFockKernelDiagonalDensity_nonneg m (by linarith) z)]
      exact polynomialFockKernelDiagonalDensity_le_anchorCurvature_of_mem_tangentBall hm hx hz
    apply integral_mono_ae hf hg
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact polynomialFockKernelDiagonalDensity_le_anchorCurvature_of_mem_tangentBall hm hx hz
  have hrpos : 0 < polynomialFockTangentRadius m x :=
    polynomialFockTangentRadius_pos (by linarith)
  calc
    (∫ z in ball (x : ℂ) (polynomialFockTangentRadius m x),
      polynomialMomentFockKernelDiagonalDensity m (by linarith) z) ≤
        ∫ _z in ball (x : ℂ) (polynomialFockTangentRadius m x), C := hle
    _ = Real.pi * polynomialFockTangentRadius m x ^ 2 * C := by
      rw [setIntegral_const]
      change volume.real (ball (x : ℂ) (polynomialFockTangentRadius m x)) * C = _
      rw [measureReal_def, Complex.volume_ball]
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hrpos.le, ENNReal.coe_toReal]
      change polynomialFockTangentRadius m x ^ 2 * Real.pi * C = _
      ring
    _ = Real.exp (2 * (polynomialFockLocalBregmanConstant m / m)) *
        3 ^ (m / 2 - 1) := by
      dsimp [C]
      rw [polynomialFockTangentRadius_sq (by linarith : 0 < m)]
      field_simp

end

end RHTower
