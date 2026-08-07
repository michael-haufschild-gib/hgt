import GaloisForLFunctions.RHTower.HedenmalmRootFluxModularCharge
import GaloisForLFunctions.RHTower.HedenmalmThetaEigenTransform
import GaloisForLFunctions.RHTower.XiHedenmalmMultiplicityFourierBridge
import GaloisForLFunctions.RHTower.BurnolHedenmalmCompletionDomain
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Completed Xi divided energy as Hedenmalm quantile root energy

The first removable completed-Xi quotient and the quantile root mode are the same divisor vector
in spectral and source coordinates.  After the exact `2π` Plancherel dilation, their energies agree:

`‖Q_ρ‖₂² = 2π M² E(-α_ρ)`.

This is unconditional at every actual Xi divisor, including multiple and off-critical divisors.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmPrimeTranslation
open HedenmalmThetaSource

/-- The source-mode and original two-ended Volterra constructions are literally the same
time-side divisor vector. -/
theorem sourceModeU_thetaSource_eq_hedenmalmCausalVolterra (alpha : ℂ) (x : ℝ) :
    sourceModeU thetaSource alpha x = hedenmalmCausalVolterra alpha x := by
  rw [sourceModeU, hedenmalmCausalVolterra_eq_profile]
  congr 1
  rw [sourceModeI, hedenmalmVolterraProfile]
  refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
  rw [thetaSource_k, HedenmalmQuantile.sourceChar, thetaCuspFourierLaplaceIntegrand]
  congr 2
  ring

/-- Physical root mode at the Plancherel normalization used by `xiThetaSchwartzSource`. -/
def scaledThetaSourceModeU (alpha : ℂ) (x : ℝ) : ℂ :=
  (2 * Real.pi : ℂ) * sourceModeU thetaSource alpha ((2 * Real.pi) * x)

theorem integrable_scaledThetaSourceModeU {alpha : ℂ} (hstrip : |alpha.im| < 1)
    (hzero : XiC alpha = 0) :
    Integrable (scaledThetaSourceModeU alpha) (volume : Measure ℝ) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  exact ((integrable_sourceModeU hstrip hzero).comp_mul_left' hscale).const_mul
    (2 * Real.pi : ℂ)

theorem integrable_norm_sq_scaledThetaSourceModeU {alpha : ℂ} (hstrip : |alpha.im| < 1)
    (hzero : XiC alpha = 0) :
    Integrable (fun x : ℝ => ‖scaledThetaSourceModeU alpha x‖ ^ 2)
      (volume : Measure ℝ) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hbase := (integrable_norm_sq_sourceModeU hstrip hzero).comp_mul_left' hscale
  refine (hbase.const_mul ((2 * Real.pi) ^ 2)).congr ?_
  filter_upwards with x
  rw [scaledThetaSourceModeU, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_pow]

theorem memLp_scaledThetaSourceModeU {alpha : ℂ} (hstrip : |alpha.im| < 1)
    (hzero : XiC alpha = 0) :
    MemLp (scaledThetaSourceModeU alpha) 2 (volume : Measure ℝ) := by
  rw [memLp_two_iff_integrable_sq_norm
    ((continuous_sourceModeU hstrip).comp
      (continuous_const.mul continuous_id) |>.const_mul (2 * Real.pi : ℂ)).aestronglyMeasurable]
  exact integrable_norm_sq_scaledThetaSourceModeU hstrip hzero

/-- Exact Fourier identification after the physical `2π` dilation. -/
theorem fourier_scaledThetaSourceModeU (alpha : ℂ) (xi : ℝ) :
    (𝓕 (scaledThetaSourceModeU alpha)) xi = hedenmalmThetaEigenTransform alpha xi := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  let G : ℝ → ℂ := fun y =>
    sourceModeU thetaSource alpha y * Complex.exp (-I * (xi : ℂ) * (y : ℂ))
  have hfun : (fun x : ℝ =>
      Complex.exp (↑(-2 * Real.pi * x * xi) * I) • scaledThetaSourceModeU alpha x) =
      fun x => (2 * Real.pi : ℂ) * G ((2 * Real.pi) * x) := by
    funext x
    rw [scaledThetaSourceModeU]
    change Complex.exp (↑(-2 * Real.pi * x * xi) * I) *
        ((2 * Real.pi : ℂ) * sourceModeU thetaSource alpha ((2 * Real.pi) * x)) = _
    dsimp [G]
    have hphase : Complex.exp (↑(-2 * Real.pi * x * xi) * I) =
        Complex.exp (-I * (xi : ℂ) * (((2 * Real.pi) * x : ℝ) : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [hphase]
    ring
  rw [hfun, integral_const_mul]
  rw [MeasureTheory.Measure.integral_comp_mul_left G (2 * Real.pi)]
  have hscale : |((2 * Real.pi)⁻¹)| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  rw [hscale]
  change (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) • (∫ y : ℝ, G y)) = _
  rw [real_smul]
  have hcancel : (2 * Real.pi : ℂ) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [← mul_assoc, hcancel, one_mul]
  rw [hedenmalmThetaEigenTransform]
  apply integral_congr_ae
  filter_upwards with y
  dsimp [G]
  rw [sourceModeU_thetaSource_eq_hedenmalmCausalVolterra]

/-- Quantile change of variables: the weighted root energy is exactly the time-side `L²` energy,
divided by the square of the source mass. -/
theorem thetaRootEnergy_eq_integral_norm_sq_sourceModeU_div_mass_sq
    {alpha : ℂ} (hstrip : |alpha.im| < 1) (hzero : XiC alpha = 0) :
    thetaRootEnergy alpha =
      (∫ x : ℝ, ‖sourceModeU thetaSource alpha x‖ ^ 2) / thetaSource.mass ^ 2 := by
  let g : ℝ → ℝ := fun x =>
    ‖sourceModeU thetaSource alpha x‖ ^ 2 /
      (thetaSource.mass * thetaSource.k x)
  have hgmeas : AEStronglyMeasurable g (volume : Measure ℝ) := by
    refine (((continuous_sourceModeU hstrip).norm.pow 2).div
      (continuous_const.mul thetaSource.continuous_k) fun x => ?_).aestronglyMeasurable
    exact mul_ne_zero thetaSource.mass_ne_zero (thetaSource.pos_k x).ne'
  have htransport := integral_comp_quantile thetaSource g hgmeas
  have hleft : (∫ t in Ioo (0 : ℝ) 1, g (thetaSource.quantileFun t)) =
      thetaRootEnergy alpha := by
    rw [thetaRootEnergy]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    dsimp [g]
    rw [rootH_eq_sourceModeU thetaSource alpha ht, quantileSpeed,
      norm_mul, Complex.norm_div, Complex.norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos thetaSource.mass_pos, one_div, mul_pow]
    have hk : thetaSource.k (thetaSource.quantileFun t) ≠ 0 :=
      (thetaSource.pos_k _).ne'
    have hM : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
    field_simp
  have hright : (∫ x : ℝ, thetaSource.normalized x • g x) =
      (∫ x : ℝ, ‖sourceModeU thetaSource alpha x‖ ^ 2) / thetaSource.mass ^ 2 := by
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards with x
    dsimp [g]
    rw [show thetaSource.normalized x = thetaSource.k x / thetaSource.mass from rfl]
    have hk : thetaSource.k x ≠ 0 := (thetaSource.pos_k x).ne'
    have hM : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
    field_simp
  rw [← hleft, htransport, hright]

end

end RHTower
