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
  have hprimitive : sourceModeI thetaSource alpha x = hedenmalmVolterraProfile alpha x := by
    unfold HedenmalmPrimeTranslation.sourceModeI hedenmalmVolterraProfile
    refine setIntegral_congr_fun measurableSet_Iic fun y _ => ?_
    rw [thetaSource_k, HedenmalmQuantile.sourceChar, thetaCuspFourierLaplaceIntegrand]
    rw [show -I * -alpha * (y : ℂ) = I * alpha * (y : ℂ) by ring]
    ring
  rw [sourceModeU, hedenmalmCausalVolterra_eq_profile, hprimitive]
  ring

/-- Physical root mode at the Plancherel normalization used by `xiThetaSchwartzSource`. -/
def scaledThetaSourceModeU (alpha : ℂ) (x : ℝ) : ℂ :=
  (2 * Real.pi : ℂ) * sourceModeU thetaSource alpha ((2 * Real.pi) * x)

theorem integrable_scaledThetaSourceModeU {alpha : ℂ} (hstrip : |alpha.im| < 1)
    (hzero : XiC alpha = 0) :
    Integrable (scaledThetaSourceModeU alpha) (volume : Measure ℝ) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hzero' : xiC thetaSource alpha = 0 := by rw [xiC_thetaSource hstrip, hzero]
  exact ((integrable_sourceModeU hstrip hzero').comp_mul_left' hscale).const_mul
    (2 * Real.pi : ℂ)

theorem integrable_norm_sq_scaledThetaSourceModeU {alpha : ℂ} (hstrip : |alpha.im| < 1)
    (hzero : XiC alpha = 0) :
    Integrable (fun x : ℝ => ‖scaledThetaSourceModeU alpha x‖ ^ 2)
      (volume : Measure ℝ) := by
  have hscale : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hzero' : xiC thetaSource alpha = 0 := by rw [xiC_thetaSource hstrip, hzero]
  have hbase := (integrable_norm_sq_sourceModeU hstrip hzero').comp_mul_left' hscale
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  refine (hbase.const_mul ((2 * Real.pi) ^ 2)).congr ?_
  filter_upwards with x
  rw [scaledThetaSourceModeU, norm_mul, hnorm, mul_pow]
  ring

theorem memLp_scaledThetaSourceModeU {alpha : ℂ} (hstrip : |alpha.im| < 1)
    (hzero : XiC alpha = 0) :
    MemLp (scaledThetaSourceModeU alpha) 2 (volume : Measure ℝ) := by
  have hcont : Continuous (scaledThetaSourceModeU alpha) := by
    unfold scaledThetaSourceModeU
    exact continuous_const.mul
      ((continuous_sourceModeU hstrip).comp (continuous_const.mul continuous_id))
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
    (integrable_norm_sq_scaledThetaSourceModeU hstrip hzero)

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
    {alpha : ℂ} (hstrip : |alpha.im| < 1) :
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
      norm_mul, Complex.norm_div, norm_neg, Complex.norm_I,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos thetaSource.mass_pos, one_div, mul_pow]
    have hk : thetaSource.k (thetaSource.quantileFun t) ≠ 0 :=
      (thetaSource.pos_k _).ne'
    have hM : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
    rw [thetaSource_k]
    field_simp
  have hright : (∫ x : ℝ, thetaSource.normalized x • g x) =
      (∫ x : ℝ, ‖sourceModeU thetaSource alpha x‖ ^ 2) / thetaSource.mass ^ 2 := by
    calc
      (∫ x : ℝ, thetaSource.normalized x • g x) =
          ∫ x : ℝ, (thetaSource.mass ^ 2)⁻¹ *
            ‖sourceModeU thetaSource alpha x‖ ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards with x
        dsimp [g]
        rw [show thetaSource.normalized x = thetaSource.k x / thetaSource.mass from rfl]
        have hk : thetaSource.k x ≠ 0 := (thetaSource.pos_k x).ne'
        have hM : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
        have hk' : thetaCuspFullSource x ≠ 0 := by simpa only [thetaSource_k] using hk
        rw [thetaSource_k]
        field_simp [hk']
      _ = (thetaSource.mass ^ 2)⁻¹ *
          ∫ x : ℝ, ‖sourceModeU thetaSource alpha x‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
      _ = (∫ x : ℝ, ‖sourceModeU thetaSource alpha x‖ ^ 2) /
          thetaSource.mass ^ 2 := by
        rw [div_eq_mul_inv]
        ring
  rw [← hleft, htransport, hright]

/-- Dilation energy of the physical `2π` normalization. -/
theorem integral_norm_sq_scaledThetaSourceModeU_eq (alpha : ℂ) :
    (∫ x : ℝ, ‖scaledThetaSourceModeU alpha x‖ ^ 2) =
      2 * Real.pi * ∫ y : ℝ, ‖sourceModeU thetaSource alpha y‖ ^ 2 := by
  let F : ℝ → ℝ := fun y => ‖sourceModeU thetaSource alpha y‖ ^ 2
  have hscale := MeasureTheory.Measure.integral_comp_mul_left F (2 * Real.pi)
  have hinvabs : |((2 * Real.pi)⁻¹)| = (2 * Real.pi)⁻¹ := by
    rw [abs_of_pos]
    positivity
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    (∫ x : ℝ, ‖scaledThetaSourceModeU alpha x‖ ^ 2) =
        ∫ x : ℝ, (2 * Real.pi) ^ 2 * F ((2 * Real.pi) * x) := by
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [scaledThetaSourceModeU, norm_mul, hnorm, mul_pow]
    _ = (2 * Real.pi) ^ 2 * ∫ x : ℝ, F ((2 * Real.pi) * x) := by
      rw [MeasureTheory.integral_const_mul]
    _ = (2 * Real.pi) ^ 2 *
        (|((2 * Real.pi)⁻¹)| • ∫ y : ℝ, F y) := by rw [hscale]
    _ = 2 * Real.pi * ∫ y : ℝ, ‖sourceModeU thetaSource alpha y‖ ^ 2 := by
      rw [hinvabs, smul_eq_mul]
      dsimp [F]
      field_simp [Real.pi_ne_zero]

/-- **Completed divided-energy identity.**  The first removable Xi quotient and the reflected
theta-source root mode are the same divisor vector in spectral and quantile coordinates. -/
theorem integral_norm_sq_completedXiFirstDividedFunction_eq_thetaRootEnergy
    (rho : XiDivisorSupport) :
    (∫ xi : ℝ, ‖completedXiFirstDividedFunction rho xi‖ ^ 2) =
      2 * Real.pi * thetaSource.mass ^ 2 *
        thetaRootEnergy (-xiSpectralPointSupport rho) := by
  let a : ℂ := xiSpectralPointSupport rho
  let alpha : ℂ := -a
  have haZero : XiC a = 0 := by
    simpa only [a] using XiC_xiSpectralPointSupport_eq_zero rho
  have hzero : XiC alpha = 0 := by
    dsimp only [alpha]
    rw [XiC_even, haZero]
  have haIm : a.im = 1 / 2 - (rho : ℂ).re := by
    simp [a, xiSpectralPointSupport, Complex.mul_im]
  have hrhoStrip := xi_divisor_support_re_mem_open_unit rho
  have hstrip : |alpha.im| < 1 := by
    rw [abs_lt]
    dsimp only [alpha]
    rw [Complex.neg_im, haIm]
    constructor <;> linarith
  have hfourierAE :
      (fun xi : ℝ => (𝓕 (scaledThetaSourceModeU alpha)) xi) =ᵐ[volume]
        fun xi : ℝ => -completedXiFirstDividedFunction rho xi := by
    filter_upwards [MeasureTheory.volume.ae_ne a.re] with xi hxi
    have hne : (xi : ℂ) ≠ -alpha := by
      intro heq
      apply hxi
      have hre := congrArg Complex.re heq
      simpa only [alpha, neg_neg, Complex.ofReal_re] using hre
    rw [fourier_scaledThetaSourceModeU,
      hedenmalmThetaEigenTransform_eq_xiThetaEigenFourier hstrip hzero
        (by simp) hne,
      xiThetaEigenFourier_eq_I_mul_dividedChain_one]
    dsimp only [alpha, a, completedXiFirstDividedFunction]
    rw [neg_neg]
    ring_nf
    rw [Complex.I_sq, neg_one_mul]
  have hleft :
      (∫ xi : ℝ, ‖completedXiFirstDividedFunction rho xi‖ ^ 2) =
        ∫ xi : ℝ, ‖(𝓕 (scaledThetaSourceModeU alpha)) xi‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [hfourierAE] with xi hxi
    rw [hxi, norm_neg]
  have hplancherel := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq
    (integrable_scaledThetaSourceModeU hstrip hzero)
    (memLp_scaledThetaSourceModeU hstrip hzero)
  have hquantile := thetaRootEnergy_eq_integral_norm_sq_sourceModeU_div_mass_sq hstrip
  have hmass : thetaSource.mass ≠ 0 := thetaSource.mass_ne_zero
  have htime :
      (∫ y : ℝ, ‖sourceModeU thetaSource alpha y‖ ^ 2) =
        thetaSource.mass ^ 2 * thetaRootEnergy alpha := by
    calc
      (∫ y : ℝ, ‖sourceModeU thetaSource alpha y‖ ^ 2) =
          thetaSource.mass ^ 2 *
            ((∫ y : ℝ, ‖sourceModeU thetaSource alpha y‖ ^ 2) /
              thetaSource.mass ^ 2) := by field_simp
      _ = thetaSource.mass ^ 2 * thetaRootEnergy alpha := by rw [← hquantile]
  calc
    (∫ xi : ℝ, ‖completedXiFirstDividedFunction rho xi‖ ^ 2) =
        ∫ xi : ℝ, ‖(𝓕 (scaledThetaSourceModeU alpha)) xi‖ ^ 2 := hleft
    _ = ∫ x : ℝ, ‖scaledThetaSourceModeU alpha x‖ ^ 2 := hplancherel
    _ = 2 * Real.pi * ∫ y : ℝ, ‖sourceModeU thetaSource alpha y‖ ^ 2 :=
      integral_norm_sq_scaledThetaSourceModeU_eq alpha
    _ = 2 * Real.pi * thetaSource.mass ^ 2 * thetaRootEnergy alpha := by
      rw [htime]
      ring
    _ = 2 * Real.pi * thetaSource.mass ^ 2 *
        thetaRootEnergy (-xiSpectralPointSupport rho) := by rfl

/-- Hilbert-space form of the completed divided-energy identity. -/
theorem norm_sq_completedXiFirstDividedL2_eq_thetaRootEnergy (rho : XiDivisorSupport) :
    ‖completedXiFirstDividedL2 rho‖ ^ 2 =
      2 * Real.pi * thetaSource.mass ^ 2 *
        thetaRootEnergy (-xiSpectralPointSupport rho) := by
  rw [GaloisForLFunctions.RHTower.lp_norm_sq_eq_integral]
  calc
    (∫ x : ℝ, ‖(completedXiFirstDividedL2 rho : ℝ → ℂ) x‖ ^ 2) =
        ∫ x : ℝ, ‖completedXiFirstDividedFunction rho x‖ ^ 2 := by
      refine integral_congr_ae ?_
      filter_upwards [completedXiFirstDividedL2_ae rho] with x hx
      rw [hx]
    _ = 2 * Real.pi * thetaSource.mass ^ 2 *
        thetaRootEnergy (-xiSpectralPointSupport rho) :=
      integral_norm_sq_completedXiFirstDividedFunction_eq_thetaRootEnergy rho

end

end RHTower
