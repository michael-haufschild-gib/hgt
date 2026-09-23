import GaloisForLFunctions.RHTower.RapidExponentialMomentFock
import GaloisForLFunctions.HTGeometry.GutzmerEntire
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Exact weighted norm for the rapid exponential moment Fock carrier

Gutzmer's identity, Tonelli summation, and the complex polar change of variables identify the
coefficient carrier norm with the literal plane integral against
`exp (-2 exp (2 a |z|)) dA`.  The proof also establishes integrability of the weighted square
density, rather than relying on the convention that a nonintegrable Bochner integral is zero.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real

namespace RHTower

noncomputable section

/-- Radial contribution of one Taylor coefficient to the exact rapid Fock norm. -/
def rapidExponentialMomentFockRadialTerm
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.pi *
      ‖momentFockCoefficient (rapidExponentialMomentFockData a ha) f n‖ ^ 2) *
    rapidExponentialFockMomentIntegrand a n r

theorem normSq_momentFockCoefficient_rapidExponential
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    ‖momentFockCoefficient (rapidExponentialMomentFockData a ha) f n‖ ^ 2 =
      ‖f n‖ ^ 2 / rapidExponentialFockMoment a n := by
  have hmoment := rapidExponentialFockMoment_pos ha n
  have hsqrt : Real.sqrt (rapidExponentialFockMoment a n) ≠ 0 :=
    (Real.sqrt_pos.2 hmoment).ne'
  rw [momentFockCoefficient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow]
  change ‖f n‖ ^ 2 / Real.sqrt (rapidExponentialFockMoment a n) ^ 2 = _
  rw [Real.sq_sqrt hmoment.le]

theorem integrableOn_rapidExponentialMomentFockRadialTerm
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    IntegrableOn (rapidExponentialMomentFockRadialTerm a ha f n) (Ioi 0) := by
  exact (integrableOn_rapidExponentialFockMomentIntegrand ha n).const_mul _

theorem integral_rapidExponentialMomentFockRadialTerm
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    ∫ r in Ioi 0, rapidExponentialMomentFockRadialTerm a ha f n r = ‖f n‖ ^ 2 := by
  unfold rapidExponentialMomentFockRadialTerm
  rw [integral_const_mul, normSq_momentFockCoefficient_rapidExponential]
  have hmoment := rapidExponentialFockMoment_pos ha n
  have hint : 0 < ∫ r in Ioi 0, rapidExponentialFockMomentIntegrand a n r := by
    unfold rapidExponentialFockMoment at hmoment
    nlinarith [Real.pi_pos]
  rw [rapidExponentialFockMoment]
  field_simp [hint.ne']

theorem integral_norm_rapidExponentialMomentFockRadialTerm
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (n : ℕ) :
    ∫ r in Ioi 0, ‖rapidExponentialMomentFockRadialTerm a ha f n r‖ = ‖f n‖ ^ 2 := by
  calc
    ∫ r in Ioi 0, ‖rapidExponentialMomentFockRadialTerm a ha f n r‖ =
        ∫ r in Ioi 0, rapidExponentialMomentFockRadialTerm a ha f n r := by
      apply integral_congr_ae
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold rapidExponentialMomentFockRadialTerm rapidExponentialFockMomentIntegrand
      positivity
    _ = ‖f n‖ ^ 2 := integral_rapidExponentialMomentFockRadialTerm a ha f n

theorem summable_integral_norm_rapidExponentialMomentFockRadialTerm
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    Summable fun n => ∫ r in Ioi 0, ‖rapidExponentialMomentFockRadialTerm a ha f n r‖ := by
  simpa only [integral_norm_rapidExponentialMomentFockRadialTerm a ha f] using
    HilbertSchmidt.summable_coe_sq f

theorem integral_tsum_rapidExponentialMomentFockRadialTerm
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    ∫ r in Ioi 0, ∑' n, rapidExponentialMomentFockRadialTerm a ha f n r = ‖f‖ ^ 2 := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => integrableOn_rapidExponentialMomentFockRadialTerm a ha f n)
    (summable_integral_norm_rapidExponentialMomentFockRadialTerm a ha f)
  calc
    ∫ r in Ioi 0, ∑' n, rapidExponentialMomentFockRadialTerm a ha f n r =
        ∑' n, ∫ r in Ioi 0, rapidExponentialMomentFockRadialTerm a ha f n r := hswap.symm
    _ = ∑' n, ‖f n‖ ^ 2 := by
      apply tsum_congr
      intro n
      exact integral_rapidExponentialMomentFockRadialTerm a ha f n
    _ = ‖f‖ ^ 2 := (HilbertSchmidt.lp_norm_sq_eq f).symm

/-- Angular square norm times the exact radial Fock density and polar Jacobian. -/
def rapidExponentialMomentFockPolarIntegrand
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (r : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..(2 * Real.pi),
      ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2) *
    Real.exp (-2 * rapidExponentialFockPotential a r) * r

theorem rapidExponentialMomentFockPolarIntegrand_eq_tsum
    (a : ℝ) (ha : 0 < a) (f : MomentFock) {r : ℝ} (hr : 0 < r) :
    rapidExponentialMomentFockPolarIntegrand a ha f r =
      ∑' n, rapidExponentialMomentFockRadialTerm a ha f n r := by
  let coeff : ℕ → ℂ := momentFockCoefficient (rapidExponentialMomentFockData a ha) f
  have hg := GaloisForLFunctions.HTGeometry.hasSum_gutzmer_coeffFun
    (entireCoeffs_momentFockCoefficient (rapidExponentialMomentFockData a ha) f) hr.le
  have hfun : GaloisForLFunctions.HTGeometry.coeffFun coeff =
      rapidExponentialMomentFockFunction a ha f := by
    rfl
  have hang :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2) =
        (2 * Real.pi) * ∑' n, ‖coeff n‖ ^ 2 * r ^ (2 * n) := by
    rw [← hfun]
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖GaloisForLFunctions.HTGeometry.coeffFun coeff (circleMap 0 r θ)‖ ^ 2) =
          (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              ‖GaloisForLFunctions.HTGeometry.coeffFun coeff (circleMap 0 r θ)‖ ^ 2) := by
        field_simp
      _ = (2 * Real.pi) * ∑' n, ‖coeff n‖ ^ 2 * r ^ (2 * n) := by
        rw [← hg.tsum_eq]
  rw [rapidExponentialMomentFockPolarIntegrand, hang]
  have hterm :
      (fun n => rapidExponentialMomentFockRadialTerm a ha f n r) =
        fun n => ((2 * Real.pi) * Real.exp (-2 * rapidExponentialFockPotential a r) * r) *
          (‖coeff n‖ ^ 2 * r ^ (2 * n)) := by
    funext n
    unfold rapidExponentialMomentFockRadialTerm rapidExponentialFockMomentIntegrand coeff
    simp only [abs_of_pos hr, pow_succ]
    ring
  rw [hterm, tsum_mul_left]
  ring

/-- Polar-coordinate weighted square norm of the represented entire function. -/
def rapidExponentialMomentFockPolarEnergy
    (a : ℝ) (ha : 0 < a) (f : MomentFock) : ℝ :=
  ∫ r in Ioi 0, rapidExponentialMomentFockPolarIntegrand a ha f r

theorem rapidExponentialMomentFockPolarEnergy_eq_normSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    rapidExponentialMomentFockPolarEnergy a ha f = ‖f‖ ^ 2 := by
  unfold rapidExponentialMomentFockPolarEnergy
  calc
    ∫ r in Ioi 0, rapidExponentialMomentFockPolarIntegrand a ha f r =
        ∫ r in Ioi 0, ∑' n, rapidExponentialMomentFockRadialTerm a ha f n r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact rapidExponentialMomentFockPolarIntegrand_eq_tsum a ha f hr
    _ = ‖f‖ ^ 2 := integral_tsum_rapidExponentialMomentFockRadialTerm a ha f

theorem integrableOn_rapidExponentialMomentFockPolarIntegrand
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    IntegrableOn (rapidExponentialMomentFockPolarIntegrand a ha f) (Ioi 0) := by
  have hsum : Integrable
      (fun r => ∑' n, rapidExponentialMomentFockRadialTerm a ha f n r)
      (volume.restrict (Ioi 0)) :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      (fun n => integrableOn_rapidExponentialMomentFockRadialTerm a ha f n)
      (summable_integral_norm_rapidExponentialMomentFockRadialTerm a ha f)
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (rapidExponentialMomentFockPolarIntegrand_eq_tsum a ha f hr).symm

/-- Reconcile the standard polar chart range with one positive angular period. -/
theorem integral_Ioo_neg_pi_pi_eq_zero_two_pi_rapidExponentialMomentFockNorm
    {g : ℝ → ℝ} (hper : Function.Periodic g (2 * Real.pi)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
  have hset : (∫ θ in Ioo (-Real.pi) Real.pi, g θ) =
      ∫ θ in (-Real.pi)..Real.pi, g θ := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    exact setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [hset]
  have hshift := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at hshift
  exact hshift

theorem periodic_rapidExponentialMomentFockCircleNormSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (r : ℝ) :
    Function.Periodic
      (fun θ => ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2)
      (2 * Real.pi) := by
  intro θ
  change ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r (θ + 2 * Real.pi))‖ ^ 2 = _
  have hcircle : circleMap 0 r (θ + 2 * Real.pi) = circleMap 0 r θ := by
    simp [circleMap, add_mul, Complex.exp_add, Complex.exp_mul_I]
  rw [hcircle]

theorem integral_Ioo_rapidExponentialMomentFockCircleNormSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2 :=
  integral_Ioo_neg_pi_pi_eq_zero_two_pi_rapidExponentialMomentFockNorm
    (periodic_rapidExponentialMomentFockCircleNormSq a ha f r)

/-- Nonnegative weighted norm density in the standard complex polar chart. -/
def rapidExponentialMomentFockPolarChartIntegrand
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (p : ℝ × ℝ) : ℝ :=
  ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 p.1 p.2)‖ ^ 2 *
    Real.exp (-2 * rapidExponentialFockPotential a p.1) * p.1

theorem integrableOn_rapidExponentialMomentFockPolarChartIntegrand_slice
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (r : ℝ) :
    IntegrableOn (fun θ => rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ))
      (Ioo (-Real.pi) Real.pi) := by
  have hcont : Continuous
      (fun θ => rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)) := by
    unfold rapidExponentialMomentFockPolarChartIntegrand
    change Continuous (fun θ =>
      ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2 *
        Real.exp (-2 * rapidExponentialFockPotential a r) * r)
    exact (((differentiable_rapidExponentialMomentFockFunction a ha f).continuous.comp
      (continuous_circleMap 0 r)).norm.pow 2).mul continuous_const |>.mul continuous_const
  apply (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
  exact Ioo_subset_Icc_self

theorem integral_norm_rapidExponentialMomentFockPolarChartIntegrand_slice
    (a : ℝ) (ha : 0 < a) (f : MomentFock) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)‖) =
      rapidExponentialMomentFockPolarIntegrand a ha f r := by
  calc
    (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)‖) =
        ∫ θ in Ioo (-Real.pi) Real.pi,
          rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ) := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold rapidExponentialMomentFockPolarChartIntegrand
      positivity
    _ = (∫ θ in Ioo (-Real.pi) Real.pi,
          ‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2) *
          Real.exp (-2 * rapidExponentialFockPotential a r) * r := by
      unfold rapidExponentialMomentFockPolarChartIntegrand
      change (∫ θ in Ioo (-Real.pi) Real.pi,
        (‖rapidExponentialMomentFockFunction a ha f (circleMap 0 r θ)‖ ^ 2 *
          Real.exp (-2 * rapidExponentialFockPotential a r)) * r) = _
      rw [integral_mul_const, integral_mul_const]
    _ = rapidExponentialMomentFockPolarIntegrand a ha f r := by
      rw [integral_Ioo_rapidExponentialMomentFockCircleNormSq]
      rfl

theorem integral_rapidExponentialMomentFockPolarChartIntegrand_slice
    (a : ℝ) (ha : 0 < a) (f : MomentFock) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)) =
      rapidExponentialMomentFockPolarIntegrand a ha f r := by
  calc
    (∫ θ in Ioo (-Real.pi) Real.pi,
        rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)) =
        ∫ θ in Ioo (-Real.pi) Real.pi,
          ‖rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)‖ := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold rapidExponentialMomentFockPolarChartIntegrand
      positivity
    _ = rapidExponentialMomentFockPolarIntegrand a ha f r :=
      integral_norm_rapidExponentialMomentFockPolarChartIntegrand_slice a ha f hr

theorem continuous_rapidExponentialMomentFockPolarChartIntegrand
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    Continuous (rapidExponentialMomentFockPolarChartIntegrand a ha f) := by
  have hcircle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) from by
      funext p
      simp [circleMap]]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hweight : Continuous
      (fun p : ℝ × ℝ => Real.exp (-2 * rapidExponentialFockPotential a p.1)) :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_rapidExponentialFockPotential a).comp continuous_fst))
  unfold rapidExponentialMomentFockPolarChartIntegrand
  exact (((differentiable_rapidExponentialMomentFockFunction a ha f).continuous.comp hcircle).norm.pow 2)
    |>.mul hweight |>.mul continuous_fst

theorem integrable_rapidExponentialMomentFockPolarChartIntegrand_restrict_prod
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    Integrable (rapidExponentialMomentFockPolarChartIntegrand a ha f)
      ((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  rw [integrable_prod_iff
    (continuous_rapidExponentialMomentFockPolarChartIntegrand a ha f).aestronglyMeasurable]
  constructor
  · exact ae_of_all _ fun r =>
      integrableOn_rapidExponentialMomentFockPolarChartIntegrand_slice a ha f r
  · have hpolar := integrableOn_rapidExponentialMomentFockPolarIntegrand a ha f
    apply hpolar.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (integral_norm_rapidExponentialMomentFockPolarChartIntegrand_slice a ha f hr).symm

theorem integral_rapidExponentialMomentFockPolarChartIntegrand_restrict_prod
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    (∫ p : ℝ × ℝ, rapidExponentialMomentFockPolarChartIntegrand a ha f p
      ∂((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)))) = ‖f‖ ^ 2 := by
  rw [MeasureTheory.integral_prod _
    (integrable_rapidExponentialMomentFockPolarChartIntegrand_restrict_prod a ha f)]
  calc
    (∫ r in Ioi 0, ∫ θ in Ioo (-Real.pi) Real.pi,
        rapidExponentialMomentFockPolarChartIntegrand a ha f (r, θ)) =
        ∫ r in Ioi 0, rapidExponentialMomentFockPolarIntegrand a ha f r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact integral_rapidExponentialMomentFockPolarChartIntegrand_slice a ha f hr
    _ = ‖f‖ ^ 2 := rapidExponentialMomentFockPolarEnergy_eq_normSq a ha f

/-- Literal weighted square density on the complex plane. -/
def rapidExponentialMomentFockWeightedNormSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (z : ℂ) : ℝ :=
  ‖rapidExponentialMomentFockFunction a ha f z‖ ^ 2 *
    Real.exp (-2 * rapidExponentialFockPotential a ‖z‖)

theorem continuous_rapidExponentialMomentFockWeightedNormSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    Continuous (rapidExponentialMomentFockWeightedNormSq a ha f) := by
  unfold rapidExponentialMomentFockWeightedNormSq
  exact ((differentiable_rapidExponentialMomentFockFunction a ha f).continuous.norm.pow 2).mul
    (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_rapidExponentialFockPotential a).comp continuous_norm)))

theorem rapidExponentialMomentFockWeightedNormSq_nonneg
    (a : ℝ) (ha : 0 < a) (f : MomentFock) (z : ℂ) :
    0 ≤ rapidExponentialMomentFockWeightedNormSq a ha f z := by
  unfold rapidExponentialMomentFockWeightedNormSq
  positivity

theorem rapidExponentialMomentFockPolarChartIntegrand_eq
    (a : ℝ) (ha : 0 < a) (f : MomentFock)
    {p : ℝ × ℝ} (hp : p ∈ Complex.polarCoord.target) :
    p.1 • rapidExponentialMomentFockWeightedNormSq a ha f (Complex.polarCoord.symm p) =
      rapidExponentialMomentFockPolarChartIntegrand a ha f p := by
  rw [Complex.polarCoord_target] at hp
  have hr : 0 < p.1 := hp.1
  have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
  have hpoint : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  unfold rapidExponentialMomentFockWeightedNormSq rapidExponentialMomentFockPolarChartIntegrand
  rw [hnorm, hpoint, smul_eq_mul]
  ring

theorem integrable_rapidExponentialMomentFockWeightedNormSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    Integrable (rapidExponentialMomentFockWeightedNormSq a ha f) := by
  refine ⟨(continuous_rapidExponentialMomentFockWeightedNormSq a ha f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (rapidExponentialMomentFockWeightedNormSq_nonneg a ha f))]
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hchart :=
    integrable_rapidExponentialMomentFockPolarChartIntegrand_restrict_prod a ha f
  calc
    (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 •
          ENNReal.ofReal
            (rapidExponentialMomentFockWeightedNormSq a ha f (Complex.polarCoord.symm p))) =
        ∫⁻ p : ℝ × ℝ,
          ‖rapidExponentialMomentFockPolarChartIntegrand a ha f p‖ₑ
          ∂((volume.restrict (Ioi 0)).prod
            (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
      rw [Complex.polarCoord_target]
      calc
        (∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 •
              ENNReal.ofReal
                (rapidExponentialMomentFockWeightedNormSq a ha f (Complex.polarCoord.symm p))) =
            ∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
              ‖rapidExponentialMomentFockPolarChartIntegrand a ha f p‖ₑ := by
          apply setLIntegral_congr_fun
            (measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          have hr : 0 ≤ p.1 := hp.1.le
          have hnonneg : 0 ≤ rapidExponentialMomentFockPolarChartIntegrand a ha f p := by
            unfold rapidExponentialMomentFockPolarChartIntegrand
            positivity
          change ENNReal.ofReal p.1 *
              ENNReal.ofReal (rapidExponentialMomentFockWeightedNormSq a ha f
                (Complex.polarCoord.symm p)) =
            ‖rapidExponentialMomentFockPolarChartIntegrand a ha f p‖ₑ
          rw [← ENNReal.ofReal_mul hr,
            show p.1 * rapidExponentialMomentFockWeightedNormSq a ha f
                (Complex.polarCoord.symm p) =
                rapidExponentialMomentFockPolarChartIntegrand a ha f p by
              simpa only [smul_eq_mul] using
                rapidExponentialMomentFockPolarChartIntegrand_eq a ha f hp,
            ← Real.enorm_eq_ofReal hnonneg]
        _ = ∫⁻ p : ℝ × ℝ,
            ‖rapidExponentialMomentFockPolarChartIntegrand a ha f p‖ₑ
            ∂((volume.restrict (Ioi 0)).prod
              (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
          rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    _ < ⊤ := hchart.hasFiniteIntegral

/-- Coefficient norm equals the literal weighted plane norm of its represented entire function. -/
theorem integral_rapidExponentialMomentFockWeightedNormSq
    (a : ℝ) (ha : 0 < a) (f : MomentFock) :
    (∫ z : ℂ, rapidExponentialMomentFockWeightedNormSq a ha f z) = ‖f‖ ^ 2 := by
  have hpolar := Complex.integral_comp_polarCoord_symm
    (rapidExponentialMomentFockWeightedNormSq a ha f)
  rw [← hpolar, polarCoord_target]
  calc
    (∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • rapidExponentialMomentFockWeightedNormSq a ha f (Complex.polarCoord.symm p)) =
        ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
          rapidExponentialMomentFockPolarChartIntegrand a ha f p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
      exact rapidExponentialMomentFockPolarChartIntegrand_eq a ha f hp
    _ = ∫ p : ℝ × ℝ, rapidExponentialMomentFockPolarChartIntegrand a ha f p
        ∂((volume.restrict (Ioi 0)).prod
          (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    _ = ‖f‖ ^ 2 :=
      integral_rapidExponentialMomentFockPolarChartIntegrand_restrict_prod a ha f

end

end RHTower
