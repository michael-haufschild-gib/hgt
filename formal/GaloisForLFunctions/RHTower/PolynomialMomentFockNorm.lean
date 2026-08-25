import GaloisForLFunctions.RHTower.PolynomialMomentFock
import GaloisForLFunctions.HTGeometry.GutzmerEntire
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Exact weighted norm for the polynomial moment Fock carrier

Gutzmer's identity, Tonelli summation, and the complex polar change of variables identify the
coefficient carrier norm with the literal plane integral against
`exp (-2 (1 + |z|²)^(m/2)) dA`.  The proof also establishes integrability of the weighted square
density, rather than relying on the convention that a nonintegrable Bochner integral is zero.
-/

open Filter Topology Set MeasureTheory Complex
open scoped Real

namespace RHTower

noncomputable section

/-- Radial contribution of one Taylor coefficient to the exact polynomial Fock norm. -/
def polynomialMomentFockRadialTerm
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) (r : ℝ) : ℝ :=
  (2 * Real.pi *
      ‖momentFockCoefficient (polynomialMomentFockData m hm) f n‖ ^ 2) *
    polynomialFockMomentIntegrand m n r

theorem normSq_momentFockCoefficient_polynomial
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    ‖momentFockCoefficient (polynomialMomentFockData m hm) f n‖ ^ 2 =
      ‖f n‖ ^ 2 / polynomialFockMoment m n := by
  have hmoment := polynomialFockMoment_pos hm n
  have hsqrt : Real.sqrt (polynomialFockMoment m n) ≠ 0 :=
    (Real.sqrt_pos.2 hmoment).ne'
  rw [momentFockCoefficient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), div_pow]
  change ‖f n‖ ^ 2 / Real.sqrt (polynomialFockMoment m n) ^ 2 = _
  rw [Real.sq_sqrt hmoment.le]

theorem integrableOn_polynomialMomentFockRadialTerm
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    IntegrableOn (polynomialMomentFockRadialTerm m hm f n) (Ioi 0) := by
  exact (integrableOn_polynomialFockMomentIntegrand hm n).const_mul _

theorem integral_polynomialMomentFockRadialTerm
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    ∫ r in Ioi 0, polynomialMomentFockRadialTerm m hm f n r = ‖f n‖ ^ 2 := by
  unfold polynomialMomentFockRadialTerm
  rw [integral_const_mul, normSq_momentFockCoefficient_polynomial]
  have hmoment := polynomialFockMoment_pos hm n
  have hint : 0 < ∫ r in Ioi 0, polynomialFockMomentIntegrand m n r := by
    unfold polynomialFockMoment at hmoment
    nlinarith [Real.pi_pos]
  rw [polynomialFockMoment]
  field_simp [hint.ne']

theorem integral_norm_polynomialMomentFockRadialTerm
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (n : ℕ) :
    ∫ r in Ioi 0, ‖polynomialMomentFockRadialTerm m hm f n r‖ = ‖f n‖ ^ 2 := by
  calc
    ∫ r in Ioi 0, ‖polynomialMomentFockRadialTerm m hm f n r‖ =
        ∫ r in Ioi 0, polynomialMomentFockRadialTerm m hm f n r := by
      apply integral_congr_ae
      filter_upwards with r
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold polynomialMomentFockRadialTerm polynomialFockMomentIntegrand
      positivity
    _ = ‖f n‖ ^ 2 := integral_polynomialMomentFockRadialTerm m hm f n

theorem summable_integral_norm_polynomialMomentFockRadialTerm
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Summable fun n => ∫ r in Ioi 0, ‖polynomialMomentFockRadialTerm m hm f n r‖ := by
  simpa only [integral_norm_polynomialMomentFockRadialTerm m hm f] using
    HilbertSchmidt.summable_coe_sq f

theorem integral_tsum_polynomialMomentFockRadialTerm
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    ∫ r in Ioi 0, ∑' n, polynomialMomentFockRadialTerm m hm f n r = ‖f‖ ^ 2 := by
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (fun n => integrableOn_polynomialMomentFockRadialTerm m hm f n)
    (summable_integral_norm_polynomialMomentFockRadialTerm m hm f)
  calc
    ∫ r in Ioi 0, ∑' n, polynomialMomentFockRadialTerm m hm f n r =
        ∑' n, ∫ r in Ioi 0, polynomialMomentFockRadialTerm m hm f n r := hswap.symm
    _ = ∑' n, ‖f n‖ ^ 2 := by
      apply tsum_congr
      intro n
      exact integral_polynomialMomentFockRadialTerm m hm f n
    _ = ‖f‖ ^ 2 := (HilbertSchmidt.lp_norm_sq_eq f).symm

/-- Angular square norm times the exact radial Fock density and polar Jacobian. -/
def polynomialMomentFockPolarIntegrand
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (r : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..(2 * Real.pi),
      ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2) *
    Real.exp (-2 * polynomialFockPotential m r) * r

theorem polynomialMomentFockPolarIntegrand_eq_tsum
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) {r : ℝ} (hr : 0 < r) :
    polynomialMomentFockPolarIntegrand m hm f r =
      ∑' n, polynomialMomentFockRadialTerm m hm f n r := by
  let a : ℕ → ℂ := momentFockCoefficient (polynomialMomentFockData m hm) f
  have hg := GaloisForLFunctions.HTGeometry.hasSum_gutzmer_coeffFun
    (entireCoeffs_momentFockCoefficient (polynomialMomentFockData m hm) f) hr.le
  have hfun : GaloisForLFunctions.HTGeometry.coeffFun a =
      polynomialMomentFockFunction m hm f := by
    rfl
  have hang :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2) =
        (2 * Real.pi) * ∑' n, ‖a n‖ ^ 2 * r ^ (2 * n) := by
    rw [← hfun]
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          ‖GaloisForLFunctions.HTGeometry.coeffFun a (circleMap 0 r θ)‖ ^ 2) =
          (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
            ∫ θ in (0 : ℝ)..(2 * Real.pi),
              ‖GaloisForLFunctions.HTGeometry.coeffFun a (circleMap 0 r θ)‖ ^ 2) := by
        field_simp
      _ = (2 * Real.pi) * ∑' n, ‖a n‖ ^ 2 * r ^ (2 * n) := by
        rw [← hg.tsum_eq]
  rw [polynomialMomentFockPolarIntegrand, hang]
  have hterm :
      (fun n => polynomialMomentFockRadialTerm m hm f n r) =
        fun n => ((2 * Real.pi) * Real.exp (-2 * polynomialFockPotential m r) * r) *
          (‖a n‖ ^ 2 * r ^ (2 * n)) := by
    funext n
    unfold polynomialMomentFockRadialTerm polynomialFockMomentIntegrand a
    simp only [abs_of_pos hr, pow_succ]
    ring
  rw [hterm, tsum_mul_left]
  ring

/-- Polar-coordinate weighted square norm of the represented entire function. -/
def polynomialMomentFockPolarEnergy
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) : ℝ :=
  ∫ r in Ioi 0, polynomialMomentFockPolarIntegrand m hm f r

theorem polynomialMomentFockPolarEnergy_eq_normSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    polynomialMomentFockPolarEnergy m hm f = ‖f‖ ^ 2 := by
  unfold polynomialMomentFockPolarEnergy
  calc
    ∫ r in Ioi 0, polynomialMomentFockPolarIntegrand m hm f r =
        ∫ r in Ioi 0, ∑' n, polynomialMomentFockRadialTerm m hm f n r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact polynomialMomentFockPolarIntegrand_eq_tsum m hm f hr
    _ = ‖f‖ ^ 2 := integral_tsum_polynomialMomentFockRadialTerm m hm f

theorem integrableOn_polynomialMomentFockPolarIntegrand
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    IntegrableOn (polynomialMomentFockPolarIntegrand m hm f) (Ioi 0) := by
  have hsum : Integrable
      (fun r => ∑' n, polynomialMomentFockRadialTerm m hm f n r)
      (volume.restrict (Ioi 0)) :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      (fun n => integrableOn_polynomialMomentFockRadialTerm m hm f n)
      (summable_integral_norm_polynomialMomentFockRadialTerm m hm f)
  apply hsum.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (polynomialMomentFockPolarIntegrand_eq_tsum m hm f hr).symm

/-- Reconcile the standard polar chart range with one positive angular period. -/
theorem integral_Ioo_neg_pi_pi_eq_zero_two_pi
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

theorem periodic_polynomialMomentFockCircleNormSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (r : ℝ) :
    Function.Periodic
      (fun θ => ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2)
      (2 * Real.pi) := by
  intro θ
  change ‖polynomialMomentFockFunction m hm f (circleMap 0 r (θ + 2 * Real.pi))‖ ^ 2 = _
  have hcircle : circleMap 0 r (θ + 2 * Real.pi) = circleMap 0 r θ := by
    simp [circleMap, add_mul, Complex.exp_add, Complex.exp_mul_I]
  rw [hcircle]

theorem integral_Ioo_polynomialMomentFockCircleNormSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (r : ℝ) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2 :=
  integral_Ioo_neg_pi_pi_eq_zero_two_pi
    (periodic_polynomialMomentFockCircleNormSq m hm f r)

/-- Nonnegative weighted norm density in the standard complex polar chart. -/
def polynomialMomentFockPolarChartIntegrand
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (p : ℝ × ℝ) : ℝ :=
  ‖polynomialMomentFockFunction m hm f (circleMap 0 p.1 p.2)‖ ^ 2 *
    Real.exp (-2 * polynomialFockPotential m p.1) * p.1

theorem integrableOn_polynomialMomentFockPolarChartIntegrand_slice
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (r : ℝ) :
    IntegrableOn (fun θ => polynomialMomentFockPolarChartIntegrand m hm f (r, θ))
      (Ioo (-Real.pi) Real.pi) := by
  have hcont : Continuous
      (fun θ => polynomialMomentFockPolarChartIntegrand m hm f (r, θ)) := by
    unfold polynomialMomentFockPolarChartIntegrand
    change Continuous (fun θ =>
      ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2 *
        Real.exp (-2 * polynomialFockPotential m r) * r)
    exact (((differentiable_polynomialMomentFockFunction m hm f).continuous.comp
      (continuous_circleMap 0 r)).norm.pow 2).mul continuous_const |>.mul continuous_const
  apply (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
  exact Ioo_subset_Icc_self

theorem integral_norm_polynomialMomentFockPolarChartIntegrand_slice
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖polynomialMomentFockPolarChartIntegrand m hm f (r, θ)‖) =
      polynomialMomentFockPolarIntegrand m hm f r := by
  calc
    (∫ θ in Ioo (-Real.pi) Real.pi,
        ‖polynomialMomentFockPolarChartIntegrand m hm f (r, θ)‖) =
        ∫ θ in Ioo (-Real.pi) Real.pi,
          polynomialMomentFockPolarChartIntegrand m hm f (r, θ) := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold polynomialMomentFockPolarChartIntegrand
      positivity
    _ = (∫ θ in Ioo (-Real.pi) Real.pi,
          ‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2) *
          Real.exp (-2 * polynomialFockPotential m r) * r := by
      unfold polynomialMomentFockPolarChartIntegrand
      change (∫ θ in Ioo (-Real.pi) Real.pi,
        (‖polynomialMomentFockFunction m hm f (circleMap 0 r θ)‖ ^ 2 *
          Real.exp (-2 * polynomialFockPotential m r)) * r) = _
      rw [integral_mul_const, integral_mul_const]
    _ = polynomialMomentFockPolarIntegrand m hm f r := by
      rw [integral_Ioo_polynomialMomentFockCircleNormSq]
      rfl

theorem integral_polynomialMomentFockPolarChartIntegrand_slice
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) {r : ℝ} (hr : 0 < r) :
    (∫ θ in Ioo (-Real.pi) Real.pi,
        polynomialMomentFockPolarChartIntegrand m hm f (r, θ)) =
      polynomialMomentFockPolarIntegrand m hm f r := by
  calc
    (∫ θ in Ioo (-Real.pi) Real.pi,
        polynomialMomentFockPolarChartIntegrand m hm f (r, θ)) =
        ∫ θ in Ioo (-Real.pi) Real.pi,
          ‖polynomialMomentFockPolarChartIntegrand m hm f (r, θ)‖ := by
      apply integral_congr_ae
      filter_upwards with θ
      rw [Real.norm_eq_abs, abs_of_nonneg]
      unfold polynomialMomentFockPolarChartIntegrand
      positivity
    _ = polynomialMomentFockPolarIntegrand m hm f r :=
      integral_norm_polynomialMomentFockPolarChartIntegrand_slice m hm f hr

theorem continuous_polynomialMomentFockPolarChartIntegrand
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Continuous (polynomialMomentFockPolarChartIntegrand m hm f) := by
  have hcircle : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
    rw [show (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) =
        fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp (p.2 * Complex.I) from by
      funext p
      simp [circleMap]]
    exact (Complex.continuous_ofReal.comp continuous_fst).mul
      (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
  have hweight : Continuous
      (fun p : ℝ × ℝ => Real.exp (-2 * polynomialFockPotential m p.1)) :=
    Real.continuous_exp.comp
      (continuous_const.mul ((continuous_polynomialFockPotential m).comp continuous_fst))
  unfold polynomialMomentFockPolarChartIntegrand
  exact (((differentiable_polynomialMomentFockFunction m hm f).continuous.comp hcircle).norm.pow 2)
    |>.mul hweight |>.mul continuous_fst

theorem integrable_polynomialMomentFockPolarChartIntegrand_restrict_prod
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Integrable (polynomialMomentFockPolarChartIntegrand m hm f)
      ((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  rw [integrable_prod_iff
    (continuous_polynomialMomentFockPolarChartIntegrand m hm f).aestronglyMeasurable]
  constructor
  · exact ae_of_all _ fun r =>
      integrableOn_polynomialMomentFockPolarChartIntegrand_slice m hm f r
  · have hpolar := integrableOn_polynomialMomentFockPolarIntegrand m hm f
    apply hpolar.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (integral_norm_polynomialMomentFockPolarChartIntegrand_slice m hm f hr).symm

theorem integral_polynomialMomentFockPolarChartIntegrand_restrict_prod
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    (∫ p : ℝ × ℝ, polynomialMomentFockPolarChartIntegrand m hm f p
      ∂((volume.restrict (Ioi 0)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)))) = ‖f‖ ^ 2 := by
  rw [MeasureTheory.integral_prod _
    (integrable_polynomialMomentFockPolarChartIntegrand_restrict_prod m hm f)]
  calc
    (∫ r in Ioi 0, ∫ θ in Ioo (-Real.pi) Real.pi,
        polynomialMomentFockPolarChartIntegrand m hm f (r, θ)) =
        ∫ r in Ioi 0, polynomialMomentFockPolarIntegrand m hm f r := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact integral_polynomialMomentFockPolarChartIntegrand_slice m hm f hr
    _ = ‖f‖ ^ 2 := polynomialMomentFockPolarEnergy_eq_normSq m hm f

/-- Literal weighted square density on the complex plane. -/
def polynomialMomentFockWeightedNormSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) : ℝ :=
  ‖polynomialMomentFockFunction m hm f z‖ ^ 2 *
    Real.exp (-2 * polynomialFockPotential m ‖z‖)

theorem continuous_polynomialMomentFockWeightedNormSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Continuous (polynomialMomentFockWeightedNormSq m hm f) := by
  unfold polynomialMomentFockWeightedNormSq
  exact ((differentiable_polynomialMomentFockFunction m hm f).continuous.norm.pow 2).mul
    (Real.continuous_exp.comp
      (continuous_const.mul ((continuous_polynomialFockPotential m).comp continuous_norm)))

theorem polynomialMomentFockWeightedNormSq_nonneg
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) (z : ℂ) :
    0 ≤ polynomialMomentFockWeightedNormSq m hm f z := by
  unfold polynomialMomentFockWeightedNormSq
  positivity

theorem polynomialMomentFockPolarChartIntegrand_eq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock)
    {p : ℝ × ℝ} (hp : p ∈ Complex.polarCoord.target) :
    p.1 • polynomialMomentFockWeightedNormSq m hm f (Complex.polarCoord.symm p) =
      polynomialMomentFockPolarChartIntegrand m hm f p := by
  rw [Complex.polarCoord_target] at hp
  have hr : 0 < p.1 := hp.1
  have hnorm : ‖Complex.polarCoord.symm p‖ = p.1 := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
  have hpoint : Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
    rw [Complex.polarCoord_symm_apply, circleMap, zero_add, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  unfold polynomialMomentFockWeightedNormSq polynomialMomentFockPolarChartIntegrand
  rw [hnorm, hpoint, smul_eq_mul]
  ring

theorem integrable_polynomialMomentFockWeightedNormSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    Integrable (polynomialMomentFockWeightedNormSq m hm f) := by
  refine ⟨(continuous_polynomialMomentFockWeightedNormSq m hm f).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal
    (ae_of_all _ (polynomialMomentFockWeightedNormSq_nonneg m hm f))]
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have hchart :=
    integrable_polynomialMomentFockPolarChartIntegrand_restrict_prod m hm f
  calc
    (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 •
          ENNReal.ofReal
            (polynomialMomentFockWeightedNormSq m hm f (Complex.polarCoord.symm p))) =
        ∫⁻ p : ℝ × ℝ,
          ‖polynomialMomentFockPolarChartIntegrand m hm f p‖ₑ
          ∂((volume.restrict (Ioi 0)).prod
            (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
      rw [Complex.polarCoord_target]
      calc
        (∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
            ENNReal.ofReal p.1 •
              ENNReal.ofReal
                (polynomialMomentFockWeightedNormSq m hm f (Complex.polarCoord.symm p))) =
            ∫⁻ p in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
              ‖polynomialMomentFockPolarChartIntegrand m hm f p‖ₑ := by
          apply setLIntegral_congr_fun
            (measurableSet_Ioi.prod measurableSet_Ioo)
          intro p hp
          have hr : 0 ≤ p.1 := hp.1.le
          have hnonneg : 0 ≤ polynomialMomentFockPolarChartIntegrand m hm f p := by
            unfold polynomialMomentFockPolarChartIntegrand
            positivity
          change ENNReal.ofReal p.1 *
              ENNReal.ofReal (polynomialMomentFockWeightedNormSq m hm f
                (Complex.polarCoord.symm p)) =
            ‖polynomialMomentFockPolarChartIntegrand m hm f p‖ₑ
          rw [← ENNReal.ofReal_mul hr,
            show p.1 * polynomialMomentFockWeightedNormSq m hm f
                (Complex.polarCoord.symm p) =
                polynomialMomentFockPolarChartIntegrand m hm f p by
              simpa only [smul_eq_mul] using
                polynomialMomentFockPolarChartIntegrand_eq m hm f hp,
            ← Real.enorm_eq_ofReal hnonneg]
        _ = ∫⁻ p : ℝ × ℝ,
            ‖polynomialMomentFockPolarChartIntegrand m hm f p‖ₑ
            ∂((volume.restrict (Ioi 0)).prod
              (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
          rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    _ < ⊤ := hchart.hasFiniteIntegral

/-- Coefficient norm equals the literal weighted plane norm of its represented entire function. -/
theorem integral_polynomialMomentFockWeightedNormSq
    (m : ℝ) (hm : 2 ≤ m) (f : MomentFock) :
    (∫ z : ℂ, polynomialMomentFockWeightedNormSq m hm f z) = ‖f‖ ^ 2 := by
  have hpolar := Complex.integral_comp_polarCoord_symm
    (polynomialMomentFockWeightedNormSq m hm f)
  rw [← hpolar, polarCoord_target]
  calc
    (∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • polynomialMomentFockWeightedNormSq m hm f (Complex.polarCoord.symm p)) =
        ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
          polynomialMomentFockPolarChartIntegrand m hm f p := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
      exact polynomialMomentFockPolarChartIntegrand_eq m hm f hp
    _ = ∫ p : ℝ × ℝ, polynomialMomentFockPolarChartIntegrand m hm f p
        ∂((volume.restrict (Ioi 0)).prod
          (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    _ = ‖f‖ ^ 2 :=
      integral_polynomialMomentFockPolarChartIntegrand_restrict_prod m hm f

end

end RHTower
