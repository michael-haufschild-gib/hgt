import GaloisForLFunctions.HTGeometry.PhaseSurvivalProfile
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import GaloisForLFunctions.HTGeometry.ExponentialWallBurnolPartner

/-!
# The phase coherence integral of the cubic wall

For the squared cubic coherence `κ(x, y)² = 64 x³y³/(x + y)⁶` and the unit exponential law `μ`,

`∬ κ(x, y)² cos(τ(x - y)) μ(dx) μ(dy) = 6 ∫₀¹ v²(1 - v²)²/(1 + τ²v²) dv = C(τ)`.

The ratio substitution `y = xt` and the complex Gamma integral `∫₀^∞ x e^{-cx} dx = 1/c²` reduce
the complex phase integral to `∫₀^∞ R(t)/c_τ(t)² dt` with `R(t) = 64t³/(1 + t)⁶` and
`c_τ(t) = (1 + t) - iτ(1 - t)`; the Cayley substitution `t = (1 - v)/(1 + v)` turns its real part
into `½ ∫₋₁¹ (1 - v²)³(1 - τ²v²)/(1 + τ²v²)² dv`, and one integration by parts against
`d/dv [v/(1 + τ²v²)]` gives the profile.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_phase : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-- The complex phase coherence `κ(x, y)² e^{iτ(x - y)}`. -/
def phaseCoherence (τ : ℝ) (z : ℝ × ℝ) : ℂ :=
  (routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 : ℂ) *
    Complex.exp (((τ * (z.1 - z.2) : ℝ) : ℂ) * Complex.I)

/-- The phase rate `c_τ(t) = (1 + t) - iτ(1 - t)`. -/
def phaseRate (τ t : ℝ) : ℂ := ((1 + t : ℝ) : ℂ) - ((τ * (1 - t) : ℝ) : ℂ) * Complex.I

theorem phaseRate_re (τ t : ℝ) : (phaseRate τ t).re = 1 + t := by
  simp [phaseRate]

theorem measurable_phaseCoherence (τ : ℝ) : Measurable (phaseCoherence τ) := by
  unfold phaseCoherence routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
  fun_prop

theorem integrable_phaseCoherence (τ : ℝ) :
    Integrable (phaseCoherence τ) ((expMeasure 1).prod (expMeasure 1)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_phaseCoherence τ).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg_fst_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero,
    ae_nonneg_snd_prod (expMeasure 1) (expMeasure 1) expMeasure_one_Iio_zero] with z h1 h2
  have h := routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one h1 h2
  rw [phaseCoherence, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

/-- The phase integrand in ratio coordinates. -/
def ratioPhaseIntegrand (τ x t : ℝ) : ℂ :=
  (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t : ℂ) *
    ((x : ℂ) ^ 1 * Complex.exp (-(phaseRate τ t * x)))

theorem inner_phaseCoherence_ratio (τ : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.exp (-x) • ∫ y, phaseCoherence τ (x, y) ∂(expMeasure 1)
      = ∫ t in Ioi (0 : ℝ), ratioPhaseIntegrand τ x t := by
  rw [integral_expMeasure_one]
  have h := integral_comp_mul_left_Ioi
    (fun y : ℝ => Real.exp (-y) • phaseCoherence τ (x, y)) 0 hx
  simp only [mul_zero] at h
  rw [show (∫ y in Ioi (0 : ℝ), Real.exp (-y) • phaseCoherence τ (x, y))
      = x • ∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) • phaseCoherence τ (x, x * t) by
    rw [h, smul_smul, mul_inv_cancel₀ hx.ne', one_smul], smul_smul, ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [ratioPhaseIntegrand, phaseCoherence]
  rw [routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_scale_right hx,
    Complex.real_smul, Complex.real_smul]
  push_cast
  have hexp : Complex.exp (-(x : ℂ)) * Complex.exp (-((x : ℂ) * t)) *
      Complex.exp ((τ : ℂ) * ((x : ℂ) - x * t) * Complex.I)
      = Complex.exp (-(phaseRate τ t * x)) := by
    rw [← Complex.exp_add, ← Complex.exp_add, phaseRate]
    congr 1
    push_cast
    ring
  rw [← hexp]
  ring

theorem norm_ratioPhaseIntegrand (τ : ℝ) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    ‖ratioPhaseIntegrand τ x t‖
      = routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * x *
          Real.exp (-((1 + t) * x)) := by
  rw [ratioPhaseIntegrand, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg ht), pow_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx, Complex.norm_exp, ← mul_assoc]
  congr 2
  simp [phaseRate, Complex.mul_re]

theorem integrable_ratioPhaseIntegrand (τ : ℝ) :
    Integrable (Function.uncurry (ratioPhaseIntegrand τ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  refine integrable_ratio_radial_prod.mono' ?_ ?_
  · unfold ratioPhaseIntegrand phaseRate routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
    exact (by fun_prop : Measurable _).aestronglyMeasurable
  · rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    exact (norm_ratioPhaseIntegrand τ (le_of_lt hp.1) (le_of_lt hp.2)).le

/-- **Ratio reduction.**  `∬ κ² e^{iτ(x-y)} dμ dμ = ∫₀^∞ R(t)/c_τ(t)² dt`. -/
theorem integral_phaseCoherence (τ : ℝ) :
    ∫ z, phaseCoherence τ z ∂((expMeasure 1).prod (expMeasure 1))
      = ∫ t in Ioi (0 : ℝ), (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t : ℂ) *
          (1 / phaseRate τ t ^ 2) := by
  rw [integral_prod _ (integrable_phaseCoherence τ), integral_expMeasure_one]
  rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => inner_phaseCoherence_ratio τ hx]
  rw [integral_integral_swap (integrable_ratioPhaseIntegrand τ)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have hc : 0 < (phaseRate τ t).re := by rw [phaseRate_re]; linarith [(show (0 : ℝ) < t from ht)]
  simp only [ratioPhaseIntegrand]
  rw [integral_const_mul, integral_Ioi_pow_mul_cexp hc 1]
  simp

/-- `Re (1/c²) = (a² - b²)/(a² + b²)²` for `c = a - ib`. -/
theorem re_one_div_sq (a b : ℝ) :
    (1 / (((a : ℝ) : ℂ) - ((b : ℝ) : ℂ) * Complex.I) ^ 2).re
      = (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
  rw [one_div, Complex.inv_re, map_pow, Complex.normSq_apply]
  simp [sq, Complex.mul_re]

/-- **Real reduction.**  `∬ κ² cos(τ(x-y)) dμ dμ = ∫₀^∞ R(t) Re(1/c_τ(t)²) dt`. -/
theorem integral_coherence_mul_cos_eq_ratio (τ : ℝ) :
    ∫ z, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
        Real.cos (τ * (z.1 - z.2)) ∂((expMeasure 1).prod (expMeasure 1))
      = ∫ t in Ioi (0 : ℝ), routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t *
          (((1 + t) ^ 2 - (τ * (1 - t)) ^ 2) / ((1 + t) ^ 2 + (τ * (1 - t)) ^ 2) ^ 2) := by
  have hre : ∀ z : ℝ × ℝ, (phaseCoherence τ z).re
      = routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
        Real.cos (τ * (z.1 - z.2)) := fun z => by
    rw [phaseCoherence, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  simp_rw [← hre]
  have hbound : Integrable (fun t =>
      (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t : ℂ) *
        (1 / phaseRate τ t ^ 2)) (volume.restrict (Ioi (0 : ℝ))) := by
    refine integrableOn_routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel.mono' ?_ ?_
    · unfold phaseRate routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
      exact (by fun_prop : Measurable _).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hc : 1 ≤ ‖phaseRate τ t‖ := by
        have := Complex.abs_re_le_norm (phaseRate τ t)
        rw [phaseRate_re, abs_of_pos (by linarith)] at this
        linarith
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg ht0.le),
        norm_div, norm_one, norm_pow]
      refine mul_le_of_le_one_right
        (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg ht0.le) ?_
      rw [div_le_one (by positivity)]
      nlinarith
  have h1 := integral_re (integrable_phaseCoherence τ)
  have h2 := integral_re hbound
  simp only [RCLike.re_to_complex] at h1 h2
  rw [h1, integral_phaseCoherence, ← h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Complex.re_ofReal_mul, phaseRate, re_one_div_sq]

/-! ## The Cayley substitution `t = (1 - v)/(1 + v)` -/

theorem image_cayleyRatio : (fun v : ℝ => (1 - v) / (1 + v)) '' Ioo (-1) 1 = Ioi 0 := by
  ext t
  constructor
  · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
    show (0 : ℝ) < (1 - v) / (1 + v)
    exact div_pos (by linarith) (by linarith)
  · intro ht
    have ht0 : (0 : ℝ) < t := ht
    refine ⟨(1 - t) / (1 + t), ⟨?_, ?_⟩, ?_⟩
    · rw [lt_div_iff₀ (by linarith)]
      linarith
    · rw [div_lt_one (by linarith)]
      linarith
    · have h1 : (1 : ℝ) + t ≠ 0 := (show (0 : ℝ) < 1 + t by linarith).ne'
      show (1 - (1 - t) / (1 + t)) / (1 + (1 - t) / (1 + t)) = t
      field_simp
      ring

theorem hasDerivAt_cayleyRatio {v : ℝ} (hv : 1 + v ≠ 0) :
    HasDerivAt (fun v : ℝ => (1 - v) / (1 + v)) (-(2 / (1 + v) ^ 2)) v := by
  have h := ((hasDerivAt_id' v).const_sub (1 : ℝ)).div ((hasDerivAt_id' v).const_add (1 : ℝ)) hv
  refine h.congr_deriv ?_
  field_simp
  ring

theorem injOn_cayleyRatio : InjOn (fun v : ℝ => (1 - v) / (1 + v)) (Ioo (-1) 1) := by
  intro v hv w hw h
  have hv1 : (1 : ℝ) + v ≠ 0 := (show (0 : ℝ) < 1 + v by linarith [hv.1]).ne'
  have hw1 : (1 : ℝ) + w ≠ 0 := (show (0 : ℝ) < 1 + w by linarith [hw.1]).ne'
  change (1 - v) / (1 + v) = (1 - w) / (1 + w) at h
  field_simp at h
  linarith

/-- `∫₀^∞ g(t) dt = ∫₋₁¹ 2/(1 + v)² g((1 - v)/(1 + v)) dv`. -/
theorem integral_Ioi_eq_cayley (g : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), g t
      = ∫ v in Ioo (-1 : ℝ) 1, 2 / (1 + v) ^ 2 * g ((1 - v) / (1 + v)) := by
  rw [← image_cayleyRatio, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun v hv => (hasDerivAt_cayleyRatio
      (show (0 : ℝ) < 1 + v by linarith [hv.1]).ne').hasDerivWithinAt)
    injOn_cayleyRatio]
  refine setIntegral_congr_fun measurableSet_Ioo fun v _ => ?_
  rw [smul_eq_mul, abs_neg, abs_of_nonneg (by positivity)]

/-- The Cayley-transported real integrand `(1 - v²)³(1 - τ²v²)/(2(1 + τ²v²)²)`. -/
def cayleyPhaseIntegrand (τ v : ℝ) : ℝ :=
  (1 - v ^ 2) ^ 3 * (1 - τ ^ 2 * v ^ 2) / (2 * (1 + τ ^ 2 * v ^ 2) ^ 2)

theorem cayley_ratio_integrand_eq (τ : ℝ) {v : ℝ} (hv : v ∈ Ioo (-1 : ℝ) 1) :
    2 / (1 + v) ^ 2 *
      (routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel ((1 - v) / (1 + v)) *
      (((1 + (1 - v) / (1 + v)) ^ 2 - (τ * (1 - (1 - v) / (1 + v))) ^ 2) /
        ((1 + (1 - v) / (1 + v)) ^ 2 + (τ * (1 - (1 - v) / (1 + v))) ^ 2) ^ 2))
      = cayleyPhaseIntegrand τ v := by
  have hv1 : (1 : ℝ) + v ≠ 0 := (show (0 : ℝ) < 1 + v by linarith [hv.1]).ne'
  have h1 : 1 + (1 - v) / (1 + v) = 2 / (1 + v) := by field_simp; ring
  have h2 : 1 - (1 - v) / (1 + v) = 2 * v / (1 + v) := by field_simp; ring
  have hq : (0 : ℝ) < 1 + τ ^ 2 * v ^ 2 := by positivity
  rw [h1, h2, routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel, h1, cayleyPhaseIntegrand]
  field_simp
  ring

theorem continuous_cayleyPhaseIntegrand (τ : ℝ) : Continuous (cayleyPhaseIntegrand τ) := by
  unfold cayleyPhaseIntegrand
  exact (by fun_prop : Continuous fun v : ℝ => (1 - v ^ 2) ^ 3 * (1 - τ ^ 2 * v ^ 2)).div
    (by fun_prop) fun v => by positivity

theorem cayleyPhaseIntegrand_neg (τ v : ℝ) :
    cayleyPhaseIntegrand τ (-v) = cayleyPhaseIntegrand τ v := by
  simp only [cayleyPhaseIntegrand, neg_sq]

/-- Evenness: `∫₋₁¹ = 2 ∫₀¹`. -/
theorem integral_Ioo_cayleyPhaseIntegrand (τ : ℝ) :
    ∫ v in Ioo (-1 : ℝ) 1, cayleyPhaseIntegrand τ v
      = ∫ v in (0 : ℝ)..1, 2 * cayleyPhaseIntegrand τ v := by
  have hc := continuous_cayleyPhaseIntegrand τ
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), intervalIntegral.integral_const_mul]
  have hneg : ∫ v in (-1 : ℝ)..0, cayleyPhaseIntegrand τ v
      = ∫ v in (0 : ℝ)..1, cayleyPhaseIntegrand τ v := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (cayleyPhaseIntegrand τ)
    simp only [cayleyPhaseIntegrand_neg, neg_zero] at h
    exact h.symm
  rw [hneg]
  ring

/-- Integration by parts against `d/dv [v/(1 + τ²v²)]`. -/
theorem integral_two_mul_cayleyPhaseIntegrand (τ : ℝ) :
    ∫ v in (0 : ℝ)..1, 2 * cayleyPhaseIntegrand τ v = phaseSurvivalProfile τ := by
  have hq : ∀ v : ℝ, (0 : ℝ) < 1 + τ ^ 2 * v ^ 2 := fun v => by positivity
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => (1 - v ^ 2) ^ 3)
      (3 * (1 - x ^ 2) ^ 2 * (-(2 * x))) x := fun x _ => by
    have h := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_pow 2 x)).pow 3
    refine h.congr_deriv ?_
    norm_num
  have hw : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun v : ℝ => v / (1 + τ ^ 2 * v ^ 2))
      ((1 - τ ^ 2 * x ^ 2) / (1 + τ ^ 2 * x ^ 2) ^ 2) x := fun x _ => by
    have h := (hasDerivAt_id' x).div (((hasDerivAt_pow 2 x).const_mul (τ ^ 2)).const_add 1)
      (hq x).ne'
    refine h.congr_deriv ?_
    field_simp
    ring
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hw
    ((by fun_prop : Continuous fun x : ℝ => 3 * (1 - x ^ 2) ^ 2 * (-(2 * x))).intervalIntegrable
      _ _)
    (((by fun_prop : Continuous fun x : ℝ => 1 - τ ^ 2 * x ^ 2).div (by fun_prop)
      fun x => pow_ne_zero 2 (hq x).ne').intervalIntegrable _ _)
  have hlhs : ∀ v : ℝ, 2 * cayleyPhaseIntegrand τ v
      = (1 - v ^ 2) ^ 3 * ((1 - τ ^ 2 * v ^ 2) / (1 + τ ^ 2 * v ^ 2) ^ 2) := fun v => by
    rw [cayleyPhaseIntegrand]
    field_simp
  simp_rw [hlhs]
  rw [hibp, phaseSurvivalProfile, phaseResponse]
  norm_num
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  field_simp
  ring

/-- **(SKPM.3).**  `∬ κ(x, y)² cos(τ(x - y)) μ(dx) μ(dy) = 6 ∫₀¹ v²(1 - v²)²/(1 + τ²v²) dv`. -/
theorem integral_coherence_mul_cos (τ : ℝ) :
    ∫ z, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2 *
        Real.cos (τ * (z.1 - z.2)) ∂((expMeasure 1).prod (expMeasure 1))
      = phaseSurvivalProfile τ := by
  rw [integral_coherence_mul_cos_eq_ratio, integral_Ioi_eq_cayley,
    setIntegral_congr_fun measurableSet_Ioo fun v hv => cayley_ratio_integrand_eq τ hv,
    integral_Ioo_cayleyPhaseIntegrand, integral_two_mul_cayleyPhaseIntegrand]

end GaloisForLFunctions.HTGeometry

