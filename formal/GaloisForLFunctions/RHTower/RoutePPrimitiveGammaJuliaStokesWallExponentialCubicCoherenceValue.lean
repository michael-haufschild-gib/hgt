import GaloisForLFunctions.HTGeometry.PairGiniLaw
import GaloisForLFunctions.HTGeometry.HalfLineBetaKernel
import GaloisForLFunctions.HTGeometry.SpectralFormFactorExponentialLimit
import GaloisForLFunctions.RHTower.LegStripContinuum

/-!
# P-G105T: exact exponential cubic-coherence value

For two independent unit exponential clocks, the squared cubic Cauchy coherence has expectation
exactly `16/35`.  A positive-quadrant ratio substitution separates the radial Gamma integral from
the beta-prime `Beta(4,4)` integral; all Fubini and integrability steps are explicit.

This module evaluates the universal limit kernel used by the SP-E wall law.  It contains no
numerical approximation and no arithmetic asymptotic input.
-/

open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

local instance : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

def routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence (a b : ℝ) : ℝ :=
  64 * a ^ 3 * b ^ 3 / (a + b) ^ 6

theorem measurable_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence :
    Measurable (fun z : ℝ × ℝ => routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2) := by
  unfold routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
  fun_prop

theorem routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence a b ∧ routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence a b ≤ 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence]
  constructor
  · positivity
  · by_cases hab : a + b = 0
    · have ha0 : a = 0 := by nlinarith
      simp [ha0]
    · have hbase : 4 * a * b ≤ (a + b) ^ 2 := by
        nlinarith [sq_nonneg (a - b)]
      have hbase0 : 0 ≤ 4 * a * b := by positivity
      have hcubes := pow_le_pow_left₀ hbase0 hbase 3
      rw [show (4 * a * b) ^ 3 = 64 * a ^ 3 * b ^ 3 by ring] at hcubes
      rw [show (a + b) ^ 6 = ((a + b) ^ 2) ^ 3 by ring]
      rw [div_le_one (pow_pos (sq_pos_of_ne_zero hab) 3)]
      exact hcubes

theorem integrable_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod :
    Integrable (fun z : ℝ × ℝ => routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2)
      ((expMeasure 1).prod (expMeasure 1)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    measurable_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence.aestronglyMeasurable ?_
  filter_upwards
    [GaloisForLFunctions.HTGeometry.ae_nonneg_fst_prod
      (expMeasure 1) (expMeasure 1)
      GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero,
     GaloisForLFunctions.HTGeometry.ae_nonneg_snd_prod
      (expMeasure 1) (expMeasure 1)
      GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero]
      with z hz1 hz2
  have h := routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_zero_le_one hz1 hz2
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_density :
    (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) =
      ∫ x : ℝ,
        Set.indicator (Set.Ici (0 : ℝ)) (fun x => Real.exp (-x)) x *
          (∫ y : ℝ,
            Set.indicator (Set.Ici (0 : ℝ)) (fun y => Real.exp (-y)) y *
              routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) := by
  let hpdf : expMeasure 1 =
      (volume : Measure ℝ).withDensity (exponentialPDF 1) := rfl
  rw [integral_prod _ integrable_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod]
  rw [hpdf, integral_withDensity_eq_integral_toReal_smul
    GaloisForLFunctions.HTGeometry.measurable_exponentialPDF_one
    (Filter.Eventually.of_forall
      GaloisForLFunctions.HTGeometry.exponentialPDF_one_lt_top)]
  simp_rw [integral_withDensity_eq_integral_toReal_smul
    GaloisForLFunctions.HTGeometry.measurable_exponentialPDF_one
    (Filter.Eventually.of_forall
      GaloisForLFunctions.HTGeometry.exponentialPDF_one_lt_top)]
  simp_rw [GaloisForLFunctions.HTGeometry.toReal_exponentialPDF_one, smul_eq_mul]

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_Ici :
    (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) =
      ∫ x : ℝ in Ici (0 : ℝ), Real.exp (-x) *
        (∫ y : ℝ in Ici (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) := by
  rw [integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_density]
  calc
    (∫ x : ℝ,
        (Ici (0 : ℝ)).indicator (fun x => Real.exp (-x)) x *
          (∫ y : ℝ,
            (Ici (0 : ℝ)).indicator (fun y => Real.exp (-y)) y *
              routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y)) =
        ∫ x : ℝ, (Ici (0 : ℝ)).indicator
          (fun x => Real.exp (-x) *
            (∫ y : ℝ,
              (Ici (0 : ℝ)).indicator (fun y => Real.exp (-y)) y *
                routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y)) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ Ici (0 : ℝ)
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    _ = ∫ x : ℝ in Ici (0 : ℝ), Real.exp (-x) *
          (∫ y : ℝ,
            (Ici (0 : ℝ)).indicator (fun y => Real.exp (-y)) y *
              routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) := by
      rw [integral_indicator measurableSet_Ici]
    _ = ∫ x : ℝ in Ici (0 : ℝ), Real.exp (-x) *
          (∫ y : ℝ in Ici (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) := by
      apply setIntegral_congr_fun measurableSet_Ici
      intro x hx
      have hinner :
        (∫ y : ℝ, (Ici (0 : ℝ)).indicator (fun y => Real.exp (-y)) y *
            routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) =
          ∫ y : ℝ in Ici (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y := by
        calc
          (∫ y : ℝ, (Ici (0 : ℝ)).indicator (fun y => Real.exp (-y)) y *
              routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) =
              ∫ y : ℝ, (Ici (0 : ℝ)).indicator
                (fun y => Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) y := by
            apply integral_congr_ae
            filter_upwards with y
            by_cases hy : y ∈ Ici (0 : ℝ)
            · simp [Set.indicator_of_mem hy]
            · simp [Set.indicator_of_notMem hy]
          _ = ∫ y : ℝ in Ici (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y := by
            rw [integral_indicator measurableSet_Ici]
      dsimp only
      rw [hinner]

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_Ioi :
    (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) =
      ∫ x : ℝ in Ioi (0 : ℝ), Real.exp (-x) *
        (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) := by
  rw [integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_Ici]
  rw [← Measure.restrict_congr_set (Ioi_ae_eq_Ici (a := (0 : ℝ)))]

def routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel (t : ℝ) : ℝ := 64 * t ^ 3 / (1 + t) ^ 6

theorem routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t := by
  rw [routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel]
  positivity

theorem routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_le_oneAddMajor {t : ℝ} (ht : 0 ≤ t) :
    routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t ≤ 64 * (1 + t) ^ (-(3 : ℝ)) := by
  have h1t : 0 < 1 + t := by linarith
  have hpow : t ^ 3 ≤ (1 + t) ^ 3 :=
    pow_le_pow_left₀ ht (by linarith) 3
  have hden3 : 0 < (1 + t) ^ 3 := pow_pos h1t 3
  have hden6 : 0 < (1 + t) ^ 6 := pow_pos h1t 6
  rw [routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel, div_le_iff₀ hden6]
  calc
    64 * t ^ 3 ≤ 64 * (1 + t) ^ 3 :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 64 * (1 + t) ^ (-(3 : ℝ)) * (1 + t) ^ 6 := by
      rw [Real.rpow_neg h1t.le]
      field_simp
      exact Real.rpow_natCast (1 + t) 3

theorem integrableOn_routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel :
    IntegrableOn routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel (Ioi (0 : ℝ)) := by
  have hmajor :=
    (RHTower.integrableOn_one_add_rpow (r := 3) (by norm_num)).const_mul 64
  refine hmajor.mono' ?_ ?_
  · exact ((measurable_const.mul (measurable_id.pow_const 3)).div
      ((measurable_const.add measurable_id).pow_const 6)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hnonneg := routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg ht.le
    have ht0 : 0 < t := ht
    have h1t : 0 < 1 + t := by linarith
    have hmajorNonneg : 0 ≤ 64 * (1 + t) ^ (-(3 : ℝ)) :=
      mul_nonneg (by norm_num) (Real.rpow_pos_of_pos h1t _).le
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_le_oneAddMajor ht.le

theorem routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_scale_right
    {x t : ℝ} (hx : 0 < x) :
    routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x (x * t) = routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t := by
  rw [routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence, routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel]
  field_simp [hx.ne']

theorem inner_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_change_of_variables
    {x : ℝ} (hx : 0 < x) :
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) =
      x * ∫ t : ℝ in Ioi (0 : ℝ),
        Real.exp (-(x * t)) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x (x * t) := by
  have h := integral_comp_mul_left_Ioi
    (fun y : ℝ => Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) 0 hx
  simp only [mul_zero, smul_eq_mul] at h
  calc
    (∫ y : ℝ in Ioi (0 : ℝ), Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) =
        x * (x⁻¹ * ∫ y : ℝ in Ioi (0 : ℝ),
          Real.exp (-y) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x y) := by field_simp
    _ = x * ∫ t : ℝ in Ioi (0 : ℝ),
        (Real.exp (-(x * t)) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x (x * t)) := by rw [← h]

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_ratio_double :
    (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) =
      ∫ x : ℝ in Ioi (0 : ℝ),
        ∫ t : ℝ in Ioi (0 : ℝ),
          routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * x * Real.exp (-((1 + t) * x)) := by
  rw [integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [inner_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_change_of_variables hx]
  rw [show Real.exp (-x) *
      (x * ∫ t : ℝ in Ioi (0 : ℝ),
        Real.exp (-(x * t)) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x (x * t)) =
      (Real.exp (-x) * x) *
        ∫ t : ℝ in Ioi (0 : ℝ),
          Real.exp (-(x * t)) * routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence x (x * t) by ring]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_scale_right hx]
  rw [show Real.exp (-x) * x * (Real.exp (-(x * t)) * routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t) =
      routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * x * (Real.exp (-x) * Real.exp (-(x * t))) by ring]
  rw [← Real.exp_add]
  congr 1
  ring

theorem integrableOn_x_mul_exp_neg_x :
    IntegrableOn (fun x : ℝ => x * Real.exp (-x)) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := 1) (p := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num)
  refine h.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [Real.rpow_one]
  ring_nf

theorem integrable_ratio_radial_prod :
    Integrable
      (fun p : ℝ × ℝ =>
        routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel p.2 * p.1 * Real.exp (-((1 + p.2) * p.1)))
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmajor := integrableOn_x_mul_exp_neg_x.mul_prod integrableOn_routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
  refine hmajor.mono' ?_ ?_
  · unfold routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
    fun_prop
  · rw [Measure.prod_restrict]
    filter_upwards
      [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    have hx : 0 < p.1 := hp.1
    have ht : 0 < p.2 := hp.2
    have hk : 0 ≤ routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel p.2 := routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_nonneg ht.le
    have he0 : 0 ≤ Real.exp (-((1 + p.2) * p.1)) := Real.exp_pos _ |>.le
    have he : Real.exp (-((1 + p.2) * p.1)) ≤ Real.exp (-p.1) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hk hx.le) he0)]
    calc
      routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel p.2 * p.1 * Real.exp (-((1 + p.2) * p.1)) ≤
          routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel p.2 * p.1 * Real.exp (-p.1) := by
        exact mul_le_mul_of_nonneg_left he (mul_nonneg hk hx.le)
      _ = (p.1 * Real.exp (-p.1)) * routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel p.2 := by ring

theorem integral_ratio_double_swap :
    (∫ x : ℝ in Ioi (0 : ℝ),
        ∫ t : ℝ in Ioi (0 : ℝ),
          routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * x * Real.exp (-((1 + t) * x))) =
      ∫ t : ℝ in Ioi (0 : ℝ),
        ∫ x : ℝ in Ioi (0 : ℝ),
          routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * x * Real.exp (-((1 + t) * x)) := by
  exact integral_integral_swap integrable_ratio_radial_prod

theorem integral_x_mul_exp_parameter
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ in Ioi (0 : ℝ),
      x * Real.exp (-((1 + t) * x))) = (1 + t) ^ (-(2 : ℝ)) := by
  have h1t : 0 < 1 + t := by linarith
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (q := (1 : ℝ)) (b := 1 + t)
    (by norm_num) (by norm_num) h1t
  norm_num [Real.rpow_one, Real.Gamma_nat_eq_factorial] at h
  convert h using 1
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    congr 2
    ring
  · rw [Real.rpow_neg h1t.le]
    exact congrArg (fun u : ℝ => u⁻¹) (Real.rpow_natCast (1 + t) 2)

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_ratio :
    (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) =
      ∫ t : ℝ in Ioi (0 : ℝ),
        routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 + t) ^ (-(2 : ℝ)) := by
  rw [integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_ratio_double,
    integral_ratio_double_swap]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  calc
    (∫ x : ℝ in Ioi (0 : ℝ),
        routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * x * Real.exp (-((1 + t) * x))) =
        routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t *
          ∫ x : ℝ in Ioi (0 : ℝ),
            x * Real.exp (-((1 + t) * x)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      ring
    _ = routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 + t) ^ (-(2 : ℝ)) := by
      rw [integral_x_mul_exp_parameter ht.le]

theorem integral_beta_three_three :
    (∫ t : ℝ in Ioi (0 : ℝ), t ^ 3 / (1 + t) ^ 8) = 1 / 140 := by
  have hcomplex :=
    GaloisForLFunctions.HTGeometry.integral_halfLine_beta
      (w := (4 : ℂ)) (c := (8 : ℂ)) (by norm_num) (by norm_num)
  have hintegrand : ∀ t ∈ Ioi (0 : ℝ),
      ((t : ℂ) ^ ((4 : ℂ) - 1) * (1 + (t : ℂ)) ^ (-(8 : ℂ))) =
        ((t ^ 3 / (1 + t) ^ 8 : ℝ) : ℂ) := by
    intro t ht
    rw [show (4 : ℂ) - 1 = ((3 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast, Complex.cpow_neg,
      show (8 : ℂ) = ((8 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    push_cast
    rw [div_eq_mul_inv]
  rw [setIntegral_congr_fun measurableSet_Ioi hintegrand,
    integral_complex_ofReal] at hcomplex
  norm_num [Complex.Gamma_nat_eq_factorial] at hcomplex
  rw [← Complex.ofReal_inj]
  norm_num
  exact hcomplex

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_mul_rpow_eq :
    (∫ t : ℝ in Ioi (0 : ℝ),
      routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 + t) ^ (-(2 : ℝ))) = 16 / 35 := by
  calc
    (∫ t : ℝ in Ioi (0 : ℝ),
        routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel t * (1 + t) ^ (-(2 : ℝ))) =
        ∫ t : ℝ in Ioi (0 : ℝ),
          64 * (t ^ 3 / (1 + t) ^ 8) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      have h1t : 0 < 1 + t := by linarith
      dsimp only
      unfold routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel
      rw [Real.rpow_neg h1t.le]
      have hpow2 : (1 + t) ^ (2 : ℝ) = (1 + t) ^ (2 : ℕ) :=
        Real.rpow_natCast (1 + t) 2
      rw [hpow2]
      field_simp
    _ = 64 * (∫ t : ℝ in Ioi (0 : ℝ),
          t ^ 3 / (1 + t) ^ 8) := by rw [integral_const_mul]
    _ = 16 / 35 := by rw [integral_beta_three_three]; norm_num

theorem integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq :
    (∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) = 16 / 35 := by
  rw [integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq_ratio,
    integral_routePPrimitiveGammaJuliaStokesWallExponentialRatioKernel_mul_rpow_eq]

end

end RHTower
