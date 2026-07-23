import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularArchimedean
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularResolventFourier

/-!
# Gamma--polar cancellation for the sharp rectangular Guinand--Weil value

Gauss's absolutely convergent digamma series and the causal resolvent evaluation are combined
here.  The first stage establishes a cutoff-independent integrable majorant, allowing the finite
resolvent identities to converge to the literal archimedean bottom-edge integral.
-/

open Complex Filter MeasureTheory Set
open scoped BigOperators Convolution

noncomputable section

namespace RHTower

def rectangularEulerDigammaPoint (xi : ℝ) : ℂ :=
  ((3 / 4 : ℝ) : ℂ) - ((Real.pi * xi : ℝ) : ℂ) * I

theorem rectangularEulerDigammaPoint_eq (xi : ℝ) :
    rectangularEulerDigammaPoint xi = rectangularEulerArchPoint xi / 2 := by
  unfold rectangularEulerDigammaPoint rectangularEulerArchPoint
  push_cast
  ring

theorem rectangularEulerDigammaPoint_re (xi : ℝ) :
    (rectangularEulerDigammaPoint xi).re = 3 / 4 := by
  simp [rectangularEulerDigammaPoint, Complex.mul_re]

def rectangularEulerGaussLogWeight (xi : ℝ) : ℝ :=
  1 + Real.log (1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖)

theorem rectangularEulerGaussLogWeight_nonneg (xi : ℝ) :
    0 ≤ rectangularEulerGaussLogWeight xi := by
  unfold rectangularEulerGaussLogWeight
  have hlog : 0 ≤ Real.log
      (1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖) :=
    Real.log_nonneg (by nlinarith [norm_nonneg (rectangularEulerDigammaPoint xi - 1)])
  linarith

theorem norm_rectangularEulerDigammaPoint_sub_one_le (xi : ℝ) :
    ‖rectangularEulerDigammaPoint xi - 1‖ ≤ 1 / 4 + Real.pi * |xi| := by
  have h := Complex.norm_le_abs_re_add_abs_im (rectangularEulerDigammaPoint xi - 1)
  have hre : (rectangularEulerDigammaPoint xi - 1).re = -1 / 4 := by
    rw [Complex.sub_re, rectangularEulerDigammaPoint_re]
    norm_num
  have him : (rectangularEulerDigammaPoint xi - 1).im = -Real.pi * xi := by
    simp [rectangularEulerDigammaPoint, Complex.mul_im]
  rw [hre, him] at h
  norm_num [abs_mul, abs_of_pos Real.pi_pos] at h ⊢
  linarith

def rectangularEulerGaussLogGrowthConstant : ℝ :=
  3 + Real.log (2 * Real.pi + 3)

theorem rectangularEulerGaussLogGrowthConstant_nonneg :
    0 ≤ rectangularEulerGaussLogGrowthConstant := by
  unfold rectangularEulerGaussLogGrowthConstant
  have hlog : 0 ≤ Real.log (2 * Real.pi + 3) :=
    Real.log_nonneg (by linarith [Real.pi_pos])
  linarith

theorem rectangularEulerGaussLogWeight_le
    {xi : ℝ} (hxi : 1 ≤ |xi|) :
    rectangularEulerGaussLogWeight xi ≤
      rectangularEulerGaussLogGrowthConstant *
        (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
  have habs : 0 < |xi| := lt_of_lt_of_le zero_lt_one hxi
  have hnorm := norm_rectangularEulerDigammaPoint_sub_one_le xi
  have harg : 1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖ ≤
      (2 * Real.pi + 3) * |xi| := by
    nlinarith
  have hK : 0 < 2 * Real.pi + 3 := by linarith [Real.pi_pos]
  have hlogarg : Real.log (1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖) ≤
      Real.log (2 * Real.pi + 3) + Real.log |xi| := by
    calc
      Real.log (1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖) ≤
          Real.log ((2 * Real.pi + 3) * |xi|) :=
        Real.log_le_log (by positivity) harg
      _ = Real.log (2 * Real.pi + 3) + Real.log |xi| := by
        rw [Real.log_mul hK.ne' habs.ne']
  have hbase : (1 : ℝ) ≤ 1 + xi ^ 2 := by nlinarith [sq_nonneg xi]
  have hquarterOne : 1 ≤ (1 + xi ^ 2) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hlogabs : Real.log |xi| ≤
      2 * (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
    have hlogsq : 2 * Real.log |xi| = Real.log (xi ^ 2) := by
      rw [← sq_abs, Real.log_pow]
      ring
    have hlogle : Real.log (xi ^ 2) ≤ Real.log (1 + xi ^ 2) :=
      Real.log_le_log (sq_pos_of_ne_zero (abs_ne_zero.mp habs.ne')) (by linarith)
    have hraw := Real.log_le_rpow_div
      (x := 1 + xi ^ 2) (by positivity) (by norm_num : (0 : ℝ) < 1 / 4)
    nlinarith
  have hlogK : 0 ≤ Real.log (2 * Real.pi + 3) :=
    Real.log_nonneg (by linarith [Real.pi_pos])
  unfold rectangularEulerGaussLogWeight rectangularEulerGaussLogGrowthConstant
  calc
    1 + Real.log (1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖) ≤
        1 + Real.log (2 * Real.pi + 3) + Real.log |xi| := by linarith
    _ ≤ (1 + Real.log (2 * Real.pi + 3)) *
          (1 + xi ^ 2) ^ (1 / 4 : ℝ) +
        2 * (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by
      exact add_le_add
        (le_mul_of_one_le_right (by positivity) hquarterOne) hlogabs
    _ = (3 + Real.log (2 * Real.pi + 3)) *
          (1 + xi ^ 2) ^ (1 / 4 : ℝ) := by ring

def rectangularEulerGaussLogMajorant (L a : ℝ) (xi : ℝ) : ℝ :=
  rectangularEulerFourierMajorant L a * rectangularEulerGaussLogGrowthConstant *
    (1 + xi ^ 2) ^ (-3 / 4 : ℝ)

theorem integrable_rectangularEulerGaussLogMajorant (L a : ℝ) :
    Integrable (rectangularEulerGaussLogMajorant L a) := by
  have hbase : Integrable (fun xi : ℝ => (1 + xi ^ 2) ^ (-3 / 4 : ℝ)) := by
    have h := integrable_rpow_neg_one_add_norm_sq
      (E := ℝ) (μ := MeasureTheory.volume) (r := (3 / 2 : ℝ)) (by
        rw [Module.finrank_self]
        norm_num)
    refine h.congr (Filter.Eventually.of_forall fun xi => ?_)
    change (1 + ‖xi‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) =
      (1 + xi ^ 2) ^ (-3 / 4 : ℝ)
    rw [Real.norm_eq_abs, sq_abs]
    congr 1
    ring
  exact hbase.const_mul
    (rectangularEulerFourierMajorant L a * rectangularEulerGaussLogGrowthConstant)

theorem integrable_rectangularEulerFourierNorm_mul_gaussLogWeight (L a : ℝ) :
    Integrable (fun xi : ℝ =>
      ‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
          rectangularEulerGaussLogWeight xi) := by
  have htransform : Continuous (fun xi : ℝ =>
      rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2) := by
    exact ((rectangularTwoEdgeTransform_differentiable L a).continuous.comp
      (by fun_prop)).pow 2
  have harg : Continuous (fun xi : ℝ =>
      1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖) := by
    unfold rectangularEulerDigammaPoint
    fun_prop
  have hargne : ∀ xi : ℝ,
      1 + 2 * ‖rectangularEulerDigammaPoint xi - 1‖ ≠ 0 := by
    intro xi
    positivity
  have hweight : Continuous rectangularEulerGaussLogWeight := by
    unfold rectangularEulerGaussLogWeight
    exact continuous_const.add (harg.log hargne)
  have hfun : Continuous (fun xi : ℝ =>
      ‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
          rectangularEulerGaussLogWeight xi) :=
    htransform.norm.mul hweight
  let S : Set ℝ := {xi : ℝ | 1 ≤ |xi|}
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (fun xi : ℝ =>
      ‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
          rectangularEulerGaussLogWeight xi) S := by
    refine (integrable_rectangularEulerGaussLogMajorant L a).integrableOn.mono' ?_ ?_
    · exact hfun.aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict hS] with xi hxi
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (norm_nonneg _)
          (rectangularEulerGaussLogWeight_nonneg xi))]
      have hF := norm_rectangularTwoEdgeTransform_eulerLine_sq_le L a xi
      have hW := rectangularEulerGaussLogWeight_le hxi
      have hM : 0 ≤ rectangularEulerFourierMajorant L a := by
        unfold rectangularEulerFourierMajorant
        positivity
      have hC := rectangularEulerGaussLogGrowthConstant_nonneg
      have hpos : 0 < 1 + xi ^ 2 := by positivity
      calc
        ‖rectangularTwoEdgeTransform L a
              (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
            rectangularEulerGaussLogWeight xi ≤
          (rectangularEulerFourierMajorant L a * (1 + xi ^ 2)⁻¹) *
            (rectangularEulerGaussLogGrowthConstant *
              (1 + xi ^ 2) ^ (1 / 4 : ℝ)) := by
          exact mul_le_mul hF hW (rectangularEulerGaussLogWeight_nonneg xi)
            (mul_nonneg hM (inv_nonneg.mpr hpos.le))
        _ = rectangularEulerGaussLogMajorant L a xi := by
          unfold rectangularEulerGaussLogMajorant
          rw [show (1 + xi ^ 2)⁻¹ = (1 + xi ^ 2) ^ (-1 : ℝ) by
            exact (Real.rpow_neg_one (1 + xi ^ 2)).symm]
          rw [show rectangularEulerFourierMajorant L a * (1 + xi ^ 2) ^ (-1 : ℝ) *
              (rectangularEulerGaussLogGrowthConstant *
                (1 + xi ^ 2) ^ (1 / 4 : ℝ)) =
              rectangularEulerFourierMajorant L a *
                rectangularEulerGaussLogGrowthConstant *
                  ((1 + xi ^ 2) ^ (-1 : ℝ) *
                    (1 + xi ^ 2) ^ (1 / 4 : ℝ)) by ring]
          rw [← Real.rpow_add hpos]
          norm_num
  have hcompact : IntegrableOn (fun xi : ℝ =>
      ‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
          rectangularEulerGaussLogWeight xi) (Icc (-1) 1) := by
    exact hfun.integrableOn_Icc
  have hcover : Icc (-1 : ℝ) 1 ∪ S = univ := by
    ext xi
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |xi| ≤ 1
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

/-! ## An integrable cutoff-independent Gauss majorant -/

theorem digamma_rectangularEulerDigammaPoint_eq_arch
    (xi : ℝ) :
    Complex.digamma (rectangularEulerDigammaPoint xi) =
      2 * logDeriv archFactor (rectangularEulerArchPoint xi) -
        2 / rectangularEulerArchPoint xi -
        2 / (rectangularEulerArchPoint xi - 1) +
        (Real.log Real.pi : ℂ) := by
  have hsre := rectangularEulerArchPoint_re xi
  have hs0 := rectangularEulerArchPoint_ne_zero xi
  have hs1 := rectangularEulerArchPoint_ne_one xi
  have hclosed := logDeriv_archFactor_closed
    (s := rectangularEulerArchPoint xi) (by rw [hsre]; norm_num) hs0 hs1
  rw [rectangularEulerDigammaPoint_eq, hclosed]
  unfold GaloisForLFunctions.gammaRealLogConnection
  ring

def rectangularEulerDigammaIntegrand (L a : ℝ) (xi : ℝ) : ℂ :=
  rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
    Complex.digamma (rectangularEulerDigammaPoint xi)

theorem integrable_rectangularEulerDigammaIntegrand (L a : ℝ) :
    Integrable (rectangularEulerDigammaIntegrand L a) := by
  let F : ℝ → ℂ := fun xi =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2
  let s : ℝ → ℂ := rectangularEulerArchPoint
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hscont : Continuous s := by
    unfold s rectangularEulerArchPoint
    fun_prop
  have hs0 : ∀ xi : ℝ, s xi ≠ 0 := rectangularEulerArchPoint_ne_zero
  have hs1 : ∀ xi : ℝ, s xi - 1 ≠ 0 := fun xi =>
    sub_ne_zero.mpr (rectangularEulerArchPoint_ne_one xi)
  have hinv0cont : Continuous (fun xi : ℝ => (s xi)⁻¹) := hscont.inv₀ hs0
  have hinv1cont : Continuous (fun xi : ℝ => (s xi - 1)⁻¹) :=
    (hscont.sub continuous_const).inv₀ hs1
  have hinv0bound : ∀ xi : ℝ, ‖(s xi)⁻¹‖ ≤ 1 := by
    intro xi
    have hre : 1 ≤ ‖s xi‖ := by
      have h := Complex.re_le_norm (s xi)
      have hsre : (s xi).re = 3 / 2 := rectangularEulerArchPoint_re xi
      linarith
    rw [norm_inv]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hre
    norm_num at h ⊢
    exact h
  have hinv1bound : ∀ xi : ℝ, ‖(s xi - 1)⁻¹‖ ≤ 2 := by
    intro xi
    have hre : (1 / 2 : ℝ) ≤ ‖s xi - 1‖ := by
      have h := Complex.re_le_norm (s xi - 1)
      have hsre : (s xi).re = 3 / 2 := rectangularEulerArchPoint_re xi
      rw [Complex.sub_re, hsre, Complex.one_re] at h
      norm_num at h ⊢
      exact h
    rw [norm_inv]
    have hpos : 0 < ‖s xi - 1‖ := lt_of_lt_of_le (by norm_num) hre
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hre
    norm_num at h ⊢
    exact h
  have hInv0 : Integrable (fun xi : ℝ => F xi * (s xi)⁻¹) :=
    hF.mul_bdd hinv0cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hinv0bound)
  have hInv1 : Integrable (fun xi : ℝ => F xi * (s xi - 1)⁻¹) :=
    hF.mul_bdd hinv1cont.aestronglyMeasurable
      (Filter.Eventually.of_forall hinv1bound)
  have harch : Integrable (rectangularEulerArchIntegrand L a) :=
    integrable_rectangularEulerArchIntegrand L a
  have hcomb : Integrable (fun xi : ℝ =>
      2 * rectangularEulerArchIntegrand L a xi -
        2 * (F xi * (s xi)⁻¹) -
        2 * (F xi * (s xi - 1)⁻¹) +
        (Real.log Real.pi : ℂ) * F xi) :=
    (((harch.const_mul 2).sub (hInv0.const_mul 2)).sub
      (hInv1.const_mul 2)).add (hF.const_mul (Real.log Real.pi : ℂ))
  apply hcomb.congr
  filter_upwards with xi
  rw [rectangularEulerDigammaIntegrand,
    digamma_rectangularEulerDigammaPoint_eq_arch]
  simp only [rectangularEulerArchIntegrand, F, s, one_div, div_eq_mul_inv]
  ring

def rectangularEulerGaussPartialMajorant (L a : ℝ) (xi : ℝ) : ℝ :=
  ‖rectangularEulerDigammaIntegrand L a xi‖ +
    (|Real.eulerMascheroniConstant| + 1) *
      ‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ +
    3 *
      (‖rectangularTwoEdgeTransform L a
        (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
          rectangularEulerGaussLogWeight xi)

theorem integrable_rectangularEulerGaussPartialMajorant (L a : ℝ) :
    Integrable (rectangularEulerGaussPartialMajorant L a) := by
  have hD := (integrable_rectangularEulerDigammaIntegrand L a).norm
  have hF := (integrable_rectangularTwoEdgeTransform_eulerLine_sq L a).norm.const_mul
    (|Real.eulerMascheroniConstant| + 1)
  have hW :=
    (integrable_rectangularEulerFourierNorm_mul_gaussLogWeight L a).const_mul 3
  apply ((hD.add hF).add hW).congr
  filter_upwards with xi
  unfold rectangularEulerGaussPartialMajorant
  simp only [Pi.add_apply]

theorem norm_rectangularEulerGaussPartial_le_majorant
    (L a : ℝ) (N : ℕ) (xi : ℝ) :
    ‖rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
        (∑ n ∈ Finset.range N,
          gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n)‖ ≤
      rectangularEulerGaussPartialMajorant L a xi := by
  have hsum := norm_sum_gaussDigammaSeriesTerm_threeQuarter_le
    (rectangularEulerDigammaPoint_re xi) N
  rw [norm_mul]
  rw [rectangularEulerGaussPartialMajorant, rectangularEulerDigammaIntegrand, norm_mul]
  have hsum' :
      ‖∑ n ∈ Finset.range N,
          gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n‖ ≤
        ‖Complex.digamma (rectangularEulerDigammaPoint xi)‖ +
          |Real.eulerMascheroniConstant| + 1 +
            3 * rectangularEulerGaussLogWeight xi := by
    simpa only [rectangularEulerGaussLogWeight] using hsum
  calc
    ‖rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
        ‖∑ n ∈ Finset.range N,
          gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n‖ ≤
      ‖rectangularTwoEdgeTransform L a
          (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2‖ *
        (‖Complex.digamma (rectangularEulerDigammaPoint xi)‖ +
          |Real.eulerMascheroniConstant| + 1 +
            3 * rectangularEulerGaussLogWeight xi) :=
      mul_le_mul_of_nonneg_left hsum' (norm_nonneg _)
    _ = _ := by ring

def rectangularEulerGaussPartialIntegrand (L a : ℝ) (N : ℕ) (xi : ℝ) : ℂ :=
  rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
    ∑ n ∈ Finset.range N,
      gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n

def rectangularEulerGaussLimitIntegrand (L a : ℝ) (xi : ℝ) : ℂ :=
  rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
    (Complex.digamma (rectangularEulerDigammaPoint xi) +
      (Real.eulerMascheroniConstant : ℂ))

theorem integrable_rectangularEulerGaussPartialIntegrand
    (L a : ℝ) (N : ℕ) :
    Integrable (rectangularEulerGaussPartialIntegrand L a N) := by
  rw [show rectangularEulerGaussPartialIntegrand L a N = fun xi : ℝ =>
      ∑ n ∈ Finset.range N,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
          gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n by
    funext xi
    rw [rectangularEulerGaussPartialIntegrand, Finset.mul_sum]]
  exact MeasureTheory.integrable_finsetSum _ fun n _ => by
    simpa only [rectangularEulerDigammaPoint] using
      integrable_rectangularEulerFourierKernel_mul_gaussDigammaSeriesTerm L a n

theorem tendsto_integral_rectangularEulerGaussPartialIntegrand
    (L a : ℝ) :
    Tendsto
      (fun N : ℕ => ∫ xi : ℝ, rectangularEulerGaussPartialIntegrand L a N xi)
      atTop
      (nhds (∫ xi : ℝ, rectangularEulerGaussLimitIntegrand L a xi)) := by
  apply tendsto_integral_of_dominated_convergence
    (rectangularEulerGaussPartialMajorant L a)
  · intro N
    exact (integrable_rectangularEulerGaussPartialIntegrand L a N).aestronglyMeasurable
  · exact integrable_rectangularEulerGaussPartialMajorant L a
  · intro N
    exact Filter.Eventually.of_forall fun xi => by
      simpa only [rectangularEulerGaussPartialIntegrand] using
        norm_rectangularEulerGaussPartial_le_majorant L a N xi
  · exact Filter.Eventually.of_forall fun xi => by
      have hs : 0 < (rectangularEulerDigammaPoint xi).re := by
        rw [rectangularEulerDigammaPoint_re]
        norm_num
      have hseries :=
        (summable_gaussDigammaSeriesTerm hs).hasSum.tendsto_sum_nat
      have hvalue :
          ∑' n : ℕ, gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n =
            Complex.digamma (rectangularEulerDigammaPoint xi) +
              (Real.eulerMascheroniConstant : ℂ) := by
        rw [digamma_eq_neg_euler_add_tsum_gauss hs]
        ring
      rw [hvalue] at hseries
      unfold rectangularEulerGaussPartialIntegrand rectangularEulerGaussLimitIntegrand
      exact tendsto_const_nhds.mul hseries

def rectangularEulerGaussTermValue (L a : ℝ) (n : ℕ) : ℂ :=
  (rectangularTwoEdgeAutocorrelation L a 0 : ℂ) / ((n : ℂ) + 1) -
    ∫ t : ℝ in Ioi 0,
      Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (t : ℂ)) *
        ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
          Complex.exp (t / 2))

def rectangularEulerGaussPartialValue (L a : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, rectangularEulerGaussTermValue L a n

theorem integral_rectangularEulerGaussPartialIntegrand_eq_value
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (N : ℕ) :
    (∫ xi : ℝ, rectangularEulerGaussPartialIntegrand L a N xi) =
      rectangularEulerGaussPartialValue L a N := by
  rw [show rectangularEulerGaussPartialIntegrand L a N = fun xi : ℝ =>
      ∑ n ∈ Finset.range N,
        rectangularTwoEdgeTransform L a
            (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
          gaussDigammaSeriesTerm (rectangularEulerDigammaPoint xi) n by
    funext xi
    rw [rectangularEulerGaussPartialIntegrand, Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  · unfold rectangularEulerGaussPartialValue
    apply Finset.sum_congr rfl
    intro n _
    unfold rectangularEulerGaussTermValue
    simpa only [rectangularEulerDigammaPoint] using
      integral_rectangularEulerFourierKernel_mul_gaussDigammaSeriesTerm hL a n
  · intro n _
    simpa only [rectangularEulerDigammaPoint] using
      integrable_rectangularEulerFourierKernel_mul_gaussDigammaSeriesTerm L a n

theorem tendsto_rectangularEulerGaussPartialValue
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    Tendsto (rectangularEulerGaussPartialValue L a) atTop
      (nhds (∫ xi : ℝ, rectangularEulerGaussLimitIntegrand L a xi)) := by
  have h := tendsto_integral_rectangularEulerGaussPartialIntegrand L a
  exact h.congr' (Filter.Eventually.of_forall fun N =>
    integral_rectangularEulerGaussPartialIntegrand_eq_value hL a N)

/-! ## Aperture-uniform time-kernel geometry -/

theorem rectangularMovingAutocorrelationTent_le_min
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 0 ≤ h) :
    max 0 (L - |h - (2 * a - L)|) ≤ min L h := by
  apply max_le
  · exact le_min hL hh
  · apply le_min
    · linarith [abs_nonneg (h - (2 * a - L))]
    · have habs := neg_le_abs (h - (2 * a - L))
      linarith

theorem rectangularTwoEdgeAutocorrelation_zero
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    rectangularTwoEdgeAutocorrelation L a 0 = 2 * L := by
  rw [rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha (le_refl 0)]
  have hcenter : L ≤ |0 - (2 * a - L)| := by
    rw [abs_of_nonpos]
    · linarith
    · linarith
  rw [sub_zero, max_eq_right hL,
    max_eq_left (by linarith : L - |0 - (2 * a - L)| ≤ 0)]
  ring

theorem rectangularTwoEdgeAutocorrelation_nonneg
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 0 ≤ h) :
    0 ≤ rectangularTwoEdgeAutocorrelation L a h := by
  rw [rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha hh]
  positivity

theorem rectangularTwoEdgeAutocorrelation_le_three_mul
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 0 ≤ h) :
    rectangularTwoEdgeAutocorrelation L a h ≤ 3 * L := by
  rw [rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha hh]
  have hfixed : max 0 (L - h) ≤ L := max_le hL (by linarith)
  have hmoving := rectangularMovingAutocorrelationTent_le_min hL ha hh
  have hmin : min L h ≤ L := min_le_left _ _
  linarith

theorem abs_rectangularTwoEdgeAutocorrelation_zero_sub_le
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 0 ≤ h) :
    |rectangularTwoEdgeAutocorrelation L a 0 -
        rectangularTwoEdgeAutocorrelation L a h| ≤ 3 * h := by
  rw [rectangularTwoEdgeAutocorrelation_zero hL ha,
    rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha hh]
  let M : ℝ := max 0 (L - |h - (2 * a - L)|)
  have hM0 : 0 ≤ M := by dsimp only [M]; positivity
  have hMh : M ≤ h :=
    (rectangularMovingAutocorrelationTent_le_min hL ha hh).trans (min_le_right _ _)
  by_cases hhL : h ≤ L
  · rw [max_eq_right (by linarith : 0 ≤ L - h)]
    dsimp only [M] at hM0 hMh ⊢
    rw [show 2 * L - (2 * (L - h) +
        max 0 (L - |h - (2 * a - L)|)) =
      2 * h - max 0 (L - |h - (2 * a - L)|) by ring]
    rw [abs_le]
    constructor <;> linarith
  · rw [max_eq_left (by linarith : L - h ≤ 0)]
    dsimp only [M] at hM0 hMh ⊢
    rw [show 2 * L - (2 * 0 +
        max 0 (L - |h - (2 * a - L)|)) =
      2 * L - max 0 (L - |h - (2 * a - L)|) by ring]
    rw [abs_le]
    constructor <;> linarith

/-! ## The removable Gamma singularity -/

/-- The numerator in the time-domain Gamma correction.  Its two summands agree at zero; this is
the cancellation which removes the apparent pole of `(1 - exp (-t))⁻¹`. -/
def rectangularGammaCancellationNumerator (L a t : ℝ) : ℝ :=
  Real.exp (-t) * rectangularTwoEdgeAutocorrelation L a 0 -
    Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2)

/-- The absolutely integrable time-domain Gamma correction kernel. -/
def rectangularGammaCancellationKernel (L a t : ℝ) : ℝ :=
  rectangularGammaCancellationNumerator L a t / (1 - Real.exp (-t))

theorem rectangularGamma_half_mul_le_one_sub_exp_neg
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t / 2 ≤ 1 - Real.exp (-t) := by
  have hden : 0 < 1 + t := by linarith
  have hexp : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have hinv : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos t) hden).2 hexp
  rw [← Real.exp_neg] at hinv
  calc
    t / 2 ≤ t / (1 + t) := div_le_div_of_nonneg_left ht0 hden (by linarith)
    _ = 1 - (1 + t)⁻¹ := by field_simp; ring
    _ ≤ 1 - Real.exp (-t) := by linarith

theorem abs_exp_neg_sub_exp_neg_quarter_le
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |Real.exp (-t) - Real.exp (-(t / 4))| ≤ 2 * t := by
  have hfac : Real.exp (-(t / 4)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hsmall : |-(3 * t / 4)| ≤ 1 := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  have hdefect := Real.abs_exp_sub_one_le hsmall
  rw [show Real.exp (-t) =
      Real.exp (-(t / 4)) * Real.exp (-(3 * t / 4)) by
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [show Real.exp (-(t / 4)) * Real.exp (-(3 * t / 4)) -
      Real.exp (-(t / 4)) =
      Real.exp (-(t / 4)) * (Real.exp (-(3 * t / 4)) - 1) by ring]
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-(t / 4)) * |Real.exp (-(3 * t / 4)) - 1| ≤
        1 * (2 * |-(3 * t / 4)|) :=
      mul_le_mul hfac hdefect (abs_nonneg _) (by norm_num)
    _ ≤ 2 * t := by
      rw [abs_of_nonpos (by linarith)]
      linarith

theorem abs_rectangularGammaCancellationNumerator_le_near_zero
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |rectangularGammaCancellationNumerator L a t| ≤
      (8 * L + 3) * (t / 2) := by
  let A0 := rectangularTwoEdgeAutocorrelation L a 0
  let At := rectangularTwoEdgeAutocorrelation L a (t / 2)
  have hA0 : A0 = 2 * L := rectangularTwoEdgeAutocorrelation_zero hL ha
  have hdiff : |A0 - At| ≤ 3 * (t / 2) := by
    simpa only [A0, At] using
      abs_rectangularTwoEdgeAutocorrelation_zero_sub_le hL ha (by positivity : 0 ≤ t / 2)
  rw [hA0] at hdiff
  have hexp : Real.exp (-(t / 4)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hexpdiff := abs_exp_neg_sub_exp_neg_quarter_le ht0 ht1
  rw [rectangularGammaCancellationNumerator]
  change |Real.exp (-t) * A0 - Real.exp (-(t / 4)) * At| ≤ _
  rw [show Real.exp (-t) * A0 - Real.exp (-(t / 4)) * At =
      Real.exp (-(t / 4)) * (A0 - At) +
        (Real.exp (-t) - Real.exp (-(t / 4))) * A0 by ring]
  calc
    |Real.exp (-(t / 4)) * (A0 - At) +
        (Real.exp (-t) - Real.exp (-(t / 4))) * A0| ≤
      |Real.exp (-(t / 4)) * (A0 - At)| +
        |(Real.exp (-t) - Real.exp (-(t / 4))) * A0| := abs_add_le _ _
    _ = Real.exp (-(t / 4)) * |A0 - At| +
        |Real.exp (-t) - Real.exp (-(t / 4))| * |A0| := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ 1 * (3 * (t / 2)) + (2 * t) * (2 * L) := by
      rw [hA0, abs_of_nonneg (by positivity : 0 ≤ 2 * L)]
      exact add_le_add
        (mul_le_mul hexp hdiff (abs_nonneg _) (by norm_num))
        (mul_le_mul hexpdiff (le_refl (2 * L)) (by positivity) (by positivity))
    _ = (8 * L + 3) * (t / 2) := by ring

theorem abs_rectangularGammaCancellationKernel_le_near_zero
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    |rectangularGammaCancellationKernel L a t| ≤ 8 * L + 3 := by
  have hhalf := rectangularGamma_half_mul_le_one_sub_exp_neg ht0.le ht1
  have hden : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hC : 0 ≤ 8 * L + 3 := by positivity
  rw [rectangularGammaCancellationKernel, abs_div, abs_of_pos hden]
  rw [div_le_iff₀ hden]
  calc
    |rectangularGammaCancellationNumerator L a t| ≤
        (8 * L + 3) * (t / 2) :=
      abs_rectangularGammaCancellationNumerator_le_near_zero hL ha ht0.le ht1
    _ ≤ (8 * L + 3) * (1 - Real.exp (-t)) :=
      mul_le_mul_of_nonneg_left hhalf hC

theorem abs_rectangularGammaCancellationNumerator_le_tail
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 1 ≤ t) :
    |rectangularGammaCancellationNumerator L a t| ≤
      5 * L * Real.exp (-(t / 4)) := by
  have ht0 : 0 ≤ t := by linarith
  have hA0 := rectangularTwoEdgeAutocorrelation_zero hL ha
  have hAt0 := rectangularTwoEdgeAutocorrelation_nonneg hL ha
    (by positivity : 0 ≤ t / 2)
  have hAt3 := rectangularTwoEdgeAutocorrelation_le_three_mul hL ha
    (by positivity : 0 ≤ t / 2)
  have hexp : Real.exp (-t) ≤ Real.exp (-(t / 4)) := by
    rw [Real.exp_le_exp]
    linarith
  rw [rectangularGammaCancellationNumerator]
  calc
    |Real.exp (-t) * rectangularTwoEdgeAutocorrelation L a 0 -
        Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2)| ≤
      |Real.exp (-t) * rectangularTwoEdgeAutocorrelation L a 0| +
        |Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2)| :=
      abs_sub _ _
    _ = Real.exp (-t) * (2 * L) +
        Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2) := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (Real.exp_pos _), hA0,
        abs_of_nonneg (by positivity : 0 ≤ 2 * L), abs_of_nonneg hAt0]
    _ ≤ Real.exp (-(t / 4)) * (2 * L) +
        Real.exp (-(t / 4)) * (3 * L) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hexp (by positivity : 0 ≤ 2 * L))
        (mul_le_mul_of_nonneg_left hAt3 (Real.exp_pos _).le)
    _ = 5 * L * Real.exp (-(t / 4)) := by ring

theorem abs_rectangularGammaCancellationKernel_le_tail
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 1 ≤ t) :
    |rectangularGammaCancellationKernel L a t| ≤
      (5 * L / (1 - Real.exp (-1))) * Real.exp (-(t / 4)) := by
  have ht0 : 0 < t := by linarith
  have hd : 0 < 1 - Real.exp (-1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hden : 0 < 1 - Real.exp (-t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hdenlower : 1 - Real.exp (-1) ≤ 1 - Real.exp (-t) := by
    have := Real.exp_le_exp.mpr (by linarith : -t ≤ -1)
    linarith
  have hnum := abs_rectangularGammaCancellationNumerator_le_tail hL ha ht
  have hnonneg : 0 ≤ 5 * L * Real.exp (-(t / 4)) := by positivity
  rw [rectangularGammaCancellationKernel, abs_div, abs_of_pos hden]
  calc
    |rectangularGammaCancellationNumerator L a t| / (1 - Real.exp (-t)) ≤
        (5 * L * Real.exp (-(t / 4))) / (1 - Real.exp (-t)) :=
      div_le_div_of_nonneg_right hnum hden.le
    _ ≤ (5 * L * Real.exp (-(t / 4))) / (1 - Real.exp (-1)) :=
      div_le_div_of_nonneg_left hnonneg hd hdenlower
    _ = (5 * L / (1 - Real.exp (-1))) * Real.exp (-(t / 4)) := by ring

theorem aestronglyMeasurable_rectangularGammaCancellationKernel (L a : ℝ) :
    AEStronglyMeasurable (rectangularGammaCancellationKernel L a) := by
  have hA : Continuous (rectangularTwoEdgeAutocorrelation L a) :=
    continuous_rectangularTwoEdgeAutocorrelation L a
  have hnum : Continuous (rectangularGammaCancellationNumerator L a) := by
    unfold rectangularGammaCancellationNumerator
    exact ((Real.continuous_exp.comp (by fun_prop)).mul (hA.comp continuous_const)).sub
      ((Real.continuous_exp.comp (by fun_prop)).mul (hA.comp (by fun_prop)))
  have hden : Continuous (fun t : ℝ => 1 - Real.exp (-t)) := by fun_prop
  exact (hnum.measurable.div hden.measurable).aestronglyMeasurable

theorem integrableOn_rectangularGammaCancellationKernel
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    IntegrableOn (rectangularGammaCancellationKernel L a) (Ioi 0) := by
  have hmeas := aestronglyMeasurable_rectangularGammaCancellationKernel L a
  have hnear : IntegrableOn (rectangularGammaCancellationKernel L a) (Ioc 0 1) := by
    have hC : 0 ≤ 8 * L + 3 := by positivity
    have hconst : IntegrableOn (fun _ : ℝ => 8 * L + 3) (Ioc 0 1) :=
      integrableOn_const (ne_of_lt measure_Ioc_lt_top)
    refine hconst.mono' hmeas.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact abs_rectangularGammaCancellationKernel_le_near_zero hL ha ht.1 ht.2
  have htail : IntegrableOn (rectangularGammaCancellationKernel L a) (Ioi 1) := by
    let C : ℝ := 5 * L / (1 - Real.exp (-1))
    have hd : 0 < 1 - Real.exp (-1) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    have hC : 0 ≤ C := by
      dsimp only [C]
      exact div_nonneg (by positivity) hd.le
    have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(t / 4))) (Ioi 1) := by
      convert (integrableOn_exp_mul_Ioi (a := (-1 / 4 : ℝ)) (by norm_num) 1) using 1 <;>
        ring
    have hmajor : IntegrableOn (fun t : ℝ => C * Real.exp (-(t / 4))) (Ioi 1) :=
      hexp.const_mul C
    refine hmajor.mono' hmeas.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simpa only [C] using
      abs_rectangularGammaCancellationKernel_le_tail hL ha ht.le
  have hcover : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases ht : t ≤ 1
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr (by linarith)
  rw [← hcover]
  exact hnear.union htail

/-! ## Finite Gauss sums as cutoff Gamma kernels -/

def rectangularEulerGaussResolventTimeIntegrand (L a : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (t : ℂ)) *
    ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) * Complex.exp (t / 2))

theorem integrableOn_rectangularEulerGaussResolventTimeIntegrand
    (L a : ℝ) (n : ℕ) :
    IntegrableOn (rectangularEulerGaussResolventTimeIntegrand L a n) (Ioi 0) := by
  have hg : Integrable (fun t : ℝ => rectangularEulerAutocorrelation L a (t / 2)) := by
    convert (integrable_rectangularEulerAutocorrelation L a).comp_mul_left'
      (by norm_num : (1 / 2 : ℝ) ≠ 0) using 1 <;> ring
  have hexpMeas : AEStronglyMeasurable (fun t : ℝ =>
      Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (t : ℂ))) :=
    (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hexpBound : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0),
      ‖Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (t : ℂ))‖ ≤ 1 := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have ht' : 0 < t := ht
    nlinarith
  have hmul := hg.integrableOn.mul_bdd hexpMeas.restrict hexpBound
  apply hmul.congr
  filter_upwards with t
  rw [rectangularEulerGaussResolventTimeIntegrand, rectangularEulerAutocorrelation]
  push_cast
  ring

def rectangularEulerGaussTimeTerm (L a : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) * (t : ℂ))) *
    (rectangularGammaCancellationNumerator L a t : ℂ)

theorem rectangularEulerGaussTimeTerm_eq_difference
    (L a : ℝ) (n : ℕ) (t : ℝ) :
    rectangularEulerGaussTimeTerm L a n t =
      Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) *
          (rectangularTwoEdgeAutocorrelation L a 0 : ℂ) -
        rectangularEulerGaussResolventTimeIntegrand L a n t := by
  rw [rectangularEulerGaussTimeTerm, rectangularGammaCancellationNumerator,
    rectangularEulerGaussResolventTimeIntegrand]
  push_cast
  have he1 : Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) =
      Complex.exp (-((n : ℂ) * (t : ℂ))) * Complex.exp (-(t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have he2 : Complex.exp (-((n : ℂ) + 3 / 4) * (t : ℂ)) *
      Complex.exp ((t : ℂ) / 2) =
      Complex.exp (-((n : ℂ) * (t : ℂ))) * Complex.exp (-((t : ℂ) / 4)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hsec : Complex.exp (-((n : ℂ) + 3 / 4) * (t : ℂ)) *
      ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) * Complex.exp ((t : ℂ) / 2)) =
      (Complex.exp (-((n : ℂ) * (t : ℂ))) * Complex.exp (-((t : ℂ) / 4))) *
        (rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) := by
    calc
      _ = (Complex.exp (-((n : ℂ) + 3 / 4) * (t : ℂ)) *
          Complex.exp ((t : ℂ) / 2)) *
            (rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) := by ring
      _ = _ := by rw [he2]
  rw [he1, hsec]
  ring

theorem integrableOn_rectangularEulerGaussTimeTerm
    (L a : ℝ) (n : ℕ) :
    IntegrableOn (rectangularEulerGaussTimeTerm L a n) (Ioi 0) := by
  have hq : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hfirst : IntegrableOn (fun t : ℝ =>
      Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) *
        (rectangularTwoEdgeAutocorrelation L a 0 : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hq 0).mul_const _
  have hdiff := hfirst.sub (integrableOn_rectangularEulerGaussResolventTimeIntegrand L a n)
  apply hdiff.congr
  filter_upwards with t
  exact (rectangularEulerGaussTimeTerm_eq_difference L a n t).symm

theorem rectangularEulerGaussTermValue_eq_integral_timeTerm
    (L a : ℝ) (n : ℕ) :
    rectangularEulerGaussTermValue L a n =
      ∫ t : ℝ in Ioi 0, rectangularEulerGaussTimeTerm L a n t := by
  let A0 : ℝ := rectangularTwoEdgeAutocorrelation L a 0
  have hq : (-((n : ℂ) + 1)).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re, Complex.one_re]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hfirstInt : IntegrableOn (fun t : ℝ =>
      Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) * (A0 : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hq 0).mul_const _
  have hfirst :
      (A0 : ℂ) / ((n : ℂ) + 1) =
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-((n : ℂ) + 1) * (t : ℂ)) * (A0 : ℂ) := by
    rw [integral_mul_const, integral_exp_mul_complex_Ioi hq 0]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    field_simp
  have hsecondInt := integrableOn_rectangularEulerGaussResolventTimeIntegrand L a n
  rw [rectangularEulerGaussTermValue]
  change (A0 : ℂ) / ((n : ℂ) + 1) -
      (∫ t : ℝ in Ioi 0, rectangularEulerGaussResolventTimeIntegrand L a n t) = _
  rw [hfirst, ← integral_sub hfirstInt hsecondInt]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [A0]
  exact (rectangularEulerGaussTimeTerm_eq_difference L a n t).symm

def rectangularGammaCancellationPartialKernel (L a : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  rectangularGammaCancellationKernel L a t *
    (1 - Real.exp (-((N : ℝ) * t)))

theorem sum_exp_mul_rectangularGammaCancellationNumerator_eq_partialKernel
    (L a : ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ n ∈ Finset.range N,
        Real.exp (-((n : ℝ) * t)) * rectangularGammaCancellationNumerator L a t =
      rectangularGammaCancellationPartialKernel L a N t := by
  let x : ℝ := Real.exp (-t)
  have hxne : 1 - x ≠ 0 := by
    have : x < 1 := by
      dsimp only [x]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hpow : ∀ n : ℕ, Real.exp (-((n : ℝ) * t)) = x ^ n := by
    intro n
    dsimp only [x]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hnum : rectangularGammaCancellationNumerator L a t =
      rectangularGammaCancellationKernel L a t * (1 - x) := by
    rw [rectangularGammaCancellationKernel]
    dsimp only [x]
    rw [div_mul_cancel₀]
    exact hxne
  rw [show (∑ n ∈ Finset.range N,
      Real.exp (-((n : ℝ) * t)) * rectangularGammaCancellationNumerator L a t) =
      (∑ n ∈ Finset.range N, x ^ n) * rectangularGammaCancellationNumerator L a t by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hpow n]]
  rw [hnum]
  unfold rectangularGammaCancellationPartialKernel
  rw [show Real.exp (-((N : ℝ) * t)) = x ^ N by exact hpow N]
  have hgeo : (∑ n ∈ Finset.range N, x ^ n) * (1 - x) = 1 - x ^ N := by
    have h := geom_sum_mul x N
    nlinarith
  calc
    (∑ n ∈ Finset.range N, x ^ n) *
        (rectangularGammaCancellationKernel L a t * (1 - x)) =
      rectangularGammaCancellationKernel L a t *
        ((∑ n ∈ Finset.range N, x ^ n) * (1 - x)) := by ring
    _ = rectangularGammaCancellationKernel L a t * (1 - x ^ N) := by rw [hgeo]

theorem sum_rectangularEulerGaussTimeTerm_eq_partialKernel
    (L a : ℝ) (N : ℕ) {t : ℝ} (ht : 0 < t) :
    ∑ n ∈ Finset.range N, rectangularEulerGaussTimeTerm L a n t =
      (rectangularGammaCancellationPartialKernel L a N t : ℂ) := by
  rw [show (∑ n ∈ Finset.range N, rectangularEulerGaussTimeTerm L a n t) =
      ((∑ n ∈ Finset.range N,
        Real.exp (-((n : ℝ) * t)) * rectangularGammaCancellationNumerator L a t : ℝ) : ℂ) by
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    rw [rectangularEulerGaussTimeTerm]]
  exact_mod_cast
    sum_exp_mul_rectangularGammaCancellationNumerator_eq_partialKernel L a N ht

theorem rectangularEulerGaussPartialValue_eq_integral_partialKernel
    (L a : ℝ) (N : ℕ) :
    rectangularEulerGaussPartialValue L a N =
      ∫ t : ℝ in Ioi 0, (rectangularGammaCancellationPartialKernel L a N t : ℂ) := by
  unfold rectangularEulerGaussPartialValue
  calc
    (∑ n ∈ Finset.range N, rectangularEulerGaussTermValue L a n) =
        ∑ n ∈ Finset.range N,
          ∫ t : ℝ in Ioi 0, rectangularEulerGaussTimeTerm L a n t := by
      apply Finset.sum_congr rfl
      intro n hn
      exact rectangularEulerGaussTermValue_eq_integral_timeTerm L a n
    _ = ∫ t : ℝ in Ioi 0,
        ∑ n ∈ Finset.range N, rectangularEulerGaussTimeTerm L a n t := by
      rw [MeasureTheory.integral_finsetSum]
      intro n hn
      exact integrableOn_rectangularEulerGaussTimeTerm L a n
    _ = ∫ t : ℝ in Ioi 0,
        (rectangularGammaCancellationPartialKernel L a N t : ℂ) := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      exact sum_rectangularEulerGaussTimeTerm_eq_partialKernel L a N ht

theorem tendsto_integral_rectangularGammaCancellationPartialKernel
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    Tendsto
      (fun N : ℕ => ∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationPartialKernel L a N t)
      atTop
      (nhds (∫ t : ℝ in Ioi 0, rectangularGammaCancellationKernel L a t)) := by
  apply tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioi 0))
    (fun t : ℝ => |rectangularGammaCancellationKernel L a t|)
  · intro N
    unfold rectangularGammaCancellationPartialKernel
    exact ((aestronglyMeasurable_rectangularGammaCancellationKernel L a).mul
      ((by fun_prop : Continuous (fun t : ℝ =>
        1 - Real.exp (-((N : ℝ) * t)))).aestronglyMeasurable)).restrict
  · exact (integrableOn_rectangularGammaCancellationKernel hL ha).norm
  · intro N
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hfac0 : 0 ≤ 1 - Real.exp (-((N : ℝ) * t)) := by
      apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      have ht' : 0 < t := ht
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      nlinarith
    have hfac1 : 1 - Real.exp (-((N : ℝ) * t)) ≤ 1 := by
      linarith [Real.exp_pos (-((N : ℝ) * t))]
    rw [rectangularGammaCancellationPartialKernel, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hfac0]
    exact mul_le_of_le_one_right (abs_nonneg _) hfac1
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    have hx0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
    have hx1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by
      have ht' : 0 < t := ht
      linarith)
    have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1
    have heq : (fun N : ℕ => Real.exp (-((N : ℝ) * t))) =
        fun N : ℕ => (Real.exp (-t)) ^ N := by
      funext N
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hexp : Tendsto (fun N : ℕ => Real.exp (-((N : ℝ) * t))) atTop (nhds 0) := by
      rw [heq]
      exact hpow
    have hK : Tendsto (fun _ : ℕ => rectangularGammaCancellationKernel L a t) atTop
        (nhds (rectangularGammaCancellationKernel L a t)) := tendsto_const_nhds
    have hOne : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa only [rectangularGammaCancellationPartialKernel, sub_zero, mul_one] using
      hK.mul (hOne.sub hexp)

theorem tendsto_rectangularEulerGaussPartialValue_to_cancellationKernel
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    Tendsto (rectangularEulerGaussPartialValue L a) atTop
      (nhds ((∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationKernel L a t : ℝ) : ℂ)) := by
  have hreal := tendsto_integral_rectangularGammaCancellationPartialKernel hL ha
  have hcomplex : Tendsto
      (fun N : ℕ => ((∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationPartialKernel L a N t : ℝ) : ℂ))
      atTop
      (nhds ((∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationKernel L a t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcomplex.congr'
  filter_upwards with N
  rw [rectangularEulerGaussPartialValue_eq_integral_partialKernel]
  exact integral_ofReal.symm

/-- Exact Gauss-to-time-domain identification.  This is the analytic core of the Gamma--polar
cancellation: the literal digamma edge is the absolutely convergent removable-singularity
integral, with no regularity or convergence hypothesis left exposed. -/
theorem integral_rectangularEulerGaussLimitIntegrand_eq_cancellationKernel
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (∫ xi : ℝ, rectangularEulerGaussLimitIntegrand L a xi) =
      ((∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationKernel L a t : ℝ) : ℂ) := by
  exact tendsto_nhds_unique
    (tendsto_rectangularEulerGaussPartialValue hL a)
    (tendsto_rectangularEulerGaussPartialValue_to_cancellationKernel hL ha)

theorem integral_rectangularEulerDigammaIntegrand_eq_cancellationKernel_sub_euler
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (∫ xi : ℝ, rectangularEulerDigammaIntegrand L a xi) =
      ((∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationKernel L a t : ℝ) : ℂ) -
        (Real.eulerMascheroniConstant : ℂ) * (2 * L : ℝ) := by
  let F : ℝ → ℂ := fun xi =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hzero := integral_rectangularEulerFourierKernel hL a 0
  have hFzero : (∫ xi : ℝ, F xi) =
      (rectangularTwoEdgeAutocorrelation L a 0 : ℂ) := by
    simpa only [F, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
      mul_one, zero_div] using hzero
  have hcore := integral_rectangularEulerGaussLimitIntegrand_eq_cancellationKernel hL ha
  rw [show (fun xi : ℝ => rectangularEulerGaussLimitIntegrand L a xi) =
      fun xi : ℝ => rectangularEulerDigammaIntegrand L a xi +
        (Real.eulerMascheroniConstant : ℂ) * F xi by
    funext xi
    rw [rectangularEulerGaussLimitIntegrand, rectangularEulerDigammaIntegrand]
    dsimp only [F]
    ring] at hcore
  rw [integral_add (integrable_rectangularEulerDigammaIntegrand L a)
    (hF.const_mul _), integral_const_mul, hFzero,
    rectangularTwoEdgeAutocorrelation_zero hL ha] at hcore
  exact eq_sub_iff_add_eq.mpr hcore

/-! ## The two rational resolvents are exactly the even polar square -/

def rectangularPolarHalfTilt (L a : ℝ) (x : ℝ) : ℂ :=
  (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp (x / 2)

def rectangularPolarHalfReflectedTilt (L a : ℝ) (x : ℝ) : ℂ :=
  (rectangularTwoEdgeProfile L a (-x) : ℂ) * Complex.exp (x / 2)

def rectangularPolarHalfAutocorrelation (L a : ℝ) (h : ℝ) : ℂ :=
  (rectangularTwoEdgeAutocorrelation L a h : ℂ) * Complex.exp (h / 2)

theorem integrable_rectangularPolarHalfTilt (L a : ℝ) :
    Integrable (rectangularPolarHalfTilt L a) := by
  unfold rectangularPolarHalfTilt
  convert integrable_rectangularTwoEdgeProfile_mul_exp L a (1 / 2) using 1
  funext x
  congr 2
  push_cast
  ring

theorem integrable_rectangularPolarHalfReflectedTilt (L a : ℝ) :
    Integrable (rectangularPolarHalfReflectedTilt L a) := by
  have h := (integrable_rectangularTwoEdgeProfile_mul_exp L a (-1 / 2)).comp_neg
  unfold rectangularPolarHalfReflectedTilt
  convert h using 1
  funext x
  congr 2
  push_cast
  ring

theorem rectangularPolarHalfAutocorrelation_eq_convolution (L a h : ℝ) :
    rectangularPolarHalfAutocorrelation L a h =
      (rectangularPolarHalfReflectedTilt L a ⋆[ContinuousLinearMap.mul ℂ ℂ]
        rectangularPolarHalfTilt L a) h := by
  rw [rectangularPolarHalfAutocorrelation, rectangularTwoEdgeAutocorrelation]
  symm
  change (∫ t : ℝ,
    rectangularPolarHalfReflectedTilt L a t * rectangularPolarHalfTilt L a (h - t)) = _
  rw [← MeasureTheory.integral_neg_eq_self]
  simp only [rectangularPolarHalfReflectedTilt, rectangularPolarHalfTilt, neg_neg,
    sub_neg_eq_add]
  calc
    _ = ∫ t : ℝ,
        (((rectangularTwoEdgeProfile L a (t + h) *
          rectangularTwoEdgeProfile L a t : ℝ) : ℂ) * Complex.exp (h / 2)) := by
      apply integral_congr_ae
      filter_upwards with t
      rw [add_comm h t]
      push_cast
      have hexp : Complex.exp (-t / 2) * Complex.exp ((t + h) / 2) =
          Complex.exp (h / 2) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        _ = (rectangularTwoEdgeProfile L a (t + h) : ℂ) *
            (rectangularTwoEdgeProfile L a t : ℂ) *
              (Complex.exp (-t / 2) * Complex.exp ((t + h) / 2)) := by ring
        _ = _ := by rw [hexp]
    _ = (∫ t : ℝ,
        ((rectangularTwoEdgeProfile L a (t + h) *
          rectangularTwoEdgeProfile L a t : ℝ) : ℂ)) * Complex.exp (h / 2) := by
      rw [integral_mul_const]
    _ = ((∫ t : ℝ,
        rectangularTwoEdgeProfile L a (t + h) *
          rectangularTwoEdgeProfile L a t : ℝ) : ℂ) * Complex.exp (h / 2) := by
      congr 1
      exact integral_ofReal
    _ = _ := by rfl

theorem rectangularTwoEdgeTransform_half_eq_evenPolarFeature
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    rectangularTwoEdgeTransform L a (1 / 2 : ℂ) =
      (rectangularEvenPolarFeature L a : ℂ) := by
  rw [rectangularTwoEdgeTransform]
  rw [rectangularWindowAmplitude_eq_div (by norm_num : (1 / 2 : ℂ) ≠ 0),
    rectangularWindowAmplitude_eq_div (by norm_num : -(1 / 2 : ℂ) ≠ 0)]
  rw [rectangularEvenPolarFeature_eq hL, Real.sinh_eq, Real.sinh_eq]
  push_cast
  ring_nf
  rw [← Complex.exp_add, ← Complex.exp_add]
  ring

theorem integral_rectangularPolarHalfTilt
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ x : ℝ, rectangularPolarHalfTilt L a x) =
      (rectangularEvenPolarFeature L a : ℂ) := by
  unfold rectangularPolarHalfTilt
  rw [show (fun x : ℝ =>
      (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp (x / 2)) =
      fun x : ℝ => (rectangularTwoEdgeProfile L a x : ℂ) *
        Complex.exp ((1 / 2 : ℂ) * x) by
    funext x
    congr 2
    push_cast
    ring]
  change rectangularTwoEdgeLaplaceIntegral L a (1 / 2 : ℂ) = _
  rw [rectangularTwoEdgeLaplaceIntegral_eq_transform hL,
    rectangularTwoEdgeTransform_half_eq_evenPolarFeature hL]

theorem integral_rectangularPolarHalfReflectedTilt
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ x : ℝ, rectangularPolarHalfReflectedTilt L a x) =
      (rectangularEvenPolarFeature L a : ℂ) := by
  rw [← MeasureTheory.integral_neg_eq_self]
  unfold rectangularPolarHalfReflectedTilt
  simp only [neg_neg]
  rw [show (fun x : ℝ =>
      (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp ((-x : ℝ) / 2)) =
      fun x : ℝ => (rectangularTwoEdgeProfile L a x : ℂ) *
        Complex.exp ((-1 / 2 : ℂ) * x) by
    funext x
    congr 2
    push_cast
    ring]
  change rectangularTwoEdgeLaplaceIntegral L a (-1 / 2 : ℂ) = _
  rw [rectangularTwoEdgeLaplaceIntegral_eq_transform hL,
    show (-1 / 2 : ℂ) = -(1 / 2 : ℂ) by ring,
    rectangularTwoEdgeTransform_even,
    rectangularTwoEdgeTransform_half_eq_evenPolarFeature hL]

theorem integral_rectangularPolarHalfAutocorrelation
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ h : ℝ, rectangularPolarHalfAutocorrelation L a h) =
      (rectangularEvenPolarFeature L a : ℂ) ^ 2 := by
  rw [show rectangularPolarHalfAutocorrelation L a =
      rectangularPolarHalfReflectedTilt L a ⋆[ContinuousLinearMap.mul ℂ ℂ]
        rectangularPolarHalfTilt L a by
    funext h
    exact rectangularPolarHalfAutocorrelation_eq_convolution L a h]
  rw [MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (integrable_rectangularPolarHalfReflectedTilt L a)
    (integrable_rectangularPolarHalfTilt L a),
    integral_rectangularPolarHalfReflectedTilt hL,
    integral_rectangularPolarHalfTilt hL]
  simp [pow_two]

theorem rectangularTwoEdgeAutocorrelation_neg (L a h : ℝ) :
    rectangularTwoEdgeAutocorrelation L a (-h) =
      rectangularTwoEdgeAutocorrelation L a h := by
  rw [rectangularTwoEdgeAutocorrelation_eq_four_tents,
    rectangularTwoEdgeAutocorrelation_eq_four_tents]
  rw [abs_neg]
  have hleft : |-h - (2 * a - L)| = |h + (2 * a - L)| := by
    rw [show -h - (2 * a - L) = -(h + (2 * a - L)) by ring, abs_neg]
  have hright : |-h + (2 * a - L)| = |h - (2 * a - L)| := by
    rw [show -h + (2 * a - L) = -(h - (2 * a - L)) by ring, abs_neg]
  rw [hleft, hright]
  ring

theorem integrable_rectangularPolarHalfAutocorrelation (L a : ℝ) :
    Integrable (rectangularPolarHalfAutocorrelation L a) := by
  rw [show rectangularPolarHalfAutocorrelation L a =
      rectangularPolarHalfReflectedTilt L a ⋆[ContinuousLinearMap.mul ℂ ℂ]
        rectangularPolarHalfTilt L a by
    funext h
    exact rectangularPolarHalfAutocorrelation_eq_convolution L a h]
  exact (integrable_rectangularPolarHalfReflectedTilt L a).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) (integrable_rectangularPolarHalfTilt L a)

theorem rectangularPolarResolventPair_eq_two_integral (L a : ℝ) :
    (∫ t : ℝ in Ioi 0,
        Complex.exp (-((3 / 4 : ℝ) : ℂ) * (t : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
            Complex.exp (t / 2))) +
      (∫ t : ℝ in Ioi 0,
        Complex.exp (-((1 / 4 : ℝ) : ℂ) * (t : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
            Complex.exp (t / 2))) =
      2 * ∫ h : ℝ, rectangularPolarHalfAutocorrelation L a h := by
  let H : ℝ → ℂ := rectangularPolarHalfAutocorrelation L a
  have hH : Integrable H := integrable_rectangularPolarHalfAutocorrelation L a
  have hsplit : (∫ h : ℝ in Iic 0, H h) + (∫ h : ℝ in Ioi 0, H h) =
      ∫ h : ℝ, H h := by
    convert! (setIntegral_union (Iic_disjoint_Ioi (Eq.le rfl)) measurableSet_Ioi
      hH.integrableOn hH.integrableOn).symm
    rw [Iic_union_Ioi, Measure.restrict_univ]
  have hplus := MeasureTheory.integral_comp_mul_left_Ioi H 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hminus := MeasureTheory.integral_comp_mul_left_Ioi (fun h : ℝ => H (-h)) 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hfirst : (fun t : ℝ =>
      Complex.exp (-((3 / 4 : ℝ) : ℂ) * (t : ℂ)) *
        ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) * Complex.exp (t / 2))) =
      fun t : ℝ => H (-(t / 2)) := by
    funext t
    dsimp only [H, rectangularPolarHalfAutocorrelation]
    rw [rectangularTwoEdgeAutocorrelation_neg]
    calc
      _ = (rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
          (Complex.exp (-((3 / 4 : ℝ) : ℂ) * (t : ℂ)) * Complex.exp (t / 2)) := by
        ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
  have hsecond : (fun t : ℝ =>
      Complex.exp (-((1 / 4 : ℝ) : ℂ) * (t : ℂ)) *
        ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) * Complex.exp (t / 2))) =
      fun t : ℝ => H (t / 2) := by
    funext t
    dsimp only [H, rectangularPolarHalfAutocorrelation]
    calc
      _ = (rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
          (Complex.exp (-((1 / 4 : ℝ) : ℂ) * (t : ℂ)) * Complex.exp (t / 2)) := by
        ring
      _ = _ := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
  rw [hfirst, hsecond]
  have hplus' : (∫ t : ℝ in Ioi 0, H (t / 2)) =
      2 * ∫ h : ℝ in Ioi 0, H h := by
    norm_num at hplus
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hplus
  have hminus' : (∫ t : ℝ in Ioi 0, H (-(t / 2))) =
      2 * ∫ h : ℝ in Iic 0, H h := by
    norm_num at hminus
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hminus
  rw [hplus', hminus']
  rw [← mul_add, hsplit]

theorem rectangularPolarResolventPair_eq_two_mul_sq
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ t : ℝ in Ioi 0,
        Complex.exp (-((3 / 4 : ℝ) : ℂ) * (t : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
            Complex.exp (t / 2))) +
      (∫ t : ℝ in Ioi 0,
        Complex.exp (-((1 / 4 : ℝ) : ℂ) * (t : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation L a (t / 2) : ℂ) *
            Complex.exp (t / 2))) =
      (2 * rectangularEvenPolarFeature L a ^ 2 : ℝ) := by
  rw [rectangularPolarResolventPair_eq_two_integral L a,
    integral_rectangularPolarHalfAutocorrelation hL a]
  push_cast
  ring

def rectangularEulerRationalIntegrand (L a : ℝ) (xi : ℝ) : ℂ :=
  rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2 *
    (2 / rectangularEulerArchPoint xi + 2 / (rectangularEulerArchPoint xi - 1))

theorem integral_rectangularEulerRationalIntegrand_eq_two_mul_polar_sq
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ xi : ℝ, rectangularEulerRationalIntegrand L a xi) =
      (2 * rectangularEvenPolarFeature L a ^ 2 : ℝ) := by
  let F : ℝ → ℂ := fun xi =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2
  let d0 : ℝ → ℂ := fun xi =>
    ((3 / 4 : ℝ) : ℂ) - ((Real.pi * xi : ℝ) : ℂ) * I
  let d1 : ℝ → ℂ := fun xi =>
    ((1 / 4 : ℝ) : ℂ) - ((Real.pi * xi : ℝ) : ℂ) * I
  have hd0 : ∀ xi, d0 xi ≠ 0 := by
    intro xi h
    have hre := congrArg Complex.re h
    dsimp only [d0] at hre
    simp [Complex.mul_re] at hre
  have hd1 : ∀ xi, d1 xi ≠ 0 := by
    intro xi h
    have hre := congrArg Complex.re h
    dsimp only [d1] at hre
    simp [Complex.mul_re] at hre
  have hfun : rectangularEulerRationalIntegrand L a =
      fun xi => F xi * (d0 xi)⁻¹ + F xi * (d1 xi)⁻¹ := by
    funext xi
    rw [rectangularEulerRationalIntegrand]
    dsimp only [F, d0, d1, rectangularEulerArchPoint]
    have hs0 : (3 / 2 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) =
        2 * (((3 / 4 : ℝ) : ℂ) - ((Real.pi * xi : ℝ) : ℂ) * I) := by
      push_cast
      ring
    have hs1 : (3 / 2 - ((2 * Real.pi * xi : ℝ) : ℂ) * I - 1) =
        2 * (((1 / 4 : ℝ) : ℂ) - ((Real.pi * xi : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [hs1, hs0]
    field_simp [hd0 xi, hd1 xi]
  rw [hfun]
  have hi0 := integrable_rectangularEulerFourierKernel_mul_verticalResolvent
    (c := (3 / 4 : ℝ)) (by norm_num) L a
  have hi1 := integrable_rectangularEulerFourierKernel_mul_verticalResolvent
    (c := (1 / 4 : ℝ)) (by norm_num) L a
  rw [integral_add hi0 hi1,
    integral_rectangularEulerFourierKernel_mul_verticalResolvent hL
      (by norm_num : (0 : ℝ) < 3 / 4) a,
    integral_rectangularEulerFourierKernel_mul_verticalResolvent hL
      (by norm_num : (0 : ℝ) < 1 / 4) a,
    rectangularPolarResolventPair_eq_two_mul_sq hL a]

theorem integrable_rectangularEulerRationalIntegrand (L a : ℝ) :
    Integrable (rectangularEulerRationalIntegrand L a) := by
  let F : ℝ → ℂ := fun xi =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hcomb : Integrable (fun xi : ℝ =>
      2 * rectangularEulerArchIntegrand L a xi -
        rectangularEulerDigammaIntegrand L a xi +
          (Real.log Real.pi : ℂ) * F xi) :=
    ((integrable_rectangularEulerArchIntegrand L a).const_mul 2).sub
      (integrable_rectangularEulerDigammaIntegrand L a) |>.add
        (hF.const_mul (Real.log Real.pi : ℂ))
  apply hcomb.congr
  filter_upwards with xi
  rw [rectangularEulerRationalIntegrand, rectangularEulerArchIntegrand,
    rectangularEulerDigammaIntegrand,
    digamma_rectangularEulerDigammaPoint_eq_arch]
  dsimp only [F]
  ring

theorem two_mul_integral_rectangularEulerArchIntegrand_eq
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    2 * (∫ xi : ℝ, rectangularEulerArchIntegrand L a xi) =
      ((∫ t : ℝ in Ioi 0,
        rectangularGammaCancellationKernel L a t : ℝ) : ℂ) +
        (2 * rectangularEvenPolarFeature L a ^ 2 : ℝ) -
          ((Real.eulerMascheroniConstant + Real.log Real.pi) : ℂ) * (2 * L : ℝ) := by
  let F : ℝ → ℂ := fun xi =>
    rectangularTwoEdgeTransform L a
      (1 - ((2 * Real.pi * xi : ℝ) : ℂ) * I) ^ 2
  have hF : Integrable F := by
    simpa only [F] using integrable_rectangularTwoEdgeTransform_eulerLine_sq L a
  have hfun : (fun xi : ℝ => 2 * rectangularEulerArchIntegrand L a xi) =
      fun xi : ℝ => rectangularEulerDigammaIntegrand L a xi +
        rectangularEulerRationalIntegrand L a xi - (Real.log Real.pi : ℂ) * F xi := by
    funext xi
    rw [rectangularEulerArchIntegrand, rectangularEulerDigammaIntegrand,
      rectangularEulerRationalIntegrand,
      digamma_rectangularEulerDigammaPoint_eq_arch]
    dsimp only [F]
    ring
  rw [← integral_const_mul]
  rw [hfun]
  have hzero := integral_rectangularEulerFourierKernel hL a 0
  have hFzero : (∫ xi : ℝ, F xi) = (2 * L : ℝ) := by
    rw [show (∫ xi : ℝ, F xi) =
        (rectangularTwoEdgeAutocorrelation L a 0 : ℂ) by
      simpa only [F, mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
        mul_one, zero_div] using hzero,
      rectangularTwoEdgeAutocorrelation_zero hL ha]
  calc
    (∫ xi : ℝ, rectangularEulerDigammaIntegrand L a xi +
        rectangularEulerRationalIntegrand L a xi - (Real.log Real.pi : ℂ) * F xi) =
      (∫ xi : ℝ, rectangularEulerDigammaIntegrand L a xi +
        rectangularEulerRationalIntegrand L a xi) -
          ∫ xi : ℝ, (Real.log Real.pi : ℂ) * F xi := by
      exact integral_sub
        ((integrable_rectangularEulerDigammaIntegrand L a).add
          (integrable_rectangularEulerRationalIntegrand L a))
        (hF.const_mul (Real.log Real.pi : ℂ))
    _ =
      (∫ xi : ℝ, rectangularEulerDigammaIntegrand L a xi) +
        (∫ xi : ℝ, rectangularEulerRationalIntegrand L a xi) -
          (Real.log Real.pi : ℂ) * ∫ xi : ℝ, F xi := by
      rw [integral_add (integrable_rectangularEulerDigammaIntegrand L a)
          (integrable_rectangularEulerRationalIntegrand L a), integral_const_mul]
    _ = _ := by
      rw [integral_rectangularEulerDigammaIntegrand_eq_cancellationKernel_sub_euler hL ha,
        integral_rectangularEulerRationalIntegrand_eq_two_mul_polar_sq hL a, hFzero]
      push_cast
      ring

theorem normalizedRectangularBottomArchContribution_eq_two_mul_eulerIntegral
    (L a : ℝ) :
    normalizedRectangularBottomArchContribution L a =
      2 * ∫ xi : ℝ, rectangularEulerArchIntegrand L a xi := by
  rw [normalizedRectangularBottomArchContribution_eq]
  let g : ℝ → ℂ := rectangularBottomArchIntegrand L a
  have hscale := MeasureTheory.Measure.integral_comp_mul_left g (-2 * Real.pi)
  have hfactor : |(-2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [abs_inv]
    have hneg : -2 * Real.pi < 0 := mul_neg_of_neg_of_pos (by norm_num) Real.pi_pos
    rw [abs_of_neg hneg]
    congr 1
    ring
  rw [hfactor] at hscale
  have hleft : (∫ xi : ℝ, g ((-2 * Real.pi) * xi)) =
      ∫ xi : ℝ, rectangularEulerArchIntegrand L a xi := by
    apply integral_congr_ae
    filter_upwards with xi
    exact rectangularBottomArchIntegrand_scale L a xi
  rw [hleft] at hscale
  dsimp only [g] at hscale
  rw [Complex.real_smul] at hscale
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast at hscale ⊢
  field_simp [hpi] at hscale
  rw [← hscale]
  field_simp [hpi]

/-- The aperture-stable remainder after the exact growing polar square has been removed from the
archimedean edge. -/
def rectangularGammaPolarCorrection (L a : ℝ) : ℝ :=
  (∫ t : ℝ in Ioi 0, rectangularGammaCancellationKernel L a t) -
    (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)

/-- **Exact Gamma--polar cancellation law.**  The entire aperture-growing part of the sharp
rectangular archimedean contribution is the elementary even polar square.  What remains is the
real, absolutely convergent cancellation kernel. -/
theorem normalizedRectangularBottomArchContribution_sub_two_mul_polar_sq
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    normalizedRectangularBottomArchContribution L a -
        (2 * rectangularEvenPolarFeature L a ^ 2 : ℝ) =
      (rectangularGammaPolarCorrection L a : ℂ) := by
  rw [normalizedRectangularBottomArchContribution_eq_two_mul_eulerIntegral,
    two_mul_integral_rectangularEulerArchIntegrand_eq hL ha,
    rectangularGammaPolarCorrection]
  push_cast
  ring

/-- An aperture-independent integrable majorant for the tail of the Gamma cancellation kernel. -/
def rectangularGammaCancellationTailMajorant (L t : ℝ) : ℝ :=
  (5 * L / (1 - Real.exp (-1))) * Real.exp (-(t / 4))

/-- One explicit aperture-independent bound for the Gamma--polar correction at fixed window length. -/
def rectangularGammaPolarUniformBound (L : ℝ) : ℝ :=
  (8 * L + 3) +
    (∫ t : ℝ in Ioi 1, rectangularGammaCancellationTailMajorant L t) +
      |(Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)|

theorem integrableOn_rectangularGammaCancellationTailMajorant (L : ℝ) :
    IntegrableOn (rectangularGammaCancellationTailMajorant L) (Ioi 1) := by
  have hexp : IntegrableOn (fun t : ℝ => Real.exp (-(t / 4))) (Ioi 1) := by
    convert (integrableOn_exp_mul_Ioi (a := (-1 / 4 : ℝ)) (by norm_num) 1) using 1 <;>
      ring_nf
  exact hexp.const_mul _

/-- **Uniform Gamma--polar remainder law.**  For fixed `L`, the exact cancellation remainder is
bounded by one explicit constant for every aperture `a ≥ L`. -/
theorem abs_rectangularGammaPolarCorrection_le_uniformBound
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    |rectangularGammaPolarCorrection L a| ≤ rectangularGammaPolarUniformBound L := by
  let K : ℝ → ℝ := rectangularGammaCancellationKernel L a
  let M : ℝ → ℝ := rectangularGammaCancellationTailMajorant L
  have hK := integrableOn_rectangularGammaCancellationKernel hL ha
  have hnearInt : IntegrableOn K (Ioc 0 1) := hK.mono_set (by
    intro t ht
    exact ht.1)
  have htailInt : IntegrableOn K (Ioi 1) := hK.mono_set (by
    intro t ht
    change 0 < t
    change 1 < t at ht
    exact lt_trans zero_lt_one ht)
  have hMInt : IntegrableOn M (Ioi 1) :=
    integrableOn_rectangularGammaCancellationTailMajorant L
  have hnear : |∫ t : ℝ in Ioc 0 1, K t| ≤ 8 * L + 3 := by
    have h := norm_setIntegral_le_of_norm_le_const
      (μ := volume) (f := K) (C := 8 * L + 3) measure_Ioc_lt_top fun t ht => by
        simpa only [Real.norm_eq_abs, K] using
          abs_rectangularGammaCancellationKernel_le_near_zero hL ha ht.1 ht.2
    simpa only [Real.norm_eq_abs, Measure.real, ENNReal.toReal_one, ENNReal.ofReal_one,
      mul_one, Real.volume_Ioc, sub_zero] using h
  have htail : |∫ t : ℝ in Ioi 1, K t| ≤ ∫ t : ℝ in Ioi 1, M t := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le hMInt
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    simpa only [K, M, rectangularGammaCancellationTailMajorant] using
      abs_rectangularGammaCancellationKernel_le_tail hL ha ht.le
  have hcover : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := by
    ext t
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (h | h) <;> linarith
    · intro h
      by_cases ht : t ≤ 1
      · exact Or.inl ⟨h, ht⟩
      · exact Or.inr (by linarith)
  have hsplit : (∫ t : ℝ in Ioi 0, K t) =
      (∫ t : ℝ in Ioc 0 1, K t) + ∫ t : ℝ in Ioi 1, K t := by
    rw [← hcover]
    exact setIntegral_union (by
      rw [disjoint_left]
      intro t ht1 ht2
      exact (not_lt_of_ge ht1.2) ht2) measurableSet_Ioi hnearInt htailInt
  rw [rectangularGammaPolarCorrection,
    show (∫ t : ℝ in Ioi 0, rectangularGammaCancellationKernel L a t) =
      ∫ t : ℝ in Ioi 0, K t by rfl, hsplit]
  unfold rectangularGammaPolarUniformBound
  dsimp only [M] at htail
  calc
    |(∫ t : ℝ in Ioc 0 1, K t) + (∫ t : ℝ in Ioi 1, K t) -
        (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)| ≤
      |∫ t : ℝ in Ioc 0 1, K t| + |∫ t : ℝ in Ioi 1, K t| +
        |(Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)| := by
      calc
        |_ - _| ≤ |(∫ t : ℝ in Ioc 0 1, K t) + (∫ t : ℝ in Ioi 1, K t)| +
            |(Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)| := abs_sub _ _
        _ ≤ _ := by gcongr; exact abs_add_le _ _
    _ ≤ (8 * L + 3) +
        (∫ t : ℝ in Ioi 1, rectangularGammaCancellationTailMajorant L t) +
          |(Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L)| := by
      gcongr

theorem rectangularGammaPolarUniformBound_nonneg {L : ℝ} (hL : 0 ≤ L) :
    0 ≤ rectangularGammaPolarUniformBound L := by
  exact le_trans (abs_nonneg (rectangularGammaPolarCorrection L L))
    (abs_rectangularGammaPolarCorrection_le_uniformBound hL le_rfl)

theorem exists_nonnegative_uniform_bound_rectangularGammaPolarCorrection
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, L ≤ a → |rectangularGammaPolarCorrection L a| ≤ C := by
  exact ⟨rectangularGammaPolarUniformBound L,
    rectangularGammaPolarUniformBound_nonneg hL,
    fun _ ha => abs_rectangularGammaPolarCorrection_le_uniformBound hL ha⟩

end RHTower
