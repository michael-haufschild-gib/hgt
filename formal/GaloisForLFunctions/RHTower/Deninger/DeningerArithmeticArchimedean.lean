import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticTimeDistribution
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaCancellation

open Complex Filter MeasureTheory Set
open scoped BigOperators FourierTransform

noncomputable section

namespace RHTower

noncomputable def deningerEulerLineSchwartz
    (φ : DeningerTimeTestFunction) : SchwartzMap ℝ ℂ :=
  𝓕 (deningerExponentiallyTiltedTimeSchwartz φ (3 / 2))

@[simp]
theorem deningerEulerLineSchwartz_apply
    (φ : DeningerTimeTestFunction) (ξ : ℝ) :
    deningerEulerLineSchwartz φ ξ =
      deningerTimeTestLaplace φ
        (((3 / 2 : ℝ) : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) * I) := by
  change
    (𝓕 (deningerExponentiallyTiltedTimeSchwartz φ (3 / 2)) :
      SchwartzMap ℝ ℂ) ξ = _
  rw [SchwartzMap.fourier_coe]
  change
    𝓕 (deningerExponentiallyTiltedTimeTest φ (3 / 2)) ξ = _
  rw [fourier_deningerExponentiallyTiltedTimeTest]

def deningerEulerDigammaGrowthConstant : ℝ :=
  Real.log Real.pi +
    GaloisForLFunctions.digammaVerticalLogConstant + 2

theorem deningerEulerDigammaGrowthConstant_nonneg :
    0 ≤ deningerEulerDigammaGrowthConstant := by
  unfold deningerEulerDigammaGrowthConstant
  have hlogpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hD :
      0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
    unfold GaloisForLFunctions.digammaVerticalLogConstant
    have hlog2 : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    positivity
  positivity

theorem norm_digamma_rectangularEulerDigammaPoint_le_probe
    {ξ : ℝ} (hξ : 1 ≤ |ξ|) :
    ‖Complex.digamma (rectangularEulerDigammaPoint ξ)‖ ≤
      deningerEulerDigammaGrowthConstant *
        (1 + ξ ^ 2) ^ (1 / 4 : ℝ) := by
  have hraw :
      ‖Complex.digamma (rectangularEulerDigammaPoint ξ)‖ ≤
        Real.log (Real.pi * |ξ|) +
          GaloisForLFunctions.digammaVerticalLogConstant := by
    rw [rectangularEulerDigammaPoint_eq]
    exact norm_digamma_rectangularEulerArchPoint_half_le hξ
  have habspos : 0 < |ξ| :=
    lt_of_lt_of_le zero_lt_one hξ
  have hlogmul :
      Real.log (Real.pi * |ξ|) =
        Real.log Real.pi + Real.log |ξ| := by
    rw [Real.log_mul Real.pi_pos.ne' habspos.ne']
  have hbase : (1 : ℝ) ≤ 1 + ξ ^ 2 := by
    nlinarith [sq_nonneg ξ]
  have hquarterOne :
      1 ≤ (1 + ξ ^ 2) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hlogabs :
      Real.log |ξ| ≤
        2 * (1 + ξ ^ 2) ^ (1 / 4 : ℝ) := by
    have hlogsq :
        2 * Real.log |ξ| = Real.log (ξ ^ 2) := by
      rw [← sq_abs, Real.log_pow]
      ring
    have hlogle :
        Real.log (ξ ^ 2) ≤
          Real.log (1 + ξ ^ 2) := by
      exact Real.log_le_log
        (sq_pos_of_ne_zero (abs_ne_zero.mp habspos.ne'))
        (by linarith)
    have hrawpow :=
      Real.log_le_rpow_div
        (x := 1 + ξ ^ 2) (by positivity)
        (by norm_num : (0 : ℝ) < 1 / 4)
    have hquarter :
        Real.log (1 + ξ ^ 2) / 4 ≤
          (1 + ξ ^ 2) ^ (1 / 4 : ℝ) := by
      nlinarith
    linarith
  have hlogpi : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hD :
      0 ≤ GaloisForLFunctions.digammaVerticalLogConstant := by
    unfold GaloisForLFunctions.digammaVerticalLogConstant
    have hlog2 : 0 ≤ Real.log 2 :=
      Real.log_nonneg (by norm_num)
    positivity
  rw [hlogmul] at hraw
  calc
    ‖Complex.digamma (rectangularEulerDigammaPoint ξ)‖ ≤
        Real.log Real.pi + Real.log |ξ| +
          GaloisForLFunctions.digammaVerticalLogConstant := hraw
    _ =
        (Real.log Real.pi +
          GaloisForLFunctions.digammaVerticalLogConstant) +
          Real.log |ξ| := by ring
    _ ≤
        (Real.log Real.pi +
            GaloisForLFunctions.digammaVerticalLogConstant) *
            (1 + ξ ^ 2) ^ (1 / 4 : ℝ) +
          2 * (1 + ξ ^ 2) ^ (1 / 4 : ℝ) := by
      exact add_le_add
        (le_mul_of_one_le_right
          (add_nonneg hlogpi hD) hquarterOne)
        hlogabs
    _ = deningerEulerDigammaGrowthConstant *
        (1 + ξ ^ 2) ^ (1 / 4 : ℝ) := by
      unfold deningerEulerDigammaGrowthConstant
      ring

def deningerEulerGaussGrowthConstant : ℝ :=
  deningerEulerDigammaGrowthConstant +
    (|Real.eulerMascheroniConstant| + 1) +
      3 * rectangularEulerGaussLogGrowthConstant

theorem deningerEulerGaussGrowthConstant_nonneg :
    0 ≤ deningerEulerGaussGrowthConstant := by
  unfold deningerEulerGaussGrowthConstant
  exact add_nonneg
    (add_nonneg
      deningerEulerDigammaGrowthConstant_nonneg
      (by positivity))
    (mul_nonneg (by norm_num)
      rectangularEulerGaussLogGrowthConstant_nonneg)

def deningerEulerGaussWeight (ξ : ℝ) : ℝ :=
  ‖Complex.digamma (rectangularEulerDigammaPoint ξ)‖ +
    |Real.eulerMascheroniConstant| + 1 +
      3 * rectangularEulerGaussLogWeight ξ

theorem deningerEulerGaussWeight_nonneg (ξ : ℝ) :
    0 ≤ deningerEulerGaussWeight ξ := by
  unfold deningerEulerGaussWeight
  have hW := rectangularEulerGaussLogWeight_nonneg ξ
  positivity

theorem deningerEulerGaussWeight_le
    {ξ : ℝ} (hξ : 1 ≤ |ξ|) :
    deningerEulerGaussWeight ξ ≤
      deningerEulerGaussGrowthConstant *
        (1 + ξ ^ 2) ^ (1 / 4 : ℝ) := by
  have hD :=
    norm_digamma_rectangularEulerDigammaPoint_le_probe hξ
  have hW :=
    rectangularEulerGaussLogWeight_le hξ
  have hbase : (1 : ℝ) ≤ 1 + ξ ^ 2 := by
    nlinarith [sq_nonneg ξ]
  have hquarterOne :
      1 ≤ (1 + ξ ^ 2) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hconst :
      |Real.eulerMascheroniConstant| + 1 ≤
        (|Real.eulerMascheroniConstant| + 1) *
          (1 + ξ ^ 2) ^ (1 / 4 : ℝ) :=
    le_mul_of_one_le_right (by positivity) hquarterOne
  have hW3 :
      3 * rectangularEulerGaussLogWeight ξ ≤
        3 *
          (rectangularEulerGaussLogGrowthConstant *
            (1 + ξ ^ 2) ^ (1 / 4 : ℝ)) :=
    mul_le_mul_of_nonneg_left hW (by norm_num)
  unfold deningerEulerGaussWeight
    deningerEulerGaussGrowthConstant
  calc
    ‖Complex.digamma (rectangularEulerDigammaPoint ξ)‖ +
          |Real.eulerMascheroniConstant| + 1 +
        3 * rectangularEulerGaussLogWeight ξ ≤
      deningerEulerDigammaGrowthConstant *
            (1 + ξ ^ 2) ^ (1 / 4 : ℝ) +
          (|Real.eulerMascheroniConstant| + 1) *
            (1 + ξ ^ 2) ^ (1 / 4 : ℝ) +
        3 *
          (rectangularEulerGaussLogGrowthConstant *
            (1 + ξ ^ 2) ^ (1 / 4 : ℝ)) := by
      linarith
    _ = _ := by ring

def deningerEulerGaussMajorant
    (φ : DeningerTimeTestFunction) (ξ : ℝ) : ℝ :=
  ‖deningerEulerLineSchwartz φ ξ‖ *
    deningerEulerGaussWeight ξ

def deningerEulerLineFourthSeminorm
    (φ : DeningerTimeTestFunction) : ℝ :=
  SchwartzMap.seminorm ℂ 4 0
    (deningerEulerLineSchwartz φ)

def deningerEulerGaussTailMajorant
    (φ : DeningerTimeTestFunction) (ξ : ℝ) : ℝ :=
  (4 * deningerEulerLineFourthSeminorm φ *
      deningerEulerGaussGrowthConstant) *
    (1 + ξ ^ 2)⁻¹

theorem continuous_deningerEulerGaussWeight :
    Continuous deningerEulerGaussWeight := by
  have hp : Continuous rectangularEulerDigammaPoint := by
    unfold rectangularEulerDigammaPoint
    fun_prop
  have hmaps :
      MapsTo rectangularEulerDigammaPoint univ
        {z : ℂ | 0 < z.re} := by
    intro ξ _
    simp only [mem_setOf_eq,
      rectangularEulerDigammaPoint_re]
    norm_num
  have hdig :
      Continuous
        (fun ξ : ℝ =>
          Complex.digamma
            (rectangularEulerDigammaPoint ξ)) :=
    digamma_continuousOn_re_pos.comp_continuous hp
      (fun ξ => hmaps (mem_univ ξ))
  have harg :
      Continuous
        (fun ξ : ℝ =>
          1 + 2 *
            ‖rectangularEulerDigammaPoint ξ - 1‖) := by
    fun_prop
  have hargne :
      ∀ ξ : ℝ,
        1 + 2 *
          ‖rectangularEulerDigammaPoint ξ - 1‖ ≠ 0 := by
    intro ξ
    positivity
  have hweight :
      Continuous rectangularEulerGaussLogWeight := by
    unfold rectangularEulerGaussLogWeight
    exact continuous_const.add (harg.log hargne)
  unfold deningerEulerGaussWeight
  exact (((hdig.norm.add continuous_const).add
    continuous_const).add
      (hweight.const_mul 3))

theorem continuous_deningerEulerGaussMajorant
    (φ : DeningerTimeTestFunction) :
    Continuous (deningerEulerGaussMajorant φ) := by
  unfold deningerEulerGaussMajorant
  exact
    (deningerEulerLineSchwartz φ).continuous.norm.mul
      continuous_deningerEulerGaussWeight

theorem integrable_deningerEulerGaussTailMajorant
    (φ : DeningerTimeTestFunction) :
    Integrable (deningerEulerGaussTailMajorant φ) := by
  exact integrable_inv_one_add_sq.const_mul
    (4 * deningerEulerLineFourthSeminorm φ *
      deningerEulerGaussGrowthConstant)

theorem norm_deningerEulerGaussMajorant_le_tail
    (φ : DeningerTimeTestFunction) {ξ : ℝ}
    (hξ : 1 ≤ |ξ|) :
    ‖deningerEulerGaussMajorant φ ξ‖ ≤
      deningerEulerGaussTailMajorant φ ξ := by
  let F : SchwartzMap ℝ ℂ :=
    deningerEulerLineSchwartz φ
  let S : ℝ :=
    deningerEulerLineFourthSeminorm φ
  let C : ℝ :=
    deningerEulerGaussGrowthConstant
  have hS : 0 ≤ S := by
    dsimp only [S, deningerEulerLineFourthSeminorm]
    positivity
  have hC : 0 ≤ C := by
    exact deningerEulerGaussGrowthConstant_nonneg
  have hF0 : 0 ≤ ‖F ξ‖ := norm_nonneg _
  have hW0 :
      0 ≤ deningerEulerGaussWeight ξ :=
    deningerEulerGaussWeight_nonneg ξ
  have hsemRaw :=
    SchwartzMap.norm_pow_mul_le_seminorm
      ℂ F 4 ξ
  have hpow :
      ‖ξ‖ ^ 4 = ξ ^ 4 := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs ξ]
  have hsem :
      ξ ^ 4 * ‖F ξ‖ ≤ S := by
    simpa only [hpow, S,
      deningerEulerLineFourthSeminorm, F] using hsemRaw
  have hweight :=
    deningerEulerGaussWeight_le hξ
  have hbase : (1 : ℝ) ≤ 1 + ξ ^ 2 := by
    nlinarith [sq_nonneg ξ]
  have hrpow :
      (1 + ξ ^ 2) ^ (1 / 4 : ℝ) ≤
        1 + ξ ^ 2 :=
    Real.rpow_le_self_of_one_le hbase (by norm_num)
  have hweight' :
      deningerEulerGaussWeight ξ ≤
        C * (1 + ξ ^ 2) := by
    exact hweight.trans
      (mul_le_mul_of_nonneg_left hrpow hC)
  have hξsq : 1 ≤ ξ ^ 2 := by
    nlinarith [sq_abs ξ]
  have hquad :
      (1 + ξ ^ 2) ^ 2 ≤ 4 * ξ ^ 4 := by
    nlinarith [sq_nonneg (ξ ^ 2 - 1)]
  have hden : 0 < 1 + ξ ^ 2 := by positivity
  rw [deningerEulerGaussMajorant,
    Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg hF0 hW0)]
  rw [deningerEulerGaussTailMajorant]
  rw [show
      (4 * deningerEulerLineFourthSeminorm φ *
          deningerEulerGaussGrowthConstant) *
          (1 + ξ ^ 2)⁻¹ =
        (4 * S * C) / (1 + ξ ^ 2) by
    dsimp only [S, C]
    rw [div_eq_mul_inv]]
  rw [le_div_iff₀ hden]
  calc
    ‖F ξ‖ * deningerEulerGaussWeight ξ *
          (1 + ξ ^ 2) ≤
        ‖F ξ‖ * (C * (1 + ξ ^ 2)) *
          (1 + ξ ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hweight' hF0)
        hden.le
    _ = ‖F ξ‖ * C * (1 + ξ ^ 2) ^ 2 := by
      ring
    _ ≤ ‖F ξ‖ * C * (4 * ξ ^ 4) := by
      exact mul_le_mul_of_nonneg_left hquad
        (mul_nonneg hF0 hC)
    _ = 4 * C * (ξ ^ 4 * ‖F ξ‖) := by ring
    _ ≤ 4 * C * S := by
      exact mul_le_mul_of_nonneg_left hsem
        (mul_nonneg (by norm_num) hC)
    _ = 4 * S * C := by ring

theorem integrable_deningerEulerGaussMajorant
    (φ : DeningerTimeTestFunction) :
    Integrable (deningerEulerGaussMajorant φ) := by
  let T : Set ℝ := {ξ : ℝ | 1 ≤ |ξ|}
  have hT : MeasurableSet T := by
    dsimp only [T]
    exact measurableSet_le measurable_const
      continuous_abs.measurable
  have htail :
      IntegrableOn (deningerEulerGaussMajorant φ) T := by
    refine
      (integrable_deningerEulerGaussTailMajorant φ).integrableOn.mono'
        ?_ ?_
    · exact
        (continuous_deningerEulerGaussMajorant φ).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict hT] with ξ hξ
      exact
        norm_deningerEulerGaussMajorant_le_tail
          φ hξ
  have hcompact :
      IntegrableOn
        (deningerEulerGaussMajorant φ)
        (Icc (-1) 1) :=
    (continuous_deningerEulerGaussMajorant φ).integrableOn_Icc
  have hcover :
      Icc (-1 : ℝ) 1 ∪ T = univ := by
    ext ξ
    simp only [mem_union, mem_Icc, mem_univ,
      iff_true, T, mem_setOf_eq]
    by_cases h : |ξ| ≤ 1
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

theorem deningerEulerLine_half_eq_rectangularEulerDigammaPoint
    (ξ : ℝ) :
    (((3 / 2 : ℝ) : ℂ) -
        ((2 * Real.pi * ξ : ℝ) : ℂ) * I) / 2 =
      rectangularEulerDigammaPoint ξ := by
  unfold rectangularEulerDigammaPoint
  push_cast
  ring

def deningerEulerGaussPartialIntegrand
    (φ : DeningerTimeTestFunction) (N : ℕ) (ξ : ℝ) : ℂ :=
  deningerEulerLineSchwartz φ ξ *
    ∑ n ∈ Finset.range N,
      gaussDigammaSeriesTerm
        (rectangularEulerDigammaPoint ξ) n

def deningerEulerGaussLimitIntegrand
    (φ : DeningerTimeTestFunction) (ξ : ℝ) : ℂ :=
  deningerEulerLineSchwartz φ ξ *
    (Complex.digamma (rectangularEulerDigammaPoint ξ) +
      (Real.eulerMascheroniConstant : ℂ))

theorem integrable_deningerEulerGaussPartialIntegrand
    (φ : DeningerTimeTestFunction) (N : ℕ) :
    Integrable
      (deningerEulerGaussPartialIntegrand φ N) := by
  rw [show
      deningerEulerGaussPartialIntegrand φ N =
        fun ξ : ℝ =>
          ∑ n ∈ Finset.range N,
            deningerEulerLineSchwartz φ ξ *
              gaussDigammaSeriesTerm
                (rectangularEulerDigammaPoint ξ) n by
    funext ξ
    rw [deningerEulerGaussPartialIntegrand,
      Finset.mul_sum]]
  exact MeasureTheory.integrable_finsetSum _ fun n _ => by
    simpa only [
      deningerEulerLineSchwartz_apply,
      ← deningerEulerLine_half_eq_rectangularEulerDigammaPoint] using
        integrable_deningerTimeTestLaplace_mul_gaussDigammaSeriesTerm
          φ n

theorem norm_deningerEulerGaussPartialIntegrand_le_majorant
    (φ : DeningerTimeTestFunction) (N : ℕ) (ξ : ℝ) :
    ‖deningerEulerGaussPartialIntegrand φ N ξ‖ ≤
      deningerEulerGaussMajorant φ ξ := by
  have hsum :=
    norm_sum_gaussDigammaSeriesTerm_threeQuarter_le
      (rectangularEulerDigammaPoint_re ξ) N
  rw [deningerEulerGaussPartialIntegrand,
    deningerEulerGaussMajorant, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [
    deningerEulerGaussWeight,
    rectangularEulerGaussLogWeight] using hsum

theorem tendsto_integral_deningerEulerGaussPartialIntegrand
    (φ : DeningerTimeTestFunction) :
    Tendsto
      (fun N : ℕ =>
        ∫ ξ : ℝ,
          deningerEulerGaussPartialIntegrand φ N ξ)
      atTop
      (nhds
        (∫ ξ : ℝ,
          deningerEulerGaussLimitIntegrand φ ξ)) := by
  apply tendsto_integral_of_dominated_convergence
    (deningerEulerGaussMajorant φ)
  · intro N
    exact
      (integrable_deningerEulerGaussPartialIntegrand
        φ N).aestronglyMeasurable
  · exact integrable_deningerEulerGaussMajorant φ
  · intro N
    exact Filter.Eventually.of_forall fun ξ =>
      norm_deningerEulerGaussPartialIntegrand_le_majorant
        φ N ξ
  · exact Filter.Eventually.of_forall fun ξ => by
      have hs :
          0 < (rectangularEulerDigammaPoint ξ).re := by
        rw [rectangularEulerDigammaPoint_re]
        norm_num
      have hseries :=
        (summable_gaussDigammaSeriesTerm hs).hasSum.tendsto_sum_nat
      have hvalue :
          ∑' n : ℕ,
              gaussDigammaSeriesTerm
                (rectangularEulerDigammaPoint ξ) n =
            Complex.digamma (rectangularEulerDigammaPoint ξ) +
              (Real.eulerMascheroniConstant : ℂ) := by
        rw [digamma_eq_neg_euler_add_tsum_gauss hs]
        ring
      rw [hvalue] at hseries
      unfold deningerEulerGaussPartialIntegrand
        deningerEulerGaussLimitIntegrand
      exact tendsto_const_nhds.mul hseries

def deningerEulerGaussPartialValue
    (φ : DeningerTimeTestFunction) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    -2 *
      deningerTimeTestLaplace φ
        (-(2 * (n : ℝ)) : ℂ)

theorem integral_deningerEulerGaussPartialIntegrand_eq_value
    (φ : DeningerTimeTestFunction) (N : ℕ) :
    (∫ ξ : ℝ,
        deningerEulerGaussPartialIntegrand φ N ξ) =
      deningerEulerGaussPartialValue φ N := by
  rw [show
      deningerEulerGaussPartialIntegrand φ N =
        fun ξ : ℝ =>
          ∑ n ∈ Finset.range N,
            deningerEulerLineSchwartz φ ξ *
              gaussDigammaSeriesTerm
                (rectangularEulerDigammaPoint ξ) n by
    funext ξ
    rw [deningerEulerGaussPartialIntegrand,
      Finset.mul_sum]]
  rw [MeasureTheory.integral_finsetSum]
  · unfold deningerEulerGaussPartialValue
    apply Finset.sum_congr rfl
    intro n _
    simpa only [
      deningerEulerLineSchwartz_apply,
      ← deningerEulerLine_half_eq_rectangularEulerDigammaPoint] using
        integral_deningerTimeTestLaplace_mul_gaussDigammaSeriesTerm
          φ n
  · intro n _
    simpa only [
      deningerEulerLineSchwartz_apply,
      ← deningerEulerLine_half_eq_rectangularEulerDigammaPoint] using
        integrable_deningerTimeTestLaplace_mul_gaussDigammaSeriesTerm
          φ n

theorem tendsto_deningerEulerGaussPartialValue
    (φ : DeningerTimeTestFunction) :
    Tendsto
      (deningerEulerGaussPartialValue φ)
      atTop
      (nhds
        (∫ ξ : ℝ,
          deningerEulerGaussLimitIntegrand φ ξ)) := by
  have h :=
    tendsto_integral_deningerEulerGaussPartialIntegrand φ
  exact h.congr'
    (Filter.Eventually.of_forall fun N =>
      integral_deningerEulerGaussPartialIntegrand_eq_value
        φ N)

/-- Compact support inside `(0,∞)` has a strictly positive lower time bound. -/
theorem exists_deningerTimeTest_support_lower_bound
    (φ : DeningerTimeTestFunction) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t ∈ Function.support (fun x : ℝ => φ x),
        δ ≤ t := by
  by_cases hK :
      tsupport (fun x : ℝ => φ x) = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro t ht
    have hts :
        t ∈ tsupport (fun x : ℝ => φ x) :=
      subset_tsupport _ ht
    rw [hK] at hts
    exact False.elim hts
  · have hKne :
        (tsupport (fun x : ℝ => φ x)).Nonempty :=
      nonempty_iff_ne_empty.mpr hK
    obtain ⟨δ, hδK, hδmin⟩ :=
      φ.hasCompactSupport.exists_isMinOn hKne
        continuous_id.continuousOn
    have hδpos : 0 < δ :=
      φ.tsupport_subset hδK
    refine ⟨δ, hδpos, ?_⟩
    intro t ht
    exact hδmin (subset_tsupport _ ht)

def deningerTimeTestL1Mass
    (φ : DeningerTimeTestFunction) : ℝ :=
  ∫ t : ℝ, ‖(φ t : ℂ)‖

theorem integrable_deningerTimeTest_norm
    (φ : DeningerTimeTestFunction) :
    Integrable (fun t : ℝ => ‖(φ t : ℂ)‖) := by
  have hcont :
      Continuous (fun t : ℝ => ‖(φ t : ℂ)‖) := by
    fun_prop
  have hcpt :
      HasCompactSupport (fun t : ℝ => ‖(φ t : ℂ)‖) := by
    have hφ :
        HasCompactSupport (fun t : ℝ => (φ t : ℂ)) := by
      simpa only [Function.comp_apply] using!
        (φ.hasCompactSupport.comp_left
          (g := fun r : ℝ => (r : ℂ)) rfl)
    exact hφ.norm
  exact hcont.integrable_of_hasCompactSupport hcpt

theorem deningerTimeTestL1Mass_nonneg
    (φ : DeningerTimeTestFunction) :
    0 ≤ deningerTimeTestL1Mass φ := by
  unfold deningerTimeTestL1Mass
  exact integral_nonneg fun _ => norm_nonneg _

def deningerNegativeEvenLaplaceIntegrand
    (φ : DeningerTimeTestFunction) (n : ℕ) (t : ℝ) : ℂ :=
  (φ t : ℂ) *
    Complex.exp
      ((t : ℂ) * (-(2 * (n : ℝ)) : ℂ))

theorem integrable_deningerNegativeEvenLaplaceIntegrand
    (φ : DeningerTimeTestFunction) (n : ℕ) :
    Integrable
      (deningerNegativeEvenLaplaceIntegrand φ n) := by
  have hcont :
      Continuous
        (deningerNegativeEvenLaplaceIntegrand φ n) := by
    unfold deningerNegativeEvenLaplaceIntegrand
    fun_prop
  have hφ :
      HasCompactSupport (fun t : ℝ => (φ t : ℂ)) := by
    simpa only [Function.comp_apply] using!
      (φ.hasCompactSupport.comp_left
        (g := fun r : ℝ => (r : ℂ)) rfl)
  exact hcont.integrable_of_hasCompactSupport hφ.mul_right

theorem integral_norm_deningerNegativeEvenLaplaceIntegrand_le
    (φ : DeningerTimeTestFunction)
    {δ : ℝ}
    (hδsupp :
      ∀ t ∈ Function.support (fun x : ℝ => φ x),
        δ ≤ t)
    (n : ℕ) :
    (∫ t : ℝ,
        ‖deningerNegativeEvenLaplaceIntegrand φ n t‖) ≤
      deningerTimeTestL1Mass φ *
        (Real.exp (-2 * δ)) ^ n := by
  let r : ℝ := Real.exp (-2 * δ)
  have hφnorm :=
    integrable_deningerTimeTest_norm φ
  have hfn :=
    integrable_deningerNegativeEvenLaplaceIntegrand
      φ n
  have hpow :
      Real.exp (-2 * (n : ℝ) * δ) = r ^ n := by
    dsimp only [r]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpoint :
      ∀ t : ℝ,
        ‖deningerNegativeEvenLaplaceIntegrand
            φ n t‖ ≤
          ‖(φ t : ℂ)‖ * r ^ n := by
    intro t
    by_cases hφt : φ t = 0
    · simp [deningerNegativeEvenLaplaceIntegrand,
        hφt]
    · have htSupp :
          t ∈ Function.support (fun x : ℝ => φ x) := by
        simpa [Function.mem_support] using hφt
      have hδt : δ ≤ t :=
        hδsupp t htSupp
      have hexp :
          Real.exp (-2 * (n : ℝ) * t) ≤
            Real.exp (-2 * (n : ℝ) * δ) := by
        apply Real.exp_le_exp.mpr
        have hn : 0 ≤ (n : ℝ) :=
          Nat.cast_nonneg n
        nlinarith
      rw [deningerNegativeEvenLaplaceIntegrand,
        norm_mul, Complex.norm_exp]
      have hre :
          (((t : ℂ) *
            (-(2 * (n : ℝ)) : ℂ))).re =
              -2 * (n : ℝ) * t := by
        simp [Complex.mul_re]
        ring
      rw [hre, ← hpow]
      exact mul_le_mul_of_nonneg_left hexp
        (norm_nonneg _)
  calc
    (∫ t : ℝ,
        ‖deningerNegativeEvenLaplaceIntegrand
          φ n t‖) ≤
      ∫ t : ℝ, ‖(φ t : ℂ)‖ * r ^ n := by
        exact integral_mono hfn.norm
          (hφnorm.mul_const _) hpoint
    _ =
        deningerTimeTestL1Mass φ * r ^ n := by
      rw [integral_mul_const]
      rfl
    _ =
        deningerTimeTestL1Mass φ *
          (Real.exp (-2 * δ)) ^ n := by
      rfl

theorem norm_deningerTimeTestLaplace_neg_even_le
    (φ : DeningerTimeTestFunction)
    {δ : ℝ}
    (hδsupp :
      ∀ t ∈ Function.support (fun x : ℝ => φ x),
        δ ≤ t)
    (n : ℕ) :
    ‖deningerTimeTestLaplace φ
        (-(2 * (n : ℝ)) : ℂ)‖ ≤
      deningerTimeTestL1Mass φ *
        (Real.exp (-2 * δ)) ^ n := by
  rw [deningerTimeTestLaplace]
  have hfun :
      (fun t : ℝ =>
        (φ t : ℂ) *
          Complex.exp
            ((t : ℂ) *
              (-(2 * (n : ℝ)) : ℂ))) =
        deningerNegativeEvenLaplaceIntegrand φ n := by
    rfl
  rw [hfun]
  exact
    (norm_integral_le_integral_norm _).trans
      (integral_norm_deningerNegativeEvenLaplaceIntegrand_le
        φ hδsupp n)

theorem summable_deningerTimeTestLaplace_neg_even
    (φ : DeningerTimeTestFunction) :
    Summable
      (fun n : ℕ =>
        deningerTimeTestLaplace φ
          (-(2 * (n : ℝ)) : ℂ)) := by
  obtain ⟨δ, hδ, hδsupp⟩ :=
    exists_deningerTimeTest_support_lower_bound φ
  let r : ℝ := Real.exp (-2 * δ)
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    dsimp only [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom :
      Summable
        (fun n : ℕ =>
          deningerTimeTestL1Mass φ * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  apply Summable.of_norm
  exact hgeom.of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun n => by
      simpa only [r] using
        norm_deningerTimeTestLaplace_neg_even_le
          φ hδsupp n)

theorem integral_deningerEulerGaussLimitIntegrand_eq_tsum
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerEulerGaussLimitIntegrand φ ξ) =
      ∑' n : ℕ,
        -2 *
          deningerTimeTestLaplace φ
            (-(2 * (n : ℝ)) : ℂ) := by
  have hsum :
      Summable
        (fun n : ℕ =>
          -2 *
            deningerTimeTestLaplace φ
              (-(2 * (n : ℝ)) : ℂ)) :=
    (summable_deningerTimeTestLaplace_neg_even φ).mul_left _
  have hseries :
      Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N,
            -2 *
              deningerTimeTestLaplace φ
                (-(2 * (n : ℝ)) : ℂ))
        atTop
        (nhds
          (∑' n : ℕ,
            -2 *
              deningerTimeTestLaplace φ
                (-(2 * (n : ℝ)) : ℂ))) :=
    hsum.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique
    (tendsto_deningerEulerGaussPartialValue φ)
    hseries

theorem tsum_deningerTimeTestLaplace_neg_even_eq_arch
    (φ : DeningerTimeTestFunction) :
    (∑' n : ℕ,
        deningerTimeTestLaplace φ
          (-(2 * (n : ℝ)) : ℂ)) =
      ∫ t : ℝ,
        (φ t : ℂ) *
          deningerArchimedeanLefschetzDensity t := by
  obtain ⟨δ, hδ, hδsupp⟩ :=
    exists_deningerTimeTest_support_lower_bound φ
  let F : ℕ → ℝ → ℂ :=
    fun n t =>
      deningerNegativeEvenLaplaceIntegrand φ n t
  have hFint : ∀ n, Integrable (F n) :=
    fun n => by
      simpa only [F] using
        integrable_deningerNegativeEvenLaplaceIntegrand
          φ n
  have hFnormSum :
      Summable (fun n => ∫ t : ℝ, ‖F n t‖) := by
    let r : ℝ := Real.exp (-2 * δ)
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      dsimp only [r]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have hgeom :
        Summable
          (fun n : ℕ =>
            deningerTimeTestL1Mass φ * r ^ n) :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    exact hgeom.of_nonneg_of_le
      (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => by
        simpa only [F, r] using
          integral_norm_deningerNegativeEvenLaplaceIntegrand_le
            φ hδsupp n)
  have hinterchange :
      (∑' n : ℕ, ∫ t : ℝ, F n t) =
        ∫ t : ℝ, ∑' n : ℕ, F n t :=
    integral_tsum_of_summable_integral_norm
      hFint hFnormSum
  have hintegral :
      (fun n : ℕ => ∫ t : ℝ, F n t) =
        fun n : ℕ =>
          deningerTimeTestLaplace φ
            (-(2 * (n : ℝ)) : ℂ) := by
    funext n
    rw [deningerTimeTestLaplace]
    rfl
  rw [hintegral] at hinterchange
  rw [show
      (fun t : ℝ => ∑' n : ℕ, F n t) =
        fun t : ℝ =>
          (φ t : ℂ) *
            deningerArchimedeanLefschetzDensity t by
    funext t
    by_cases ht : 0 < t
    · let r : ℂ := (Real.exp (-2 * t) : ℂ)
      have hr : ‖r‖ < 1 := by
        dsimp only [r]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact Real.exp_lt_one_iff.mpr (by linarith)
      have hpow :
          ∀ n : ℕ,
            Complex.exp
                ((t : ℂ) *
                  (-(2 * (n : ℝ)) : ℂ)) =
              r ^ n := by
        intro n
        calc
          Complex.exp
              ((t : ℂ) *
                (-(2 * (n : ℝ)) : ℂ)) =
            ((Real.exp
              (-2 * (n : ℝ) * t) : ℝ) : ℂ) := by
              rw [show
                  (t : ℂ) *
                      (-(2 * (n : ℝ)) : ℂ) =
                    ((-2 * (n : ℝ) * t : ℝ) : ℂ) by
                push_cast
                ring]
              exact
                (Complex.ofReal_exp
                  (-2 * (n : ℝ) * t)).symm
          _ =
            (((Real.exp (-2 * t)) ^ n : ℝ) : ℂ) := by
              rw [← Real.exp_nat_mul]
              congr 2
              ring
          _ = r ^ n := by
            dsimp only [r]
            push_cast
            rfl
      rw [show
          (fun n : ℕ => F n t) =
            fun n : ℕ => (φ t : ℂ) * r ^ n by
        funext n
        dsimp only [F,
          deningerNegativeEvenLaplaceIntegrand]
        rw [hpow n]]
      rw [tsum_mul_left,
        tsum_geometric_of_norm_lt_one hr]
      unfold deningerArchimedeanLefschetzDensity
      dsimp only [r]
      push_cast
      ring
    · have ht0 : t ≤ 0 := le_of_not_gt ht
      have hφt :
          φ t = 0 :=
        deningerTimeTest_eq_zero_of_nonpos φ ht0
      simp [F,
        deningerNegativeEvenLaplaceIntegrand,
        hφt]] at hinterchange
  exact hinterchange

theorem continuous_deningerEulerGaussLimitIntegrand
    (φ : DeningerTimeTestFunction) :
    Continuous (deningerEulerGaussLimitIntegrand φ) := by
  have hp : Continuous rectangularEulerDigammaPoint := by
    unfold rectangularEulerDigammaPoint
    fun_prop
  have hdig :
      Continuous
        (fun ξ : ℝ =>
          Complex.digamma
            (rectangularEulerDigammaPoint ξ)) := by
    apply digamma_continuousOn_re_pos.comp_continuous hp
    intro ξ
    change 0 < (rectangularEulerDigammaPoint ξ).re
    rw [rectangularEulerDigammaPoint_re]
    norm_num
  unfold deningerEulerGaussLimitIntegrand
  exact
    (deningerEulerLineSchwartz φ).continuous.mul
      (hdig.add continuous_const)

theorem norm_deningerEulerGaussLimitIntegrand_le_majorant
    (φ : DeningerTimeTestFunction) (ξ : ℝ) :
    ‖deningerEulerGaussLimitIntegrand φ ξ‖ ≤
      deningerEulerGaussMajorant φ ξ := by
  rw [deningerEulerGaussLimitIntegrand,
    deningerEulerGaussMajorant, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖Complex.digamma
          (rectangularEulerDigammaPoint ξ) +
        (Real.eulerMascheroniConstant : ℂ)‖ ≤
        ‖Complex.digamma
          (rectangularEulerDigammaPoint ξ)‖ +
          ‖(Real.eulerMascheroniConstant : ℂ)‖ :=
      norm_add_le _ _
    _ =
        ‖Complex.digamma
          (rectangularEulerDigammaPoint ξ)‖ +
          |Real.eulerMascheroniConstant| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ deningerEulerGaussWeight ξ := by
      unfold deningerEulerGaussWeight
      have hW :=
        rectangularEulerGaussLogWeight_nonneg ξ
      linarith

theorem integrable_deningerEulerGaussLimitIntegrand
    (φ : DeningerTimeTestFunction) :
    Integrable (deningerEulerGaussLimitIntegrand φ) := by
  exact
    (integrable_deningerEulerGaussMajorant φ).mono'
      (continuous_deningerEulerGaussLimitIntegrand
        φ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ =>
        norm_deningerEulerGaussLimitIntegrand_le_majorant
          φ ξ)

theorem integral_deningerEulerGaussLimitIntegrand_eq_arch
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerEulerGaussLimitIntegrand φ ξ) =
      -2 *
        ∫ t : ℝ,
          (φ t : ℂ) *
            deningerArchimedeanLefschetzDensity t := by
  rw [
    integral_deningerEulerGaussLimitIntegrand_eq_tsum,
    tsum_mul_left,
    tsum_deningerTimeTestLaplace_neg_even_eq_arch]

theorem integrable_deningerEulerLine_mul_digamma
    (φ : DeningerTimeTestFunction) :
    Integrable
      (fun ξ : ℝ =>
        deningerEulerLineSchwartz φ ξ *
          Complex.digamma
            (rectangularEulerDigammaPoint ξ)) := by
  have hconst :
      Integrable
        (fun ξ : ℝ =>
          deningerEulerLineSchwartz φ ξ *
            (Real.eulerMascheroniConstant : ℂ)) :=
    (deningerEulerLineSchwartz φ).integrable.mul_const _
  rw [show
      (fun ξ : ℝ =>
        deningerEulerLineSchwartz φ ξ *
          Complex.digamma
            (rectangularEulerDigammaPoint ξ)) =
        fun ξ : ℝ =>
          deningerEulerGaussLimitIntegrand φ ξ -
            deningerEulerLineSchwartz φ ξ *
              (Real.eulerMascheroniConstant : ℂ) by
    funext ξ
    unfold deningerEulerGaussLimitIntegrand
    ring]
  exact
    (integrable_deningerEulerGaussLimitIntegrand φ).sub
      hconst

theorem integral_deningerEulerLine_mul_digamma
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerEulerLineSchwartz φ ξ *
          Complex.digamma
            (rectangularEulerDigammaPoint ξ)) =
      -2 *
        ∫ t : ℝ,
          (φ t : ℂ) *
            deningerArchimedeanLefschetzDensity t := by
  have hdig :=
    integrable_deningerEulerLine_mul_digamma φ
  have hconst :
      Integrable
        (fun ξ : ℝ =>
          deningerEulerLineSchwartz φ ξ *
            (Real.eulerMascheroniConstant : ℂ)) :=
    (deningerEulerLineSchwartz φ).integrable.mul_const _
  have hzero :
      (∫ ξ : ℝ,
        deningerEulerLineSchwartz φ ξ) = 0 := by
    simpa only [deningerEulerLineSchwartz_apply] using
      integral_deningerTimeTestLaplace_fourierLine_eq_zero
        φ (3 / 2)
  have harch :=
    integral_deningerEulerGaussLimitIntegrand_eq_arch φ
  rw [show
      deningerEulerGaussLimitIntegrand φ =
        fun ξ : ℝ =>
          deningerEulerLineSchwartz φ ξ *
              Complex.digamma
                (rectangularEulerDigammaPoint ξ) +
            deningerEulerLineSchwartz φ ξ *
              (Real.eulerMascheroniConstant : ℂ) by
    funext ξ
    unfold deningerEulerGaussLimitIntegrand
    ring,
    integral_add hdig hconst,
    integral_mul_const,
    hzero,
    zero_mul,
    add_zero] at harch
  exact harch

theorem integrable_deningerTimeTestLaplace_mul_gammaRealLogConnection
    (φ : DeningerTimeTestFunction) :
    Integrable
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          GaloisForLFunctions.gammaRealLogConnection
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) := by
  let F : ℝ → ℂ :=
    fun ξ => deningerEulerLineSchwartz φ ξ
  let D : ℝ → ℂ :=
    fun ξ =>
      F ξ *
        Complex.digamma
          (rectangularEulerDigammaPoint ξ)
  have hF : Integrable F := by
    exact (deningerEulerLineSchwartz φ).integrable
  have hD : Integrable D := by
    simpa only [D, F] using
      integrable_deningerEulerLine_mul_digamma φ
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          GaloisForLFunctions.gammaRealLogConnection
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
        fun ξ : ℝ =>
          (-(((Real.log Real.pi : ℝ) : ℂ) / 2)) *
              F ξ +
            (1 / 2 : ℂ) * D ξ by
    funext ξ
    dsimp only [F, D]
    rw [deningerEulerLineSchwartz_apply,
      GaloisForLFunctions.gammaRealLogConnection,
      deningerEulerLine_half_eq_rectangularEulerDigammaPoint]
    ring]
  exact
    (hF.const_mul _).add
      (hD.const_mul _)

theorem integral_deningerTimeTestLaplace_mul_gammaRealLogConnection
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          GaloisForLFunctions.gammaRealLogConnection
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
      -(∫ t : ℝ,
          (φ t : ℂ) *
            deningerArchimedeanLefschetzDensity t) := by
  let F : ℝ → ℂ :=
    fun ξ => deningerEulerLineSchwartz φ ξ
  let D : ℝ → ℂ :=
    fun ξ =>
      F ξ *
        Complex.digamma
          (rectangularEulerDigammaPoint ξ)
  have hF : Integrable F := by
    exact (deningerEulerLineSchwartz φ).integrable
  have hD : Integrable D := by
    simpa only [D, F] using
      integrable_deningerEulerLine_mul_digamma φ
  have hzero : (∫ ξ : ℝ, F ξ) = 0 := by
    simpa only [F, deningerEulerLineSchwartz_apply] using
      integral_deningerTimeTestLaplace_fourierLine_eq_zero
        φ (3 / 2)
  have hdig :
      (∫ ξ : ℝ, D ξ) =
        -2 *
          ∫ t : ℝ,
            (φ t : ℂ) *
              deningerArchimedeanLefschetzDensity t := by
    simpa only [D, F] using
      integral_deningerEulerLine_mul_digamma φ
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          GaloisForLFunctions.gammaRealLogConnection
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
        fun ξ : ℝ =>
          (-(((Real.log Real.pi : ℝ) : ℂ) / 2)) *
              F ξ +
            (1 / 2 : ℂ) * D ξ by
    funext ξ
    dsimp only [F, D]
    rw [deningerEulerLineSchwartz_apply,
      GaloisForLFunctions.gammaRealLogConnection,
      deningerEulerLine_half_eq_rectangularEulerDigammaPoint]
    ring,
    integral_add (hF.const_mul _) (hD.const_mul _),
    integral_const_mul,
    integral_const_mul,
    hzero,
    hdig]
  ring

theorem integrable_deningerTimeTestLaplace_mul_archRationalTerms
    (φ : DeningerTimeTestFunction) :
    Integrable
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          (1 /
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) +
            1 /
              ((((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) - 1))) := by
  let F : ℝ → ℂ :=
    fun ξ =>
      deningerTimeTestLaplace φ
        (((3 / 2 : ℝ) : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I)
  have hfirst :
      Integrable
        (fun ξ : ℝ =>
          F ξ *
            ((((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)⁻¹)) := by
    simpa only [F] using
      integrable_deningerTimeTestLaplace_mul_verticalResolvent
        φ (3 / 2) (by norm_num : (0 : ℝ) < 3 / 2)
  have hsecond :
      Integrable
        (fun ξ : ℝ =>
          F ξ *
            ((((1 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)⁻¹)) := by
    simpa only [F] using
      integrable_deningerTimeTestLaplace_mul_verticalResolvent
        φ (3 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          (1 /
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) +
            1 /
              ((((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) - 1))) =
        fun ξ : ℝ =>
          F ξ *
              ((((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I)⁻¹) +
            F ξ *
              ((((1 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I)⁻¹) by
    funext ξ
    dsimp only [F]
    have hden :
        (((3 / 2 : ℝ) : ℂ) -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I - 1) =
          (((1 / 2 : ℝ) : ℂ) -
            ((2 * Real.pi * ξ : ℝ) : ℂ) *
              Complex.I) := by
      push_cast
      ring
    rw [hden]
    simp only [one_div]
    ring]
  exact hfirst.add hsecond

theorem integral_deningerTimeTestLaplace_mul_logDeriv_archFactor
    (φ : DeningerTimeTestFunction) :
    (∫ ξ : ℝ,
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          logDeriv archFactor
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
      deningerTimeTestLaplace φ 0 +
        deningerTimeTestLaplace φ 1 -
          ∫ t : ℝ,
            (φ t : ℂ) *
              deningerArchimedeanLefschetzDensity t := by
  have hrat :=
    integrable_deningerTimeTestLaplace_mul_archRationalTerms
      φ
  have hgamma :=
    integrable_deningerTimeTestLaplace_mul_gammaRealLogConnection
      φ
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          logDeriv archFactor
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
        fun ξ : ℝ =>
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) *
            (1 /
                (((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) *
                    Complex.I) +
              1 /
                ((((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) *
                    Complex.I) - 1)) +
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) *
            GaloisForLFunctions.gammaRealLogConnection
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) by
    funext ξ
    let s : ℂ :=
      ((3 / 2 : ℝ) : ℂ) -
        ((2 * Real.pi * ξ : ℝ) : ℂ) *
          Complex.I
    have hspos : 0 < s.re := by
      dsimp only [s]
      simp [Complex.mul_re]
    have hs0 : s ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      dsimp only [s] at hre
      simp [Complex.mul_re] at hre
    have hs1 : s ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      dsimp only [s] at hre
      simp [Complex.mul_re] at hre
      norm_num at hre
    rw [show
        (((3 / 2 : ℝ) : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I) = s by rfl,
      logDeriv_archFactor_closed hspos hs0 hs1]
    ring,
    integral_add hrat hgamma,
    integral_deningerTimeTestLaplace_mul_archRationalTerms,
    integral_deningerTimeTestLaplace_mul_gammaRealLogConnection]
  ring

theorem integrable_deningerTimeTestLaplace_mul_logDeriv_archFactor
    (φ : DeningerTimeTestFunction) :
    Integrable
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          logDeriv archFactor
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) := by
  have hrat :=
    integrable_deningerTimeTestLaplace_mul_archRationalTerms
      φ
  have hgamma :=
    integrable_deningerTimeTestLaplace_mul_gammaRealLogConnection
      φ
  rw [show
      (fun ξ : ℝ =>
        deningerTimeTestLaplace φ
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I) *
          logDeriv archFactor
            (((3 / 2 : ℝ) : ℂ) -
              ((2 * Real.pi * ξ : ℝ) : ℂ) *
                Complex.I)) =
        fun ξ : ℝ =>
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) *
            (1 /
                (((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) *
                    Complex.I) +
              1 /
                ((((3 / 2 : ℝ) : ℂ) -
                  ((2 * Real.pi * ξ : ℝ) : ℂ) *
                    Complex.I) - 1)) +
          deningerTimeTestLaplace φ
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) *
            GaloisForLFunctions.gammaRealLogConnection
              (((3 / 2 : ℝ) : ℂ) -
                ((2 * Real.pi * ξ : ℝ) : ℂ) *
                  Complex.I) by
    funext ξ
    let s : ℂ :=
      ((3 / 2 : ℝ) : ℂ) -
        ((2 * Real.pi * ξ : ℝ) : ℂ) *
          Complex.I
    have hspos : 0 < s.re := by
      dsimp only [s]
      simp [Complex.mul_re]
    have hs0 : s ≠ 0 := by
      intro hs
      have hre := congrArg Complex.re hs
      dsimp only [s] at hre
      simp [Complex.mul_re] at hre
    have hs1 : s ≠ 1 := by
      intro hs
      have hre := congrArg Complex.re hs
      dsimp only [s] at hre
      simp [Complex.mul_re] at hre
      norm_num at hre
    rw [show
        (((3 / 2 : ℝ) : ℂ) -
          ((2 * Real.pi * ξ : ℝ) : ℂ) *
            Complex.I) = s by rfl,
      logDeriv_archFactor_closed hspos hs0 hs1]
    ring]
  exact hrat.add hgamma

end RHTower
