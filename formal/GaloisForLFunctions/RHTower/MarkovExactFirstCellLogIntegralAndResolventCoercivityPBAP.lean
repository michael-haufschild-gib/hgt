import GaloisForLFunctions.RHTower.MarkovGeometricMeanCurvatureAndTwoHundredTwoFifteenthsPBAP

/-!
# Exact First-Cell Logarithmic Quadrature, the `19 / 360` Geometric-Mean Law, the Spectral Resolvent Cauchy–Schwarz Inequality, and Resolvent-Enhanced Coercivity up to `16.4` and `53 / 3 > 17.666` for Route HF / PBAP

In Module 59 (`MarkovHermiteQuinticLogSecantAndThirteenPointFourRatioPBAP`) and Module 60
(`MarkovGeometricMeanCurvatureAndTwoHundredTwoFifteenthsPBAP`), we proved the Geometric-Mean Law
`-(1 / 18) * √(S * (S + 2 * L)) ≤ secantNumeratorCellDefect f.1 N`, where `1 / 18 = 20 / 360` came
from bounding `(Real.log x - cellSecant Real.log n x) / √x` by the product of the Cubic Hermite
logarithmic envelope and the linear secant of `1 / √x`. On the first cell `n = 2` (`[1, 2]`), which
carries over `65%` of the entire series, replacing `1 / √x` by its linear secant lost `0.00287`
(`~9%` of the cell weight). Moreover, in `one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero`,
the term `(θ - 1) * bochnerResolventEnergy (EF.weilTest F F)` was previously discarded as `≥ 0`.

In this module, we eliminate both sources of slack simultaneously:

1. **Section 1 (Exact Closed-Form Antiderivative of `(Real.log x - cellSecant Real.log 2 x) / √x`
   on `[1, 2]`, Three-Panel Simpson Bound `Real.log 2 ≤ 14411 / 20790`, and the `19 / 360`
   Geometric-Mean Law):**
   - For `x > 0`, `HasDerivAt (fun x => 2 * √x * Real.log x - 4 * √x) (Real.log x / √x) x`
     (`hasDerivAt_two_mul_sqrt_mul_log_sub_four_mul_sqrt`) and
     `HasDerivAt (fun x => (2 / 3) * x * √x - 2 * √x) ((x - 1) / √x) x`
     (`hasDerivAt_two_thirds_mul_sqrt_sub_two_mul_sqrt`).
   - By the Fundamental Theorem of Calculus (`integral_one_two_log_sub_cellSecant_div_sqrt_eq`),
     `∫ x in 1..2, (Real.log x - cellSecant Real.log 2 x) / √x = 4 * (1 - √2) + ((8 * √2 - 4) / 3) * Real.log 2`.
   - Applying Module 58's `log_sub_log_le_simpson` on `[1, 5/4]`, `[5/4, 3/2]`, and `[3/2, 2]` proves
     `Real.log 2 ≤ 14411 / 20790` (`log_two_le_fourteen_thousand_four_hundred_eleven_twenty_thousand_seven_hundred_ninetieths`,
     accurate to `2.2 × 10⁻⁵`), which with `8119 / 5741 ≤ √2` yields
     `∫ x in 1..2, (Real.log x - cellSecant Real.log 2 x) / √x ≤ 119 / 3600`
     (`integral_one_two_log_sub_cellSecant_div_sqrt_le`).
   - Combining `119 / 3600` on `n = 2` with `∑ n ∈ Icc 3 N, hermiteQuinticCellWeight n ≤ 71 / 3600`
     (`sum_Icc_three_hermiteQuinticCellWeight_le`) lowers the global quadrature constant from
     `1 / 18 = 20 / 360` to **`19 / 360`** (`neg_nineteen_three_sixtieths_variational_le_secantNumeratorCellDefect`
     and `neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect`),
     upgrading pure `rightCellQuadratureDefect ≥ 0` coercivity to `S / L ≤ 128 / 9 > 14.222`
     (general) and `S / L ≤ 78 / 5 = 15.6` (Nonnegative Log-Value Cone and Prime-Blind Cone).

2. **Section 2 (The Spectral Resolvent Quadratic Form and the Exact Spectral Resolvent
   Cauchy–Schwarz Inequality `4 L² ≤ bochnerResolventEnergy k_f * (2 S + L)`):**
   - Using `bochnerResolventEnergy_weilTest_eq` (`bochnerResolventEnergy (EF.weilTest f.1 f.1) = (1 / (2 * π)) * ∫ r, ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))`)
     and the pointwise square identity
     `1 / (1 / 4 + r ^ 2) - 4 * t + t ^ 2 * (1 + 4 * r ^ 2) = (1 - (t / 2) * (1 + 4 * r ^ 2)) ^ 2 / (1 / 4 + r ^ 2) ≥ 0`,
     we prove that for every `t : ℝ` (`four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy`):
     `4 * t * (∫ u, ‖f.1 u‖ ^ 2) - t ^ 2 * (2 * spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2) ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1)`,
     and consequently (`four_mul_sq_l2_le_bochnerResolventEnergy_mul_two_spectralSecondMoment_add_l2`):
     `4 * (∫ u, ‖f.1 u‖ ^ 2) ^ 2 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) * (2 * spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2)`.

3. **Section 3 (Resolvent-Enhanced Quadrature Coercivity and Unconditional `markovEnergy ≥ 0` up to
   `82 / 5 = 16.4` and `53 / 3 > 17.666`):**
   - Retaining `(θ - 1) * bochnerResolventEnergy k_F` alongside `θ * rightCellQuadratureDefect`
     boosts the critical ratio for `bochnerResolventEnergy k_f + rightCellQuadratureDefect ≥ 0` and
     unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane (`coshHalfMoment f = 0`) to
     **`82 / 5 = 16.4`** for general `m : ℕ` (`markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_eighty_two_fifths_of_cosh_zero`),
     and to **`53 / 3 > 17.666`** for `m = 0` (`markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_fifty_three_thirds_of_cosh_zero_of_logValue_nonneg`)!
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: Exact Closed-Form Antiderivative of `(Real.log x - cellSecant Real.log 2 x) / √x` on `[1, 2]`, Three-Panel Simpson Bound `Real.log 2 ≤ 14411 / 20790`, and the `19 / 360` Geometric-Mean Law -/

/-- For `0 < x`, the derivative of `2 * √x * Real.log x - 4 * √x` is `Real.log x / √x`. -/
theorem hasDerivAt_two_mul_sqrt_mul_log_sub_four_mul_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => 2 * Real.sqrt t * Real.log t - 4 * Real.sqrt t)
      (Real.log x / Real.sqrt x) x := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have h1 := ((hsqrt.const_mul 2).mul hlog).sub (hsqrt.const_mul 4)
  refine h1.congr_deriv ?_
  have hx_ne : x ≠ 0 := hx.ne'
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsqrt_ne : Real.sqrt x ≠ 0 := hsqrt_pos.ne'
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  calc 2 * (1 / (2 * Real.sqrt x)) * Real.log x + 2 * Real.sqrt x * x⁻¹ -
        4 * (1 / (2 * Real.sqrt x))
    _ = Real.log x / Real.sqrt x + (2 * (Real.sqrt x * Real.sqrt x) * x⁻¹ - 2) / Real.sqrt x := by
        field_simp [hsqrt_ne]
        ring
    _ = Real.log x / Real.sqrt x := by
        rw [hsq, mul_assoc 2 x x⁻¹, mul_inv_cancel₀ hx_ne]
        ring

/-- For `0 < x`, the derivative of `(2 / 3) * x * √x - 2 * √x` is `(x - 1) / √x`. -/
theorem hasDerivAt_two_thirds_mul_sqrt_sub_two_mul_sqrt {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => (2 / 3) * t * Real.sqrt t - 2 * Real.sqrt t)
      ((x - 1) / Real.sqrt x) x := by
  have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x := Real.hasDerivAt_sqrt hx.ne'
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have h1 := (((hid.const_mul (2 / 3)).mul hsqrt).sub (hsqrt.const_mul 2))
  refine h1.congr_deriv ?_
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsqrt_ne : Real.sqrt x ≠ 0 := hsqrt_pos.ne'
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx.le
  calc (2 / 3 * 1 * Real.sqrt x + 2 / 3 * x * (1 / (2 * Real.sqrt x))) -
        2 * (1 / (2 * Real.sqrt x))
    _ = ((2 / 3) * (Real.sqrt x * Real.sqrt x) + (1 / 3) * x - 1) / Real.sqrt x := by
        field_simp [hsqrt_ne]
    _ = (x - 1) / Real.sqrt x := by
        rw [hsq]
        ring

/-- **Exact Closed-Form Evaluation of `∫ x in 1..2, (Real.log x - cellSecant Real.log 2 x) / √x`**:
by the Fundamental Theorem of Calculus,
`∫ x in 1..2, (Real.log x - cellSecant Real.log 2 x) / √x = 4 * (1 - √2) + ((8 * √2 - 4) / 3) * Real.log 2`. -/
theorem integral_one_two_log_sub_cellSecant_div_sqrt_eq :
    (∫ x in (1 : ℝ)..(2 : ℝ),
      (Real.log x - cellSecant Real.log 2 x) / Real.sqrt x) =
      4 * (1 - Real.sqrt 2) + ((8 * Real.sqrt 2 - 4) / 3) * Real.log 2 := by
  let F : ℝ → ℝ := fun x =>
    (2 * Real.sqrt x * Real.log x - 4 * Real.sqrt x) -
      ((2 / 3) * x * Real.sqrt x - 2 * Real.sqrt x) * Real.log 2
  have hderiv : ∀ x ∈ uIcc (1 : ℝ) (2 : ℝ),
      HasDerivAt F ((Real.log x - cellSecant Real.log 2 x) / Real.sqrt x) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
    have hx_pos : 0 < x := lt_of_lt_of_le one_pos hx.1
    have h1 := hasDerivAt_two_mul_sqrt_mul_log_sub_four_mul_sqrt hx_pos
    have h2 := (hasDerivAt_two_thirds_mul_sqrt_sub_two_mul_sqrt hx_pos).mul_const (Real.log 2)
    refine (h1.sub h2).congr_deriv ?_
    unfold cellSecant
    have h21 : ((2 : ℕ) : ℝ) - 1 = 1 := by norm_num
    have h20 : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [h21, h20, Real.log_one]
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => (Real.log x - cellSecant Real.log 2 x) / Real.sqrt x)
      volume (1 : ℝ) (2 : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    have hlog_cont : ContinuousOn Real.log (Icc 1 2) :=
      Real.continuousOn_log.mono fun x hx => ne_of_gt (lt_of_lt_of_le one_pos hx.1)
    have hsec_cont : ContinuousOn (cellSecant Real.log 2) (Icc 1 2) := by
      unfold cellSecant
      exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
    have hsqrt_cont : ContinuousOn Real.sqrt (Icc 1 2) := Real.continuous_sqrt.continuousOn
    exact (hlog_cont.sub hsec_cont).div hsqrt_cont fun x hx =>
      ne_of_gt (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hx.1))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [F]
  rw [Real.sqrt_one, Real.log_one]
  ring

/-- **Three-Panel Simpson Upper Bound `Real.log 2 ≤ 14411 / 20790` (`≈ 0.6931698`)**:
applying `log_sub_log_le_simpson` on `[1, 5 / 4]`, `[5 / 4, 3 / 2]`, and `[3 / 2, 2]` gives
`Real.log 2 ≤ 241 / 1080 + 361 / 1980 + 145 / 504 = 14411 / 20790`. -/
theorem log_two_le_fourteen_thousand_four_hundred_eleven_twenty_thousand_seven_hundred_ninetieths :
    Real.log 2 ≤ 14411 / 20790 := by
  have h1 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 5 / 4)
  have h2 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 5 / 4) (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2)
  have h3 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  rw [Real.log_one] at h1
  linarith

/-- **Sharp First-Cell Logarithmic Quadrature Bound `≤ 119 / 3600` on `[1, 2]`**:
combining `integral_one_two_log_sub_cellSecant_div_sqrt_eq` with `Real.log 2 ≤ 14411 / 20790` and
the Pell convergent `8119 / 5741 ≤ √2` (`8119² = 65918161 < 65918162 = 2 * 5741²`) proves
`∫ x in 1..2, (Real.log x - cellSecant Real.log 2 x) / √x ≤ 119 / 3600`. -/
theorem integral_one_two_log_sub_cellSecant_div_sqrt_le :
    (∫ x in (1 : ℝ)..(2 : ℝ),
      (Real.log x - cellSecant Real.log 2 x) / Real.sqrt x) ≤ 119 / 3600 := by
  rw [integral_one_two_log_sub_cellSecant_div_sqrt_eq]
  have hsqrt2 : (8119 / 5741 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 8119 / 5741)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hcoeff_pos : 0 ≤ (8 * Real.sqrt 2 - 4) / 3 := by linarith
  have hlog2 :=
    log_two_le_fourteen_thousand_four_hundred_eleven_twenty_thousand_seven_hundred_ninetieths
  have hmul := mul_le_mul_of_nonneg_left hlog2 hcoeff_pos
  linarith

/-- **Tail Cell-Weight Sum Bound on `Icc 3 N` (`≤ 71 / 3600`)**:
for every `N : ℕ`, `∑ n ∈ Finset.Icc 3 N, hermiteQuinticCellWeight n ≤ 71 / 3600`. -/
theorem sum_Icc_three_hermiteQuinticCellWeight_le (N : ℕ) :
    (∑ n ∈ Finset.Icc 3 N, hermiteQuinticCellWeight n) ≤ 71 / 3600 := by
  have h3_bound :
      hermiteQuinticCellWeight 3 ≤
        (1 / 12) * ((1 / 2) * (1 / Real.sqrt 2) - (1 / 3) * (1 / Real.sqrt 3)) -
          (1 / Real.sqrt 2 - 1 / Real.sqrt 3) * (31 / 900) := by
    rw [hermiteQuinticCellWeight_eq]
    have hlog3 := two_mul_sub_div_add_le_log_sub_log
      (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    have hsqrt3_ge : Real.sqrt 2 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt (by norm_num)
    have hdiff3 : 0 ≤ 1 / Real.sqrt 2 - 1 / Real.sqrt 3 :=
      sub_nonneg.mpr (one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hsqrt3_ge)
    have h1 : ((3 : ℕ) : ℝ) - 1 = 2 := by norm_num
    have h2 : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [h1, h2]
    have hmul := mul_le_mul_of_nonneg_left hlog3 hdiff3
    linarith
  have h4_bound :
      hermiteQuinticCellWeight 4 ≤
        (1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
          (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520) := by
    rw [hermiteQuinticCellWeight_eq]
    have hlog4 := two_mul_sub_div_add_le_log_sub_log
      (by norm_num : (0 : ℝ) < 3) (by norm_num : (3 : ℝ) ≤ 4)
    have h4_eq : (4 : ℝ) = 2 ^ 2 := by norm_num
    have hsqrt4 : Real.sqrt 4 = 2 := by
      rw [h4_eq, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrt4_ge : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
    have hdiff4 : 0 ≤ 1 / Real.sqrt 3 - 1 / 2 := by
      have := one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hsqrt4_ge
      rw [hsqrt4] at this
      linarith
    have h1 : ((4 : ℕ) : ℝ) - 1 = 3 := by norm_num
    have h2 : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [h1, h2, hsqrt4]
    have hmul := mul_le_mul_of_nonneg_left hlog4 hdiff4
    linarith
  have hsqrt2_ge : (181 / 128 : ℝ) ≤ Real.sqrt 2 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 181 / 128)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt3_ge : (19 / 11 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 19 / 11)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv_sqrt2_le : 1 / Real.sqrt 2 ≤ 128 / 181 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 181 / 128) hsqrt2_ge
    linarith
  have hinv_sqrt3_le : 1 / Real.sqrt 3 ≤ 11 / 19 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 19 / 11) hsqrt3_ge
    linarith
  have hsqrt3_le_2 : Real.sqrt 3 ≤ 2 := by
    have h4 : (2 : ℝ) = Real.sqrt (2 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [h4]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hinv_sqrt3_ge_half : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 3 :=
    one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by norm_num)) hsqrt3_le_2
  have htail5 := sum_Icc_five_hermiteQuinticCellWeight_le N
  by_cases hN4 : 4 ≤ N
  · rw [sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight (by omega : 3 ≤ N),
      sum_Icc_eq_add_sum_Icc_succ hermiteQuinticCellWeight hN4]
    linarith
  · by_cases hN3 : 3 ≤ N
    · have hN_eq : N = 3 := by omega
      subst hN_eq
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h4_rhs_nonneg :
          0 ≤ (1 / 12) * ((1 / 3) * (1 / Real.sqrt 3) - 1 / 8) -
            (1 / Real.sqrt 3 - 1 / 2) * (61 / 2520) := by linarith
      linarith
    · rw [Finset.Icc_eq_empty hN3, Finset.sum_empty]
      norm_num

/-- **Pointwise Cell Integral Bound `(Real.log x - cellSecant Real.log n x) / √x ≤ hermiteQuinticCellWeight n`**
for every `2 ≤ n`: -/
theorem integral_log_sub_cellSecant_div_sqrt_le_hermiteQuinticCellWeight
    {n : ℕ} (hn : 2 ≤ n) :
    (∫ x in ((n : ℝ) - 1)..(n : ℝ),
      (Real.log x - cellSecant Real.log n x) / Real.sqrt x) ≤
      hermiteQuinticCellWeight n := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hle : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
  have hlog_int : IntervalIntegrable
      (fun x : ℝ => (Real.log x - cellSecant Real.log n x) / Real.sqrt x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hle]
    have hlog_cont : ContinuousOn Real.log (Icc ((n : ℝ) - 1) (n : ℝ)) :=
      Real.continuousOn_log.mono fun x hx => ne_of_gt (hn1_pos.trans_le hx.1)
    have hsec_cont : ContinuousOn (cellSecant Real.log n) (Icc ((n : ℝ) - 1) (n : ℝ)) := by
      unfold cellSecant
      exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
        ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
    have hsqrt_cont : ContinuousOn Real.sqrt (Icc ((n : ℝ) - 1) (n : ℝ)) :=
      Real.continuous_sqrt.continuousOn
    exact (hlog_cont.sub hsec_cont).div hsqrt_cont fun x hx =>
      ne_of_gt (Real.sqrt_pos.mpr (hn1_pos.trans_le hx.1))
  have hquintic_int : IntervalIntegrable
      (fun x : ℝ =>
        (hermiteLogEndpoint0 n * ((n : ℝ) - x) +
          hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) *
        ((1 / Real.sqrt ((n : ℝ) - 1)) * ((n : ℝ) - x) +
          (1 / Real.sqrt (n : ℝ)) * (x - ((n : ℝ) - 1))) *
        cellParabola n x)
      volume ((n : ℝ) - 1) (n : ℝ) := by
    apply Continuous.intervalIntegrable
    unfold cellParabola
    continuity
  have hquintic_eval :
      (∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (hermiteLogEndpoint0 n * ((n : ℝ) - x) +
          hermiteLogEndpoint1 n * (x - ((n : ℝ) - 1))) *
        ((1 / Real.sqrt ((n : ℝ) - 1)) * ((n : ℝ) - x) +
          (1 / Real.sqrt (n : ℝ)) * (x - ((n : ℝ) - 1))) *
        cellParabola n x) = hermiteQuinticCellWeight n :=
    integral_secant_mul_secant_mul_cellParabola_eq
      (hermiteLogEndpoint0 n) (hermiteLogEndpoint1 n)
      (1 / Real.sqrt ((n : ℝ) - 1)) (1 / Real.sqrt (n : ℝ)) n
  rw [← hquintic_eval]
  exact intervalIntegral.integral_mono_on hle hlog_int hquintic_int fun x hx =>
    hermite_log_sub_cellSecant_log_div_sqrt_le hn hx

/-- **The Global `19 / 360` Series Bound for `∑_{n=2}^N ∫_{n-1}^n (Real.log x - cellSecant Real.log n x) / √x`**:
combining the exact FTC bound `≤ 119 / 3600` on cell `n = 2` with the Quintic Chebyshev bound
`≤ 71 / 3600` on `n ∈ [3, N]` gives `119 / 3600 + 71 / 3600 = 19 / 360`! -/
theorem sum_Icc_two_integral_log_sub_cellSecant_div_sqrt_le_nineteen_three_sixtieths (N : ℕ) :
    (∑ n ∈ Finset.Icc 2 N,
      ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (Real.log x - cellSecant Real.log n x) / Real.sqrt x) ≤ 19 / 360 := by
  have hcell_nonneg : ∀ n : ℕ, 2 ≤ n →
      0 ≤ ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (Real.log x - cellSecant Real.log n x) / Real.sqrt x := by
    intro n hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hle : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
    refine intervalIntegral.integral_nonneg hle fun x hx => ?_
    have hlog_ge : 0 ≤ Real.log x - cellSecant Real.log n x := by
      have h := neg_mul_log_sub_cellSecant_le_sub_cellSecant_of_deriv2_le_div_sq
        (g := Real.log) (g' := fun t => t⁻¹) (g'' := fun t => -(t ^ 2)⁻¹) hn (A := 0)
        (fun t ht => Real.hasDerivAt_log (by linarith [ht.1]))
        (fun t ht => hasDerivAt_inv (by linarith [ht.1]))
        (fun t _ => by
          rw [zero_div, neg_nonpos, inv_nonneg]
          exact sq_nonneg t) hx
      linarith
    exact div_nonneg hlog_ge (Real.sqrt_nonneg x)
  have h2_eq :
      (∫ x in (((2 : ℕ) : ℝ) - 1)..((2 : ℕ) : ℝ),
        (Real.log x - cellSecant Real.log 2 x) / Real.sqrt x) =
      ∫ x in (1 : ℝ)..(2 : ℝ),
        (Real.log x - cellSecant Real.log 2 x) / Real.sqrt x := by
    norm_num
  have h2_le := integral_one_two_log_sub_cellSecant_div_sqrt_le
  rw [← h2_eq] at h2_le
  by_cases hN2 : 2 ≤ N
  · rw [sum_Icc_eq_add_sum_Icc_succ _ hN2]
    have htail_le :
        (∑ n ∈ Finset.Icc 3 N,
          ∫ x in ((n : ℝ) - 1)..(n : ℝ),
            (Real.log x - cellSecant Real.log n x) / Real.sqrt x) ≤
        ∑ n ∈ Finset.Icc 3 N, hermiteQuinticCellWeight n := by
      refine Finset.sum_le_sum fun n hn => ?_
      rw [Finset.mem_Icc] at hn
      exact integral_log_sub_cellSecant_div_sqrt_le_hermiteQuinticCellWeight (by omega)
    have htail_71 := sum_Icc_three_hermiteQuinticCellWeight_le N
    linarith
  · rw [Finset.Icc_eq_empty hN2, Finset.sum_empty]
    norm_num

/-- **Upgraded `19 / 360` One-Parameter Variational Lower Bound on `secantNumeratorCellDefect`**:
for every `f : WeilTestFn`, `0 < b`, and `N : ℕ`,
`-(19 / 360) * ((b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_nineteen_three_sixtieths_variational_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {b : ℝ} (hb : 0 < b) (N : ℕ) :
    -(19 / 360) * ((b + 1 / (4 * b)) * spectralSecondMoment f.1 +
        2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  let M : ℝ := (b + 1 / (4 * b)) * spectralSecondMoment f.1 + 2 * b * ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hsec_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hcell_le : ∀ n ∈ Finset.Icc 2 N,
      -(M * ∫ x in ((n : ℝ) - 1)..(n : ℝ),
        (Real.log x - cellSecant Real.log n x) / Real.sqrt x) ≤
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (weilSymmetricLogNumerator f.1 x -
            cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x := by
    intro n hn
    have hn_mem := Finset.mem_Icc.mp hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_mem.1
    have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hle : (n : ℝ) - 1 ≤ (n : ℝ) := by linarith
    have hnum_int : IntervalIntegrable
        (fun x : ℝ =>
          (weilSymmetricLogNumerator f.1 x -
            cellSecant (weilSymmetricLogNumerator f.1) n x) / Real.sqrt x)
        volume ((n : ℝ) - 1) (n : ℝ) := by
      have hinv : ContinuousOn (fun x : ℝ => (Real.sqrt x)⁻¹) (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
        refine ContinuousOn.inv₀ (Real.continuous_sqrt.continuousOn) fun x hx => ?_
        rw [uIcc_of_le hle] at hx
        exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hx.1]))
      have hnum : ContinuousOn
          (fun x : ℝ => weilSymmetricLogNumerator f.1 x)
          (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
        refine (continuousOn_weilSymmetricLogNumerator f).mono fun x hx => ?_
        rw [uIcc_of_le hle] at hx
        rw [mem_Ici]
        linarith [hx.1]
      have hsec : ContinuousOn
          (fun x : ℝ => cellSecant (weilSymmetricLogNumerator f.1) n x)
          (uIcc ((n : ℝ) - 1) (n : ℝ)) := by
        unfold cellSecant
        exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
      simp_rw [div_eq_mul_inv]
      exact ((hnum.sub hsec).mul hinv).intervalIntegrable
    have hlog_int : IntervalIntegrable
        (fun x : ℝ => -M * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x))
        volume ((n : ℝ) - 1) (n : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hle]
      have hlog_cont : ContinuousOn Real.log (Icc ((n : ℝ) - 1) (n : ℝ)) :=
        Real.continuousOn_log.mono fun x hx => ne_of_gt (hn1_pos.trans_le hx.1)
      have hsec_cont : ContinuousOn (cellSecant Real.log n) (Icc ((n : ℝ) - 1) (n : ℝ)) := by
        unfold cellSecant
        exact ((continuousOn_const.sub continuousOn_id).mul continuousOn_const).add
          ((continuousOn_id.sub continuousOn_const).mul continuousOn_const)
      have hsqrt_cont : ContinuousOn Real.sqrt (Icc ((n : ℝ) - 1) (n : ℝ)) :=
        Real.continuous_sqrt.continuousOn
      exact continuousOn_const.mul ((hlog_cont.sub hsec_cont).div hsqrt_cont fun x hx =>
        ne_of_gt (Real.sqrt_pos.mpr (hn1_pos.trans_le hx.1)))
    have hpull :
        (∫ x in ((n : ℝ) - 1)..(n : ℝ),
          -M * ((Real.log x - cellSecant Real.log n x) / Real.sqrt x)) =
        -(M * ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (Real.log x - cellSecant Real.log n x) / Real.sqrt x) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    rw [← hpull]
    refine intervalIntegral.integral_mono_on hle hlog_int hnum_int fun x hx => ?_
    have hlog_cmp :
        |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
          M * (Real.log x - cellSecant Real.log n x) :=
      abs_weilSymmetricLogNumerator_sub_cellSecant_le_variational f hint2 hb hn_mem.1 hx
    have hlow := (abs_le.mp hlog_cmp).1
    have hdiv := div_le_div_of_nonneg_right hlow (Real.sqrt_nonneg x)
    linarith [mul_div_assoc M (Real.log x - cellSecant Real.log n x) (Real.sqrt x),
      neg_div (Real.sqrt x) (M * (Real.log x - cellSecant Real.log n x))]
  have hsum_mono := Finset.sum_le_sum hcell_le
  unfold secantNumeratorCellDefect
  have hsum_pull :
      (∑ n ∈ Finset.Icc 2 N,
        -(M * ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (Real.log x - cellSecant Real.log n x) / Real.sqrt x)) =
      -(M * ∑ n ∈ Finset.Icc 2 N,
        ∫ x in ((n : ℝ) - 1)..(n : ℝ),
          (Real.log x - cellSecant Real.log n x) / Real.sqrt x) := by
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hsum_19 := mul_le_mul_of_nonneg_left
    (sum_Icc_two_integral_log_sub_cellSecant_div_sqrt_le_nineteen_three_sixtieths N) hM_nonneg
  linarith

/-- **The Upgraded `19 / 360` Exact Geometric-Mean Law**:
for every `f : WeilTestFn` and `N : ℕ`,
`-(19 / 360) * √(spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ ‖f.1‖²)) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(19 / 360) *
        Real.sqrt (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      secantNumeratorCellDefect f.1 N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  rcases eq_or_lt_of_le hS_nonneg with hS_zero | hS_pos
  · change -(19 / 360) * Real.sqrt (S * (S + 2 * L)) ≤ secantNumeratorCellDefect f.1 N
    rw [← hS_zero, zero_mul, Real.sqrt_zero, mul_zero]
    by_contra! hneg
    let D := secantNumeratorCellDefect f.1 N
    have hD_neg : D < 0 := hneg
    have h2L1_pos : 0 < 2 * L + 1 := by positivity
    let b := (-D) / (2 * L + 1)
    have hb_pos : 0 < b := div_pos (by linarith) h2L1_pos
    have hvar := neg_nineteen_three_sixtieths_variational_le_secantNumeratorCellDefect f hint2 hb_pos N
    change -(19 / 360) * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤ D at hvar
    rw [← hS_zero, mul_zero, zero_add] at hvar
    have hb_mul : b * (2 * L + 1) = -D := div_mul_cancel₀ (-D) h2L1_pos.ne'
    have hbL_le : b * (2 * L) ≤ b * (2 * L + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hb_pos.le
    linarith
  · have hS2L_pos : 0 < S + 2 * L := by positivity
    let s₁ := Real.sqrt S
    let s₂ := Real.sqrt (S + 2 * L)
    have hs₁_pos : 0 < s₁ := Real.sqrt_pos.mpr hS_pos
    have hs₂_pos : 0 < s₂ := Real.sqrt_pos.mpr hS2L_pos
    have hs₁_sq : s₁ ^ 2 = S := Real.sq_sqrt hS_pos.le
    have hs₂_sq : s₂ ^ 2 = S + 2 * L := Real.sq_sqrt hS2L_pos.le
    let b := s₁ / (2 * s₂)
    have hb_pos : 0 < b := by dsimp [b]; positivity
    have hvar := neg_nineteen_three_sixtieths_variational_le_secantNumeratorCellDefect f hint2 hb_pos N
    change -(19 / 360) * ((b + 1 / (4 * b)) * S + 2 * b * L) ≤
      secantNumeratorCellDefect f.1 N at hvar
    have hval :
        (b + 1 / (4 * b)) * S + 2 * b * L =
          Real.sqrt (S * (S + 2 * L)) := by
      have hsqrt_mul : Real.sqrt (S * (S + 2 * L)) = s₁ * s₂ :=
        Real.sqrt_mul hS_pos.le (S + 2 * L)
      have hsplit : (b + 1 / (4 * b)) * S + 2 * b * L =
          b * s₂ ^ 2 + (1 / (4 * b)) * s₁ ^ 2 := by
        rw [hs₁_sq, hs₂_sq]
        ring
      have hs₁_ne : s₁ ≠ 0 := hs₁_pos.ne'
      have hs₂_ne : s₂ ≠ 0 := hs₂_pos.ne'
      have hterm1 : b * s₂ ^ 2 = (1 / 2) * s₁ * s₂ := by
        dsimp [b]
        field_simp
      have hterm2 : (1 / (4 * b)) * s₁ ^ 2 = (1 / 2) * s₁ * s₂ := by
        dsimp [b]
        field_simp
        ring
      rw [hsplit, hterm1, hterm2, hsqrt_mul]
      ring
    rwa [hval] at hvar

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity at Critical Ratio `128 / 9 > 14.2222`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_twenty_eight_ninths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (128 / 9) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 := four_thirty_three_five_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    f hN1 hN0 hN
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((866 / 57) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (146 / 9) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((128 / 9) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((128 / 9) * L) * (S + 2 * L) ≤ ((128 / 9) * L) * ((146 / 9) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((128 / 9) * L) * ((146 / 9) * L) ≤ ((866 / 57) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (866 / 57) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (866 / 57) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity on the Nonnegative Log-Value Cone at
Critical Ratio `78 / 5 = 15.6`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_seventy_eight_fifths_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (78 / 5) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hprod_le : S * (S + 2 * L) ≤ ((1261 / 76) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (88 / 5) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((78 / 5) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((78 / 5) * L) * (S + 2 * L) ≤ ((78 / 5) * L) * ((88 / 5) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((78 / 5) * L) * ((88 / 5) * L) ≤ ((1261 / 76) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (1261 / 76) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (1261 / 76) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-! ## Section 2: The Spectral Resolvent Quadratic Form and the Exact Spectral Resolvent Cauchy–Schwarz Inequality `4 L² ≤ bochnerResolventEnergy k_f * (2 S + L)` -/

/-- **Pointwise Nonnegative Resolvent–Polynomial Square Identity**:
for every `t, r : ℝ`,
`0 ≤ 1 / (1 / 4 + r ^ 2) - 4 * t + t ^ 2 * (1 + 4 * r ^ 2)`. -/
theorem resolvent_quadratic_pointwise_nonneg (t r : ℝ) :
    0 ≤ 1 / (1 / 4 + r ^ 2) - 4 * t + t ^ 2 * (1 + 4 * r ^ 2) := by
  have hpos : 0 < 1 / 4 + r ^ 2 := by positivity
  have heq :
      1 / (1 / 4 + r ^ 2) - 4 * t + t ^ 2 * (1 + 4 * r ^ 2) =
        (1 - (t / 2) * (1 + 4 * r ^ 2)) ^ 2 / (1 / 4 + r ^ 2) := by
    have hne : 1 / 4 + r ^ 2 ≠ 0 := hpos.ne'
    field_simp [hne]
    ring
  rw [heq]
  exact div_nonneg (sq_nonneg _) hpos.le

/-- **Integrability of `r ↦ ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2))`** for any `f : WeilTestFn`: -/
theorem integrable_paperFT_norm_sq_mul_inv_quarter_add_sq (f : WeilTestFn) :
    Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) := by
  have hsq := integrable_paperFT_norm_sq f
  refine (hsq.mul_const 4).mono' ?_ ?_
  · refine (hsq.aestronglyMeasurable).mul ?_
    apply Continuous.aestronglyMeasurable
    exact continuous_const.div (continuous_const.add (continuous_id.pow 2)) fun r => by positivity
  · refine Eventually.of_forall fun r => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    have hle : 1 / (1 / 4 + r ^ 2) ≤ 4 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [sq_nonneg r]
    exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)

/-- **The Universal Spectral Resolvent Quadratic Form Inequality**:
for every `f : WeilTestFn` with integrable second spectral moment and every `t : ℝ`,
`4 * t * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - t ^ 2 * (2 * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1)`. -/
theorem four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (t : ℝ) :
    4 * t * (∫ u : ℝ, ‖f.1 u‖ ^ 2) -
        t ^ 2 * (2 * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) := by
  have hsq := integrable_paperFT_norm_sq f
  have hres_int := integrable_paperFT_norm_sq_mul_inv_quarter_add_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hres_eq := bochnerResolventEnergy_weilTest_eq f
  have hcomb :
      bochnerResolventEnergy (EF.weilTest f.1 f.1) -
        4 * t * (∫ u : ℝ, ‖f.1 u‖ ^ 2) +
        t ^ 2 * (2 * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) =
      (1 / (2 * Real.pi)) * ∫ r : ℝ,
        ((‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) -
          (2 * t) * (‖paperFT f.1 r‖ ^ 2 * 2)) +
          t ^ 2 * ((1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2) +
            2 * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)))) := by
    rw [hres_eq]
    unfold spectralSecondMoment
    have hint_sub := integral_sub hres_int ((hsq.mul_const 2).const_mul (2 * t))
    have hint_inner := integral_add
      ((hsq.mul_const 2).const_mul (1 / 2))
      (hint2.const_mul 2)
    have hint_add := integral_add
      (hres_int.sub ((hsq.mul_const 2).const_mul (2 * t)))
      (((hsq.mul_const 2).const_mul (1 / 2)).add (hint2.const_mul 2) |>.const_mul (t ^ 2))
    dsimp at hint_sub hint_inner hint_add
    rw [hint_add, hint_sub, integral_const_mul, integral_const_mul,
      hint_inner, integral_const_mul, integral_const_mul]
    linear_combination ((2 * t - t ^ 2 / 2) : ℝ) * hplanch
  have hnonneg :
      0 ≤ (1 / (2 * Real.pi)) * ∫ r : ℝ,
        ((‖paperFT f.1 r‖ ^ 2 * (1 / (1 / 4 + r ^ 2)) -
          (2 * t) * (‖paperFT f.1 r‖ ^ 2 * 2)) +
          t ^ 2 * ((1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2) +
            2 * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)))) := by
    refine mul_nonneg (div_nonneg zero_le_one Real.two_pi_pos.le) (integral_nonneg fun r => ?_)
    dsimp
    have hpt := mul_nonneg (sq_nonneg ‖paperFT f.1 r‖) (resolvent_quadratic_pointwise_nonneg t r)
    linarith
  linarith

/-- **Exact Spectral Resolvent Cauchy–Schwarz Inequality**:
for every `f : WeilTestFn` with integrable second spectral moment,
`4 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ^ 2 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) * (2 * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2)`. -/
theorem four_mul_sq_l2_le_bochnerResolventEnergy_mul_two_spectralSecondMoment_add_l2
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    4 * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ^ 2 ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) *
        (2 * spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have hdenom_nonneg : 0 ≤ 2 * S + L := by positivity
  rcases eq_or_lt_of_le hdenom_nonneg with hzero | hpos
  · have hL_zero : L = 0 := by linarith
    have hS_zero : S = 0 := by linarith
    change 4 * L ^ 2 ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) * (2 * S + L)
    rw [hL_zero, hS_zero]
    norm_num
  · let t := (2 * L) / (2 * S + L)
    have hq := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
      f hint2 t
    change 4 * t * L - t ^ 2 * (2 * S + L) ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) at hq
    have hmul := mul_le_mul_of_nonneg_right hq hpos.le
    have hne : 2 * S + L ≠ 0 := hpos.ne'
    have halg : (4 * t * L - t ^ 2 * (2 * S + L)) * (2 * S + L) = 4 * L ^ 2 := by
      dsimp [t]
      field_simp [hne]
      ring
    linarith

/-! ## Section 3: Resolvent-Enhanced Quadrature Coercivity and Unconditional `markovEnergy ≥ 0` on the Primitive Hyperplane up to `82 / 5 = 16.4` and `53 / 3 > 17.666` -/

/-- **Resolvent-Enhanced Quadrature Coercivity up to Critical Ratio `82 / 5 = 16.4`**:
whenever `spectralSecondMoment f.1 ≤ (82 / 5) * ∫ ‖f.1‖²`, we have
`(1 / 360) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`
(and in particular `0 ≤ bochnerResolventEnergy k_f + rightCellQuadratureDefect`)! -/
theorem one_three_sixtieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_eighty_two_fifths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (82 / 5) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 360) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 := four_thirty_three_five_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    f hN1 hN0 hN
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (10 / 169)
  have hprod_le : S * (S + 2 * L) ≤ ((869 / 50) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (92 / 5) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((82 / 5) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((82 / 5) * L) * (S + 2 * L) ≤ ((82 / 5) * L) * ((92 / 5) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((82 / 5) * L) * ((92 / 5) * L) ≤ ((869 / 50) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (869 / 50) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (869 / 50) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Nonnegative Log-Value Cone up to Critical
Ratio `53 / 3 > 17.6666`**:
since `53 * 59 = 3127 < 3136 = 56²`, whenever `∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n` and
`spectralSecondMoment f.1 ≤ (53 / 3) * ∫ ‖f.1‖²`, we have
`(1 / 1800) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_eighteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_three_thirds_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (53 / 3) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1800) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      f hint2 N
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (6 / 109)
  have hprod_le : S * (S + 2 * L) ≤ ((56 / 3) * L) ^ 2 := by
    have hS2L_le : S + 2 * L ≤ (59 / 3) * L := by linarith [hsec]
    have hmul1 : S * (S + 2 * L) ≤ ((53 / 3) * L) * (S + 2 * L) :=
      mul_le_mul_of_nonneg_right hsec (by positivity)
    have hmul2 : ((53 / 3) * L) * (S + 2 * L) ≤ ((53 / 3) * L) * ((59 / 3) * L) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth : ((53 / 3) * L) * ((59 / 3) * L) ≤ ((56 / 3) * L) ^ 2 := by
      have hsq : 0 ≤ L ^ 2 := sq_nonneg L
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le : Real.sqrt (S * (S + 2 * L)) ≤ (56 / 3) * L := by
    rw [← Real.sqrt_sq (by positivity : 0 ≤ (56 / 3) * L)]
    exact Real.sqrt_le_sqrt hprod_le
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (82 / 5) * ∫ ‖F‖² = 16.4 * ∫ ‖F‖²` (No `- δ` Needed!)**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_eighty_two_fifths_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (82 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hS_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 :=
    spectralSecondMoment_nonneg (realWeilTestFn f hf hfc).1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 801
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (801 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (800 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 := four_thirty_three_five_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hprod_le :
      spectralSecondMoment (realWeilTestFn f hf hfc).1 *
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
            2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        ((869 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
    have hS2L_le :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          2 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        (92 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
      linarith [hsec_bound]
    have hmul1 :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((82 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hsec_bound (by positivity)
    have hmul2 :
        ((82 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((82 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((92 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth :
        ((82 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((92 / 5) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((869 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
      have hsq : 0 ≤ (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := sq_nonneg _
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le :
      Real.sqrt
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (869 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rw [← Real.sqrt_sq
      (by positivity : 0 ≤ (869 / 50) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)]
    exact Real.sqrt_le_sqrt hprod_le
  have hcomb :=
    one_three_sixtieth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_eighty_two_fifths
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec_bound
  have hθ_comb :
      (800 : ℝ) * ((1 / 360) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Nonnegative Log-Value Cone (`m = 0`) of the
Primitive Hyperplane whenever `spectralSecondMoment F ≤ (53 / 3) * ∫ ‖F‖² > 17.6666 * ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_fifty_three_thirds_of_cosh_zero_of_logValue_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue (realWeilTestFn f hf hfc).1 n)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (53 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hS_nonneg : 0 ≤ spectralSecondMoment (realWeilTestFn f hf hfc).1 :=
    spectralSecondMoment_nonneg (realWeilTestFn f hf hfc).1
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 4001
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (4001 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (4000 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    0 hf hfc hcosh hN1 hθlog hN hpos
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_nineteen_three_sixtieths_sqrt_spectralSecondMoment_mul_add_two_l2_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hprod_le :
      spectralSecondMoment (realWeilTestFn f hf hfc).1 *
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
            2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        ((56 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
    have hS2L_le :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 +
          2 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
        (59 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
      linarith [hsec_bound]
    have hmul1 :
        spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((53 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hsec_bound (by positivity)
    have hmul2 :
        ((53 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((53 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((59 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hS2L_le (by positivity)
    have hpyth :
        ((53 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) *
            ((59 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ≤
          ((56 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := by
      have hsq : 0 ≤ (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) ^ 2 := sq_nonneg _
      linarith
    exact (hmul1.trans hmul2).trans hpyth
  have hsqrt_le :
      Real.sqrt
          (spectralSecondMoment (realWeilTestFn f hf hfc).1 *
            (spectralSecondMoment (realWeilTestFn f hf hfc).1 +
              2 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (56 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 := by
    rw [← Real.sqrt_sq
      (by positivity : 0 ≤ (56 / 3) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)]
    exact Real.sqrt_le_sqrt hprod_le
  have hcomb :=
    one_eighteen_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_three_thirds_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hsec_bound
  have hθ_comb :
      (4000 : ℝ) * ((1 / 1800) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
