import GaloisForLFunctions.RHTower.MarkovExactFirstCellCosLogIntegralAndTwentyThreeRatioPBAP

/-!
# Degree-16 First-Cell Cosine-Log Taylor Hierarchy, the `7 / 480 = 52.5 / 3600` Pure-Second-Moment Law, Four-Stage Secular Counterterm Telescoping (`247 / 300 = 2964 / 3600`), and Coercivity & Spectral Gap Laws up to `117 / 5 = 23.4`, `124 / 5 = 24.8`, `51 / 2 = 25.5`, and `27` for Route HF / PBAP

1. **Section 1:** Universal alternating Taylor polynomial hierarchy up to degree 16 for
   `1 - Real.cos θ`, `Real.sin θ`, and `θ * Real.sin θ`, together with eight-panel midpoint/Simpson
   bounds `693146 / 1000000 ≤ Real.log 2 ≤ 693148 / 1000000` and Pell bounds on `Real.sqrt 2`.
2. **Section 2:** Tight pure-second-moment inequality `-(7 / 480) * r ^ 2 ≤ I_2(r)`
   (`neg_seven_four_eightieths_mul_sq_le_integral_one_two_cosLogProfile`) on `n = 2`, reducing the
   first-cell curvature coefficient from `13 / 720 = 65 / 3600` to `7 / 480 = 52.5 / 3600` (`-19.2%`),
   and the split secant numerator law
   `-(7 / 480) * S - (71 / 3600) * √(S(S + 2L)) ≤ secantNumeratorCellDefect f.1 N`.
3. **Section 3:** Four-stage secular counterterm potential `secantFourStagePotential` isolating
   `n = 2, 3, 4` and bounding `1 / √n ≤ 1 / √5` for `n ≥ 5`, boosting the general origin $L^2$
   surplus from `2953 / 3600` to `247 / 300 = 2964 / 3600`, and upgrading coercivity & spectral gap
   laws to `S / L ≤ 117 / 5 = 23.4`, `124 / 5 = 24.8`, `51 / 2 = 25.5`, and `27`.
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

/-! ## Section 1: Universal Alternating Taylor Polynomial Hierarchy up to Degree 16 and Eight-Panel Bounds on `Real.log 2` -/

/-- Step 13 (`f₁₃`): for all `0 ≤ θ`,
`Real.sin θ ≤ θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800`. -/
theorem sin_le_taylor_degree_thirteen_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    Real.sin θ ≤
      θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 -
        θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t =>
      (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
        t ^ 11 / 39916800 + t ^ 13 / 6227020800) - Real.sin t)
    (f' := fun t =>
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 -
        t ^ 10 / 3628800 + t ^ 12 / 479001600) - Real.cos t)
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
        ((hasDerivAt_pow 9 t).div_const 362880)).sub
        ((hasDerivAt_pow 11 t).div_const 39916800)).add
        ((hasDerivAt_pow 13 t).div_const 6227020800)).sub (Real.hasDerivAt_sin t)).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [taylor_degree_twelve_le_one_sub_cos t])
    hθ
  linarith

/-- Step 14 (`f₁₄`): for all `θ : ℝ`,
`1 - Real.cos θ ≤ θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200`. -/
theorem one_sub_cos_le_taylor_degree_fourteen (θ : ℝ) :
    1 - Real.cos θ ≤
      θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
        θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 := by
  suffices h : ∀ u : ℝ, 0 ≤ u →
      0 ≤ Real.cos u -
        (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 -
          u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200) by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      have hpow6 : (-θ) ^ 6 = θ ^ 6 := by ring
      have hpow8 : (-θ) ^ 8 = θ ^ 8 := by ring
      have hpow10 : (-θ) ^ 10 = θ ^ 10 := by ring
      have hpow12 : (-θ) ^ 12 = θ ^ 12 := by ring
      have hpow14 : (-θ) ^ 14 = θ ^ 14 := by ring
      rw [Real.cos_neg, neg_sq, hpow4, hpow6, hpow8, hpow10, hpow12, hpow14] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => Real.cos t -
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 -
        t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200))
    (f' := fun t => -Real.sin t +
      (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
        t ^ 11 / 39916800 + t ^ 13 / 6227020800))
    (by norm_num)
    (fun t => by
      refine ((Real.hasDerivAt_cos t).sub
        ((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
          ((hasDerivAt_pow 8 t).div_const 40320)).sub
          ((hasDerivAt_pow 10 t).div_const 3628800)).add
          ((hasDerivAt_pow 12 t).div_const 479001600)).sub
          ((hasDerivAt_pow 14 t).div_const 87178291200))).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [sin_le_taylor_degree_thirteen_of_nonneg ht])
    hu

/-- Step 15 (`f₁₅`): for all `0 ≤ θ`,
`θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 - θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 ≤ Real.sin θ`. -/
theorem taylor_degree_fifteen_le_sin_of_nonneg {θ : ℝ} (hθ : 0 ≤ θ) :
    θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 -
        θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000 ≤
      Real.sin θ := by
  have h := nonneg_of_deriv_nonneg
    (f := fun t => Real.sin t -
      (t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
        t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000))
    (f' := fun t => Real.cos t -
      (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 -
        t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200))
    (by norm_num [Real.sin_zero])
    (fun t => by
      refine ((Real.hasDerivAt_sin t).sub
        ((((((((hasDerivAt_id t).sub ((hasDerivAt_pow 3 t).div_const 6)).add
          ((hasDerivAt_pow 5 t).div_const 120)).sub ((hasDerivAt_pow 7 t).div_const 5040)).add
          ((hasDerivAt_pow 9 t).div_const 362880)).sub
          ((hasDerivAt_pow 11 t).div_const 39916800)).add
          ((hasDerivAt_pow 13 t).div_const 6227020800)).sub
          ((hasDerivAt_pow 15 t).div_const 1307674368000))).congr_deriv ?_
      norm_num
      ring)
    (fun t _ => by linarith [one_sub_cos_le_taylor_degree_fourteen t])
    hθ
  linarith

/-- **Global Even-Degree-16 Lower Bound on `θ * Real.sin θ`**: -/
theorem mul_sin_ge_taylor_degree_sixteen (θ : ℝ) :
    θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 -
        θ ^ 12 / 39916800 + θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000 ≤
      θ * Real.sin θ := by
  rcases le_total 0 θ with hθ | hθ
  · have h := mul_le_mul_of_nonneg_left (taylor_degree_fifteen_le_sin_of_nonneg hθ) hθ
    linarith [show θ * (θ - θ ^ 3 / 6 + θ ^ 5 / 120 - θ ^ 7 / 5040 + θ ^ 9 / 362880 -
        θ ^ 11 / 39916800 + θ ^ 13 / 6227020800 - θ ^ 15 / 1307674368000) =
      θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 -
        θ ^ 12 / 39916800 + θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000 by ring]
  · have hθ_neg : 0 ≤ -θ := by linarith
    have h := mul_le_mul_of_nonneg_left (taylor_degree_fifteen_le_sin_of_nonneg hθ_neg) hθ_neg
    rw [Real.sin_neg] at h
    linarith [show (-θ) * ((-θ) - (-θ) ^ 3 / 6 + (-θ) ^ 5 / 120 - (-θ) ^ 7 / 5040 +
        (-θ) ^ 9 / 362880 - (-θ) ^ 11 / 39916800 + (-θ) ^ 13 / 6227020800 -
        (-θ) ^ 15 / 1307674368000) =
      θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 + θ ^ 10 / 362880 -
        θ ^ 12 / 39916800 + θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000 by ring,
      show (-θ) * -Real.sin θ = θ * Real.sin θ by ring]

/-- Step 16 (`f₁₆`): for all `θ : ℝ`,
`θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 + θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 - θ ^ 16 / 20922789888000 ≤ 1 - Real.cos θ`. -/
theorem taylor_degree_sixteen_le_one_sub_cos (θ : ℝ) :
    θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
        θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 -
        θ ^ 16 / 20922789888000 ≤
      1 - Real.cos θ := by
  suffices h : ∀ u : ℝ, 0 ≤ u →
      0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 + u ^ 8 / 40320 -
        u ^ 10 / 3628800 + u ^ 12 / 479001600 - u ^ 14 / 87178291200 +
        u ^ 16 / 20922789888000) - Real.cos u by
    rcases le_total 0 θ with hθ | hθ
    · linarith [h θ hθ]
    · have hneg := h (-θ) (by linarith)
      have hpow4 : (-θ) ^ 4 = θ ^ 4 := by ring
      have hpow6 : (-θ) ^ 6 = θ ^ 6 := by ring
      have hpow8 : (-θ) ^ 8 = θ ^ 8 := by ring
      have hpow10 : (-θ) ^ 10 = θ ^ 10 := by ring
      have hpow12 : (-θ) ^ 12 = θ ^ 12 := by ring
      have hpow14 : (-θ) ^ 14 = θ ^ 14 := by ring
      have hpow16 : (-θ) ^ 16 = θ ^ 16 := by ring
      rw [Real.cos_neg, neg_sq, hpow4, hpow6, hpow8, hpow10, hpow12, hpow14, hpow16] at hneg
      linarith
  intro u hu
  refine nonneg_of_deriv_nonneg
    (f := fun t => (1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720 + t ^ 8 / 40320 -
      t ^ 10 / 3628800 + t ^ 12 / 479001600 - t ^ 14 / 87178291200 +
      t ^ 16 / 20922789888000) - Real.cos t)
    (f' := fun t => -(t - t ^ 3 / 6 + t ^ 5 / 120 - t ^ 7 / 5040 + t ^ 9 / 362880 -
      t ^ 11 / 39916800 + t ^ 13 / 6227020800 - t ^ 15 / 1307674368000) + Real.sin t)
    (by norm_num)
    (fun t => by
      refine ((((((((((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_pow 2 t).div_const 2)).add
        ((hasDerivAt_pow 4 t).div_const 24)).sub ((hasDerivAt_pow 6 t).div_const 720)).add
        ((hasDerivAt_pow 8 t).div_const 40320)).sub
        ((hasDerivAt_pow 10 t).div_const 3628800)).add
        ((hasDerivAt_pow 12 t).div_const 479001600)).sub
        ((hasDerivAt_pow 14 t).div_const 87178291200)).add
        ((hasDerivAt_pow 16 t).div_const 20922789888000)).sub (Real.hasDerivAt_cos t)).congr_deriv ?_
      norm_num
      ring)
    (fun t ht => by linarith [taylor_degree_fifteen_le_sin_of_nonneg ht])
    hu

/-- **Eight-Panel Fourth-Order Midpoint Lower Bound `693146 / 1000000 ≤ Real.log 2`**. -/
theorem eight_panel_log_two_lower :
    (693146 / 1000000 : ℝ) ≤ Real.log 2 := by
  have h1 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 1) (b := 9 / 8) (by norm_num) (by norm_num)
  have h2 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 9 / 8) (b := 5 / 4) (by norm_num) (by norm_num)
  have h3 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 5 / 4) (b := 11 / 8) (by norm_num) (by norm_num)
  have h4 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 11 / 8) (b := 3 / 2) (by norm_num) (by norm_num)
  have h5 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 3 / 2) (b := 13 / 8) (by norm_num) (by norm_num)
  have h6 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 13 / 8) (b := 7 / 4) (by norm_num) (by norm_num)
  have h7 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 7 / 4) (b := 15 / 8) (by norm_num) (by norm_num)
  have h8 := two_mul_sub_div_add_add_two_mul_cube_div_three_cube_le_log_sub_log
    (a := 15 / 8) (b := 2) (by norm_num) (by norm_num)
  rw [Real.log_one] at h1
  linarith

/-- **Eight-Panel Simpson Upper Bound `Real.log 2 ≤ 693148 / 1000000`**. -/
theorem eight_panel_log_two_upper :
    Real.log 2 ≤ 693148 / 1000000 := by
  have h1 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 9 / 8)
  have h2 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 9 / 8) (by norm_num : (9 / 8 : ℝ) ≤ 5 / 4)
  have h3 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 5 / 4) (by norm_num : (5 / 4 : ℝ) ≤ 11 / 8)
  have h4 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 11 / 8) (by norm_num : (11 / 8 : ℝ) ≤ 3 / 2)
  have h5 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 13 / 8)
  have h6 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 13 / 8) (by norm_num : (13 / 8 : ℝ) ≤ 7 / 4)
  have h7 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 7 / 4) (by norm_num : (7 / 4 : ℝ) ≤ 15 / 8)
  have h8 := log_sub_log_le_simpson (by norm_num : (0 : ℝ) < 15 / 8) (by norm_num : (15 / 8 : ℝ) ≤ 2)
  rw [Real.log_one] at h1
  linarith

/-- Pell convergent lower bound `47321 / 33461 ≤ Real.sqrt 2`. -/
theorem pell_sqrt_two_lower :
    (47321 / 33461 : ℝ) ≤ Real.sqrt 2 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 47321 / 33461)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-- Pell convergent upper bound `Real.sqrt 2 ≤ 114243 / 80782`. -/
theorem pell_sqrt_two_upper :
    Real.sqrt 2 ≤ 114243 / 80782 := by
  rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 114243 / 80782)]
  exact Real.sqrt_le_sqrt (by norm_num)

/-! ## Section 2: The Tight Pure-Second-Moment First-Cell Bound `-(7 / 480) * r ^ 2 ≤ I_2(r)` and the Split Secant Numerator Law -/

/-- Sum-of-squares polynomial inequality on `0 ≤ u ≤ 49` for `(7 / 480) * (1 / 4 + u)`. -/
lemma first_cell_poly_of_coeffs_low {c0 c1 c2 c3 c4 c5 c6 c7 c8 u : ℝ}
    (hc0 : c0 ≤ -5415 / 1000000) (hc1 : c1 ≤ -21160 / 1000000)
    (hc2 : c2 ≤ 19647 / 10000000) (hc3 : c3 ≤ -39380 / 1000000000)
    (hc4 : c4 ≤ 37740 / 100000000000) (hc5 : c5 ≤ -21409 / 10000000000000)
    (hc6 : c6 ≤ 8140 / 1000000000000000) (hc7 : c7 ≤ -2201 / 100000000000000000)
    (hc8 : c8 ≤ 531 / 10000000000000000000)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 49) :
    c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 +
        c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8 ≤
      (7 / 480) * (1 / 4 + u) := by
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hm1 := mul_le_mul_of_nonneg_right hc1 hu_nonneg
  have hm2 := mul_le_mul_of_nonneg_right hc2 hu2
  have hm3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ u ^ 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ u ^ 4)
  have hm5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ u ^ 5)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 6)
  have hm7 := mul_le_mul_of_nonneg_right hc7 (by positivity : 0 ≤ u ^ 7)
  have hm8 := mul_le_mul_of_nonneg_right hc8 (by positivity : 0 ≤ u ^ 8)
  have hb8 : 0 ≤ -u ^ 8 + 147 * u ^ 7 - 7203 * u ^ 6 + 117649 * u ^ 5 := by
    rw [show -u ^ 8 + 147 * u ^ 7 - 7203 * u ^ 6 + 117649 * u ^ 5 =
      u ^ 5 * (49 - u) * (u - 49) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb7 : 0 ≤ u ^ 7 - 98 * u ^ 6 + 2401 * u ^ 5 := by
    rw [show u ^ 7 - 98 * u ^ 6 + 2401 * u ^ 5 = u ^ 5 * (u - 49) ^ 2 by ring]
    positivity
  have hb6 : 0 ≤ -u ^ 6 + 147 * u ^ 5 - 7203 * u ^ 4 + 117649 * u ^ 3 := by
    rw [show -u ^ 6 + 147 * u ^ 5 - 7203 * u ^ 4 + 117649 * u ^ 3 =
      u ^ 3 * (49 - u) * (u - 49) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb5 : 0 ≤ u ^ 5 - 98 * u ^ 4 + 2401 * u ^ 3 := by
    rw [show u ^ 5 - 98 * u ^ 4 + 2401 * u ^ 3 = u ^ 3 * (u - 49) ^ 2 by ring]
    positivity
  have hb4 : 0 ≤ -u ^ 4 + 147 * u ^ 3 - 7203 * u ^ 2 + 117649 * u := by
    rw [show -u ^ 4 + 147 * u ^ 3 - 7203 * u ^ 2 + 117649 * u =
      u * (49 - u) * (u - 49) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg hu_nonneg (by linarith)) (sq_nonneg _)
  have hb4b : 0 ≤ -u ^ 4 + 81 * u ^ 3 - 1824 * u ^ 2 + 12544 * u := by
    rw [show -u ^ 4 + 81 * u ^ 3 - 1824 * u ^ 2 + 12544 * u =
      u * (49 - u) * (u - 16) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg hu_nonneg (by linarith)) (sq_nonneg _)
  have hb3 : 0 ≤ u ^ 3 - 98 * u ^ 2 + 2401 * u := by
    rw [show u ^ 3 - 98 * u ^ 2 + 2401 * u = u * (u - 49) ^ 2 by ring]
    positivity
  have hb3b : 0 ≤ u ^ 3 - 90 * u ^ 2 + 2025 * u := by
    rw [show u ^ 3 - 90 * u ^ 2 + 2025 * u = u * (u - 45) ^ 2 by ring]
    positivity
  have hb2 : 0 ≤ u ^ 2 - 98 * u + 2401 := by
    rw [show u ^ 2 - 98 * u + 2401 = (u - 49) ^ 2 by ring]
    positivity
  have hb1 : 0 ≤ 49 * u - u ^ 2 := by
    rw [show 49 * u - u ^ 2 = u * (49 - u) by ring]
    exact mul_nonneg hu_nonneg (by linarith)
  linarith only [hc0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8,
    hb8, hb7, hb6, hb5, hb4, hb4b, hb3, hb3b, hb2, hb1, hu_nonneg, hu2, hr]

/-- Sum-of-squares polynomial inequality on `49 ≤ u ≤ 60` for `(7 / 480) * (1 / 4 + u)`. -/
lemma first_cell_poly_of_coeffs_mid {c0 c1 c2 c3 c4 c5 c6 c7 c8 u : ℝ}
    (hc0 : c0 ≤ -5415 / 1000000) (hc1 : c1 ≤ -21160 / 1000000)
    (hc2 : c2 ≤ 19647 / 10000000) (hc3 : c3 ≤ -39380 / 1000000000)
    (hc4 : c4 ≤ 37740 / 100000000000) (hc5 : c5 ≤ -21409 / 10000000000000)
    (hc6 : c6 ≤ 8140 / 1000000000000000) (hc7 : c7 ≤ -2201 / 100000000000000000)
    (hc8 : c8 ≤ 531 / 10000000000000000000)
    (hr_low : 49 ≤ u) (hr_high : u ≤ 60) :
    c0 + c1 * u + c2 * u ^ 2 + c3 * u ^ 3 + c4 * u ^ 4 +
        c5 * u ^ 5 + c6 * u ^ 6 + c7 * u ^ 7 + c8 * u ^ 8 ≤
      (7 / 480) * (1 / 4 + u) := by
  have hu_nonneg : 0 ≤ u := by linarith
  have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
  have hm1 := mul_le_mul_of_nonneg_right hc1 hu_nonneg
  have hm2 := mul_le_mul_of_nonneg_right hc2 hu2
  have hm3 := mul_le_mul_of_nonneg_right hc3 (by positivity : 0 ≤ u ^ 3)
  have hm4 := mul_le_mul_of_nonneg_right hc4 (by positivity : 0 ≤ u ^ 4)
  have hm5 := mul_le_mul_of_nonneg_right hc5 (by positivity : 0 ≤ u ^ 5)
  have hm6 := mul_le_mul_of_nonneg_right hc6 (by positivity : 0 ≤ u ^ 6)
  have hm7 := mul_le_mul_of_nonneg_right hc7 (by positivity : 0 ≤ u ^ 7)
  have hm8 := mul_le_mul_of_nonneg_right hc8 (by positivity : 0 ≤ u ^ 8)
  have hb8 : 0 ≤ -u ^ 8 + 160 * u ^ 7 - 8500 * u ^ 6 + 150000 * u ^ 5 := by
    rw [show -u ^ 8 + 160 * u ^ 7 - 8500 * u ^ 6 + 150000 * u ^ 5 =
      u ^ 5 * (60 - u) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb7 : 0 ≤ u ^ 7 - 149 * u ^ 6 + 7400 * u ^ 5 - 122500 * u ^ 4 := by
    rw [show u ^ 7 - 149 * u ^ 6 + 7400 * u ^ 5 - 122500 * u ^ 4 =
      u ^ 4 * (u - 49) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb6 : 0 ≤ -u ^ 6 + 160 * u ^ 5 - 8500 * u ^ 4 + 150000 * u ^ 3 := by
    rw [show -u ^ 6 + 160 * u ^ 5 - 8500 * u ^ 4 + 150000 * u ^ 3 =
      u ^ 3 * (60 - u) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb5 : 0 ≤ u ^ 5 - 149 * u ^ 4 + 7400 * u ^ 3 - 122500 * u ^ 2 := by
    rw [show u ^ 5 - 149 * u ^ 4 + 7400 * u ^ 3 - 122500 * u ^ 2 =
      u ^ 2 * (u - 49) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
  have hb4 : 0 ≤ -u ^ 4 + 160 * u ^ 3 - 8500 * u ^ 2 + 150000 * u := by
    rw [show -u ^ 4 + 160 * u ^ 3 - 8500 * u ^ 2 + 150000 * u =
      u * (60 - u) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (mul_nonneg hu_nonneg (by linarith)) (sq_nonneg _)
  have hb3 : 0 ≤ u ^ 3 - 149 * u ^ 2 + 7400 * u - 122500 := by
    rw [show u ^ 3 - 149 * u ^ 2 + 7400 * u - 122500 =
      (u - 49) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hb3b : 0 ≤ -u ^ 3 + 160 * u ^ 2 - 8500 * u + 150000 := by
    rw [show -u ^ 3 + 160 * u ^ 2 - 8500 * u + 150000 =
      (60 - u) * (u - 50) ^ 2 by ring]
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hb2 : 0 ≤ u ^ 2 - 100 * u + 2500 := by
    rw [show u ^ 2 - 100 * u + 2500 = (u - 50) ^ 2 by ring]
    positivity
  have hb2b : 0 ≤ -u ^ 2 + 109 * u - 2940 := by
    rw [show -u ^ 2 + 109 * u - 2940 = (u - 49) * (60 - u) by ring]
    exact mul_nonneg (by linarith) (by linarith)
  linarith only [hc0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8,
    hb8, hb7, hb6, hb5, hb4, hb3, hb3b, hb2, hb2b, hr_low, hr_high]

/-- **Degree-16 Polynomial Taylor Upper Bound for the First Cell (`0 ≤ u ≤ 60`)**. -/
theorem first_cell_taylor_poly_le_seven_four_eightieths {ℓ s2 u : ℝ}
    (hℓ_low : 693146 / 1000000 ≤ ℓ) (hℓ_high : ℓ ≤ 693148 / 1000000)
    (hs2_low : 47321 / 33461 ≤ s2) (hs2_high : s2 ≤ 114243 / 80782)
    (hu_nonneg : 0 ≤ u) (hr : u ≤ 60) :
    (2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2) +
      (s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2) * u +
      (-s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4) * u ^ 2 +
      (s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
        (2 * s2 - 1) / 120960 * ℓ ^ 8) * u ^ 3 +
      (-s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
        (2 * s2 - 1) / 10886400 * ℓ ^ 10) * u ^ 4 +
      (s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
        (2 * s2 - 1) / 1437004800 * ℓ ^ 12) * u ^ 5 +
      (-s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
        (2 * s2 - 1) / 261534873600 * ℓ ^ 14) * u ^ 6 +
      (s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14) * u ^ 7 +
      ((4 - 2 * s2) / 62768369664000 * ℓ ^ 16) * u ^ 8 ≤
    (7 / 480) * (1 / 4 + u) := by
  have hℓ0 : 0 ≤ ℓ := by linarith only [hℓ_low]
  have hs2_0 : 0 ≤ s2 := by linarith only [hs2_low]
  have hℓ1_1 : (693146 / 1000000 : ℝ) ≤ ℓ := hℓ_low
  have hℓ1_2 : ℓ ≤ 693148 / 1000000 := hℓ_high
  have hℓ2_1 : (480451 / 1000000 : ℝ) ≤ ℓ ^ 2 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hℓ1_1 2)
  have hℓ2_2 : ℓ ^ 2 ≤ 480455 / 1000000 :=
    le_trans (pow_le_pow_left₀ hℓ0 hℓ1_2 2) (by norm_num)
  have hℓ3_1 : (333022 / 1000000 : ℝ) ≤ ℓ ^ 3 := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ2_1 hℓ1_1 (by norm_num) (sq_nonneg ℓ))
  have hℓ3_2 : ℓ ^ 3 ≤ 333027 / 1000000 := by
    rw [show ℓ ^ 3 = ℓ ^ 2 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ4_1 : (230833 / 1000000 : ℝ) ≤ ℓ ^ 4 := by
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ2_1 hℓ2_1 (by norm_num) (sq_nonneg ℓ))
  have hℓ4_2 : ℓ ^ 4 ≤ 230838 / 1000000 := by
    rw [show ℓ ^ 4 = ℓ ^ 2 * ℓ ^ 2 by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ2_2 (sq_nonneg ℓ) (by norm_num)) (by norm_num)
  have hℓ5_1 : (159999 / 1000000 : ℝ) ≤ ℓ ^ 5 := by
    rw [show ℓ ^ 5 = ℓ ^ 4 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ4_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ6_1 : (110903 / 1000000 : ℝ) ≤ ℓ ^ 6 := by
    rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ3_1 hℓ3_1 (by norm_num) (by positivity))
  have hℓ6_2 : ℓ ^ 6 ≤ 110907 / 1000000 := by
    rw [show ℓ ^ 6 = ℓ ^ 3 * ℓ ^ 3 by ring]
    exact le_trans (mul_le_mul hℓ3_2 hℓ3_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ7_2 : ℓ ^ 7 ≤ 76875 / 1000000 := by
    rw [show ℓ ^ 7 = ℓ ^ 6 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ6_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ8_1 : (53283 / 1000000 : ℝ) ≤ ℓ ^ 8 := by
    rw [show ℓ ^ 8 = ℓ ^ 4 * ℓ ^ 4 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ4_1 hℓ4_1 (by norm_num) (by positivity))
  have hℓ8_2 : ℓ ^ 8 ≤ 53286 / 1000000 := by
    rw [show ℓ ^ 8 = ℓ ^ 2 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ2_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ9_1 : (36932 / 1000000 : ℝ) ≤ ℓ ^ 9 := by
    rw [show ℓ ^ 9 = ℓ ^ 8 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ8_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ10_1 : (25599 / 1000000 : ℝ) ≤ ℓ ^ 10 := by
    rw [show ℓ ^ 10 = ℓ ^ 5 * ℓ ^ 5 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ5_1 hℓ5_1 (by norm_num) (by positivity))
  have hℓ10_2 : ℓ ^ 10 ≤ 25602 / 1000000 := by
    rw [show ℓ ^ 10 = ℓ ^ 4 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ4_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ11_2 : ℓ ^ 11 ≤ 17746 / 1000000 := by
    rw [show ℓ ^ 11 = ℓ ^ 10 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ10_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ12_1 : (12299 / 1000000 : ℝ) ≤ ℓ ^ 12 := by
    rw [show ℓ ^ 12 = ℓ ^ 6 * ℓ ^ 6 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ6_1 hℓ6_1 (by norm_num) (by positivity))
  have hℓ12_2 : ℓ ^ 12 ≤ 12301 / 1000000 := by
    rw [show ℓ ^ 12 = ℓ ^ 6 * ℓ ^ 6 by ring]
    exact le_trans (mul_le_mul hℓ6_2 hℓ6_2 (by positivity) (by norm_num)) (by norm_num)
  have hℓ13_1 : (8525 / 1000000 : ℝ) ≤ ℓ ^ 13 := by
    rw [show ℓ ^ 13 = ℓ ^ 12 * ℓ by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ12_1 hℓ1_1 (by norm_num) (by positivity))
  have hℓ14_1 : (5909 / 1000000 : ℝ) ≤ ℓ ^ 14 := by
    rw [show ℓ ^ 14 = ℓ ^ 12 * ℓ ^ 2 by ring]
    exact le_trans (by norm_num) (mul_le_mul hℓ12_1 hℓ2_1 (by norm_num) (by positivity))
  have hℓ14_2 : ℓ ^ 14 ≤ 5911 / 1000000 := by
    rw [show ℓ ^ 14 = ℓ ^ 12 * ℓ ^ 2 by ring]
    exact le_trans (mul_le_mul hℓ12_2 hℓ2_2 (sq_nonneg ℓ) (by norm_num)) (by norm_num)
  have hℓ15_2 : ℓ ^ 15 ≤ 4098 / 1000000 := by
    rw [show ℓ ^ 15 = ℓ ^ 14 * ℓ by ring]
    exact le_trans (mul_le_mul hℓ14_2 hℓ1_2 hℓ0 (by norm_num)) (by norm_num)
  have hℓ16_2 : ℓ ^ 16 ≤ 2840 / 1000000 := by
    rw [show ℓ ^ 16 = ℓ ^ 8 * ℓ ^ 8 by ring]
    exact le_trans (mul_le_mul hℓ8_2 hℓ8_2 (by positivity) (by norm_num)) (by norm_num)
  have hc0 : 2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2 ≤ -5415 / 1000000 := by
    have hlin : 2 - ℓ + ℓ ^ 2 / 3 ≤ 2 - 693146 / 1000000 + (480455 / 1000000) / 3 := by
      linarith only [hℓ1_1, hℓ2_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : 2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2 =
        (2 - ℓ + ℓ ^ 2 / 3) * s2 - 2 - ℓ ^ 2 / 6 := by ring
    linarith only [hℓ2_1, hmul, hexp]
  have hc1 : s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2 ≤
      -21160 / 1000000 := by
    have hlin : ℓ ^ 3 / 6 - ℓ ^ 4 / 36 + ℓ ^ 2 / 3 ≤
        (333027 / 1000000) / 6 - (230833 / 1000000) / 36 + (480455 / 1000000) / 3 := by
      linarith only [hℓ3_2, hℓ4_1, hℓ2_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2 =
        (ℓ ^ 3 / 6 - ℓ ^ 4 / 36 + ℓ ^ 2 / 3) * s2 + ℓ ^ 4 / 72 - 2 / 3 * ℓ ^ 2 := by ring
    linarith only [hℓ4_2, hℓ2_1, hmul, hexp]
  have hc2 : -s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4 ≤
      19647 / 10000000 := by
    have hlin : (159999 / 1000000 : ℝ) / 120 - (110907 / 1000000) / 1080 +
        (230833 / 1000000) / 36 ≤ ℓ ^ 5 / 120 - ℓ ^ 6 / 1080 + ℓ ^ 4 / 36 := by
      linarith only [hℓ5_1, hℓ6_2, hℓ4_1]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4 =
        -(ℓ ^ 5 / 120 - ℓ ^ 6 / 1080 + ℓ ^ 4 / 36) * s2 - ℓ ^ 6 / 2160 + ℓ ^ 4 / 18 := by ring
    linarith only [hℓ6_1, hℓ4_2, hmul, hexp]
  have hc3 : s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
      (2 * s2 - 1) / 120960 * ℓ ^ 8 ≤ -39380 / 1000000000 := by
    have hlin : ℓ ^ 7 / 5040 + ℓ ^ 6 / 1080 - ℓ ^ 8 / 60480 ≤
        (76875 / 1000000) / 5040 + (110907 / 1000000) / 1080 - (53283 / 1000000) / 60480 := by
      linarith only [hℓ7_2, hℓ6_2, hℓ8_1]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
        (2 * s2 - 1) / 120960 * ℓ ^ 8 =
        (ℓ ^ 7 / 5040 + ℓ ^ 6 / 1080 - ℓ ^ 8 / 60480) * s2 - ℓ ^ 6 / 540 + ℓ ^ 8 / 120960 := by
      ring
    linarith only [hℓ6_1, hℓ8_2, hmul, hexp]
  have hc4 : -s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
      (2 * s2 - 1) / 10886400 * ℓ ^ 10 ≤ 37740 / 100000000000 := by
    have hlin : (36932 / 1000000 : ℝ) / 362880 + (53283 / 1000000) / 60480 -
        (25602 / 1000000) / 5443200 ≤
        ℓ ^ 9 / 362880 + ℓ ^ 8 / 60480 - ℓ ^ 10 / 5443200 := by
      linarith only [hℓ9_1, hℓ8_1, hℓ10_2]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
        (2 * s2 - 1) / 10886400 * ℓ ^ 10 =
        -(ℓ ^ 9 / 362880 + ℓ ^ 8 / 60480 - ℓ ^ 10 / 5443200) * s2 +
          ℓ ^ 8 / 30240 - ℓ ^ 10 / 10886400 := by ring
    linarith only [hℓ8_2, hℓ10_1, hmul, hexp]
  have hc5 : s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
      (2 * s2 - 1) / 1437004800 * ℓ ^ 12 ≤ -21409 / 10000000000000 := by
    have hlin : ℓ ^ 11 / 39916800 + ℓ ^ 10 / 5443200 - ℓ ^ 12 / 718502400 ≤
        (17746 / 1000000) / 39916800 + (25602 / 1000000) / 5443200 -
          (12299 / 1000000) / 718502400 := by
      linarith only [hℓ11_2, hℓ10_2, hℓ12_1]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
        (2 * s2 - 1) / 1437004800 * ℓ ^ 12 =
        (ℓ ^ 11 / 39916800 + ℓ ^ 10 / 5443200 - ℓ ^ 12 / 718502400) * s2 -
          ℓ ^ 10 / 2721600 + ℓ ^ 12 / 1437004800 := by ring
    linarith only [hℓ10_1, hℓ12_2, hmul, hexp]
  have hc6 : -s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
      (2 * s2 - 1) / 261534873600 * ℓ ^ 14 ≤ 8140 / 1000000000000000 := by
    have hlin : (8525 / 1000000 : ℝ) / 6227020800 + (12299 / 1000000) / 718502400 -
        (5911 / 1000000) / 130767436800 ≤
        ℓ ^ 13 / 6227020800 + ℓ ^ 12 / 718502400 - ℓ ^ 14 / 130767436800 := by
      linarith only [hℓ13_1, hℓ12_1, hℓ14_2]
    have hmul := mul_le_mul hlin hs2_low (by norm_num) (by linarith only [hlin])
    have hexp : -s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
        (2 * s2 - 1) / 261534873600 * ℓ ^ 14 =
        -(ℓ ^ 13 / 6227020800 + ℓ ^ 12 / 718502400 - ℓ ^ 14 / 130767436800) * s2 +
          ℓ ^ 12 / 359251200 - ℓ ^ 14 / 261534873600 := by ring
    linarith only [hℓ12_2, hℓ14_1, hmul, hexp]
  have hc7 : s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14 ≤
      -2201 / 100000000000000000 := by
    have hlin : ℓ ^ 15 / 1307674368000 + ℓ ^ 14 / 130767436800 ≤
        (4098 / 1000000) / 1307674368000 + (5911 / 1000000) / 130767436800 := by
      linarith only [hℓ15_2, hℓ14_2]
    have hmul := mul_le_mul hlin hs2_high hs2_0 (by norm_num)
    have hexp : s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14 =
        (ℓ ^ 15 / 1307674368000 + ℓ ^ 14 / 130767436800) * s2 - ℓ ^ 14 / 65383718400 := by ring
    linarith only [hℓ14_1, hmul, hexp]
  have hc8 : (4 - 2 * s2) / 62768369664000 * ℓ ^ 16 ≤ 531 / 10000000000000000000 := by
    have hlin : (4 - 2 * s2) / 62768369664000 ≤ (4 - 2 * (47321 / 33461)) / 62768369664000 := by
      linarith only [hs2_low]
    have hmul := mul_le_mul hlin hℓ16_2 (by positivity) (by norm_num)
    linarith only [hmul]
  rcases le_total u 49 with h49 | h49
  · exact first_cell_poly_of_coeffs_low hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hu_nonneg h49
  · exact first_cell_poly_of_coeffs_mid hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 h49 hr

/-- **Small/Medium Frequency Bound (`r ^ 2 ≤ 60`)**:
for every `r : ℝ` with `r ^ 2 ≤ 60`,
`-(1 / 4 + r ^ 2) * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x ≤ (7 / 480) * r ^ 2 * (1 / 4 + r ^ 2)`. -/
theorem neg_mul_integral_one_two_cosLogProfile_le_of_sq_le_sixty {r : ℝ} (hr : r ^ 2 ≤ 60) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
      (7 / 480) * r ^ 2 * (1 / 4 + r ^ 2) := by
  rw [neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r]
  set ℓ := Real.log 2
  set s2 := Real.sqrt 2
  set u := r ^ 2
  have hu_nonneg : 0 ≤ u := sq_nonneg r
  have hℓ_low : (693146 / 1000000 : ℝ) ≤ ℓ := eight_panel_log_two_lower
  have hℓ_high : ℓ ≤ 693148 / 1000000 := eight_panel_log_two_upper
  have hℓ_pos : 0 < ℓ := lt_of_lt_of_le (by norm_num) hℓ_low
  have hs2_low : (47321 / 33461 : ℝ) ≤ s2 := pell_sqrt_two_lower
  have hs2_high : s2 ≤ 114243 / 80782 := pell_sqrt_two_upper
  set θ := r * ℓ
  have hcos_up := one_sub_cos_le_taylor_degree_fourteen θ
  have hcos_low := taylor_degree_sixteen_le_one_sub_cos θ
  have hsin_low := mul_sin_ge_taylor_degree_sixteen θ
  have hsin_scaled :
      r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
        ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800 +
        ℓ ^ 13 * u ^ 6 / 6227020800 - ℓ ^ 15 * u ^ 7 / 1307674368000) ≤
        r * Real.sin θ := by
    have hdiv := div_le_div_of_nonneg_right hsin_low hℓ_pos.le
    have h1 : (θ ^ 2 - θ ^ 4 / 6 + θ ^ 6 / 120 - θ ^ 8 / 5040 +
        θ ^ 10 / 362880 - θ ^ 12 / 39916800 +
        θ ^ 14 / 6227020800 - θ ^ 16 / 1307674368000) / ℓ =
        r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
          ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800 +
          ℓ ^ 13 * u ^ 6 / 6227020800 - ℓ ^ 15 * u ^ 7 / 1307674368000) := by
      dsimp [θ, u]
      field_simp [hℓ_pos.ne']
    have h2 : θ * Real.sin θ / ℓ = r * Real.sin θ := by
      dsimp [θ]
      field_simp [hℓ_pos.ne']
    linarith
  have hcoeff_pos1 : 0 ≤ (2 * s2 - 1) / 3 := by linarith
  have hcoeff_pos2 : 0 ≤ ((4 - 2 * s2) / 3) * r ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg r)
  have hterm_cos1 := mul_le_mul_of_nonneg_left hcos_up hcoeff_pos1
  have hterm_cos2 := mul_le_mul_of_nonneg_left hcos_low hcoeff_pos2
  have hterm_sin := mul_le_mul_of_nonneg_left hsin_scaled (by linarith : 0 ≤ s2)
  have hpoly_id :
      2 * (s2 - 1) * r ^ 2 -
        s2 * (r ^ 2 * (ℓ - ℓ ^ 3 * u / 6 + ℓ ^ 5 * u ^ 2 / 120 - ℓ ^ 7 * u ^ 3 / 5040 +
          ℓ ^ 9 * u ^ 4 / 362880 - ℓ ^ 11 * u ^ 5 / 39916800 +
          ℓ ^ 13 * u ^ 6 / 6227020800 - ℓ ^ 15 * u ^ 7 / 1307674368000)) +
        ((2 * s2 - 1) / 3) *
          (θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
            θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200) -
        (((4 - 2 * s2) / 3) * r ^ 2) *
          (θ ^ 2 / 2 - θ ^ 4 / 24 + θ ^ 6 / 720 - θ ^ 8 / 40320 +
            θ ^ 10 / 3628800 - θ ^ 12 / 479001600 + θ ^ 14 / 87178291200 -
            θ ^ 16 / 20922789888000) =
      u * ((2 * (s2 - 1) - s2 * ℓ + (2 * s2 - 1) / 6 * ℓ ^ 2) +
        (s2 * ℓ ^ 3 / 6 - (2 * s2 - 1) / 72 * ℓ ^ 4 - (4 - 2 * s2) / 6 * ℓ ^ 2) * u +
        (-s2 * ℓ ^ 5 / 120 + (2 * s2 - 1) / 2160 * ℓ ^ 6 + (4 - 2 * s2) / 72 * ℓ ^ 4) * u ^ 2 +
        (s2 * ℓ ^ 7 / 5040 - (4 - 2 * s2) / 2160 * ℓ ^ 6 -
          (2 * s2 - 1) / 120960 * ℓ ^ 8) * u ^ 3 +
        (-s2 * ℓ ^ 9 / 362880 + (4 - 2 * s2) / 120960 * ℓ ^ 8 +
          (2 * s2 - 1) / 10886400 * ℓ ^ 10) * u ^ 4 +
        (s2 * ℓ ^ 11 / 39916800 - (4 - 2 * s2) / 10886400 * ℓ ^ 10 -
          (2 * s2 - 1) / 1437004800 * ℓ ^ 12) * u ^ 5 +
        (-s2 * ℓ ^ 13 / 6227020800 + (4 - 2 * s2) / 1437004800 * ℓ ^ 12 +
          (2 * s2 - 1) / 261534873600 * ℓ ^ 14) * u ^ 6 +
        (s2 * ℓ ^ 15 / 1307674368000 - (4 - 2 * s2) / 261534873600 * ℓ ^ 14) * u ^ 7 +
        ((4 - 2 * s2) / 62768369664000 * ℓ ^ 16) * u ^ 8) := by
    dsimp [θ, u]
    ring
  have hinner_le :=
    first_cell_taylor_poly_le_seven_four_eightieths hℓ_low hℓ_high hs2_low hs2_high hu_nonneg hr
  have hprod_le := mul_le_mul_of_nonneg_left hinner_le hu_nonneg
  dsimp [u] at hprod_le hpoly_id ⊢
  linarith

/-- **Large Frequency Bound (`60 ≤ r ^ 2`)**:
for every `r : ℝ` with `60 ≤ r ^ 2`,
`-(1 / 4 + r ^ 2) * ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x ≤ (7 / 480) * r ^ 2 * (1 / 4 + r ^ 2)`. -/
theorem neg_mul_integral_one_two_cosLogProfile_le_of_le_sq_sixty {r : ℝ} (hr : 60 ≤ r ^ 2) :
    -(1 / 4 + r ^ 2) *
        (∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
      (7 / 480) * r ^ 2 * (1 / 4 + r ^ 2) := by
  rw [neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r]
  set s2 := Real.sqrt 2
  set u := r ^ 2
  have hu_nonneg : 0 ≤ u := by linarith
  have hs2_low : (8119 / 5741 : ℝ) ≤ s2 := eight_thousand_one_hundred_nineteen_le_sqrt_two
  have hs2_high : s2 ≤ 577 / 408 := sqrt_two_le_five_seventy_seven_four_hundred_eighths
  have hs2_sq : s2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsplit :
      2 * (s2 - 1) * r ^ 2 - s2 * r * Real.sin (r * Real.log 2) +
        ((2 * s2 - 1) / 3 - ((4 - 2 * s2) / 3) * r ^ 2) * (1 - Real.cos (r * Real.log 2)) =
      ((8 * s2 - 10) / 3 * u + (2 * s2 - 1) / 3) +
        ((((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
          (-s2 * r) * Real.sin (r * Real.log 2)) := by
    dsimp [u]
    ring
  have hcs := sq_linear_cos_sin_le
    (((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) (-s2 * r) (r * Real.log 2)
  have hamp_sq :
      (((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) ^ 2 + (-s2 * r) ^ 2 ≤
        ((391 / 1000) * u + 39 / 20) ^ 2 := by
    have hrew : (-s2 * r) ^ 2 = 2 * u := by
      dsimp [u]
      linear_combination r ^ 2 * hs2_sq
    have hcoeff_sq : (((4 - 2 * s2) / 3) ^ 2 - (391 / 1000) ^ 2) * u ^ 2 ≤ 0 := by
      refine mul_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg u)
      nlinarith [hs2_low, hs2_high]
    rw [hrew]
    nlinarith [hs2_low, hs2_high, hcoeff_sq]
  have hosc_le :
      (((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
        (-s2 * r) * Real.sin (r * Real.log 2) ≤ (391 / 1000) * u + 39 / 20 := by
    have h1 := le_abs_self
      ((((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
        (-s2 * r) * Real.sin (r * Real.log 2))
    have h2 :
        |(((4 - 2 * s2) / 3) * u - (2 * s2 - 1) / 3) * Real.cos (r * Real.log 2) +
          (-s2 * r) * Real.sin (r * Real.log 2)| ≤ (391 / 1000) * u + 39 / 20 := by
      rw [← Real.sqrt_sq_eq_abs,
        ← Real.sqrt_sq (by positivity : 0 ≤ (391 / 1000) * u + 39 / 20)]
      exact Real.sqrt_le_sqrt (hcs.trans hamp_sq)
    exact h1.trans h2
  have hmain_le :
      ((8 * s2 - 10) / 3 * u + (2 * s2 - 1) / 3) + ((391 / 1000) * u + 39 / 20) ≤
        (7 / 480) * u * (1 / 4 + u) := by
    have hu_quad : 0 ≤ u ^ 2 - 120 * u + 3600 := by
      have h : 0 ≤ (u - 60) ^ 2 := sq_nonneg (u - 60)
      linarith [show (u - 60) ^ 2 = u ^ 2 - 120 * u + 3600 by ring]
    have hs2_u : (8 * s2 - 10) / 3 * u ≤ (8 * (577 / 408) - 10) / 3 * u :=
      mul_le_mul_of_nonneg_right (by linarith) hu_nonneg
    linarith [hs2_high, hr, hu_quad, hs2_u,
      show (7 / 480) * u * (1 / 4 + u) = (7 / 1920) * u + (7 / 480) * u ^ 2 by ring]
  dsimp [u] at hsplit hosc_le hmain_le ⊢
  linarith

/-- **Tight Global Pure-Second-Moment First-Cell Quadrature Inequality (`7 / 480 = 52.5 / 3600`)**:
for **every** `r : ℝ`,
`-(7 / 480) * r ^ 2 ≤ ∫ x in 1..2, (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x`. -/
theorem neg_seven_four_eightieths_mul_sq_le_integral_one_two_cosLogProfile (r : ℝ) :
    -(7 / 480) * r ^ 2 ≤
      ∫ x in (1 : ℝ)..2,
        (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
  have hden_pos : (0 : ℝ) < 1 / 4 + r ^ 2 := by positivity
  have hmul :
      -(1 / 4 + r ^ 2) *
          (∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) ≤
        (7 / 480) * r ^ 2 * (1 / 4 + r ^ 2) := by
    rcases le_total (r ^ 2) 60 with hle | hge
    · exact neg_mul_integral_one_two_cosLogProfile_le_of_sq_le_sixty hle
    · exact neg_mul_integral_one_two_cosLogProfile_le_of_le_sq_sixty hge
  nlinarith

/-- **Tight First-Cell Pure Second-Moment Quadrature Lower Bound (`7 / 480 = 52.5 / 3600`)**:
for every `f : WeilTestFn` with `Integrable (fun r => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))`,
`-(7 / 480) * spectralSecondMoment f.1 ≤ ∫ x in 1..2, (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) / Real.sqrt x`. -/
theorem neg_seven_four_eightieths_spectralSecondMoment_le_integral_one_two
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) :
    -(7 / 480) * spectralSecondMoment f.1 ≤
      ∫ x in (1 : ℝ)..2,
        (weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) 2 x) /
          Real.sqrt x := by
  rw [integral_one_two_weilSymmetricLogNumerator_sub_cellSecant_div_sqrt_eq_spectral f]
  have hrhs_eq :
      -(7 / 480) * spectralSecondMoment f.1 =
        (1 / (2 * π)) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * (2 * (-(7 / 480) * r ^ 2)) := by
    unfold spectralSecondMoment
    rw [← mul_assoc, mul_comm (-(7 / 480 : ℝ)), mul_assoc, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    ring
  rw [hrhs_eq]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg zero_le_one Real.two_pi_pos.le)
  have hint_lhs : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 * (2 * (-(7 / 480) * r ^ 2)) := by
    have heq : (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (-(7 / 480) * r ^ 2))) =
        fun r : ℝ => (-(7 / 480)) * (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2)) := by
      ext r; ring
    rw [heq]
    exact hint2.const_mul _
  have hint_rhs : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 *
        (2 * ∫ x in (1 : ℝ)..2,
          (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) := by
    have hmeas : AEStronglyMeasurable (fun r : ℝ =>
        ‖paperFT f.1 r‖ ^ 2 *
          (2 * ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)) volume := by
      have h1 : AEStronglyMeasurable (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2) volume :=
        (integrable_paperFT_norm_sq f).aestronglyMeasurable
      have h2 : Continuous fun r : ℝ =>
          ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x := by
        have hrew : (fun r : ℝ =>
            ∫ x in (1 : ℝ)..2,
              (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x) =
            fun r : ℝ =>
              -(2 * (Real.sqrt 2 - 1) * r ^ 2 - Real.sqrt 2 * r * Real.sin (r * Real.log 2) +
                ((2 * Real.sqrt 2 - 1) / 3 - ((4 - 2 * Real.sqrt 2) / 3) * r ^ 2) *
                  (1 - Real.cos (r * Real.log 2))) / (1 / 4 + r ^ 2) := by
          ext r
          have h := neg_mul_integral_one_two_cosLogProfile_sub_cellSecant_div_sqrt_eq r
          have hden_ne : (1 / 4 + r ^ 2 : ℝ) ≠ 0 := by positivity
          apply mul_left_cancel₀ hden_ne
          rw [mul_div_cancel₀ _ hden_ne]
          linarith
        rw [hrew]
        refine Continuous.div (by fun_prop) (by fun_prop) (fun r => by positivity)
      exact h1.mul (continuous_const.mul h2).aestronglyMeasurable
    have hbound : ∀ r : ℝ,
        ‖‖paperFT f.1 r‖ ^ 2 *
          (2 * ∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)‖ ≤
          6 * ‖paperFT f.1 r‖ ^ 2 := by
      intro r
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hint_abs :
          |∫ x in (1 : ℝ)..2,
            (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x| ≤ 3 := by
        have h := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := 1) (b := 2) (C := 3)
          (f := fun x => (cosLogProfile r x - cellSecant (cosLogProfile r) 2 x) / Real.sqrt x)
          (fun x hx => by
            rw [uIoc_of_le (by norm_num : (1 : ℝ) ≤ 2)] at hx
            have hx1 : 1 ≤ x := hx.1.le
            have hx2 : x ≤ 2 := hx.2
            have hsqrt_ge : 1 ≤ Real.sqrt x := by
              rw [← Real.sqrt_one]
              exact Real.sqrt_le_sqrt hx1
            have hcos_abs : |cosLogProfile r x| ≤ 1 := Real.abs_cos_le_one _
            have hsec_abs : |cellSecant (cosLogProfile r) 2 x| ≤ 2 := by
              unfold cellSecant
              norm_num
              have ha : |cosLogProfile r 1| ≤ 1 := Real.abs_cos_le_one _
              have hb : |cosLogProfile r 2| ≤ 1 := Real.abs_cos_le_one _
              have htri := abs_add_le ((2 - x) * cosLogProfile r 1)
                ((x - 1) * cosLogProfile r 2)
              have hw1 : |2 - x| = 2 - x := abs_of_nonneg (by linarith)
              have hw2 : |x - 1| = x - 1 := abs_of_nonneg (by linarith)
              rw [abs_mul, abs_mul, hw1, hw2] at htri
              nlinarith
            rw [Real.norm_eq_abs, abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hsqrt_ge)]
            refine (div_le_self (abs_nonneg _) hsqrt_ge).trans ?_
            have htri := abs_sub (cosLogProfile r x) (cellSecant (cosLogProfile r) 2 x)
            linarith)
        rw [Real.norm_eq_abs] at h
        linarith [show |(2 : ℝ) - 1| = 1 by norm_num]
      nlinarith [sq_nonneg ‖paperFT f.1 r‖]
    exact Integrable.mono' ((integrable_paperFT_norm_sq f).const_mul 6)
      hmeas (Eventually.of_forall hbound)
  refine integral_mono hint_lhs hint_rhs fun r => ?_
  dsimp only
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (neg_seven_four_eightieths_mul_sq_le_integral_one_two_cosLogProfile r)
      (by norm_num))
    (sq_nonneg _)

/-- **The Tight Split First-Cell / Tail Secant Numerator Law (`7 / 480 = 52.5 / 3600`)**:
for every `f : WeilTestFn` and `N : ℕ`,
`-(7 / 480) * spectralSecondMoment f.1 - (71 / 3600) * Real.sqrt (spectralSecondMoment f.1 * (spectralSecondMoment f.1 + 2 * ∫ u, ‖f.1 u‖ ^ 2)) ≤ secantNumeratorCellDefect f.1 N`. -/
theorem neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(7 / 480) * spectralSecondMoment f.1 -
        (71 / 3600) *
          Real.sqrt
            (spectralSecondMoment f.1 *
              (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      secantNumeratorCellDefect f.1 N := by
  have hS_nonneg : 0 ≤ spectralSecondMoment f.1 := spectralSecondMoment_nonneg f.1
  unfold secantNumeratorCellDefect
  by_cases hN : 2 ≤ N
  · rw [sum_Icc_two_eq_add_sum_Icc_three _ hN]
    have h2 := neg_seven_four_eightieths_spectralSecondMoment_le_integral_one_two f hint2
    have h3 := neg_seventy_one_thirty_six_hundredths_sqrt_le_sum_Icc_three f hint2 N
    linarith
  · rw [Finset.Icc_eq_empty hN, Finset.sum_empty]
    have hsqrt_nonneg : 0 ≤ Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) := Real.sqrt_nonneg _
    linarith

/-! ## Section 3: Four-Stage Secular Counterterm Potential `secantFourStagePotential`, the `247 / 300 = 2964 / 3600` Origin Surplus, and Coercivity & Spectral Gap Laws up to `117 / 5 = 23.4`, `124 / 5 = 24.8`, `51 / 2 = 25.5`, and `27` -/

/-- The **Four-Stage Secular Counterterm Potential** `secantFourStagePotential n`:
isolates `n = 2` (with denominator `√2`), `n = 3` (with denominator `√3`), and `n = 4` (with
denominator `2 = √4`), and uses denominator `√5` for `n ≥ 5`. -/
def secantFourStagePotential (n : ℕ) : ℝ :=
  if n = 2 then
    (secantQuadTerm 2 - secantQuadTerm 3) / Real.sqrt 2 +
      (secantQuadTerm 3 - secantQuadTerm 4) / Real.sqrt 3 +
      (secantQuadTerm 4 - secantQuadTerm 5) / 2 +
      secantQuadTerm 5 / Real.sqrt 5 - 2 * secantCubeTerm 2 / 3
  else if n = 3 then
    (secantQuadTerm 3 - secantQuadTerm 4) / Real.sqrt 3 +
      (secantQuadTerm 4 - secantQuadTerm 5) / 2 +
      secantQuadTerm 5 / Real.sqrt 5 - 2 * secantCubeTerm 3 / 3
  else if n = 4 then
    (secantQuadTerm 4 - secantQuadTerm 5) / 2 +
      secantQuadTerm 5 / Real.sqrt 5 - 2 * secantCubeTerm 4 / 3
  else
    secantQuadTerm n / Real.sqrt 5 - 2 * secantCubeTerm n / 3

/-- **Four-Stage Telescoping Step Bound**:
for every `2 ≤ n`,
`secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤ secantFourStagePotential n - secantFourStagePotential (n + 1)`. -/
theorem secantCombinedSecularWeight_mul_two_div_sqrt_le_fourStage {n : ℕ} (hn : 2 ≤ n) :
    secantCombinedSecularWeight n * (2 / Real.sqrt n) ≤
      secantFourStagePotential n - secantFourStagePotential (n + 1) := by
  have hn_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
  have hne : Real.sqrt n ≠ 0 := hn_pos.ne'
  have hterm2 :
      ((secantCubeTerm n - secantCubeTerm (n + 1)) * Real.sqrt n / 3) * (2 / Real.sqrt n) =
        2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
    rw [div_eq_mul_inv (_ * Real.sqrt n) 3, div_eq_mul_inv 2 (Real.sqrt n)]
    calc (secantCubeTerm n - secantCubeTerm (n + 1)) * Real.sqrt n * 3⁻¹ *
          (2 * (Real.sqrt n)⁻¹)
      _ = (2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3) *
            (Real.sqrt n * (Real.sqrt n)⁻¹) := by ring
      _ = 2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
          rw [mul_inv_cancel₀ hne, mul_one]
  have hlhs :
      secantCombinedSecularWeight n * (2 / Real.sqrt n) =
        (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt n -
          2 * (secantCubeTerm n - secantCubeTerm (n + 1)) / 3 := by
    unfold secantCombinedSecularWeight trapezoidalSecularDiffWeight secantCubicCountertermWeight
    simp only [if_pos hn]
    have hq :
        (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 2 -
          (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 2 =
        secantQuadTerm n - secantQuadTerm (n + 1) := by
      unfold secantQuadTerm
      push_cast
      rw [add_sub_cancel_right]
    have hc :
        (Real.sqrt n - Real.sqrt ((n : ℝ) - 1)) ^ 3 -
          (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n) ^ 3 =
        secantCubeTerm n - secantCubeTerm (n + 1) := by
      unfold secantCubeTerm
      push_cast
      rw [add_sub_cancel_right]
    rw [hq, hc, sub_mul, hterm2]
    congr 1
    ring
  rw [hlhs]
  by_cases hn2 : n = 2
  · subst hn2
    unfold secantFourStagePotential
    norm_num
    ring_nf
    exact le_rfl
  · by_cases hn3 : n = 3
    · subst hn3
      unfold secantFourStagePotential
      norm_num
      ring_nf
      exact le_rfl
    · by_cases hn4 : n = 4
      · subst hn4
        unfold secantFourStagePotential
        norm_num
        ring_nf
        exact le_rfl
      · have hn5 : 5 ≤ n := by omega
        have h1 : n ≠ 2 := hn2
        have h2 : n ≠ 3 := hn3
        have h3 : n ≠ 4 := hn4
        have h4 : n + 1 ≠ 2 := by omega
        have h5 : n + 1 ≠ 3 := by omega
        have h6 : n + 1 ≠ 4 := by omega
        unfold secantFourStagePotential
        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6]
        have hsqrt_ge : Real.sqrt 5 ≤ Real.sqrt n :=
          Real.sqrt_le_sqrt (by exact_mod_cast hn5)
        have hinv_le : (Real.sqrt n)⁻¹ ≤ (Real.sqrt 5)⁻¹ :=
          inv_anti₀ (Real.sqrt_pos.mpr (by norm_num)) hsqrt_ge
        have hΔ2_nonneg := secantQuadTerm_sub_succ_nonneg (by omega : 1 ≤ n)
        have hdiv_le :
            (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt n ≤
              (secantQuadTerm n - secantQuadTerm (n + 1)) / Real.sqrt 5 := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left hinv_le hΔ2_nonneg
        linarith [sub_div (secantQuadTerm n) (secantQuadTerm (n + 1)) (Real.sqrt 5)]

/-- For every `5 ≤ n`, `0 ≤ secantFourStagePotential n`. -/
theorem secantFourStagePotential_nonneg_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    0 ≤ secantFourStagePotential n := by
  have h1 : n ≠ 2 := by omega
  have h2 : n ≠ 3 := by omega
  have h3 : n ≠ 4 := by omega
  unfold secantFourStagePotential
  rw [if_neg h1, if_neg h2, if_neg h3]
  unfold secantQuadTerm secantCubeTerm
  set d := Real.sqrt n - Real.sqrt ((n : ℝ) - 1)
  have hd_nonneg : 0 ≤ d := sub_nonneg.mpr (Real.sqrt_le_sqrt (by linarith))
  have hsqrt5_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have hd_le : d * Real.sqrt 5 ≤ 1 := by
    have hn5 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hconj : d * (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) = 1 := by
      have hsq0 : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (by linarith)
      have hsq1 : Real.sqrt ((n : ℝ) - 1) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt (by linarith)
      dsimp [d]
      linear_combination hsq0 - hsq1
    have hsum_ge : Real.sqrt 5 ≤ Real.sqrt n + Real.sqrt ((n : ℝ) - 1) := by
      have hsqrt_n : Real.sqrt 5 ≤ Real.sqrt n := Real.sqrt_le_sqrt hn5
      have hsqrt_pred : 0 ≤ Real.sqrt ((n : ℝ) - 1) := Real.sqrt_nonneg _
      linarith
    have hmul := mul_le_mul_of_nonneg_left hsum_ge hd_nonneg
    linarith
  have hfactor :
      d ^ 2 / Real.sqrt 5 - 2 * d ^ 3 / 3 =
        (d ^ 2 / (3 * Real.sqrt 5)) * (3 - 2 * (d * Real.sqrt 5)) := by
    have hne : Real.sqrt 5 ≠ 0 := hsqrt5_pos.ne'
    field_simp [hne]
  rw [hfactor]
  exact mul_nonneg (by positivity) (by linarith)

/-- For every `2 ≤ n`, `0 ≤ secantFourStagePotential n`. -/
theorem secantFourStagePotential_nonneg {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ secantFourStagePotential n := by
  have hstep : ∀ k : ℕ, 2 ≤ k → secantFourStagePotential (k + 1) ≤ secantFourStagePotential k := by
    intro k hk
    have h1 := secantCombinedSecularWeight_mul_two_div_sqrt_le_fourStage hk
    have h2 : 0 ≤ secantCombinedSecularWeight k * (2 / Real.sqrt k) :=
      mul_nonneg (secantCombinedSecularWeight_nonneg k) (by positivity)
    linarith
  have h5 : 0 ≤ secantFourStagePotential 5 :=
    secantFourStagePotential_nonneg_of_five_le (by omega)
  have h4 : 0 ≤ secantFourStagePotential 4 := le_trans h5 (hstep 4 (by omega))
  have h3 : 0 ≤ secantFourStagePotential 3 := le_trans h4 (hstep 3 (by omega))
  have h2 : 0 ≤ secantFourStagePotential 2 := le_trans h3 (hstep 2 (by omega))
  by_cases hn2 : n = 2
  · subst hn2; exact h2
  · by_cases hn3 : n = 3
    · subst hn3; exact h3
    · by_cases hn4 : n = 4
      · subst hn4; exact h4
      · exact secantFourStagePotential_nonneg_of_five_le (by omega)

/-- **Exact Closed Form of `secantFourStagePotential 2`**:
`secantFourStagePotential 2 = (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6 - (17 / 2 - 19 * Real.sqrt 5 / 5)`. -/
theorem secantFourStagePotential_two_eq :
    secantFourStagePotential 2 =
      (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6 - (17 / 2 - 19 * Real.sqrt 5 / 5) := by
  rw [← secantThreeStagePotential_two_eq]
  unfold secantFourStagePotential secantThreeStagePotential
  simp only [↓reduceIte]
  have hq5 : secantQuadTerm 5 = (Real.sqrt 5 - 2) ^ 2 := by
    unfold secantQuadTerm
    norm_num
  have hdiff :
      secantQuadTerm 5 / 2 - secantQuadTerm 5 / Real.sqrt 5 =
        17 / 2 - 19 * Real.sqrt 5 / 5 := by
    rw [hq5]
    set s5 := Real.sqrt 5
    have h5 : s5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    have hs5_ne : s5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    apply mul_right_cancel₀ hs5_ne
    field_simp [hs5_ne]
    linear_combination (8 + 5 * s5) * h5
  linarith

/-- **Four-Stage Telescoping Upper Bound on `∑_{n=2}^N secantCombinedSecularWeight n * (2 / √n)`**: -/
theorem sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_fourStage {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
      (61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6 - (17 / 2 - 19 * Real.sqrt 5 / 5) := by
  have hle_sum :
      (∑ n ∈ Finset.Icc 2 N, secantCombinedSecularWeight n * (2 / Real.sqrt n)) ≤
        ∑ n ∈ Finset.Icc 2 N,
          (secantFourStagePotential n - secantFourStagePotential (n + 1)) := by
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    exact secantCombinedSecularWeight_mul_two_div_sqrt_le_fourStage hn.1
  rw [sum_Icc_two_sub_succ_nat secantFourStagePotential hN] at hle_sum
  have h2 := secantFourStagePotential_two_eq
  have hN1 : 0 ≤ secantFourStagePotential (N + 1) :=
    secantFourStagePotential_nonneg (by omega)
  linarith

/-- **Upgraded Four-Stage Uniform Bound on `primeBlindCounterterm secantCombinedSecularWeight f`**: -/
theorem abs_primeBlindCounterterm_secantCombinedSecularWeight_le_fourStage
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    |primeBlindCounterterm secantCombinedSecularWeight f| ≤
      ((61 - 38 * Real.sqrt 2 - 4 * Real.sqrt 3) / 6 - (17 / 2 - 19 * Real.sqrt 5 / 5)) *
        ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  rw [primeBlindCounterterm_eq_sum_Icc secantCombinedSecularWeight f hN]
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ n ∈ Finset.Icc 2 N,
       |secantCombinedSecularWeight n * logValue f.1 n| ≤
        (secantCombinedSecularWeight n * (2 / Real.sqrt n)) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [abs_mul, abs_of_nonneg (secantCombinedSecularWeight_nonneg n), mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (abs_logValue_le_two_div_sqrt_mul_integral_norm_sq f (by omega : 1 ≤ n))
      (secantCombinedSecularWeight_nonneg n)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right
    (sum_Icc_secantCombinedSecularWeight_mul_two_div_sqrt_le_fourStage hN1) hnorm_nonneg

/-- **Sharp Rational Lower Bound `247 / 300 = 2964 / 3600` on the Four-Stage Origin Surplus**: -/
theorem two_forty_seven_three_hundredths_le_fourStage_surplus :
    (247 / 300 : ℝ) ≤
      (70 * Real.sqrt 2 + 4 * Real.sqrt 3 - 101) / 6 + (17 / 2 - 19 * Real.sqrt 5 / 5) := by
  have hsqrt2 : (47321 / 33461 : ℝ) ≤ Real.sqrt 2 := pell_sqrt_two_lower
  have hsqrt3 : (989 / 571 : ℝ) ≤ Real.sqrt 3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 989 / 571)]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrt5 : Real.sqrt 5 ≤ 2889 / 1292 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2889 / 1292)]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- **Upgraded `247 / 300 = 2964 / 3600` (`> 0.82333`) Positive $L^2$ Surplus over `secantNumeratorCellDefect`**:
for every `f : WeilTestFn` and support cutoff `1 ≤ N` with `EF.weilTest f.1 f.1 (±log N) = 0`,
`(247 / 300) * (∫ u, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`. -/
theorem two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
    (f : WeilTestFn) {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (247 / 300) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) + secantNumeratorCellDefect f.1 N ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have heq :=
    rightCellQuadratureDefect_weilContinuumLogProfile_eq_origin_add_combinedCounterterm_add_secantNumerator
      f hN1 hN0 hN
  have habs :=
    (abs_le.mp (abs_primeBlindCounterterm_secantCombinedSecularWeight_le_fourStage f hN1 hN)).1
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsurplus := mul_le_mul_of_nonneg_right
    two_forty_seven_three_hundredths_le_fourStage_surplus hnorm_nonneg
  linarith

/-- **Universal Tangent Upper Bound `Real.sqrt (S * (S + 2 * L)) ≤ (1405 / 1404) * S + (26 / 27) * L`**:
evaluating the variational envelope at `b = 13 / 27` (`((1405 / 1404) S + (26 / 27) L)² - S(S + 2L) = ((53 / 1404) S - (26 / 27) L)² ≥ 0`) gives a linear upper bound that is exact at `S / L = 1352 / 53 ≈ 25.5094`. -/
theorem sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths
    (f : WeilTestFn) :
    Real.sqrt
        (spectralSecondMoment f.1 *
          (spectralSecondMoment f.1 + 2 * ∫ u : ℝ, ‖f.1 u‖ ^ 2)) ≤
      (1405 / 1404) * spectralSecondMoment f.1 + (26 / 27) * ∫ u : ℝ, ‖f.1 u‖ ^ 2 := by
  let S := spectralSecondMoment f.1
  let L := ∫ u : ℝ, ‖f.1 u‖ ^ 2
  have hS_nonneg : 0 ≤ S := spectralSecondMoment_nonneg f.1
  have hL_nonneg : 0 ≤ L := integral_nonneg fun _ => sq_nonneg _
  rw [← Real.sqrt_sq (by positivity : 0 ≤ (1405 / 1404) * S + (26 / 27) * L)]
  refine Real.sqrt_le_sqrt ?_
  have hsq : 0 ≤ ((53 / 1404) * S - (26 / 27) * L) ^ 2 := sq_nonneg _
  linarith

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity up to Critical Ratio `117 / 5 = 23.4`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_seventeen_fifths
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (117 / 5) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths f
  linarith

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity on the Nonnegative Log-Value Cone up to
Critical Ratio `124 / 5 = 24.8`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_twenty_four_fifths_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ (124 / 5) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths f
  linarith

/-- **Pure `rightCellQuadratureDefect ≥ 0` Coercivity on the Prime-Blind Cone (`logVector f = 0`) up to
Critical Ratio `124 / 5 = 24.8`**: -/
theorem rightCellQuadratureDefect_nonneg_of_spectralSecondMoment_le_one_twenty_four_fifths_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (124 / 5) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    0 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind hN1 hN0 hN
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity up to Critical Ratio `51 / 2 = 25.5`**:
whenever `spectralSecondMoment f.1 ≤ (51 / 2) * ∫ ‖f.1‖²`, we have
`(1 / 1200) * ∫ ‖f.1‖² ≤ bochnerResolventEnergy (EF.weilTest f.1 f.1) + rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`! -/
theorem one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_one_halves
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ (51 / 2) * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1200) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (1 / 26)
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      f hN1 hN0 hN
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Nonnegative Log-Value Cone up to `27`**: -/
theorem one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logValue_nonneg
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hpos : ∀ n ∈ Finset.Icc 2 N, 0 ≤ logValue f.1 n)
    (hsec : spectralSecondMoment f.1 ≤ 27 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1200) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (2 / 55)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      f hN1 hN0 hN hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths f
  linarith

/-- **Resolvent-Enhanced Quadrature Coercivity on the Prime-Blind Cone (`logVector f = 0`) up to `27`**: -/
theorem one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0)
    (hsec : spectralSecondMoment f.1 ≤ 27 * ∫ u : ℝ, ‖f.1 u‖ ^ 2) :
    (1 / 1200) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      bochnerResolventEnergy (EF.weilTest f.1 f.1) +
        rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have hL : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hres := four_mul_l2_sub_sq_mul_two_spectralSecondMoment_add_l2_le_bochnerResolventEnergy
    f hint2 (2 / 55)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
      f hblind hN1 hN0 hN
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      f hint2 N
  have hamgm := sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths f
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane up to `(51 / 2) * ∫ ‖F‖² = 25.5 * ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_fifty_one_halves_of_cosh_zero
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
      (51 / 2) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 2501
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (2501 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (2500 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    m hf hfc hcosh hN1 hθlog hN hdiff
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    two_forty_seven_three_hundredths_l2_add_secantNumerator_le_rightCellQuadratureDefect
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn))
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm :=
    sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths
      (realWeilTestFn f hf hfc)
  have hcomb :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_one_halves
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hsec_bound
  have hθ_comb :
      (2500 : ℝ) * ((1 / 1200) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Nonnegative Log-Value Cone up to `27 * ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_twenty_seven_of_cosh_zero_of_logValue_nonneg
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
      27 * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  have hL_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  let θ := max (max 1 (Real.log (N : ℝ))) 2601
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ_large : (2601 : ℝ) ≤ θ := le_max_right _ _
  have hθ_sub : (2600 : ℝ) ≤ θ - 1 := by linarith
  have hbase := one_hundredth_l2_add_theta_slope_quadrature_le_markovEnergy_of_cosh_zero
    0 hf hfc hcosh hN1 hθlog hN (fun n hn => by simpa [iteratedForwardDiff] using hpos n hn)
  have hatom := atomPairRe_weilTest_le_two_mul_integral_norm_sq (realWeilTestFn f hf hfc)
  have h1 :=
    twelve_sixty_one_fourteen_fortieths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos
  have h2 :=
    neg_seven_four_eightieths_second_sub_seventy_one_geom_le_secantNumeratorCellDefect
      (realWeilTestFn f hf hfc) hint2 N
  have hamgm :=
    sqrt_spectralSecondMoment_mul_add_two_l2_le_add_thirteen_twenty_sevenths
      (realWeilTestFn f hf hfc)
  have hcomb :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hsec_bound
  have hθ_comb :
      (2600 : ℝ) * ((1 / 1200) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2)) ≤
        (θ - 1) *
          (bochnerResolventEnergy
            (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) +
            rightCellQuadratureDefect (weilContinuumLogProfile (realWeilTestFn f hf hfc).1) N) :=
    mul_le_mul hθ_sub hcomb (by positivity) (by linarith)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `51 / 2 = 25.5` Spectral Poincaré / Uncertainty Gap Law on the Primitive Hyperplane**: -/
theorem fifty_one_halves_l2_lt_spectralSecondMoment_of_cosh_zero_of_unitStep_nonneg
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hunit : 0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc))
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    (51 / 2) * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_fifty_one_halves
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `27` Spectral Poincaré / Uncertainty Gap Law on the Nonnegative Log-Value Cone**: -/
theorem twenty_seven_l2_lt_spectralSecondMoment_of_cosh_zero_of_logValue_nonneg
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
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    27 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logValue_nonneg
      (realWeilTestFn f hf hfc) hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hpos hle
  have hunit_nonneg :
      0 ≤ primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) := by
    rw [primeBlindCounterterm_eq_sum_Icc unitStepCountertermWeight (realWeilTestFn f hf hfc)
      (fun n hn => hN n (by exact_mod_cast hn))]
    refine Finset.sum_nonneg fun n hn => ?_
    have hn_mem := Finset.mem_Icc.mp hn
    unfold unitStepCountertermWeight
    rw [if_pos hn_mem.1]
    exact mul_nonneg zero_le_one (hpos n hn)
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

/-- **The `27` Spectral Poincaré / Uncertainty Gap Law on the Prime-Blind Cone**: -/
theorem twenty_seven_l2_lt_spectralSecondMoment_of_cosh_zero_of_logVector_eq_zero
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hblind : logVector (realWeilTestFn f hf hfc) = 0)
    (hpos_l2 : 0 < ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    27 * (∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) <
      spectralSecondMoment (realWeilTestFn f hf hfc).1 := by
  by_contra! hle
  have hcons :=
    unitStep_add_rightCellQuadratureDefect_add_bochnerResolventEnergy_add_sinh_sq_eq_zero_of_cosh_zero
      hf hfc hcosh hN1 hN
  have hcoerc :=
    one_twelve_hundredth_l2_le_bochnerResolventEnergy_add_rightCellQuadratureDefect_of_spectralSecondMoment_le_twenty_seven_of_logVector_eq_zero
      (realWeilTestFn f hf hfc) hblind hint2 hN1 hN0 (fun n hn => hN n (by exact_mod_cast hn)) hle
  have hunit_zero :
      primeBlindCounterterm unitStepCountertermWeight (realWeilTestFn f hf hfc) = 0 := by
    unfold primeBlindCounterterm
    rw [hblind, map_zero]
  have hsinh_nonneg : 0 ≤ 2 * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
