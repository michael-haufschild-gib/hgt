import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact certificates for the first theta atom Gaussian score envelope

Finite exponential Taylor bounds, rational pi bounds and an exact Bernstein
identity control both sides of the split at x = 1/3. The polynomial surplus
retains the exact factor 110843/111104 used by the actual-source envelope.
-/

open scoped BigOperators
namespace RHTower
noncomputable section

private theorem exp_taylor_nine_upper {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 17 / 6) :
    Real.exp u ≤ (∑ k ∈ Finset.range 9, u ^ k / (k.factorial : ℝ)) +
      2 * u ^ 9 / (9 : ℕ).factorial := by
  have hc := Complex.exp_bound' (x := (u : ℂ)) (n := 9) (by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]
    norm_num
    linarith)
  have hr : |Real.exp u - ∑ k ∈ Finset.range 9, u ^ k / (k.factorial : ℝ)| ≤
      |u| ^ 9 / (9 : ℕ).factorial * 2 := by
    convert hc using 1 <;> norm_cast
  rw [abs_of_nonneg hu] at hr
  have h := (abs_le.mp hr).2
  linarith

/-- Exact quadratic exponential upper bound on the required compact interval. -/
theorem thetaGaussianScore_exp_le_quadratic {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 17 / 6) :
    Real.exp u ≤ 1 + u + (7 / 4 : ℝ) * u ^ 2 := by
  have he := exp_taylor_nine_upper hu hu1
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hp (j : ℕ) : u ^ (j + 2) ≤ u ^ 2 * (17 / 6 : ℝ) ^ j := by
    rw [pow_add, mul_comm (u ^ j)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hu hu1 j) (sq_nonneg u)
  have h1 := hp 1
  have h2 := hp 2
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  have h7 := hp 7
  norm_num at h1 h2 h3 h4 h5 h6 h7
  nlinarith [sq_nonneg u]

/-- Polynomial upper bound for the compact Gaussian compensation exponent. -/
theorem thetaGaussianScore_exp_small_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) :
    Real.exp (18 * x ^ 2 + (5 / 2 : ℝ) * x) ≤ 1 + 3 * x + 177 * x ^ 2 := by
  have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
  have hu : 0 ≤ 18 * x ^ 2 + (5 / 2 : ℝ) * x := by positivity
  have hu1 : 18 * x ^ 2 + (5 / 2 : ℝ) * x ≤ 17 / 6 := by nlinarith
  have he := thetaGaussianScore_exp_le_quadratic hu hu1
  have h3 : x ^ 3 ≤ x ^ 2 / 3 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 / 3 - x by linarith)]
  have h4 : x ^ 4 ≤ x ^ 2 / 9 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1 / 9 - x ^ 2 by linarith)]
  nlinarith

/-- The Gaussian exponent is dominated by the literal first-atom exponential coordinate. -/
theorem thetaGaussianScore_exponent_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Real.pi * Real.exp (2 * x) - 18 * x ^ 2 - (9 / 2 : ℝ) * x := by
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_d2]
  by_cases hx1 : x ≤ 3 / 4
  · have ht := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * x by positivity) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht
    have he : (157 / 50 : ℝ) *
        (1 + 2 * x + 2 * x ^ 2 + (4 / 3 : ℝ) * x ^ 3 + (2 / 3 : ℝ) * x ^ 4) ≤
        Real.pi * Real.exp (2 * x) := by
      calc
        _ ≤ (157 / 50 : ℝ) * Real.exp (2 * x) := by nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    have hy : 0 ≤ (4 / 3 : ℝ) * x := by positivity
    have hy1 : 0 ≤ 1 - (4 / 3 : ℝ) * x := by linarith
    have hbern : (157 / 50 : ℝ) *
        (1 + 2 * x + 2 * x ^ 2 + (4 / 3 : ℝ) * x ^ 3 + (2 / 3 : ℝ) * x ^ 4) -
        18 * x ^ 2 - (9 / 2 : ℝ) * x =
        (157 / 50 : ℝ) * (1 - (4 / 3 : ℝ) * x) ^ 4 +
        4 * (2779 / 800 : ℝ) * ((4 / 3 : ℝ) * x) * (1 - (4 / 3 : ℝ) * x) ^ 3 +
        6 * (2167 / 800 : ℝ) * ((4 / 3 : ℝ) * x) ^ 2 * (1 - (4 / 3 : ℝ) * x) ^ 2 +
        4 * (4117 / 3200 : ℝ) * ((4 / 3 : ℝ) * x) ^ 3 * (1 - (4 / 3 : ℝ) * x) +
        (1991 / 6400 : ℝ) * ((4 / 3 : ℝ) * x) ^ 4 := by ring
    have hn : 0 ≤ (157 / 50 : ℝ) *
        (1 + 2 * x + 2 * x ^ 2 + (4 / 3 : ℝ) * x ^ 3 + (2 / 3 : ℝ) * x ^ 4) -
        18 * x ^ 2 - (9 / 2 : ℝ) * x := by
      rw [hbern]
      positivity
    linarith
  · have hh : 0 ≤ x - 3 / 4 := by linarith
    have ht0 := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) 6
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht0
    have ht1 := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * (x - 3 / 4) by positivity) 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at ht1
    have he : (157 / 50 : ℝ) * (5711 / 1280 : ℝ) *
        (1 + 2 * (x - 3 / 4) + 2 * (x - 3 / 4) ^ 2) ≤
        Real.pi * Real.exp (2 * x) := by
      have hn : 0 ≤ 1 + 2 * (x - 3 / 4) + 2 * (x - 3 / 4) ^ 2 := by positivity
      have h0 : (5711 / 1280 : ℝ) *
          (1 + 2 * (x - 3 / 4) + 2 * (x - 3 / 4) ^ 2) ≤
          Real.exp (3 / 2) * Real.exp (2 * (x - 3 / 4)) :=
        mul_le_mul (by linarith) (by nlinarith) hn (Real.exp_pos _).le
      have hid : Real.exp (3 / 2) * Real.exp (2 * (x - 3 / 4)) =
          Real.exp (2 * x) := by rw [← Real.exp_add]; congr 1; ring
      rw [hid] at h0
      calc
        _ ≤ (157 / 50 : ℝ) * Real.exp (2 * x) :=
          by simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left h0 (by norm_num : (0 : ℝ) ≤ 157 / 50)
        _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    have hq : 0 ≤ (x - 3 / 4 - 7 / 36) ^ 2 := sq_nonneg _
    nlinarith

/-- Rational square-root certificate used by both scalar comparisons. -/
theorem thetaGaussianScore_sqrt_two_pi_le :
    Real.sqrt (2 * Real.pi) ≤ (251 / 100 : ℝ) := by
  have hp : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hs := Real.sq_sqrt (show 0 ≤ 2 * Real.pi by positivity)
  have hn := Real.sqrt_nonneg (2 * Real.pi)
  nlinarith

/-- Exact normalization bound for the compact first-atom decay factor. -/
theorem thetaGaussianScore_small_scalar_le :
    4 * Real.pi * (Real.pi - 3 / 2) * Real.exp (-Real.pi) ≤
      (15 / 16 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) := by
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hpi0 : 0 ≤ Real.pi - 3 / 2 := by linarith [Real.pi_gt_d2]
  have hp := mul_le_mul hpi (show Real.pi - 3 / 2 ≤ (23 / 14 : ℝ) by linarith)
    hpi0 (by norm_num : (0 : ℝ) ≤ 22 / 7)
  have hs := thetaGaussianScore_sqrt_two_pi_le
  have hs0 := Real.sqrt_nonneg (2 * Real.pi)
  have hn : 4 * Real.pi * (Real.pi - 3 / 2) * Real.sqrt (2 * Real.pi) ≤
      4 * (22 / 7 : ℝ) * (23 / 14 : ℝ) * (251 / 100 : ℝ) := by
    have h := mul_le_mul hp hs hs0 (by norm_num : (0 : ℝ) ≤ (22 / 7) * (23 / 14))
    nlinarith
  have ht := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 157 / 50) 10
  norm_num [Finset.sum_range_succ, Nat.factorial] at ht
  have he : (23 : ℝ) ≤ Real.exp Real.pi := by
    have hem := Real.exp_le_exp.mpr Real.pi_gt_d2.le
    linarith
  have hc : 4 * Real.pi * (Real.pi - 3 / 2) * Real.sqrt (2 * Real.pi) ≤
      (15 / 16 : ℝ) * (243 / 100) * Real.exp Real.pi := by nlinarith
  have hspos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  rw [Real.exp_neg]
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 100 * Real.sqrt (2 * Real.pi))).2
  apply (mul_le_mul_iff_left₀ (Real.exp_pos Real.pi)).mp
  field_simp [Real.exp_ne_zero] at *
  nlinarith

/-- The compact polynomial comparison retains a uniform strict rational surplus. -/
theorem thetaGaussianScore_small_polynomial_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1 / 3) :
    (15 / 16 : ℝ) * (1 + 3 * x + 177 * x ^ 2) * (1 - x) ^ 2 ≤
      (110843 / 111104 : ℝ) * (1 + 177 * x ^ 2) := by
  have hi : (16 / 15 : ℝ) * (1 + 177 * x ^ 2) -
      (1 + 3 * x + 177 * x ^ 2) * (1 - x) ^ 2 =
      (84 / 5 : ℝ) * (x - 5 / 168) ^ 2 + 29 / 560 + x ^ 3 * (351 - 177 * x) := by ring
  have hn := mul_nonneg (pow_nonneg hx 3) (show 0 ≤ 351 - 177 * x by linarith)
  have hs := sq_nonneg (x - 5 / 168)
  have hb : 1 + 177 * x ^ 2 ≤ (62 / 3 : ℝ) := by nlinarith
  nlinarith

/-- Sharp elementary polynomial comparison on the tail side of the split. -/
theorem thetaGaussianScore_large_polynomial_le {x : ℝ} (hx : (1 / 3 : ℝ) ≤ x) :
    (x - 1) ^ 2 ≤ (2 / 93 : ℝ) * (1 + 177 * x ^ 2) := by
  nlinarith [mul_nonneg (show 0 ≤ 3 * x - 1 by linarith)
    (show 0 ≤ 87 * x + 91 by linarith)]

/-- The tail scalar comparison fits under the same exact surplus factor. -/
theorem thetaGaussianScore_large_scalar_le :
    4 * Real.pi ^ 2 * (2 / 93 : ℝ) ≤
      (110843 / 111104 : ℝ) * (243 / (100 * Real.sqrt (2 * Real.pi))) := by
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hp2 : Real.pi ^ 2 ≤ (22 / 7 : ℝ) ^ 2 := by nlinarith [Real.pi_pos]
  have hs := thetaGaussianScore_sqrt_two_pi_le
  have hs0 := Real.sqrt_nonneg (2 * Real.pi)
  have h := mul_le_mul hp2 hs hs0 (by positivity : (0 : ℝ) ≤ (22 / 7) ^ 2)
  have hspos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  rw [← mul_div_assoc (110843 / 111104 : ℝ) 243 (100 * Real.sqrt (2 * Real.pi))]
  apply (le_div_iff₀ (by positivity : 0 < 100 * Real.sqrt (2 * Real.pi))).2
  nlinarith

/-- First-atom exponential decay comparison beyond the initial Morse coordinate. -/
theorem thetaGaussianScore_firstAtomDecay_le {y : ℝ} (hy : Real.pi ≤ y) :
    (y - 3 / 2) * Real.exp (-y) ≤
      (Real.pi - 3 / 2) * Real.exp (-Real.pi) := by
  have hz : 0 ≤ y - Real.pi := by linarith
  have hp : 1 ≤ Real.pi - 3 / 2 := by linarith [Real.pi_gt_d2]
  have he := Real.add_one_le_exp (y - Real.pi)
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ Real.pi - 3 / 2 by linarith)
  have hlin : y - 3 / 2 ≤ (Real.pi - 3 / 2) * Real.exp (y - Real.pi) := by
    nlinarith [mul_nonneg hz (show 0 ≤ Real.pi - 3 / 2 - 1 by linarith)]
  have hm := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-y)).le
  have hid : Real.exp (y - Real.pi) * Real.exp (-y) = Real.exp (-Real.pi) := by
    rw [← Real.exp_add]; congr 1; ring
  simpa only [mul_assoc, hid] using hm

end
end RHTower
