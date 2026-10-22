import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Leading exponential term in the three-atom fourth logarithmic numerator

For the reduced three-atom theta sum
`G(q) = (2q - 3) + (32q - 12) exp(-3q) + (162q - 27) exp(-8q)`,
the numerator of `-q + (q d/dq)^4 log G` has leading terms
`-A₀(q) + A₃(q) exp(-3q)`. Cancelling their common factor `q` and
translating by three gives the positive polynomials below.

Their exact derivative identity proves that `A₃ exp(-3q) / A₀`
is strictly decreasing for `q ≥ 3` and is less than `63/100` for `q ≥ π`.
-/

open Polynomial Set

namespace RHTower.ThetaCuspThreeAtomFourth

/-- The polynomial `A₀(q)/q` in the coordinate `q - 3`. -/
noncomputable def basePolynomial : Polynomial ℝ :=
  16 * X ^ 4 + 96 * X ^ 3 + 240 * X ^ 2 + 504 * X + 783

/-- The polynomial `A₃(q)/(4q)` in the coordinate `q - 3`. -/
noncomputable def leadingPolynomial : Polynomial ℝ :=
  5184 * X ^ 7 + 73224 * X ^ 6 + 444348 * X ^ 5 + 1513442 * X ^ 4 +
    3159561 * X ^ 3 + 4106253 * X ^ 2 + 3139920 * X + 1115559

/-- Positive numerator certifying decay of the exponentially weighted ratio. -/
noncomputable def decayPolynomial : Polynomial ℝ :=
  82944 * X ^ 11 + 1586304 * X ^ 10 + 13938624 * X ^ 9 + 75586016 * X ^ 8 +
    286355472 * X ^ 7 + 804327768 * X ^ 6 + 1701811572 * X ^ 5 +
    2668450842 * X ^ 4 + 2987269767 * X ^ 3 + 2259950436 * X ^ 2 +
    1055824470 * X + 241377489

theorem basePolynomial_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < basePolynomial.eval y := by
  simp only [basePolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  positivity

theorem leadingPolynomial_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < leadingPolynomial.eval y := by
  simp only [leadingPolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  positivity

theorem decayPolynomial_pos {y : ℝ} (hy : 0 ≤ y) :
    0 < decayPolynomial.eval y := by
  simp only [decayPolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  positivity

theorem basePolynomial_unshift (q : ℝ) :
    basePolynomial.eval (q - 3) = 16 * q ^ 4 - 96 * q ^ 3 +
      240 * q ^ 2 - 72 * q + 135 := by
  simp only [basePolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  ring

theorem leadingPolynomial_unshift (q : ℝ) :
    leadingPolynomial.eval (q - 3) = 5184 * q ^ 7 - 35640 * q ^ 6 +
      106092 * q ^ 5 - 165418 * q ^ 4 + 145257 * q ^ 3 - 64680 * q ^ 2 +
      13113 * q - 945 := by
  simp only [leadingPolynomial, eval_add, eval_mul, eval_pow, eval_ofNat, eval_X]
  ring

/-- Exact logarithmic derivative certificate for the dominant positive term. -/
theorem leadingPolynomial_decay_identity :
    leadingPolynomial.derivative * basePolynomial -
      leadingPolynomial * basePolynomial.derivative -
      3 * leadingPolynomial * basePolynomial = -3 * decayPolynomial := by
  norm_num [leadingPolynomial, basePolynomial, decayPolynomial, derivative_mul,
    C_eq_natCast]
  simp only [C_ofNat]
  ring

/-- The dominant positive term divided by the negative constant term. -/
noncomputable def leadingRatio (q : ℝ) : ℝ :=
  4 * leadingPolynomial.eval (q - 3) * Real.exp (-3 * q) /
    basePolynomial.eval (q - 3)

theorem hasDerivAt_leadingRatio {q : ℝ} (hq : 3 ≤ q) :
    HasDerivAt leadingRatio
      (-12 * decayPolynomial.eval (q - 3) * Real.exp (-3 * q) /
        (basePolynomial.eval (q - 3)) ^ 2) q := by
  have hbase := (basePolynomial.hasDerivAt (q - 3)).comp q
    ((hasDerivAt_id q).sub_const 3)
  have hlead := (leadingPolynomial.hasDerivAt (q - 3)).comp q
    ((hasDerivAt_id q).sub_const 3)
  have hexp := ((hasDerivAt_id q).const_mul (-3)).exp
  have h := ((hlead.const_mul 4).mul hexp).div hbase
    (ne_of_gt (basePolynomial_pos (sub_nonneg.mpr hq)))
  have hid := congrArg (Polynomial.eval (q - 3)) leadingPolynomial_decay_identity
  simp only [eval_sub, eval_mul, eval_neg, eval_ofNat] at hid
  convert! h using 1
  dsimp
  simp only [mul_one]
  congr 1
  linear_combination -4 * Real.exp (-3 * q) * hid

theorem leadingRatio_strictAntiOn : StrictAntiOn leadingRatio (Ici 3) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici 3)
  · intro q hq
    exact (hasDerivAt_leadingRatio hq).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3 ≤ q := le_of_lt (by simpa only [interior_Ici, mem_Ioi] using hq)
    rw [(hasDerivAt_leadingRatio hq').deriv]
    have hdecay := decayPolynomial_pos (sub_nonneg.mpr hq')
    have hbase := basePolynomial_pos (sub_nonneg.mpr hq')
    apply div_neg_of_neg_of_pos _ (sq_pos_of_pos hbase)
    exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hdecay)
      (Real.exp_pos _)

theorem twentyThree_lt_exp_lower_pi : (23 : ℝ) < Real.exp (157 / 50) := by
  have he : (1359 / 500 : ℝ) < Real.exp 1 := by
    linarith [Real.exp_one_gt_d9]
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 50) 4
  norm_num [Finset.sum_range_succ] at hs
  have hc : (1359 / 500 : ℝ) ^ 3 < Real.exp 1 ^ 3 := by gcongr
  have hexact : Real.exp (157 / 50) = Real.exp 1 ^ 3 * Real.exp (7 / 50) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
  rw [hexact]
  calc
    (23 : ℝ) < (1359 / 500) ^ 3 * (862693 / 750000) := by norm_num
    _ ≤ Real.exp 1 ^ 3 * Real.exp (7 / 50) := by gcongr

theorem leadingRatio_lower_pi_lt : leadingRatio (157 / 50) < 63 / 100 := by
  have he : Real.exp (-(3 * (157 / 50 : ℝ))) < 1 / (23 : ℝ) ^ 3 := by
    rw [Real.exp_neg, one_div]
    apply (inv_lt_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 23 ^ 3)).mpr
    rw [show Real.exp (3 * (157 / 50 : ℝ)) = Real.exp (157 / 50) ^ 3 from
      Real.exp_nat_mul (157 / 50) 3]
    gcongr
    exact twentyThree_lt_exp_lower_pi
  have hb : 0 < basePolynomial.eval ((157 / 50 : ℝ) - 3) :=
    basePolynomial_pos (by norm_num)
  have hl : 0 < leadingPolynomial.eval ((157 / 50 : ℝ) - 3) :=
    leadingPolynomial_pos (by norm_num)
  calc
    leadingRatio (157 / 50) <
        4 * leadingPolynomial.eval ((157 / 50 : ℝ) - 3) * (1 / (23 : ℝ) ^ 3) /
          basePolynomial.eval ((157 / 50 : ℝ) - 3) := by
      unfold leadingRatio
      apply (div_lt_div_iff_of_pos_right hb).mpr
      apply mul_lt_mul_of_pos_left _ (by positivity)
      simpa only [neg_mul] using he
    _ < 63 / 100 := by norm_num [leadingPolynomial, basePolynomial]

/-- Uniform bound throughout the theta half-line. -/
theorem leadingRatio_lt {q : ℝ} (hq : Real.pi ≤ q) :
    leadingRatio q < 63 / 100 := by
  have hpi : (157 / 50 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  exact (leadingRatio_strictAntiOn (by norm_num) (by change 3 ≤ q; linarith)
    (hpi.trans_le hq)).trans leadingRatio_lower_pi_lt

end RHTower.ThetaCuspThreeAtomFourth
