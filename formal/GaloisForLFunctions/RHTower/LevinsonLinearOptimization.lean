import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Exact scalar optimization for Levinson's linear mollifier

This file evaluates Young's mollified-moment constant for
`P(x) = x`, `Q(x) = 1 - x`, `R = 13/10`, and `theta = 1/2`.  Exact rational
Taylor bounds for the real exponential then give the strict Levinson margin
`1 - log(c) / R > 1/3`.

The analytic mollified-moment asymptotic is deliberately not assumed here:
this module is the unconditional scalar certificate consumed after that
asymptotic has been proved.
-/

noncomputable section

namespace RHTower

open MeasureTheory

/-- Derivative in Young's linear `P,Q` mollified-moment integrand at the
classical parameters. -/
def levinsonLinearOptimizationDerivative (u v : ℝ) : ℝ :=
  (1 - v) * (1 + (13 / 20) * u) - (1 / 2) * u

/-- Young's mollified-moment constant for `P(x)=x`, `Q(x)=1-x`, `R=13/10`,
`theta=1/2`. -/
def levinsonLinearOptimizationConstant : ℝ :=
  1 + 2 * ∫ v in (0 : ℝ)..1,
    Real.exp ((13 / 5) * v) *
      (∫ u in (0 : ℝ)..1, levinsonLinearOptimizationDerivative u v ^ (2 : ℕ))

private def levinsonLinearOptimizationPrimitive (v : ℝ) : ℝ :=
  Real.exp ((13 / 5) * v) *
    ((565661 / 527280 : ℝ) + (-8273 / 5070 : ℝ) * v +
      (2149 / 3120 : ℝ) * v ^ (2 : ℕ))

lemma integral_levinsonLinearOptimizationDerivative_sq (v : ℝ) :
    (∫ u in (0 : ℝ)..1, levinsonLinearOptimizationDerivative u v ^ (2 : ℕ)) =
      (1389 - 3438 * v + 2149 * v ^ (2 : ℕ)) / 1200 := by
  let a : ℝ := 1 - v
  let b : ℝ := (3 - 13 * v) / 20
  let F : ℝ → ℝ := fun u =>
    a ^ (2 : ℕ) * u + (a * b) * u ^ (2 : ℕ) + (b ^ (2 : ℕ) / 3) * u ^ (3 : ℕ)
  have hderiv : ∀ u : ℝ,
      HasDerivAt F (levinsonLinearOptimizationDerivative u v ^ (2 : ℕ)) u := by
    intro u
    have hraw := (((hasDerivAt_id u).const_mul (a ^ (2 : ℕ))).add
        (((hasDerivAt_id u).pow 2).const_mul (a * b))).add
          (((hasDerivAt_id u).pow 3).const_mul (b ^ (2 : ℕ) / 3))
    change HasDerivAt F _ u at hraw
    exact hraw.congr_deriv (by
      dsimp only [a, b, levinsonLinearOptimizationDerivative] at *
      simp only [id_eq] at *
      ring)
  have hint : IntervalIntegrable
      (fun u : ℝ => levinsonLinearOptimizationDerivative u v ^ (2 : ℕ)) volume 0 1 :=
    (show Continuous (fun u : ℝ =>
      levinsonLinearOptimizationDerivative u v ^ (2 : ℕ)) by
        unfold levinsonLinearOptimizationDerivative
        fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hderiv u) hint]
  dsimp only [F, a, b]
  norm_num
  ring_nf

lemma hasDerivAt_levinsonLinearOptimizationPrimitive (v : ℝ) :
    HasDerivAt levinsonLinearOptimizationPrimitive
      (Real.exp ((13 / 5) * v) *
        (1389 - 3438 * v + 2149 * v ^ (2 : ℕ)) / 1200) v := by
  have hraw := (((hasDerivAt_id v).const_mul (13 / 5 : ℝ)).exp).mul
    ((((hasDerivAt_const v (565661 / 527280 : ℝ)).add
      ((hasDerivAt_id v).const_mul (-8273 / 5070 : ℝ))).add
        (((hasDerivAt_id v).pow 2).const_mul (2149 / 3120 : ℝ))))
  change HasDerivAt
    (fun x : ℝ => Real.exp ((13 / 5) * x) *
      ((565661 / 527280 : ℝ) + (-8273 / 5070 : ℝ) * x +
        (2149 / 3120 : ℝ) * x ^ (2 : ℕ))) _ v
  exact hraw.congr_deriv (by norm_num; ring)

lemma integral_levinsonLinearOptimization_exp_polynomial :
    (∫ v in (0 : ℝ)..1,
        Real.exp ((13 / 5) * v) *
          (1389 - 3438 * v + 2149 * v ^ (2 : ℕ)) / 1200) =
      Real.exp (13 / 5) *
          ((565661 / 527280 : ℝ) - 8273 / 5070 + 2149 / 3120) -
        (565661 / 527280 : ℝ) := by
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.exp ((13 / 5) * v) *
        (1389 - 3438 * v + 2149 * v ^ (2 : ℕ)) / 1200) volume 0 1 :=
    (show Continuous (fun v : ℝ => Real.exp ((13 / 5) * v) *
      (1389 - 3438 * v + 2149 * v ^ (2 : ℕ)) / 1200) by
        fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_levinsonLinearOptimizationPrimitive v) hint]
  dsimp only [levinsonLinearOptimizationPrimitive]
  norm_num

theorem levinsonLinearOptimizationConstant_eq :
    levinsonLinearOptimizationConstant =
      1 + 2 * (Real.exp (13 / 5) *
          ((565661 / 527280 : ℝ) - 8273 / 5070 + 2149 / 3120) -
        (565661 / 527280 : ℝ)) := by
  rw [levinsonLinearOptimizationConstant]
  simp_rw [integral_levinsonLinearOptimizationDerivative_sq]
  convert congrArg (fun z : ℝ => 1 + 2 * z)
    integral_levinsonLinearOptimization_exp_polynomial using 1
  ring_nf

lemma exp_thirteen_twentieth_lt : Real.exp (13 / 20 : ℝ) < 479 / 250 := by
  have hb := Real.exp_bound (x := (13 / 20 : ℝ)) (by norm_num)
    (n := 10) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb ⊢
  have h := (abs_le.mp hb).2
  linarith

lemma exp_thirteen_fifths_lt : Real.exp (13 / 5 : ℝ) < 27 / 2 := by
  have hroot := exp_thirteen_twentieth_lt
  have hpow : Real.exp (13 / 5 : ℝ) = Real.exp (13 / 20 : ℝ) ^ (4 : ℕ) := by
    rw [show (13 / 5 : ℝ) = (4 : ℕ) * (13 / 20 : ℝ) by norm_num,
      Real.exp_nat_mul]
  rw [hpow]
  nlinarith [pow_le_pow_left₀ (Real.exp_pos _).le hroot.le 4]

lemma nineteen_eighths_lt_exp_thirteen_fifteenths :
    (19 / 8 : ℝ) < Real.exp (13 / 15 : ℝ) := by
  have hb := Real.exp_bound (x := (13 / 15 : ℝ)) (by norm_num)
    (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hb ⊢
  have h := (abs_le.mp hb).1
  linarith

theorem levinsonLinearOptimizationConstant_lt_nineteen_eighths :
    levinsonLinearOptimizationConstant < 19 / 8 := by
  rw [levinsonLinearOptimizationConstant_eq]
  have hexp := exp_thirteen_fifths_lt
  have hcoeff : (0 : ℝ) <
      (565661 / 527280 : ℝ) - 8273 / 5070 + 2149 / 3120 := by
    norm_num
  nlinarith

theorem one_sub_log_levinsonLinearOptimizationConstant_div_gt_one_third :
    1 - Real.log levinsonLinearOptimizationConstant / (13 / 10) > 1 / 3 := by
  have hnonnegInner : ∀ v : ℝ,
      0 ≤ ∫ u in (0 : ℝ)..1,
        levinsonLinearOptimizationDerivative u v ^ (2 : ℕ) := by
    intro v
    exact intervalIntegral.integral_nonneg (by norm_num) fun u hu => sq_nonneg _
  have houter : 0 ≤ ∫ v in (0 : ℝ)..1,
      Real.exp ((13 / 5) * v) *
        (∫ u in (0 : ℝ)..1,
          levinsonLinearOptimizationDerivative u v ^ (2 : ℕ)) := by
    exact intervalIntegral.integral_nonneg (by norm_num) fun v hv =>
      mul_nonneg (Real.exp_pos _).le (hnonnegInner v)
  have hcpos : 0 < levinsonLinearOptimizationConstant := by
    rw [levinsonLinearOptimizationConstant]
    linarith
  have hcexp : levinsonLinearOptimizationConstant < Real.exp (13 / 15) :=
    levinsonLinearOptimizationConstant_lt_nineteen_eighths.trans
      nineteen_eighths_lt_exp_thirteen_fifteenths
  have hlog : Real.log levinsonLinearOptimizationConstant < 13 / 15 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hcpos]
    exact hcexp
  norm_num at hlog ⊢
  linarith

end RHTower
