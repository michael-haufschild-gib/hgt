import GaloisForLFunctions.RHTower.LevinsonLinearOptimizationInterior

/-!
# An explicit rational Levinson exponent

The exponent `49/100` lies strictly below the square-root barrier while retaining the strict
`> 1/3` scalar margin in Young's linear mollifier optimization.  Unlike the abstract interior
parameter obtained from continuity, this rational value is compatible with exact natural-power
scales `M = N^49`, `L = N^100`.
-/

noncomputable section

namespace RHTower

open MeasureTheory

/-- Explicit rational mollifier exponent used by the integer-power analytic scale. -/
def levinsonLinearFortyNineTheta : ℝ := 49 / 100

theorem levinsonLinearFortyNineTheta_pos :
    0 < levinsonLinearFortyNineTheta := by
  norm_num [levinsonLinearFortyNineTheta]

theorem levinsonLinearFortyNineTheta_lt_half :
    levinsonLinearFortyNineTheta < 1 / 2 := by
  norm_num [levinsonLinearFortyNineTheta]

private def levinsonLinearFortyNinePolynomial (v : ℝ) : ℝ :=
  (3462609 - 8539278 * v + 5316769 * v ^ 2) / 3000000

private lemma integral_levinsonLinearOptimizationDerivativeAt_fortyNine_sq (v : ℝ) :
    (∫ u in (0 : ℝ)..1,
      levinsonLinearOptimizationDerivativeAt (49 / 100) u v ^ 2) =
      levinsonLinearFortyNinePolynomial v := by
  let A : ℝ := 1 - v
  let B : ℝ := (49 / 100) * ((13 / 10) * (1 - v) - 1)
  let F : ℝ → ℝ := fun u =>
    A ^ 2 * u + (A * B) * u ^ 2 + (B ^ 2 / 3) * u ^ 3
  have hderiv : ∀ u : ℝ,
      HasDerivAt F
        (levinsonLinearOptimizationDerivativeAt (49 / 100) u v ^ 2) u := by
    intro u
    have hraw := (((hasDerivAt_id u).const_mul (A ^ 2)).add
        (((hasDerivAt_id u).pow 2).const_mul (A * B))).add
          (((hasDerivAt_id u).pow 3).const_mul (B ^ 2 / 3))
    change HasDerivAt F _ u at hraw
    exact hraw.congr_deriv (by
      dsimp only [F, A, B, levinsonLinearOptimizationDerivativeAt] at *
      simp only [id_eq] at *
      ring)
  have hint : IntervalIntegrable
      (fun u : ℝ => levinsonLinearOptimizationDerivativeAt (49 / 100) u v ^ 2)
      volume 0 1 :=
    (show Continuous (fun u : ℝ =>
      levinsonLinearOptimizationDerivativeAt (49 / 100) u v ^ 2) by
        unfold levinsonLinearOptimizationDerivativeAt
        fun_prop).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hderiv u) hint]
  dsimp only [F, A, B, levinsonLinearFortyNinePolynomial]
  norm_num
  ring

private def levinsonLinearFortyNinePrimitive (v : ℝ) : ℝ :=
  let a : ℝ := 3462609 / 3000000
  let b : ℝ := -8539278 / 3000000
  let c : ℝ := 5316769 / 3000000
  let k : ℝ := 13 / 5
  Real.exp (k * v) *
    (c / k * v ^ 2 + (b / k - 2 * c / k ^ 2) * v +
      (a / k - b / k ^ 2 + 2 * c / k ^ 3))

private lemma hasDerivAt_levinsonLinearFortyNinePrimitive (v : ℝ) :
    HasDerivAt levinsonLinearFortyNinePrimitive
      (Real.exp ((13 / 5) * v) * levinsonLinearFortyNinePolynomial v) v := by
  have hraw := (((hasDerivAt_id v).const_mul (13 / 5 : ℝ)).exp).mul
    (((((hasDerivAt_id v).pow 2).const_mul
      ((5316769 / 3000000 : ℝ) / (13 / 5))).add
      ((hasDerivAt_id v).const_mul
        ((-8539278 / 3000000 : ℝ) / (13 / 5) -
          2 * (5316769 / 3000000 : ℝ) / (13 / 5) ^ 2))).add
      (hasDerivAt_const v
        ((3462609 / 3000000 : ℝ) / (13 / 5) -
          (-8539278 / 3000000 : ℝ) / (13 / 5) ^ 2 +
          2 * (5316769 / 3000000 : ℝ) / (13 / 5) ^ 3)))
  change HasDerivAt levinsonLinearFortyNinePrimitive _ v at hraw
  exact hraw.congr_deriv (by
    dsimp only [levinsonLinearFortyNinePrimitive,
      levinsonLinearFortyNinePolynomial] at *
    norm_num
    ring)

private lemma integral_levinsonLinearFortyNine_exp_polynomial :
    (∫ v in (0 : ℝ)..1,
      Real.exp ((13 / 5) * v) * levinsonLinearFortyNinePolynomial v) =
      levinsonLinearFortyNinePrimitive 1 - levinsonLinearFortyNinePrimitive 0 := by
  have hint : IntervalIntegrable
      (fun v : ℝ => Real.exp ((13 / 5) * v) *
        levinsonLinearFortyNinePolynomial v) volume 0 1 :=
    (show Continuous (fun v : ℝ => Real.exp ((13 / 5) * v) *
      levinsonLinearFortyNinePolynomial v) by
        unfold levinsonLinearFortyNinePolynomial
        fun_prop).intervalIntegrable 0 1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hasDerivAt_levinsonLinearFortyNinePrimitive v) hint

private theorem levinsonLinearOptimizationConstantAt_fortyNine_eq :
    levinsonLinearOptimizationConstantAt (49 / 100) =
      1 + (100 / 49 : ℝ) *
        (levinsonLinearFortyNinePrimitive 1 -
          levinsonLinearFortyNinePrimitive 0) := by
  rw [levinsonLinearOptimizationConstantAt]
  norm_num
  simp_rw [integral_levinsonLinearOptimizationDerivativeAt_fortyNine_sq]
  rw [integral_levinsonLinearFortyNine_exp_polynomial]

/-- Exact upper bound placing the `49/100` scalar below the Levinson `>1/3` threshold. -/
theorem levinsonLinearOptimizationConstantAt_fortyNine_lt_nineteen_eighths :
    levinsonLinearOptimizationConstantAt (49 / 100) < 19 / 8 := by
  rw [levinsonLinearOptimizationConstantAt_fortyNine_eq]
  have hroot : Real.exp (13 / 20 : ℝ) < 19157 / 10000 := by
    have hb := Real.exp_bound (x := (13 / 20 : ℝ)) (by norm_num)
      (n := 12) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb ⊢
    have h := (abs_le.mp hb).2
    linarith
  have hpow : Real.exp (13 / 5 : ℝ) = Real.exp (13 / 20 : ℝ) ^ 4 := by
    rw [show (13 / 5 : ℝ) = (4 : ℕ) * (13 / 20 : ℝ) by norm_num,
      Real.exp_nat_mul]
  have hexp : Real.exp (13 / 5 : ℝ) < (19157 / 10000 : ℝ) ^ 4 := by
    rw [hpow]
    exact pow_lt_pow_left₀ hroot (Real.exp_pos _).le (by norm_num)
  dsimp only [levinsonLinearFortyNinePrimitive]
  norm_num at hexp ⊢
  nlinarith

/-- The explicit exponent `49/100` retains Young's strict Levinson proportion margin. -/
theorem levinsonLinearOptimizationProportionAt_fortyNine_gt_one_third :
    levinsonLinearOptimizationProportionAt (49 / 100) > 1 / 3 := by
  have hcpos := levinsonLinearOptimizationConstantAt_pos
    (theta := (49 / 100 : ℝ)) (by norm_num)
  have hcexp : levinsonLinearOptimizationConstantAt (49 / 100) <
      Real.exp (13 / 15) :=
    levinsonLinearOptimizationConstantAt_fortyNine_lt_nineteen_eighths.trans
      nineteen_eighths_lt_exp_thirteen_fifteenths
  have hlog : Real.log (levinsonLinearOptimizationConstantAt (49 / 100)) <
      13 / 15 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log hcpos]
    exact hcexp
  rw [levinsonLinearOptimizationProportionAt]
  norm_num at hlog ⊢
  linarith

theorem levinsonLinearFortyNineTheta_proportion_gt_one_third :
    levinsonLinearOptimizationProportionAt levinsonLinearFortyNineTheta > 1 / 3 := by
  simpa only [levinsonLinearFortyNineTheta] using
    levinsonLinearOptimizationProportionAt_fortyNine_gt_one_third

end RHTower
