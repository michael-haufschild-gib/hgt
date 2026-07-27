import GaloisForLFunctions.HTGeometry.CubicMomentGammaFamily

/-!
# A log-concave counterexample to the cubic moment conjecture

The Beta `(1, 3)` density

```text
f(x) = 3 (1 - x)^2,  0 ≤ x ≤ 1
```

is log-concave on its convex support: on `0 ≤ x < 1`,
`log f(x) = log 3 + 2 log (1 - x)`, a concave function. Its even raw moments are

```text
(m₀, m₁, m₂, m₃) = (1, 1/10, 1/35, 1/84).
```

The cubic functional is `-3/9800`, hence negative. This exact witness refutes the proposed
implication from ordinary log-concavity to nonnegativity of the unsplit theta-cusp cubic.
The density's log-concavity is an elementary paper input; this module verifies the exact integral
moments and negative algebraic certificate without numerical approximation.
-/

namespace GaloisForLFunctions

namespace CubicMoment

/-- The `2j`-th raw moment of the Beta `(1, 3)` density `3(1-x)^2` on `[0,1]`. -/
noncomputable def betaOneThreeRawEvenMoment (j : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ (2 * j) * (3 * (1 - x) ^ 2)

/-- Closed form for every even raw moment of the Beta `(1, 3)` witness. -/
theorem betaOneThreeRawEvenMoment_formula (j : ℕ) :
    betaOneThreeRawEvenMoment j =
      3 / (2 * j + 1 : ℕ) - 6 / (2 * j + 2 : ℕ) + 3 / (2 * j + 3 : ℕ) := by
  unfold betaOneThreeRawEvenMoment
  rw [show (fun x : ℝ => x ^ (2 * j) * (3 * (1 - x) ^ 2)) =
      fun x : ℝ => 3 * x ^ (2 * j) - 6 * x ^ (2 * j + 1) + 3 * x ^ (2 * j + 2) by
    funext x
    simp only [pow_succ]
    ring]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, integral_pow, integral_pow, integral_pow]
      push_cast
      ring
    · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _
  · exact
      ((continuous_const.mul (continuous_id.pow _)).sub
        (continuous_const.mul (continuous_id.pow _))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _

theorem betaOneThreeRawEvenMoment_zero :
    betaOneThreeRawEvenMoment 0 = 1 := by
  rw [betaOneThreeRawEvenMoment_formula]
  norm_num

theorem betaOneThreeRawEvenMoment_one :
    betaOneThreeRawEvenMoment 1 = 1 / 10 := by
  rw [betaOneThreeRawEvenMoment_formula]
  norm_num

theorem betaOneThreeRawEvenMoment_two :
    betaOneThreeRawEvenMoment 2 = 1 / 35 := by
  rw [betaOneThreeRawEvenMoment_formula]
  norm_num

theorem betaOneThreeRawEvenMoment_three :
    betaOneThreeRawEvenMoment 3 = 1 / 84 := by
  rw [betaOneThreeRawEvenMoment_formula]
  norm_num

/-- The Beta `(1, 3)` moment vector makes the cubic functional exactly `-3/9800`. -/
theorem betaOneThree_cubicFunctional_eq :
    cubicFunctional
        (betaOneThreeRawEvenMoment 0)
        (betaOneThreeRawEvenMoment 1)
        (betaOneThreeRawEvenMoment 2)
        (betaOneThreeRawEvenMoment 3) =
      -(3 / 9800 : ℝ) := by
  rw [betaOneThreeRawEvenMoment_zero, betaOneThreeRawEvenMoment_one,
    betaOneThreeRawEvenMoment_two, betaOneThreeRawEvenMoment_three]
  unfold cubicFunctional
  norm_num

/-- Exact negative certificate refuting the proposed universal cubic moment inequality. -/
theorem betaOneThree_cubicFunctional_neg :
    cubicFunctional
        (betaOneThreeRawEvenMoment 0)
        (betaOneThreeRawEvenMoment 1)
        (betaOneThreeRawEvenMoment 2)
        (betaOneThreeRawEvenMoment 3) < 0 := by
  rw [betaOneThree_cubicFunctional_eq]
  norm_num

end CubicMoment

end GaloisForLFunctions
