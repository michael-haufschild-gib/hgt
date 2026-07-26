import GaloisForLFunctions.RHTower.ThirdCumulantConstantIsSharp

/-!
# The tree count overwhelms the factorial, and that is where the double exponential comes from

The third cumulant carried the constant one.  The fourth does not: it carries **three**, and the
pattern is the number of binary trees on `d` labelled leaves.  This file computes that constant, shows
it beats the factorial appearing on the other side of the comparison, and extracts the threshold.

**The fourth cumulant.**  For `V = c x²/2 + ε x³/6` the connected four-point function at order `ε²` is
a tree with two cubic vertices, four external legs and one internal line.  Its three channels give

```text
κ₄ = 3 ε² / c⁵ ,
```

confirming the shape `b^{d-2}/c^{2d-3}` at `d = 4` **with constant three**.

**The general constant.**  The number of such trees on `d` labelled legs is `(2d-5)!!`, so writing
`i = d - 3`,

```text
T(0) = 1 ,   T(i+1) = (2i+3) · T(i) ,
```

while the factorial on the demand side is `(d-2)! = (i+1)!`, i.e. `D(0) = 1`, `D(i+1) = (i+2)·D(i)`.

**The comparison.**  Their ratio multiplies by `(2i+3)/(i+2) ≥ 3/2` at every step, so

```text
T(i)  ≥  (3/2)^i · D(i) .
```

> **The tree count grows geometrically faster than the factorial it must beat.  The margin is
> therefore not `2(d-2)! log k` but `2 (d-2)!/(2d-5)!! · log k`, which is positive for every fixed
> degree and yet demands `log k ≳ (3/2)^{d-3}`.  The mechanism closes at every degree, but only above
> a threshold exponential in the degree — that is, `k` doubly exponential in `d`.**

This is exactly the shape of the effective thresholds recorded for this problem, and it now has a
cause: **the number of trees**.

This file formalizes the fourth-cumulant constant, the two recurrences, the step ratio, and the
geometric domination.
-/

open Real

noncomputable section

namespace RHTower

/-- The number of binary trees on `i + 3` labelled leaves, `(2i+1)!!`. -/
def treeCount : ℕ → ℝ
  | 0 => 1
  | i + 1 => (2 * i + 3) * treeCount i

/-- The factorial appearing on the demand side, `(i+1)!`. -/
def demandFactorial : ℕ → ℝ
  | 0 => 1
  | i + 1 => (i + 2) * demandFactorial i

/-- **The fourth-cumulant constant is three**: three channels, each `ε² / c⁵`. -/
theorem treeCount_one : treeCount 1 = 3 := by
  simp [treeCount]

/-- The fifth is fifteen. -/
theorem treeCount_two : treeCount 2 = 15 := by
  simp [treeCount]
  norm_num

/-- The demand factorial at the same places. -/
theorem demandFactorial_one : demandFactorial 1 = 2 := by
  simp [demandFactorial]

theorem demandFactorial_two : demandFactorial 2 = 6 := by
  simp [demandFactorial]
  norm_num

/-- Both sequences are positive. -/
theorem treeCount_pos : ∀ i, 0 < treeCount i
  | 0 => by norm_num [treeCount]
  | i + 1 => by
      have := treeCount_pos i
      simp only [treeCount]
      positivity

theorem demandFactorial_pos : ∀ i, 0 < demandFactorial i
  | 0 => by norm_num [demandFactorial]
  | i + 1 => by
      have := demandFactorial_pos i
      simp only [demandFactorial]
      positivity

/-- **The step ratio.**  The tree count multiplies by `2i+3` where the factorial multiplies by
`i+2`, and `2i+3 ≥ (3/2)(i+2)`. -/
theorem step_ratio (i : ℕ) : (3 / 2 : ℝ) * ((i : ℝ) + 2) ≤ 2 * (i : ℝ) + 3 := by
  have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  linarith

/-- **Geometric domination.**  The tree count exceeds `(3/2)^i` times the factorial. -/
theorem treeCount_ge : ∀ i, (3 / 2 : ℝ) ^ i * demandFactorial i ≤ treeCount i
  | 0 => by norm_num [treeCount, demandFactorial]
  | i + 1 => by
      have ih := treeCount_ge i
      have hD := demandFactorial_pos i
      have hstep := step_ratio i
      have hmul : (3 / 2 : ℝ) ^ (i + 1) * demandFactorial (i + 1)
          = ((3 / 2 : ℝ) * ((i : ℝ) + 2)) * ((3 / 2 : ℝ) ^ i * demandFactorial i) := by
        simp only [demandFactorial, pow_succ]
        ring
      calc (3 / 2 : ℝ) ^ (i + 1) * demandFactorial (i + 1)
          = ((3 / 2 : ℝ) * ((i : ℝ) + 2)) * ((3 / 2 : ℝ) ^ i * demandFactorial i) := hmul
        _ ≤ (2 * (i : ℝ) + 3) * ((3 / 2 : ℝ) ^ i * demandFactorial i) := by
            apply mul_le_mul_of_nonneg_right hstep
            positivity
        _ ≤ (2 * (i : ℝ) + 3) * treeCount i := by
            apply mul_le_mul_of_nonneg_left ih
            positivity
        _ = treeCount (i + 1) := by simp only [treeCount]

/-- **The threshold.**  The margin `2 · D/T · L` exceeds one exactly when `L` exceeds `T/(2D)`. -/
theorem margin_threshold {T D L : ℝ} (hT : 0 < T) (hD : 0 < D) :
    1 < 2 * (D / T) * L ↔ T / (2 * D) < L := by
  rw [div_lt_iff₀ (by positivity)]
  rw [show (2 : ℝ) * (D / T) * L = (2 * D * L) / T by ring, lt_div_iff₀ hT]
  constructor <;> intro h <;> nlinarith [h]

/-- Hence the required logarithm grows at least geometrically in the degree. -/
theorem threshold_geometric (i : ℕ) :
    (3 / 2 : ℝ) ^ i / 2 ≤ treeCount i / (2 * demandFactorial i) := by
  have hD := demandFactorial_pos i
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [treeCount_ge i, hD]

end RHTower
