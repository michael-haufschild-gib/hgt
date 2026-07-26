/-
The frontier bound needs two conditions, not one.

Split the frontier sum by `√d`-class: `≍ N^(1/3)` classes of size `≍ N^(1/3)`.  Two independent
properties control the total.

* **(i) Few resonant classes.**  Only `N^(o(1))` of the classes are coherent with the evaluation
  point.  A coherent class contributes its full size `N^(1/3)`.
* **(ii) Across-class cancellation.**  The non-resonant classes, each contributing at most
  `N^(1/6)` by square-root cancellation within the class, add with square-root cancellation across
  classes rather than by the triangle inequality.

The accounting:

    neither          coherent part `N^(1/3)·N^(1/3) = N^(2/3)`   →  **N^(2/3)**
    (i) only         coherent `N^(1/3)`, rest `N^(1/3)·N^(1/6)`  →  **N^(1/2)**
    (i) and (ii)     coherent `N^(1/3)`, rest `N^(1/6)·N^(1/6)`  →  **N^(1/3)**

These are exactly the three levels recorded earlier.  So **the simultaneous-non-resonance statement
the campaign has been pursuing is condition (i) alone, and it buys only the first of the two steps of
`1/6`**; the Lindelöf bound for the frontier object requires (ii) as well, and (ii) is a genuine
across-class cancellation statement, not a counting one.
-/
import GaloisForLFunctions.HTGeometry.ResonanceCountExponents

namespace HTGeometry

/-! ### The pieces -/

/-- Exponent of the contribution of the resonant classes, given `N^(c)` of them. -/
def resonantContribution (c : ℚ) : ℚ := c + classSizeExponent

/-- Exponent of a single non-resonant class's contribution, by square-root cancellation within it. -/
def nonResonantClassBound : ℚ := classSizeExponent / 2

/-- **It is `1/6`.** -/
@[simp] theorem nonResonantClassBound_eq : nonResonantClassBound = 1 / 6 := by
  unfold nonResonantClassBound classSizeExponent; norm_num

/-- Contribution of the non-resonant classes summed by the triangle inequality. -/
def nonResonantTriangle : ℚ := classCountExponent + nonResonantClassBound

/-- Contribution of the non-resonant classes summed with square-root cancellation. -/
def nonResonantSqrt : ℚ := classCountExponent / 2 + nonResonantClassBound

/-- **Triangle gives `1/2`, square root gives `1/3`.** -/
theorem nonResonant_values : nonResonantTriangle = 1 / 2 ∧ nonResonantSqrt = 1 / 3 := by
  constructor
  · unfold nonResonantTriangle classCountExponent; rw [nonResonantClassBound_eq]; norm_num
  · unfold nonResonantSqrt classCountExponent; rw [nonResonantClassBound_eq]; norm_num

/-- **The step between them is `1/6`.** -/
theorem nonResonant_step : nonResonantTriangle - nonResonantSqrt = 1 / 6 := by
  obtain ⟨h1, h2⟩ := nonResonant_values
  rw [h1, h2]; norm_num

/-! ### The three totals -/

/-- No condition: every class resonant, triangle inequality throughout. -/
def totalNeither : ℚ := resonantContribution classCountExponent

/-- Condition (i) only: few resonant classes, triangle inequality across the rest. -/
def totalFirstOnly : ℚ := max (resonantContribution 0) nonResonantTriangle

/-- Both conditions. -/
def totalBoth : ℚ := max (resonantContribution 0) nonResonantSqrt

/-- **The resonant part under (i) is `1/3`.** -/
@[simp] theorem resonantContribution_zero : resonantContribution 0 = 1 / 3 := by
  unfold resonantContribution classSizeExponent; norm_num

/-- **Without (i) it is `2/3`.** -/
@[simp] theorem totalNeither_eq : totalNeither = 2 / 3 := by
  unfold totalNeither resonantContribution classCountExponent classSizeExponent; norm_num

/-- **With (i) only the total is `1/2`.** -/
@[simp] theorem totalFirstOnly_eq : totalFirstOnly = 1 / 2 := by
  unfold totalFirstOnly
  rw [resonantContribution_zero, nonResonant_values.1]
  norm_num

/-- **With both, the total is `1/3` — the Lindelöf value.** -/
@[simp] theorem totalBoth_eq : totalBoth = 1 / 3 := by
  unfold totalBoth
  rw [resonantContribution_zero, nonResonant_values.2]
  norm_num

/-! ### Agreement with the recorded levels -/

/-- **The three totals are exactly the three levels of the class ladder.** -/
theorem totals_are_levels :
    totalNeither = levelTotal ∧ totalFirstOnly = levelWithinClass ∧
      totalBoth = levelNoConspiracy := by
  refine ⟨?_, ?_, ?_⟩
  · rw [totalNeither_eq]; unfold levelTotal; norm_num
  · rw [totalFirstOnly_eq]; unfold levelWithinClass; norm_num
  · rw [totalBoth_eq]; unfold levelNoConspiracy; norm_num

/-! ### What each condition buys -/

/-- **Condition (i) buys `1/6`.** -/
theorem first_condition_value : totalNeither - totalFirstOnly = 1 / 6 := by
  rw [totalNeither_eq, totalFirstOnly_eq]; norm_num

/-- **Condition (ii) buys the other `1/6`.** -/
theorem second_condition_value : totalFirstOnly - totalBoth = 1 / 6 := by
  rw [totalFirstOnly_eq, totalBoth_eq]; norm_num

/-- **They are worth the same**, and together they are one Farey order. -/
theorem conditions_equal_and_total :
    totalNeither - totalFirstOnly = totalFirstOnly - totalBoth ∧
      totalNeither - totalBoth = fareyOrderExponent := by
  constructor
  · rw [first_condition_value, second_condition_value]
  · rw [totalNeither_eq, totalBoth_eq]; unfold fareyOrderExponent; norm_num

/-- **The sharpening.**  Simultaneous non-resonance — the statement the campaign has been pursuing —
is condition (i), and it delivers only half the required saving.  The Lindelöf bound for the frontier
object needs across-class cancellation as well. -/
theorem resonance_is_only_half :
    totalFirstOnly - totalBoth = 1 / 6 ∧
      totalNeither - totalBoth = 1 / 3 ∧
      totalFirstOnly ≠ totalBoth := by
  refine ⟨second_condition_value, ?_, ?_⟩
  · rw [totalNeither_eq, totalBoth_eq]; norm_num
  · rw [totalFirstOnly_eq, totalBoth_eq]; norm_num

end HTGeometry
