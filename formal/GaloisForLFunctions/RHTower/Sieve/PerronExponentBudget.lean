import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# The exponent budget of the Perron analytic term

Every analytic estimate for the vertical integral of the Cesàro route produces a bound of the form
`x^σ·(log L)^e` for the analytic term, and the routes differ only in `e`.  Following the accounting style
of `HTGeometry/CorrelationExponentBridge.lean`, the exponents are recorded as rationals and the ranking
becomes a checked identity rather than prose — the same discipline that catches an arithmetic slip in a
balance computation.

* pointwise Euler bound: `e = 1`, from `‖L‖ ≤ (log z)e^{−𝔻²}` with `𝔻² = O(1)` at the worst frequency;
* Cauchy–Schwarz against the affine mean square: `e = 1/2`, from `√Q` with `Q ≍ log L`;
* damped route at distance level `δ² = c·logLog L`: balancing `(log L/A)(log L)^{−c}e^{2A}` against
  `(log L/A)e^{−A}` at `A ≍ (c/3)logLog L` gives `e = 1 − c/3`.

The `c` a *uniform* distance can supply is at most `1` — the prime mass, by the averaging theorem — so the
damped route's floor is `e = 2/3`; the corpus's zero-free input gives only `c = 2/9`, hence `e = 1 − 2/27`.
The level `c = 2` is attainable at a single frequency but not uniformly, and even it would give `e = 1/3`.

Every exponent is strictly positive, and that is the arithmetic content of the family being capped: the
analytic term is never `o(x^σ)`, so at `x = N` never `o(N)`.  The comparisons also record that the
unconditional mean square beats every damped variant, which is the fact that made the zero-free region
inert in this chain.
-/

namespace RHTower.Sieve

/-- Exponent of `log L` in the analytic term from the pointwise Euler bound. -/
def pointwiseEulerExponent : ℚ := 1

/-- Exponent from Cauchy–Schwarz against the affine mean square. -/
def meanSquareExponent : ℚ := 1 / 2

/-- Exponent of the damped route at distance level `δ² = c·logLog L`, after balancing the abscissa. -/
def dampedExponent (c : ℚ) : ℚ := 1 - c / 3

/-- The largest level a *uniform* distance can supply: the prime mass. -/
def uniformDistanceLevel : ℚ := 1

/-- The level the corpus's zero-free input supplies. -/
def corpusDistanceLevel : ℚ := 2 / 9

/-- The level attainable at a *single* frequency, twice the prime mass. -/
def pointDistanceLevel : ℚ := 2

/-- **The damped floor for a uniform level.** -/
@[simp] theorem dampedExponent_uniform : dampedExponent uniformDistanceLevel = 2 / 3 := by
  unfold dampedExponent uniformDistanceLevel; norm_num

/-- **The damped exponent from the corpus's zero-free input.** -/
@[simp] theorem dampedExponent_corpus : dampedExponent corpusDistanceLevel = 1 - 2 / 27 := by
  unfold dampedExponent corpusDistanceLevel; norm_num

/-- **Even the single-frequency level leaves a positive exponent.** -/
@[simp] theorem dampedExponent_point : dampedExponent pointDistanceLevel = 1 / 3 := by
  unfold dampedExponent pointDistanceLevel; norm_num

/-- **The mean square beats the damped route at every admissible level.**  This is the arithmetic of the
zero-free region being inert in this chain. -/
theorem meanSquare_lt_dampedExponent_uniform :
    meanSquareExponent < dampedExponent uniformDistanceLevel := by
  unfold meanSquareExponent dampedExponent uniformDistanceLevel; norm_num

theorem meanSquare_lt_dampedExponent_corpus :
    meanSquareExponent < dampedExponent corpusDistanceLevel := by
  unfold meanSquareExponent dampedExponent corpusDistanceLevel; norm_num

/-- **The damped route does beat the pointwise Euler bound.**  The gain is real; it is just smaller than
the unconditional one. -/
theorem dampedExponent_corpus_lt_pointwise :
    dampedExponent corpusDistanceLevel < pointwiseEulerExponent := by
  unfold dampedExponent corpusDistanceLevel pointwiseEulerExponent; norm_num

/-- **Every exponent in the family is positive.**  The analytic term is never `o(x^σ)`, whatever the
route: the arithmetic content of the cap. -/
theorem all_exponents_pos :
    0 < meanSquareExponent ∧ 0 < dampedExponent uniformDistanceLevel
      ∧ 0 < dampedExponent corpusDistanceLevel ∧ 0 < dampedExponent pointDistanceLevel
      ∧ 0 < pointwiseEulerExponent := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [meanSquareExponent, dampedExponent, uniformDistanceLevel, corpusDistanceLevel,
      pointDistanceLevel, pointwiseEulerExponent] <;> norm_num

/-- **The best exponent in the family.**  No route recorded here goes below `1/2`. -/
theorem meanSquare_is_least :
    meanSquareExponent ≤ dampedExponent uniformDistanceLevel
      ∧ meanSquareExponent ≤ dampedExponent corpusDistanceLevel
      ∧ meanSquareExponent ≤ pointwiseEulerExponent := by
  refine ⟨le_of_lt meanSquare_lt_dampedExponent_uniform,
    le_of_lt meanSquare_lt_dampedExponent_corpus, ?_⟩
  unfold meanSquareExponent pointwiseEulerExponent
  norm_num

end RHTower.Sieve
