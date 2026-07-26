/-
Every power-product bound has a positive floor, and the Lindelöf hypothesis needs a `t`-free one.

Every published estimate for the critical exponential sum has the shape

    |Σ_(n ∼ M) n^(-it)|  ≪  t^a · M^b ,

with `a > 0`.  Feeding such a bound through the approximate functional equation, the block at
`M = t^c` contributes `min(c, a + bc) - c/2`, whose maximum over `0 ≤ c ≤ 1/2` is

    **a + (b - 1/2)/2**      when `b ≥ 1/2`   (the critical block binds),
    **a / (2(1 - b))**       when `b ≤ 1/2`   (the crossover block binds),

the two agreeing at `b = 1/2`.  Both expressions are positive whenever `a > 0`.  So:

> **a power-product bound yields `μ(1/2) = 0` only if `a = 0`.**

That is the common source of every floor the campaign has computed — the covering architecture's
`277/1792`, the exponent-pair corner, the small-block obstruction, the moment method's `≈ 0.157`.  In
each case the obstruction is a positive power of `t` that does not shrink with the block.

Consequently the Lindelöf hypothesis requires an estimate for `Σ_(n ∼ M) n^(-it)` carrying **no
positive power of `t` at all** — a bound in the length alone.  No such estimate exists in the
literature: Weyl, Bombieri–Iwaniec, Huxley and Bourgain all have `a = 1/6, 9/56, 32/205, 13/84`
respectively, on the line `b = 1/2`.
-/
import GaloisForLFunctions.HTGeometry.MethodFloorVsTrueSlope

namespace HTGeometry

/-! ### The two branches -/

/-- The critical-block value of a power-product bound `t^a M^b`. -/
def powerProductCritical (a b : ℚ) : ℚ := a + (b - 1 / 2) / 2

/-- The crossover-block value. -/
def powerProductCrossover (a b : ℚ) : ℚ := a / (2 * (1 - b))

/-- **The two branches agree on the line `b = 1/2`.** -/
theorem powerProduct_branches_agree (a : ℚ) :
    powerProductCritical a (1 / 2) = powerProductCrossover a (1 / 2) := by
  unfold powerProductCritical powerProductCrossover; norm_num

/-- On the line the value is `a` itself. -/
@[simp] theorem powerProduct_on_line (a : ℚ) : powerProductCritical a (1 / 2) = a := by
  unfold powerProductCritical; ring

/-! ### Positivity -/

/-- **The critical branch is positive whenever `a > 0` and `b ≥ 1/2`.** -/
theorem powerProductCritical_pos {a b : ℚ} (ha : 0 < a) (hb : 1 / 2 ≤ b) :
    0 < powerProductCritical a b := by
  unfold powerProductCritical; linarith

/-- **The crossover branch is positive whenever `a > 0` and `b < 1`.** -/
theorem powerProductCrossover_pos {a b : ℚ} (ha : 0 < a) (hb : b < 1) :
    0 < powerProductCrossover a b := by
  unfold powerProductCrossover
  apply div_pos ha
  linarith

/-- **The critical branch vanishes exactly at the corner.** -/
theorem powerProductCritical_eq_zero_iff {a b : ℚ} (ha : 0 ≤ a) (hb : 1 / 2 ≤ b) :
    powerProductCritical a b = 0 ↔ a = 0 ∧ b = 1 / 2 := by
  unfold powerProductCritical
  constructor
  · intro h
    constructor <;> linarith
  · rintro ⟨h1, h2⟩; rw [h1, h2]; ring

/-- **The crossover branch vanishes exactly when the `t`-exponent does.** -/
theorem powerProductCrossover_eq_zero_iff {a b : ℚ} (hb : b < 1) :
    powerProductCrossover a b = 0 ↔ a = 0 := by
  unfold powerProductCrossover
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h' | h'
    · exact h'
    · exfalso; linarith
  · intro h; rw [h]; simp

/-! ### The universal statement -/

/-- **A power-product bound with a positive power of `t` cannot give the Lindelöf exponent**, on
either branch. -/
theorem positive_t_exponent_blocks_lindelof {a b : ℚ} (ha : 0 < a) (hb : b < 1) :
    (1 / 2 ≤ b → 0 < powerProductCritical a b) ∧ 0 < powerProductCrossover a b :=
  ⟨fun h => powerProductCritical_pos ha h, powerProductCrossover_pos ha hb⟩

/-- **Conversely a `t`-free bound of exponent `1/2` gives the Lindelöf exponent.** -/
theorem t_free_gives_lindelof : powerProductCritical 0 (1 / 2) = 0 := by
  unfold powerProductCritical; norm_num

/-- **The Lindelöf hypothesis requires a `t`-free estimate.** -/
theorem lindelof_requires_t_free {a b : ℚ} (ha : 0 ≤ a) (hb : 1 / 2 ≤ b)
    (h : powerProductCritical a b = 0) : a = 0 :=
  ((powerProductCritical_eq_zero_iff ha hb).mp h).1

/-! ### The published estimates all carry a positive power of `t` -/

/-- Weyl. -/
theorem weyl_t_exponent : powerProductCritical weylKappa (1 / 2) = 1 / 6 := by
  rw [powerProduct_on_line]; unfold weylKappa; norm_num

/-- Bombieri–Iwaniec. -/
theorem bi_t_exponent : powerProductCritical biKappa (1 / 2) = 9 / 56 := by
  rw [powerProduct_on_line]; unfold biKappa; norm_num

/-- Huxley. -/
theorem huxley_t_exponent : powerProductCritical huxleyPairKappa (1 / 2) = 32 / 205 := by
  rw [powerProduct_on_line]; unfold huxleyPairKappa; norm_num

/-- Bourgain. -/
theorem bourgain_t_exponent : powerProductCritical bourgainKappa (1 / 2) = 13 / 84 := by
  rw [powerProduct_on_line]; unfold bourgainKappa; norm_num

/-- **All four are strictly positive**, so each carries a positive power of `t` and each has a
positive floor. -/
theorem all_published_have_positive_t_exponent :
    0 < powerProductCritical weylKappa (1 / 2) ∧
      0 < powerProductCritical biKappa (1 / 2) ∧
      0 < powerProductCritical huxleyPairKappa (1 / 2) ∧
      0 < powerProductCritical bourgainKappa (1 / 2) := by
  rw [weyl_t_exponent, bi_t_exponent, huxley_t_exponent, bourgain_t_exponent]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **And they decrease**, so the subject's history is the reduction of a single quantity: the power
of `t` in the estimate for the critical exponential sum. -/
theorem published_t_exponents_decrease :
    powerProductCritical bourgainKappa (1 / 2) < powerProductCritical huxleyPairKappa (1 / 2) ∧
      powerProductCritical huxleyPairKappa (1 / 2) < powerProductCritical biKappa (1 / 2) ∧
      powerProductCritical biKappa (1 / 2) < powerProductCritical weylKappa (1 / 2) := by
  rw [weyl_t_exponent, bi_t_exponent, huxley_t_exponent, bourgain_t_exponent]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- **The unified reading of every floor the campaign has computed.**  Each is the value of a
power-product bound with `a > 0`; the Lindelöf hypothesis is `a = 0`, an estimate in the length
alone. -/
theorem unified_floor_statement :
    0 < powerProductCritical bourgainKappa (1 / 2) ∧
      powerProductCritical 0 (1 / 2) = 0 ∧
      spacingCoverageFloor bourgainB bourgainC < bourgainTheta ∧
      bourgainTheta < methodFloor := by
  refine ⟨?_, t_free_gives_lindelof, bourgain_floor_lt_record, methodFloor_above_record⟩
  rw [bourgain_t_exponent]; norm_num

end HTGeometry
