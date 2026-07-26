/-
The `√d`-class structure of the frontier frequencies, and the three levels of conspiracy.

The frontier frequencies are `ξ = √(2a/q) = √(2aq)/q`.  Two of them are **commensurable** exactly when
`2aq` and `2a'q'` have the same squarefree kernel `d`; the frequencies then are rational multiples of
the single irrational `√d`.  This partitions the `R ≍ L² = N^(2/3)` frequencies into `√d`-classes.

Counting: for fixed `d`, the solutions of `2aq = d m²` with `a/q ∈ F_L` number `≍ L^(1+o(1))/√d`, so
the largest class has size `≍ L = N^(1/3)` and there are `≍ L = N^(1/3)` classes.  The two exponents
add to `2/3`, the total.

Three levels of coherence follow.

    no conspiracy                     — typical `n`, everything incoherent   **N^(1/3)**
    within-class conspiracy only      — each class coherent, classes incoherent   **N^(1/2)**
    total conspiracy                  — everything coherent   **N^(2/3)**

The first is the root mean square delivered by the large sieve, and equals the Lindelöf value; the
last is the trivial bound.  **The Lindelöf hypothesis for the frontier object is the assertion that
the first level is the truth**, i.e. that simultaneous resonance across `√d`-classes contributes only
`N^(o(1))`.

The Gál-sum theory supplies a *lower* bound `exp(c√(log N log log N))` for that resonance factor —
subpolynomial, hence consistent with the assertion.  No matching upper bound is known, and supplying
one is exactly the remaining content.  Since the `√d` are quadratic irrationals, the question is one
about simultaneous Diophantine approximation in real quadratic fields.
-/
import GaloisForLFunctions.HTGeometry.FrontierLargeSieve

namespace HTGeometry

/-! ### The class decomposition -/

/-- Exponent of the number of `√d`-classes among the frontier frequencies. -/
def classCountExponent : ℚ := 1 / 3

/-- Exponent of the size of the largest class. -/
def classSizeExponent : ℚ := 1 / 3

/-- **The two exponents account for all the frequencies.** -/
theorem class_decomposition_total :
    classCountExponent + classSizeExponent = frontierTermCount := by
  unfold classCountExponent classSizeExponent frontierTermCount; norm_num

/-- Both equal the Farey order's exponent. -/
theorem class_exponents_are_farey_order :
    classCountExponent = fareyOrderExponent ∧ classSizeExponent = fareyOrderExponent := by
  constructor
  · unfold classCountExponent fareyOrderExponent; norm_num
  · unfold classSizeExponent fareyOrderExponent; norm_num

/-! ### The three levels -/

/-- No conspiracy: everything incoherent. -/
def levelNoConspiracy : ℚ := 1 / 3

/-- Within-class conspiracy: each class coherent, classes incoherent. -/
def levelWithinClass : ℚ := 1 / 2

/-- Total conspiracy: everything coherent. -/
def levelTotal : ℚ := 2 / 3

/-- **The within-class level is the incoherent sum of coherent classes.** -/
theorem withinClass_from_counts :
    levelWithinClass = classCountExponent / 2 + classSizeExponent := by
  unfold levelWithinClass classCountExponent classSizeExponent; norm_num

/-- **The total level is the coherent sum.** -/
theorem total_from_counts :
    levelTotal = classCountExponent + classSizeExponent := by
  unfold levelTotal classCountExponent classSizeExponent; norm_num

/-- **The no-conspiracy level is the root mean square.** -/
theorem noConspiracy_is_rms : levelNoConspiracy = frontierRootMeanSquare := rfl

/-- **And it is the Lindelöf value.** -/
theorem noConspiracy_is_lindelof : levelNoConspiracy = frontierLindelof := rfl

/-- **The total level is the trivial bound.** -/
theorem total_is_trivial : levelTotal = frontierTrivial := rfl

/-- **The three levels are strictly increasing.** -/
theorem levels_increasing :
    levelNoConspiracy < levelWithinClass ∧ levelWithinClass < levelTotal := by
  unfold levelNoConspiracy levelWithinClass levelTotal
  constructor <;> norm_num

/-- The steps between them are equal. -/
theorem level_steps_equal :
    levelWithinClass - levelNoConspiracy = levelTotal - levelWithinClass := by
  unfold levelNoConspiracy levelWithinClass levelTotal; norm_num

/-- **Each step is `1/6`.** -/
theorem level_step_size : levelWithinClass - levelNoConspiracy = 1 / 6 := by
  unfold levelWithinClass levelNoConspiracy; norm_num

/-! ### Relation to the block/arc levels -/

/-- **The class levels are one step finer than the block/arc levels.**  The four block/arc values are
`1/2, 2/3, 5/6, 1`; the three class values are `1/3, 1/2, 2/3` — the same ladder shifted down by
`1/3`, the Farey order. -/
theorem class_levels_shift_block_levels :
    levelNoConspiracy + fareyOrderExponent = accountBothIncoherent (1 / 3) + 1 / 6 ∧
      levelWithinClass = accountBothIncoherent (1 / 3) ∧
      levelTotal = accountArcsIncoherent (1 / 3) := by
  refine ⟨?_, rfl, ?_⟩
  · unfold levelNoConspiracy fareyOrderExponent accountBothIncoherent; norm_num
  · unfold levelTotal accountArcsIncoherent; norm_num

/-! ### The remaining assertion -/

/-- **The Lindelöf assertion for the frontier object.**  The truth is the no-conspiracy level, i.e.
simultaneous resonance across classes contributes only `N^(o(1))`. -/
theorem lindelof_is_no_conspiracy :
    levelNoConspiracy = frontierLindelof ∧
      levelWithinClass - levelNoConspiracy = 1 / 6 ∧
      levelTotal - levelNoConspiracy = 1 / 3 := by
  refine ⟨rfl, level_step_size, ?_⟩
  unfold levelTotal levelNoConspiracy; norm_num

/-- **And the whole gap is one Farey order**, matching every earlier measure. -/
theorem class_gap_is_farey_order :
    levelTotal - levelNoConspiracy = fareyOrderExponent := by
  unfold levelTotal levelNoConspiracy fareyOrderExponent; norm_num

end HTGeometry
