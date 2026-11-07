# Boundary quotient convergence does not control Abel budgets

- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement refuted:** `mean |P(v)/P(ρv)|² → 1` forces near-unit holomorphic Abel budgets.

## Exact obstruction

For every finite curve datum, the boundary quotient mean tends to 1 as `ρ→1⁻`. For the golden datum every Abel budget is at least `φ²>1`. Eventually, uniformly in the truncation degree `N`,

`abelBudget(ρ,N) − mean |P(v)/P(ρv)|² ≥ (φ²−1)/2`.

This refutes the implication from a boundary quotient limit. It does not refute the existing Castelnuovo/holomorphic-budget equivalence, nor classify bounds required at every dilation parameter.

## Positive survivor and proof

Every finite datum has an explicit terminal uniform bound. A factor with `|β|≤1` is bounded by 2. For `|β|>1`, eventually its denominator is at least `(|β|−1)/2`, giving bound `2(1+|β|)/(|β|−1)`. Multiply the squared bounds. Outside the finite boundary zero set, the quotient tends to 1; dominated convergence proves the mean limit. The golden budget floor gives the uniform positive gap.

The distinction is holomorphic convergence: identifying the Euler-log truncations with a reciprocal requires its convergence domain. A meromorphic boundary reciprocal does not establish that identification.

## Lean evidence

Module: `formal/GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheBoundaryQuotientForgetsTheInnerMass.lean`.

- `eventually_abs_abelRatio_le`
- `tendsto_circleAverage_abelRatio_unconditional`
- `golden_boundary_limit_and_mollifier_gap`
- `eventually_golden_budget_sub_quotient_ge`

Final check: `lake --old env lean GaloisForLFunctions/ArithmeticInnerFunctionTheory/TheBoundaryQuotientForgetsTheInnerMass.lean`, exit 0, no diagnostics. All four transitive axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`. Imported by `ArithmeticInnerFunctionTheory.lean`; umbrella not compiled.

This is an analytic correction to the frontier interpretation. It provides no arithmetic budget estimate or breakthrough mechanism. The [source problem remains active](../1-in-progress/arithmetic-abel-continuation-mechanism.md).
