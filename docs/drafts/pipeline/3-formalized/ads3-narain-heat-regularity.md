# Scalar Narain heat regularity and exponential decay

- **ID:** W11-NH
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** At every target pair, the nonvacuum scalar Narain heat sum
  is continuous and locally integrable on positive heights. It satisfies
  `|H(y)|≤B exp(−cy)` for `y≥1`, with `B≥0` and `c>0`.

## Proof

Each Boltzmann weight decreases with height. Around a positive height `y`,
the summable weights at `y/2` uniformly dominate the series, proving
continuity. Let `K>0` be the proved mass coercivity constant. Every
nonvacuum mass satisfies `M²≥1/K`. For `y≥1`,
`yM²≥M²/2+y/(2K)`. Summing the resulting exponential bound gives
`B=Σ exp(−πM²/2)` and `c=π/(2K)`.

This discharges the large-height and local-integrability inputs to the
scalar Mellin decay obstruction. It gives no small-height remainder.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/NarainHeatRegularity.lean`.
Declarations: `continuousOn_narainScalarHeat`,
`locallyIntegrableOn_narainScalarHeat`, `narainScalarHeat_exp_tail`,
`exists_isBigO_narainScalarHeat_exp`.

The direct `lake --old env lean` check passes without warnings.
Three endpoint axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`. The topic umbrella imports the module.

## Gates

- [x] 0 → 1: Gaussian majorant and explicit mass gap identified.
- [x] 1 → 2: continuity and exponential estimate proved.
- [x] 2 → 3: direct Lean check, axiom audits and umbrella import.
