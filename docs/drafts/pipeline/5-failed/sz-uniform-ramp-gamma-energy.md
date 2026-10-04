# SZ: uniform literal exponential-ramp Gamma energy

- **ID:** SZ-UNIFORM-RAMP-GAMMA-ENERGY
- **Stage:** 5-failed
- **Scope:** eventual uniform bounds for visible or full arithmetic
  Gamma energy of the literal exponential-ramp current at physical cutoff
  floor(exp T)+1.

## Obstruction and positive survivor

For every radius delta>0 and bound B, cofinally the visible energy on
|r|<delta exceeds B while the absolute signed action exceeds the fixed
positive constant poleSharpConstant/8. The full arithmetic energy
dominates visible energy, so it has no eventual uniform bound either.

The positive survivor is this simultaneous concentration/nonvanishing
law, together with vanishing of the complete signed current integral
outside every fixed cusp window. It retains all prime powers and both
terminal orientations. The proof uses the actual quantile-height limit,
future deficit-flux convolution and unconditional Weil-lag recurrence.

Paper proof, exact Lean statements and all six public axiom audits are
closed in [sz-ramp-cusp-energy-concentration](../3-formalized/sz-ramp-cusp-energy-concentration.md).
Final leaf93039 and axiom45260 exited0; standard axioms only.

## Survivor after a second pass

Restricting energy to a fixed small window does not repair this candidate:
unbounded energy occurs inside every such window at nonvanishing-action
times. A moving-window or renormalized signed estimate must preserve the
inner/outer balance; neither is excluded by this theorem. In particular,
bounded signed action, canonical-head positivity, and route SZ remain
open. No negative Weil witness or RH falsification is claimed.
