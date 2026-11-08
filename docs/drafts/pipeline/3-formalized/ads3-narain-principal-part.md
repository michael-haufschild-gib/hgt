# Exact scalar Narain principal part

- **ID:** W11-NP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** The continued scalar Mellin transform has principal part
  `(3/π)/(s−1)²+B(ρ,σ)/(s−1)`, with an explicit derivative formula for
  `B` and a holomorphic remainder near `s=1`.

## Proof

Write `u=s−1/2` and let `T_z` be the entire filled Eisenstein numerator.
Put `A(u)=T_ρ(u)T_σ(u)/[2u(1+2u)ξ(1+2u)]`.
The filled-numerator construction gives `A(1/2)=3/π` and
`M(u)=A(u)/(u−1/2)²` away from `u=1/2`.
The denominator of `A` is nonzero at `1/2`, so two removable divided
differences give the exact principal part with `B=A′(1/2)`.
Equivalently,

`B=(3/π)[T_ρ′(1/2)+T_σ′(1/2)−3−2ξ′(2)/ξ(2)]`.

The [central-zero cancellation](ads3-narain-central-zero.md) extends the
holomorphic remainder to every point where `(1+2u)ξ(1+2u)≠0`, including zero.

This supplies the exact constant required in the scalar remainder problem.
It does not establish a small-height expansion. The corpus's
`HTGeometry/AnalyticDoublePoleSplit.lean` supplies the general
second-order Taylor factorization. The quotient rule gives the displayed
derivative formula, using `T_z(1/2)=1` and `ξ(1)/ξ(2)=3/π`.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/NarainPrincipalPart.lean`.

- `narainMellinContinuation_principalPart`: exact subtraction identity.
- `differentiableOn_narainMellinRegularPart`: holomorphic remainder wherever
  `(1+2u)ξ(1+2u)≠0`, including the removed main pole and the central zero.
- `narainScalarConstant_eq`: explicit simple-pole coefficient.

The direct `lake --old env lean` check passes without warnings.
All three endpoint axiom audits contain only `propext`, `Classical.choice`,
`Quot.sound`. The topic umbrella imports the module.

## Gates

- [x] 0 → 1: normalized coefficient and removable-difference mechanism identified.
- [x] 1 → 2: exact actual-source principal part and derivative evaluation.
- [x] 2 → 3: direct Lean check, axiom audits and umbrella import.
