# Arithmetic poles force a scalar decay boundary

- **ID:** W11-NB
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** For every arithmetic resonance `p`, and every pair of
  positive target heights, some pair of horizontal coordinates admits no
  estimate `yH(y)−a log y−b=O(y^α)` as `y→0+` whenever
  `α>1/2−Re p`. Here `H` is the actual nonvacuum scalar Narain heat sum;
  `a,b` are arbitrary constants. In the zeta variable `ρ=1+2p`, the
  boundary is `α≤1−Re ρ/2`.

## Proof

The mass gap and Gaussian convergence give local continuity of `H` and
`|H(y)|≤B exp(−cy)` for `y≥1`, with `c>0`. Suppose the displayed remainder
bound holds. Put
`g(y)=H(y)−1_(0,1](y)(a log y+b)/y`.
Then `g=O(y^(α−1))` at zero and decays exponentially at infinity.
Its Mellin transform is holomorphic on `Re s>1−α`.

Write `s=1/2+u`, `w=u−1/2`, `D(u)=ξ(1+2u)`, `c(u)=u(1+2u)`.
The cutoff main term has Mellin transform `−a/w²+b/w` on `Re w>0`.
For each target modulus, define the entire filled numerator

`T(u)=(2u−1)Y^(1/2+u)D(u)+(1+2u)ξ(2u)Y^(1/2−u)`
`       +(2u−1)(1+2u)(2u)Tail(u)`.

Away from `u=1/2`, this is `(2u−1)N(u)`. The actual scalar Mellin identity
therefore gives

`c(u)D(u)[w² Mellin(g)(1/2+u)−a+bw]=T₁(u)T₂(u)/2`.

Both sides are holomorphic on `Re u>1/2−α`; uniqueness extends the identity
from the absolute-convergence half-plane. At `u=p` the left side vanishes.
The proved horocycle detector chooses targets with `N₁(p)N₂(p)≠0`.
Since `2p−1≠0`, the right side is nonzero, a contradiction.

This proves an obstruction to faster decay. It does not prove any
RH-strength remainder estimate. Multiple zeros need no simplicity assumption.

The same filled numerator exposes the universal main pole: `T(1/2)=1`,
`c(1/2)=1` and `D(1/2)=ξ(2)=π/6`. Consequently the principal-part
limit for the continued transform is `(s−1)² M_H(s)→3/π`, independently of the target moduli.
This fixes the logarithmic main coefficient `−3/π`. Evaluating the extended cleared
identity at `u=1/2` also forces `a=−3/π` in any positive-power remainder,
without assuming that such a remainder exists.

## Lean

All modules lie in `ArithmeticScatteringHolography/ModularBootstrap/`.

- `NarainHeatRegularity.lean`: [continuity, local integrability and exponential tail](ads3-narain-heat-regularity.md).
- `ScalarMellinMainTerms.lean`: cutoff logarithmic Mellin identity and convergence.
- `NarainPoleClearing.lean`: entire filled numerator, cleared source identity
  and `tendsto_narainMellin_mainPole`, with coefficient `3/π`.
- `NarainDecayBoundary.lean`: `exists_narainScalarHeat_no_faster_decay`
  and `narainScalarRate_log_coefficient`.

All four modules pass their direct `lake --old env lean` checks without
warnings. All twelve endpoint axiom audits contain only `propext`,
`Classical.choice`, `Quot.sound`. The topic umbrella imports all four.
No rate or zero-location hypothesis is assumed in the obstruction theorem.

## Gates

- [x] 0 → 1: pole location and precise decay exponent identified.
- [x] 1 → 2: all analytic inputs discharged for the literal source.
- [x] 2 → 3: direct Lean check, transitive axiom audits and umbrella imports.
