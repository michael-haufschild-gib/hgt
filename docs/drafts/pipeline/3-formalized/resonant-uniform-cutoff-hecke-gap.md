# Uniform cutoff obstruction to Hecke quasimodes

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [arithmetic measure rigidity](../1-in-progress/resonant-state-arithmetic-measure-rigidity.md).

## Statement

For every resonant `u` with `-1/2<Re u<0`, `Im u>0`, and every `Y≥1`, put
`κ=-2 Re u`, `N(u,Y)=||Λ^Y E_u||²`, and
`R_(u,Y)=(T₂−(2^u+2^(-u)))Λ^Y_aut E_u`. Then

`∫_fd |R_(u,Y)|² dμ ≥ κ N(u,Y)/1024`.

## Proof

For `1≤Y≤33/32`, the rectangle
`R={|x|≤1/4, 7/4≤y≤15/8}` has exactly its central return above `Y`:
`h₀>33/32`, `h_±₁≤1`. Its residual equals the cutoff-one residual, so its
mass is at least `|B(u)|²/512`. Since `0<κ<1` and `Y^κ≤2`, Maass–Selberg
normalization gives the stated bound.

For `Y≥33/32`, use
`S_Y={|x|≤1/2, 63Y/32<y≤127Y/64}`. Here `y>2`, all returns lie below one,
and `Y<y<2Y`. The residual is exactly `B(u)2^u y^(1/2-u)`. Its density in
`dx dy` is `|B(u)|²2^(-κ)y^(κ-1)≥|B(u)|²Y^κ/(4Y)`.
The band has area `Y/64`, yielding mass at least `κ N(u,Y)/256`.
Lean integrates the equivalent quadratic height test against hyperbolic volume.

The coordinate remainder and three modular return terms are measurable and
bounded on `fd`; this proves global square integrability before either
local-to-global comparison.

## Positive survivor

For every `Y≥1`, the full residual is exactly

`R_(u,Y)=heckeRemainder(2,u,Y,y)−B(u)/√2 Σ_(k=-1,0,1) 1_(h_k>Y) h_k^(1/2-u)`.

Every return height is at most two on `fd`. Consequently, for `Y≥2`,

`∫_fd |R_(u,Y)|² dμ = N(u,Y)(2^κ−2^(-κ))`.

The [compact-core weak limit](resonant-core-source-limit.md) retains the real
parameter in a strictly positive density. These exact sources, rather than a
vanishing-error eigen-equation, remain inputs to any arithmetic recurrence law.

## Lean and audit

Modules in `RenormalizedIntersectionTheory/ResonantStates`:

- `HeckeCutoffSource`: `automorphic_dyadic_correction_at`,
  `dyadicEigenResidualAt_eq`, `returnHeight_le_two`,
  `dyadicEigenResidualAt_integrable_norm_sq`, `dyadicEigenResidualAt_mass_of_two_le`.
- `UniformHeckeResidual`: `dyadicEigenResidualAt_eq_one_on_core`,
  `dyadicEigenResidualAt_eq_upperBand`,
  `dyadicEigenResidualAt_large_cutoff_mass_lower`,
  `dyadicEigenResidualAt_small_cutoff_mass_lower`,
  `dyadicEigenResidualAt_uniform_mass_lower`.

Both modules passed direct `lake --old env lean` checks. The uniform bound,
global integrability and exact mass have only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms. Modules are imported by the umbrella.

## Boundary

No choice of a single cutoff gives an `L²` Hecke-quasimode approximation when
the real parameter stays negative away from zero. This includes the critical
rate and therefore supplies no critical-line selector. Arbitrary complex
superpositions of cutoffs require a separate [packet bound](../1-in-progress/resonant-cutoff-packet-gap.md).
