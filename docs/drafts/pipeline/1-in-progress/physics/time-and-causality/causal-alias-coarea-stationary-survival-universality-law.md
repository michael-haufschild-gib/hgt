# Causal alias/coarea stationary-survival universality law

## Status

Law 248; paper proof and exact Lean module audit passed. Literature novelty audit pending.

## Corpus sources

- `RHTower/CausallyAnchoredFutureAliasRegrouping.lean`
- `RHTower/PhysicalCutoffConnectedCoarea.lean`
- `RHTower/PhysicalCutoffConnectedCoareaSuccessor.lean`

## Theorem-first derivation

The causal regrouping theorem weights every future remainder `r` by the local quadratic-root
survival product over `(N / r).primeFactors`. A separate coarea theorem identifies that exact
product with the negative affine physical-cutoff drift for the same prime coordinates. Successor
theorems then classify this drift as stationary and prohibit bounded primitives when it is nonzero.

## Universal law

At every physical cutoff `H`, the causal future-alias formula can be written with each local Euler
survival coefficient replaced by negative coarea affine drift. Thus every regrouped remainder
mode is a cutoff-stationary class. For even gap `h`, every such class is nonzero and no uniformly
bounded successor primitive can absorb it over a cofinal aperture.

## Paper proof

1. Apply `causallyAnchoredFutureAliasRegrouping`.
2. For every remainder `r`, rewrite its survival product using
   `physicalCutoffCoareaAffineDrift_eq_neg_survival`; the two minus signs cancel.
3. Prime-factor membership gives primality of every coordinate in `(N / r).primeFactors`.
4. Apply `quadraticSurvivalRamp_stationary_and_ne_zero` with even gap to obtain cutoff stationarity
   and nonvanishing.
5. Apply `no_bounded_primitive_of_ne_zero` to the nonzero negative-drift survival coefficient.

No numerical pre-certification applies: all claims are exact finite-product identities and logical
consequences of formal source theorems.

## Lean target

- Module: `GaloisForLFunctions.RHTower.CausalAliasCoareaStationarySurvivalUniversalityLaw`
- Capstone: `RHTower.causalAlias_coareaStationarySurvivalUniversality`
- Exact check: `lake env lean GaloisForLFunctions/RHTower/CausalAliasCoareaStationarySurvivalUniversalityLaw.lean`

## Novelty

Pending primary-source literature search after corpus discovery reaches exhaustion.
