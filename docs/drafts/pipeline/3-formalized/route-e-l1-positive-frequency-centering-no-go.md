# Route E ℓ¹ positive-frequency centering no-go

## Status

`[FORMALIZED]` Paper proof and unconditional Lean proof closed. Frontier map unchanged/read-only.

## RH chain closed

`literal squarefree Ramaré source`
`→ source-faithful scalar centering`
`→ conditional-negative incidence control`
`→ strict Ramaré mean square`
`→ Möbius half-power`
`→ RH`.

Regular infinite centering step is impossible; this kills that proof-chain branch.

## Theorem

For nonempty `ramareSquarefreeActiveSet P M`, no compensation `b : ℕ → ℂ` can satisfy all of:

1. `Summable (fun n => ‖b n‖)` and `b 0 = 0`;
2. `b n = 0` on literal squarefree Ramaré support;
3. source-plus-compensation positive-natural log-frequency series vanishes on a nondegenerate
   interval.

Lean:
`not_routeERamare_sourceFaithfulLOnePositiveFrequencyCentering`.

Exact source expansion:
`routeERamareLOneCenteringBoundary_eq_tsum`.

Reusable analytic core:
`LSeries_coeff_eq_zero_of_l1_boundary_interval`.

## Proof core

Absolute summability makes the ordinary Dirichlet series continuous on the closed right half-plane
and holomorphic inside. Zero-extend it across the vanishing boundary interval. Morera reflection
makes the extension holomorphic; identity theorem gives zero on the right half-plane; successive
Dirichlet coefficient extraction forces every coefficient zero. Source faithfulness leaves a
squarefree coefficient `μ(n)=±1`, contradiction.

## Exact survivors

- source-overlapping coefficientwise cancellation;
- non-`ℓ¹`/singular compensation;
- negative/two-sided frequencies;
- collective Ramaré control that does not center the scalar packet.

## Novelty audit through August 2026

Hardy/Schwarz boundary uniqueness is classical. Corpus and literature searches found no prior
classification applying it to source-faithful infinite Ramaré compensation. Novelty claim is the
Route E obstruction/classification, not the analytic uniqueness engine.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Sieve/RouteERamareL1PositiveFrequencyCenteringNoGo.lean`
- `lake build GaloisForLFunctions.RHTower.Sieve.RouteERamareL1PositiveFrequencyCenteringNoGo`
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- wired into `GaloisForLFunctions/RHTower.lean`
