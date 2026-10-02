# Completed doubling does not give uniform negative payment

- **ID:** MC-SOURCE-C02
- **Stage:** 5-failed
- **Type:** FALSIFIED mechanism; THEOREM (Lean) positive survivor
- **Source:** Route MC, legacy E; `../1-in-progress/mc-source-cancellation-loop-2026-10-01.md`.
- **Statement:** Completing denominator cofactors before pairing `a` with `2a` does not extend prime-pair negativity to every odd squarefree numerator.

## Goal

Produce collective source cancellation from the known negative prime/double payment. The tested extension was a common negative sign after completing each numerator fibre. Only this extension is retired; route MC remains open.

## Exact obstruction and positive survivor

Write `F_r(a,q)=routeEFixedOrderIntegerNumeratorFibre r a q`. For every positive odd squarefree `a`, prime `q≥2048a`, and `1≤r≤2`,

`μ(a) [F_r(a,q)+F_r(2a,q)] ≥ (1/64) a q^(-(r+1)) > 0`.

Thus the completed pair has exactly the Möbius sign of its odd core. Moreover, for every `N`, there are odd squarefree `a,b>N` and one prime `q≥2048 max(a,b)` such that the `a` pair is negative and the `b` pair is positive, simultaneously for every `r∈[1,2]`.

**New insight:** completing all physical denominator cofactors does not remove the parity obstruction. It reverses the individual-fibre orientation while preserving an uncontrolled signed sum over odd cores. The global problem is a comparison of opposite-parity core magnitudes with moving cutoff terms retained.

## Dependency-closed paper proof

Set `m=μ(a)`, `t=q^(-(r+1))`, and `M_a=Σ_(0<d<q,(d,a)=1) μ(d)d^(-(r+1))`. The existing linearization theorem gives

`F_r(a,q)=-m r a t M_a+e_a`, with `|e_a|≤24a²q^(-(r+2))`.

Odd squarefreeness gives `μ(2a)=-m`, `m²=|m|=1`. Therefore the oriented pair has main term `r a t(2M_(2a)-M_a)` and error at most `120a²q^(-(r+2))`. The existing moment-payment theorem gives `2M_(2a)-M_a≥7/90`. The far-cone assumption bounds the error by `(15/256)at`; since `r≥1`, the claimed `(1/64)at` margin follows.

For the unconditional common-denominator existence theorem, choose odd primes `p>N` and `l>p`, then a prime `q≥2048pl`. Take `a=p`, `b=pl`. Their Möbius signs are `-1` and `1`. Prime existence, squarefreeness and coprimality are proved within Lean. No numerical experiment, RH premise, or source estimate is assumed.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/RouteECompletedDoublePairParity.lean`.

- `RHTower.routeE_completed_double_pair_margin`
- `RHTower.routeE_completed_double_pair_parity`
- `RHTower.routeE_completed_double_pairs_both_signs`

Imports the existing `RouteEFixedOrderTwoGradeOverpayment` dependency chain. Wired into `formal/GaloisForLFunctions/RHTower.lean`; generated declaration indexes refreshed. No heartbeat increase or new axiom.

- `lake build --old GaloisForLFunctions.RHTower.RouteECompletedDoublePairParity`: PASS. Only the two needed leaf modules rebuilt; remaining dependencies replayed.
- `lake env lean GaloisForLFunctions/RHTower/RouteECompletedDoublePairParity.lean`: PASS, no output or warnings.
- Separate `/tmp` `#print axioms` audit of all three declarations: exactly `[propext, Classical.choice, Quot.sound]`; no added or unproved axioms.
- `scripts/formal_tools.py index`: PASS.
- `scripts/formal_tools.py lint`: repository gate FAIL on ten unrelated modules unreachable from the RHTower umbrella. No forbidden-declaration finding was reported. Unwired modules at that audit: CCMApertureChainProfile, CCMApertureTranslationChains, CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation, CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower, MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase, ZetaZeroDensityPowerSaving. This module was wired and was not among the findings.

## Remaining hard problem

Prove a half-power estimate for the complete signed source. This result supplies no such bound and proves neither RH nor its negation. The next conjecture concerns collective finite-cutoff cancellation across odd cores; another fixed insertion grade or infinite-moment reweighting is insufficient as a proof argument.
