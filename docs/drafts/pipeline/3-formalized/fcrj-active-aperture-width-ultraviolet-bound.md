# FCRJ active-aperture width ultraviolet bound

- **ID:** FCRJ-AAWUB
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper-proven; Lean implementation complete, lint promotion pending)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 64
- **Statement:** Active physical aperture width controls primewise dipole chord and hence complete
  raw FCRJ ultraviolet energy.

## Goal

For `A>0`, finite prime aperture `P`, every active clipped interval, width `0<=k-m`, total endpoint
weight `W`, and `N>=1`, prove

```text
D <= (2 pi/A) L,                                      (AW1)
L <= (k-m) W,                                         (AW2)
N sum_(n>N)|a_n|^2 <= (2A/pi) N (k-m) W^2,            (AW3)
```

where `D` is weighted endpoint chord, `L` weighted clipped-interval length, and `a_n` raw FCRJ
character amplitude.

## Gates

- [x] 0 → 1 in-progress: corpus search, primary-literature audit, frozen source statement
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile constant audit
- [x] 2 → 3 formalized: exact Lean theorem, direct check, targeted build, and standard-axiom audit; global lint blocked only by unrelated modules
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. Physical endpoints are explicit clipped values `max 0 (m-log p)` and `min A (k-log p)`.
2. `xiPhysicalPrimeLogApertureWeightedLengthMass` is exact weighted interval-length source.
3. `GaloisForLFunctions.HTGeometry.norm_exp_sub_exp_le` is unit-circle arc-to-chord Lipschitz law.
4. Loop 63 gives raw tail `<=A^2/(4pi^2) * 4NWD`.
5. Corpus search found no source theorem eliminating `D` in favor of aperture width.

## External frontier `[LITERATURE]`

Chord-below-arc and Fourier/transport interpolation are classical. Targeted current search found no
clipped prime-log aperture formula `(AW1)--(AW3)` or FCRJ ultraviolet application. Novelty claim is
restricted to exact physical specialization and route consequence.

## Conjecture loop A — use clipped length without activity

`[FALSE]` When raw endpoints reverse, clipped length is zero but literal endpoint chord need not be;
`D<=const*L` requires activity. Raw amplitude differentiation already has same activity condition.

## Conjecture loop B — active width law

`[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]` `(AW1)--(AW3)` hold.

### Paper proof plan

Activity turns clipped length into `end-start>0`. Fourier character has angular speed `2pi/A`, so
chord is at most `(2pi/A)length`; weighted summation proves `(AW1)`. Since `start>=m-log p` and
`end<=k-log p`, every active length is at most `k-m`; weighted summation proves `(AW2)`. Substitute
both into loop-63 raw energy and simplify constants to `(AW3)`.

### Hostile audit

- Activity is necessary and already required by exact raw-amplitude differentiation.
- Clipping at `0,A` only shortens interval, including boundary-touching intervals.
- No prime counting, phase separation, asymptotic, or RH premise enters.
- `(AW3)` still needs moving-scale control of `N(k-m)W^2`; no vanishing is asserted.

## Open core

Lean implementation is complete in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointActiveApertureWidthEnergy.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass; capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Global lint is blocked by unrelated concurrent
unwired modules, so Stage-3 promotion is withheld. Remaining arithmetic burden is moving-scale
control of `N(k-m)W^2`.
