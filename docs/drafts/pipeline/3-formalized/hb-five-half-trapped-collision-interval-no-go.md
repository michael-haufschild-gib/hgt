# HB five-half trapped-collision regularity no-go

## RH chain cut

Horizontally robust five-half Xi collision trapping → universal literal HB source extinction →
BM darkness → HB / FZZ-P / RBH / PW-B → RH.

Lebesgue-regular five-half Xi collision source → literal HB source extinction → BM darkness →
HB / FZZ-P / RBH / PW-B → RH.

Both initial mechanisms are impossible.

## Formal result

The real part of the remaining five-half collision step is

`x ↦ if 3/5 < x then 5x/2 - 1 else 2 - 5x/2`.

The point `3/5` immediately leaves the unresolved band `[8/15, 2/3]`. Any nondegenerate interval
of perpetually trapped points must therefore stay on one branch at each iteration. Each iteration
expands its length by `5/2`, while the interval must remain inside a band of width `2/15`, a
contradiction.

More strongly, each of the two affine inverse branches scales Lebesgue measure by `2/5`.
The `n`th finite trapped approximation therefore loses at least a `1/5` share per step:

`volume A_(n+1) ≤ (4/5) volume A_n`.

Geometric decay proves `volume xiFiveHalfRealTrappedSet = 0`.

Premise-free capstones:

- `hbXiFiveHalfHorizontallyRobustTrappedCollisionProducerRouteKilled`.
- `hbXiFiveHalfRegularTrappedCollisionProducerRouteKilled`.

## Consequence and survivor

The trapped alternative left by `xiFiveHalf_trapped_orbit_dichotomy` cannot carry any nonzero
horizontal source measure absolutely continuous to Lebesgue measure. Any surviving all-collision
producer must be singular in horizontal real part; atomic or singular-Cantor configurations remain.
This does not close HB or RH.

## Novelty and verification

Corpus deep search found no prior interval or measure theorem for this exact five-half Xi
source-collision survivor. Literature searches through August 2026 found general Xi-zero dynamics
but no result for this affine collision law.

Verified directly:

```text
lake env lean GaloisForLFunctions/RHTower/XiFiveHalfTrappedCollisionIntervalNoGo.lean
```

Result: exit 0 under a 20-second guard. No `lake build` was run.
