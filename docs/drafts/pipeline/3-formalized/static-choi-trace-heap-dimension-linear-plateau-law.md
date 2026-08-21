# Static Choi trace-heap dimension-linear plateau law

- **Stage:** 3 -- formalized
- **Status:** `[UNCONDITIONAL] [LEAN-CERTIFIED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-21
- **Parent:** `universal-static-choi-complexity-plateau.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/StaticChoiTraceHeapComplexityPlateau.lean`

## Result

Let `alpha` be a finite local gate alphabet.  Declare two letters independent when their actions
commute, as disjoint-support gates do.  Assume each letter fails to commute with at most `Delta`
other letters.  For exact word length `ell`, adjacent exchanges of independent letters leave the
circuit endpoint unchanged.  The number of semantically distinct trace classes is therefore at
most

```text
choose (|alpha| + ell - 1) ell * 2^(Delta * ell).                 (1)
```

For a static Hamiltonian with spectral dimension `D`, every target ball in the Choi phase torus has
the existing eigenbasis-free bound

```text
B_D(delta)
 = D exp(D/2) sqrt(pi * delta^2)^(D-1).                          (2)
```

The complete local-circuit union consequently has Haar mass and upper completed-time occupation at
most

```text
choose (|alpha| + ell - 1) ell * 2^(Delta * ell) * B_D(delta).   (3)
```

When `(3) < 1`, every maximally projective static spectrum has one finite `L` such that every time
interval of length `L` contains an endpoint farther than `delta` from **every** length-`ell` word.
For a gate alphabet containing an identity action, exact-shell padding upgrades this with no extra
entropy cost to **every word of length at most `ell`**.  The conclusion is proved directly for
commuting gate actions; neither trace invariance nor padding is left as a semantic premise.

## Why this moves the frontier

The former free-word estimate paid `|alpha|^ell`.  With a spatially local alphabet,
`|alpha| = poly(n)` while `Delta = O(1)`.  At `ell = cD`, the logarithm of the binomial profile in
`(1)` is `o(D)` by the already formalized subexponential profile theorem, whereas the dependence
term is `c Delta D log 2`.  For sufficiently small fixed `c>0`, `(3)` is exponentially small in
`D`.  Thus bounded-dependence locality upgrades the certified plateau depth from
`Theta(D / log |alpha|)` to `Theta(D)`.

This is not a word-count cosmetic improvement.  It removes exactly the label-entropy loss caused
by counting different schedules of commuting local gates as different physical targets.  All ball
overlaps are retained, and the projective global phase is removed without measure loss.

## Principal declarations

- `GaloisForLFunctions.RHTower.wordEval_eq_of_traceEq`
- `GaloisForLFunctions.RHTower.fixedTraceWordEval`
- `RHTower.measureReal_iUnion_uniformPhaseDensity_traceWords_le`
- `RHTower.completedTime_zeroAnchoredTraceWordTargets`
- `RHTower.maximallyProjective_traceWordsHardTimes_syndetic`
- `RHTower.maximallyProjective_commutingGateWordsHardTimes_syndetic`
- `RHTower.maximallyProjective_commutingGateWordsAtMostHardTimes_syndetic`

## Hostile boundary

This closes the plateau-height loss for bounded-dependence local dictionaries.  It does **not**
quantify first plateau onset, the syndetic gap `L`, or the first post-departure return.  It therefore
does not yet prove the Brown growth--plateau--recurrence shape.  Remaining hard input is narrower:
prove time-aligned escape to this now dimension-linear plateau for one ordinary static local draw.
