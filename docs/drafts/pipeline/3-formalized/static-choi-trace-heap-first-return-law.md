# Static Choi trace-heap first-return law

- **Stage:** 3 -- formalized
- **Status:** `[UNCONDITIONAL] [LEAN-CERTIFIED] [FRONTIER ADVANCE] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-21
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/StaticChoiTraceHeapFirstReturnLaw.lean`
  - `formal/GaloisForLFunctions/RHTower/NearestNeighborGaussianSameDrawTraceHeapLaw.lean`

## New result

For a finite local gate alphabet, let independent letters denote commuting gate actions and assume
each letter is dependent on at most `Delta` letters.  The complete circuit set of gate count at most
`s` has no larger endpoint occupation cost than

```text
K(s, Delta) = choose(|alpha| + s - 1, s) * 2^(Delta*s).
```

Identity padding places every shorter circuit endpoint on the exact `s` shell, so there is no sum
over depths.  For a maximally projective static spectrum, normalized gate actions, radii
`0 < epsn < epsw`, and block width `W`, define

```text
b = K(s, Delta)
    * D exp(D/2) sqrt(pi * (sqrt(2)*epsw)^2)^(D-1),
m = (epsw - epsn) / projectiveChoiSpeed.
```

If

```text
b < m / (W + m),
```

then arbitrarily late times contain a continuous interval of width `W` whose Choi channel is more
than `epsn` in pure-state trace distance from every circuit endpoint of gate count at most `s`.
That block lies strictly between consecutive visits to the same complete bounded-depth circuit
set.  Hence its right endpoint is a literal first re-entry and the excursion length is at least
`W`.

This criterion has a matching inverse-occupation realization.  Whenever `0 < b < 1`, Lean proves
that one may choose

```text
W >= (m / 2) * (b^(-1) - 1).
```

Thus exponentially small circuit occupation certifies an exponentially long consecutive-return
gap; the theorem does not merely assert an unspecified positive duration.

The final theorem binds this plateau and first re-entry to the same ordinary time-independent
nearest-neighbour Gaussian Hamiltonian draw that supplies the already-proved robust laboratory-time
linear complexity ramp.  No Hamiltonian redraw, time-dependent noise, or independent time samples
occur.

A closed existence theorem uses positive Gaussian measure of the growth--maximal event to select
such a draw.  The draw is no longer a premise: under the explicit finite-size laboratory and
entropy inequalities, one ordinary product-Gaussian nearest-neighbour Hamiltonian exists with both
the ramp and the inverse-occupation first-reentry gap.

## Principal declarations

- `RHTower.maximallyProjective_projectedTraceWords_explicit_late_hard_intervals`
- `RHTower.maximallyProjective_pureTraceWords_explicit_late_hard_intervals`
- `RHTower.maximallyProjective_commutingGateWordsAtMost_explicit_late_hard_intervals`
- `RHTower.maximallyProjective_commutingGateWordsAtMost_explicit_consecutiveVisitGap`
- `RHTower.nearestNeighborPath_sameDraw_growth_lateTraceHeapPlateau_firstReturn`
- `RHTower.exists_inverseOccupation_hardBlockWidth`
- `RHTower.exists_nearestNeighborPath_sameDraw_growth_positiveTraceHeapFirstReturnGap`

## Conjecture / failure / proof ledger

- **C1: free-word counting is intrinsic.** Failed.  Independent adjacent swaps preserve endpoints.
- **C2: shorter depth shells require another union bound.** Failed.  Identity padding preserves the
  endpoint and places every depth-`<=s` circuit on the exact `s` shell.
- **C3: completed occupation cannot imply first re-entry.** Failed.  Continuity makes capture times
  closed; recurrence supplies visits on both sides; extremal selection gives consecutive visits.
- **C4: trace occupation yields an initial Brown-time plateau.** Failed.  The argument gives
  arbitrarily late blocks and a quantitative width, but no upper bound on their first onset.

## Exact remaining frontier

This closes the full bounded-depth circuit union and its same-draw first re-entry at plateau scale.
It does **not** close the complete Brown--Susskind law because the plateau block is not yet aligned
with the end of the laboratory ramp.  Remaining theorem is preparation-sensitive autonomous
Bellman escape on the `O(n)` geometric time skeleton for one fixed local draw.  Neither spectral
equidistribution nor another target-capacity estimate can supply that onset.
