# A holomorphic lift of one observable rectangular Weil tail forces RH

- **ID:** `ccm-observable-tail-holomorphic-continuation-rh-criterion`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / TOP-DOWN BRIDGE
- **Scientific status:** `[FORMALIZATION] [NOT AN RH PROOF] [NOVELTY UNASSESSED]`
- **Statement:** If, for one fixed positive rectangular width and one admissible finite cutoff, the
  ordinary Dirichlet series of the observable logarithmic Weil tail admits an independent
  holomorphic continuation to `Re s > 1`, then RH holds.

## Goal

Replace the internally Xi-defined meromorphic continuation by a genuine continuation property of
one scalar coefficient sequence.  The resulting chain is

```text
independent holomorphic lift of one observable rectangular Weil tail on Re s > 1
  -> full-order divisibility of the Xi-cancelled carrier at every right Xi zero
  -> contradiction with its exact multiplicity-minus-one order
  -> no right Xi zero
  -> RH.
```

The holomorphic lift is allowed to agree with the ordinary Dirichlet series only on an arbitrary
far-right half-plane.  No Xi zero location, real-rootedness, or positivity assumption occurs in the
lift property.

## Theorem

The Lean module
`GaloisForLFunctions.RHTower.CCMRectangularObservableHolomorphicCriterion` defines

```text
XiRectangularWeilTailHolomorphicContinuation L N
```

as the existence of a function analytic on `Re s > 1` which agrees with the ordinary tail
L-series for all sufficiently large real parts.  It proves

```text
riemannHypothesis_of_xiRectangularWeilTailHolomorphicContinuation
```

for every `L>0` and every cutoff `N` beyond which `1<=n` and `L<=log(n)/2`.

## Proof

Let `F` be the independent holomorphic lift.  Subtract the entire finite-prefix series and the
bounded-remainder L-series, then divide by two.  This produces a function `A` analytic on
`Re s>1`.  On a far-right half-plane, the observable-tail identity gives

```text
xiRectangularCancelledSeries L s = xi(s-1/2) * A(s).
```

Both sides are analytic on the connected half-plane, so analytic continuation propagates the
identity throughout `Re s>1`.  If a right Xi zero has multiplicity `m`, the product on the right
has analytic order at least `m`.  The exact cancellation theorem gives order `m-1` on the left.
This contradiction excludes every right Xi zero, hence proves RH.

## Boundary

The present Lean coefficient `xiRectangularWeilLogCoefficient` is the multiplicity-exact
zero-side Weil polarization.  Therefore this theorem is a completed divisor-observable bridge,
not yet an unconditional source proof.  The remaining positive producer is:

```text
derive the independent Re s>1 holomorphic lift from the completed prime--Gamma /
critical-Mellin formula for the same rectangular two-edge values.
```

That producer must not define its continuation through the Xi divisor or assume any equivalent
zero-locus, anti-Herglotz, or limiting-positive-measure condition.

## Gates

- [x] 0 → 1 in-progress: source of the continuation hypothesis isolated
- [x] 1 → 2 fully-proven: analytic-continuation and local-order proof complete
- [x] 2 → 3 formalized: exact module compiles without `sorry`, `axiom`, or `opaque`
- [ ] 3 → 4 publication-ready: primary-literature and independent proof audit

## Log

- 2026-07-12 — Formalized the independent holomorphic-lift criterion and isolated the remaining
  prime--Gamma/critical-Mellin producer.
