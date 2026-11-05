# Real-weight camera and local count transfer

- **ID:** real-weight-camera-and-local-count-transfer
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511, A40.

## Target

Extend the local moment camera to real coefficients with absolute Lorentzian
mass, retaining its aperture and explicit error. Transfer local weighted counts
to positive on-line mimics by band-limited interval majorants and minorants.

## Available inputs

`exists_local_slow_pair` constructs windows from the carrier count, independently
of coefficient values. `tsum_far_le` already handles arbitrary complex coefficients
with summable absolute Lorentzian mass. The remaining moment argument must combine
these inputs without an integer lower bound on a nonzero coefficient.

## Count distinction

The isolating product uses the number of distinct support points. A weighted
count alone cannot provide that number without a positive lower bound on atom
weights. The proposed sharp example is the simple lattice
`{1/2 + πik/L}`, with weight `1/(2L)` per point: for `L≥a`,
`W_simpleHalfLatticeConfig` gives the same normalized form `∫f·conj(g)` at
aperture `a`, while the number of points in a fixed interval grows with `L`.
Formalize this distinction alongside the weighted transfer; it does not refute
transfer of weighted mass.

## Lean obligations

Weighted local moment readout; band-limited interval bounds; weighted count
transfer; exact lattice example separating mass from support cardinality.
No new theorem is yet verified.
