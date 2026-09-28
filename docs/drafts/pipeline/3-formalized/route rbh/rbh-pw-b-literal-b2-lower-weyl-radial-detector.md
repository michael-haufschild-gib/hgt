# Literal B2 lower-Weyl radial detector

- **ID:** RBH-PW-B-LWRD
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/rh-current-frontier-map.md · RBH/PW-B literal cyclic Peierls B2
- **Statement:** For a left-half self-copy `q`, either one-branch metric
  residual, either reader side and unit source amplitude, the normalized lower
  Weyl coefficient cannot vanish on both literal radial fibres `R=2` and
  `R=3`.

## Goal

Establish the sharp radial obstruction carried by the existing one-branch
metric residual.  It is not itself a Peierls incidence: the separately proved
same-rate causal-source no-go makes that scalar identification impossible.

## Paper proof

Write `s = physicalRate q branch`, `w = physicalFundamentalFrequency q side`
and use unit source amplitude.  The common radial transport is then nonzero:
the source rate, reader frequency, source/reader gap, profile, exponential
envelope and exterior radius are all nonzero.
The exact radial source identities give a common nonzero transport factor `P(R)`
such that

`bulkOverlapCoefficient = P(R) · (overlapConstant s w + overlapInverseSquare s w / R²)`

and

`cyclicPeierlsCapFluxCoefficient = P(R) · s(s−1)/2`.

The lower square-reader Weyl coefficient is

`L(q) = 1/2 · Λ(2q−1)² · Λ(q−1) · (1−q/2)`.

For `Re q < 1/2`, `L(q) ≠ 0`: `Λ(2q−1)=0` is excluded by the affine
left-half zero theorem, while the reader factors are nonzero.  The literal
fundamental-frequency formula identifies `overlapInverseSquare s w` with the
self-copy normal-form factor; its four branch/side cases each force `Im q=0`
if zero.  Hence `L(q) · overlapInverseSquare s w ≠ 0`.

At the lower Weyl exponent, all cap angular-flux contributions have the same
common `P(R)` and are radial-constant (their full Fourier remainder is rapid).
Therefore the complete lower coefficient has form

`P(R) · (A + L(q) · overlapInverseSquare s w / R²)`

for some `A` independent of `R`.  If it vanished at both `R=2` and `R=3`,
subtracting the two equalities gives

`5 · L(q) · overlapInverseSquare s w = 0`, contradiction.  Both radii are
literal tortoise fibres, not formal substitutions.

## Gates

- [x] 0 → 1 in-progress: exact residual, cap, reader and radial source factors identified.
- [x] 1 → 2 fully-proven: two-fibre algebra closes without a spectral premise.
- [x] 2 → 3 formalized: `lowerWeylRadialDetector_two_or_three_ne_zero` with the physical
  overlap bridge `self_overlapInverseSquare_ne_zero` and the lower factor
  `lowerWeylFaceCoefficient`; see the Lean certificate.
- [ ] 3 → 4 publication-ready: no scalar same-rate transport is admissible.
  A surviving realization must first construct a complementary-rate,
  metric-valued bidegree contact carrier.

## Boundary

This theorem does not assert a causal cap/contact identity.  In particular it
cannot be paired with a same-rate scalar Peierls source: both full and native
pairings, and their lift defect, vanish there.  Its valid use is as a retained
metric-side radial constraint while the complementary-rate bidegree carrier is
built.

## Log

- 2026-09-27: formalized in Lean (leaves compile with `lake --old env lean`, oleans built, wired in
  `RHTower.lean`, `#print axioms` = `propext`, `Classical.choice`, `Quot.sound`); moved to stage 3.
  Certificate: `rbh-pw-b-literal-b2-lower-weyl-radial-detector-formalized.md`.
