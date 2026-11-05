# Effective horizons for finite sign tests

- **ID:** effective-finite-sign-horizons
- **Stage:** 3-formalized
- **Type:** THEOREMS (Lean 4)
- **Source:** review-0511 §2.1, A18.

## Results

Explicit fixed-degree Jensen horizons, finite-data two-grid detector degrees,
and Hausdorff shifts are formalized. Every bound is a finite expression;
none chooses a threshold from qualitative convergence.

Explicit Hausdorff shifts are [formalized](explicit-symmetric-zero-mass-and-hausdorff-shifts.md).

Pólya frequency order beyond 37 is already supplied by
`RHTower.xi_centre_pfSeq_fortyFive` in `XiSliceCoeffOrderTwentyThreeBand.lean`.
Its direct source check and transitive axiom audit passed; the owning umbrella
imports it. Only `propext`, `Classical.choice`, and `Quot.sound` occur. This is
existing mathematics, not a new theorem.

## Explicit Hausdorff shifts

With `K=10(k+1)+20`, the explicit bound is

`r₀=⌈20K⌉+⌈K·max(Z(1/500),500,42(k+1)+44K)²⌉+1`.

Here `A(ε)=max(4,exp(20/ε),200/ε)` and
`Z(ε)=max(A(ε/2)+1,6/(πε)+3,8)`. The explicit symmetric zero-mass theorem
holds at every height `T≥Z(ε)`. Three direct source checks, six transitive axiom
audits and umbrella wiring are complete.

The [two-grid degree bound](explicit-two-grid-detection-degrees.md)
is formalized, with explicit source polynomials, arbitrary odd offsets and pole
cancellation. Its bound retains finite spectral separation products. Both direct
source checks, eight axiom audits and umbrella wiring passed.

[Jensen horizons](explicit-jensen-real-rootedness-horizons.md) preserve the
Hermite signs using explicit source-moment error bounds and finite algebraic
root margins. `RHTower.xiJensenPoly_splits_of_horizon_le` proves splitting at
every shift above the stated expression. Four direct source checks, twelve
transitive axiom audits and umbrella wiring passed.

The two-grid degree bound depends on finite sampled spectral separation data;
it is not a bound in height and off-line depth alone.
