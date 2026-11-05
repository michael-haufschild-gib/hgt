# Effective horizons for finite sign tests

- **ID:** effective-finite-sign-horizons
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511 §2.1, A18.

## Obligations

Give explicit Hausdorff shifts, Jensen horizons, and two-grid detection degrees.
An existential threshold renamed by `Classical.choose` is not an effective bound.

The fourth obligation, Pólya frequency order beyond 37, is already supplied by
`RHTower.xi_centre_pfSeq_fortyFive` in `XiSliceCoeffOrderTwentyThreeBand.lean`.
Its direct source check and transitive axiom audit passed; the owning umbrella
imports it. Only `propext`, `Classical.choice`, and `Quot.sound` occur. This is
existing mathematics, not a new theorem.

## Hausdorff reduction

The existing proof uses `K=10(k+1)+20`, endpoint radius `R`, and

`r₀=⌈20K⌉+⌈KR·max(T₀,500,42(k+1)+44K)²⌉+1`.

Here `T₀` is the unspecified threshold in `exists_xiSymmetricMass_close(1/500)`.
An explicit symmetric zero-mass estimate at relative error `1/500` would make
this shift bound effective. The current mass proof uses an unspecified
horizontal argument bound and convergence of the vertical ratio. These inputs
must be quantified, not assumed.

Jensen and two-grid horizons remain open.
