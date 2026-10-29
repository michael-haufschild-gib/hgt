# The density-matched lattice boundary is `X²=T`

- **ID:** density-matched-length-height-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; overlap-length-height-dictionary.
- **Statement:** For the paired lattice at density `log T/(2π)`, the position and depth mimics
  agree on aperture `log X/2` exactly when `X²≤T`. A negative off-line test exists exactly
  when `T<X²`.

## Gates

- [x] Source declarations inspected in `PositionAndDepthShareOneNyquistAperture.lean`.
- [x] Dependency-closed paper proof below.
- [x] Direct Lean check and transitive axiom audits pass; SRT umbrella import added.

## Paper proof

The double on-line lattice, simple half-spacing lattice, and off-line lattice pair each have
density `L/π`. Matching `log T/(2π)` sets `L=log T/2`. The existing sharp theorem says that
both pairs of forms agree on every compact `C²` test in `[-a,a]` exactly when `a≤L/2`.
With prime cutoff `X=exp(2a)`, this is `log X/2≤log T/4`, equivalent to `X²≤T`.

If `T<X²`, the existing two-bump construction supplies a negative off-line test. Conversely,
if `X²≤T`, agreement with the nonnegative on-line form excludes every negative test.
At atomic touching `X=T>1`, one has `T<T²`, so this matched lattice already admits a negative
test. These are exact model statements, not claims about zeta's actual zeros.

## Formal anchors

Module: `formal/GaloisForLFunctions/SquareRootThreshold/DensityMatchedLengthHeightBoundary.lean`.

- `densityMatchedPeriod_density`
- `aperture_le_densityMatchedPeriod_half_iff`
- `densityMatched_lattices_agree_iff`
- `densityMatched_negative_test_iff`
- `densityMatched_negative_at_atomic_touching`

Validation: `lake --old env lean GaloisForLFunctions/SquareRootThreshold/DensityMatchedLengthHeightBoundary.lean`
from `formal/`, exit 0. The three main classification/witness declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Rejected inference and positive survivor

The report's identification of this SRT aperture with the atomic boundary `X=T` does not
survive matching both multiplicity and density. The positive survivor is the complete
position/depth classification and negative-test converse above. It distinguishes two exact
boundaries and prevents transporting a model obstruction across a factor-of-two aperture error.

## Log

- 2026-10-29 — Formalized and axiom-audited; umbrella wired without compiling the umbrella.
