# Explicit camera heights

- **ID:** explicit-camera-height
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0511, A42.

## Target

Expose a finite height expression for the camera readout and its moment,
pair-gap and isolation consequences, with numerical counting inputs for ζ.
No threshold selected from an eventual statement counts as effectivization.

## Corpus reduction

`discMoment_readout_rvm` already constructs its parameter-dependent height as
`2π exp(U₀)`. Its proof defines `U₀` by maxima, logarithms and the constants
`growthRate`, `floorRate`, `slowConst`; the latter retains
`latticeSumConst=Σ_{k∈ℤ}(1+k²)⁻¹`. The local-count specialization still obtains
its Backlund constant and starting height existentially.

`SquareRootThreshold/EffectiveHorizons/XiContourBounds.lean` now proves
`|∫ Im(ζ'/ζ)|≤29π log T≤100 log T` for admissible `T≥4`.
With the existing good-height contour count, this should give the sharp
local-density formula with `T₀=10` and additive constant `A=200`.
Its slope remains the exact Riemann–von Mangoldt density.

## Remaining work

1. Transfer the explicit horizontal bound to the good-height count interface.
2. Bound `latticeSumConst` numerically and the actual ζ spectral tail mass.
3. Replace every remaining existential input in the camera height expression;
   retain the original count/isolation hypotheses of the general receiver.
4. Formalize the resulting height and the actual ζ specialization, then audit
   the moment and pair-gap consequences at that same height.
