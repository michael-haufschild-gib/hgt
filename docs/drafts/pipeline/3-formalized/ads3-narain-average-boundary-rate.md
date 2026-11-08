# The unconditional boundary rate of the averaged Narain source

- **ID:** W11-NB
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Sharp-rate equivalence](../0-backlog/ads3-narain-average-sharp-rate.md)
- **Statement:** For every positive target-height pair `Y,Z`,
  `yA_YZ(y)+(3/π)log y−B_YZ = o(y^(1/2))` as `y→0+`.

Here `A_YZ=narainScalarHeatAverage Y Z` is the actual double horocycle
heat average and `B_YZ=narainAverageConstant Y Z` its exact constant term.

## Proof

Write `M(s)=narainMellinMean Y Z (s−1/2)`. Its equality with the
Mellin transform of the actual average on `Re s>1`, central removability,
and residue `Res_(s=1)[y^(−s)M(s)]=y⁻¹[B_YZ−(3/π)log y]`
are already formalized.

The filled numerator has strip bound
`|T_Y(u)|≤C(1+|Im u|)^N exp(−π|Im u|/2)`.
Its product and the corpus's damped reciprocal-xi bound give
`|M(1/2+u)|≤C(1+|Im u|)^N exp(−π|Im u|/2)|ζ(1+2u)⁻¹|`
for `|Im u|≥1`. On `Re u=0`, the proved polynomial bound for
`ζ(1+2it)⁻¹` gives integrability; the removable center supplies continuity.
On `Re s=2`, the Euler-region bound gives integrability directly.

Shift the Mellin contour from `Re s=2` to `Re s=1/2` along heights
`goodHeight k/2`. The corpus's reciprocal-zeta bound at those heights,
combined with the exponential numerator bound, makes both horizontal
edges vanish. The sole crossed pole is the double pole at `s=1`.
Consequently the normalized remainder is a Fourier transform of the
integrable boundary value `t↦M(1/2+it)`, evaluated at `log y`.
Riemann–Lebesgue gives the stated little-o limit.

## Lean endpoints

Main theorem:
[`narainScalarHeatAverage_boundary_rate`](../../../../formal/GaloisForLFunctions/ArithmeticScatteringHolography/ModularBootstrap/NarainAverageBoundaryRate.lean).
The exact remainder identity is `narainScalarHeatAverage_boundary_identity`;
`narainMeanMellin_contour_shift` supplies its residue calculation.

Supporting modules in `ArithmeticScatteringHolography/ModularBootstrap`:
`NarainMeanStripBounds`, `NarainMeanVerticalBounds`, `NarainMeanHalfPlane`,
`NarainMeanLineBounds`, `NarainMeanHorizontal`, `MellinBoundaryDecay`,
`NarainMeanContour`, `NarainAverageBoundaryRate`.

All eight modules passed final direct Lean checks. Seventeen endpoint
axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.
All umbrella imports are wired. Both Mellin lines are absolutely integrable;
all actual-source inversion and contour premises are discharged.

This proves no exponent above `1/2` and supplies no RH-strength rate.
The [quantitative saving](../3-formalized/ads3-narain-quantitative-boundary-saving.md)
is also formalized and gives every fixed logarithmic saving.

## Gates

- [x] 0 → 1: exact source, pole, boundary and horizontal-edge inputs identified.
- [x] 1 → 2: actual-source contour proof and Fourier boundary limit complete.
- [x] 2 → 3: direct Lean checks, transitive axiom audits and umbrella imports.
