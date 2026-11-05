# The logarithmic backward convolution has boundary values

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For measurable L² forcing essentially bounded on `(-∞,δ]`, `δ>0`, the literal backward convolution `h(x)=∫v(y-x)f(y)dy` is absolutely convergent for `x<δ` and continuous at zero.

## Proof

For globally bounded forcing, integration against the forcing is a bounded
functional on L¹. Strong continuity of translations of the actual causal
density therefore gives continuity of the convolution.

Monotonicity and unit mass imply square-integrability of `v` on every ray
separated from zero. For `y>δ` and `x<δ/2`,
`v(y-x)≤v(y-δ/2)`. This majorant pairs integrably with remote L² forcing;
dominated convergence gives continuity of its readout at zero.

Split forcing at `δ`. The bounded part and remote part give the full result.
Changing the forcing on a null set leaves the readout unchanged at every
point, so essential local bounds suffice. The same split proves absolute
integrability of the defining integral.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicBackwardConvolutionHasBoundaryValues.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `continuous_logarithmicBackwardConvolution_of_bounded`
- `memLp_logarithmicCausalKernel_away`
- `integrable_logarithmicBackwardConvolution_of_ae_locally_bounded`
- `continuousAt_logarithmicBackwardConvolution_remote`
- `continuousAt_logarithmicBackwardConvolution_of_ae_locally_bounded`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
