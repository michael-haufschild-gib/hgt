# The logarithmic renewal average reads the boundary

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For measurable `h` continuous from the right at zero, `u(x)=∫₀ˣv(t)h(x-t)dt` satisfies `u(x)√log(1/x)→h(0)` as `x↓0`.

## Proof

Positivity and monotonicity give `V(x)≥xv(x)>0`. The normalized convolution
`u(x)/V(x)` is a positive weighted average. Its distance from `h(0)` is at
most `sup₀≤s≤x |h(s)-h(0)|`. The estimate includes absolute integrability of
the local error. Right continuity therefore gives `u(x)/V(x)→h(0)`.
Multiplying by the proved limit `V(x)√log(1/x)→1` gives the stated exact scale.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheLogarithmicRenewalAverageReadsTheBoundary.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logarithmicRenewalMass_pos`
- `norm_logarithmicBoundaryAverage_sub_le`
- `tendsto_logarithmicBoundaryAverage`
- `tendsto_logarithmicCausalConvolution_normalized`

Production plain audit passed. Transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`; the umbrella imports the module.
Actual Weil traces still require forcing extension and backward-convolution continuity.
