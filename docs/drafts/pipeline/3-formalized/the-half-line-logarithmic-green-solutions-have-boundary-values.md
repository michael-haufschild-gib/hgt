# The half-line logarithmic Green solutions have boundary values

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For half-line L² forcing essentially bounded near zero, the actual logarithmic Green solution has a measurable representative satisfying
  `u(x)√log(1/x)→∫₀∞v(y)f(y)dy`. The coefficient is absolutely convergent.

## Proof

The actual causal adjoint is half-line restriction of backward convolution.
Its readout `h(x)=∫v(y-x)f(y)dy` is continuous at zero under the stated essential
local bound. The variational inverse `WW*f` therefore has the measurable
representative `u(x)=∫₀ˣv(t)h(x-t)dt`. Positivity and the exact renewal mass give
`u(x)/V(x)→h(0)`; `V(x)√log(1/x)→1` gives the stated normalization.
Schur adjoint and convolution formulas identify this representative with the
actual L² inverse almost everywhere.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheHalfLineLogarithmicGreenSolutionsHaveBoundaryValues.lean`.
Namespace `GaloisForLFunctions.CanonicalSystemOfTheWindowTower`.

- `logarithmicCausalOperator_adjoint_coeFn`
- `measurable_logarithmicGreenRepresentative`
- `logarithmicHalfLineGreenOperator_eq_representative`
- `integrable_logarithmicGreen_boundary_readout`
- `logarithmicHalfLineGreenOperator_normalized_boundary_limit`

Production plain audit passed; transitive axioms are exactly
`[propext, Classical.choice, Quot.sound]`. Umbrella imports the module.
Actual Weil-source localization remains open.
