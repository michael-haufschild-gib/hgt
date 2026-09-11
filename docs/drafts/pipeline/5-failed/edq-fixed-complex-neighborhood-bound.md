# EDQ: fixed complex neighborhood as a Cauchy input

Status: false strengthening. EDQ and its original endpoint estimate remain open.

The rejected input is a subpower energy upper bound, uniform on a fixed
complex neighborhood of the original parameter `z=1`, for the complete
prime-count deformation `P_N(z)`.

The positive survivor is a precise growth law: on every fixed circle of
positive radius, and for every epsilon>0, its maximal energy lies between
`c N^(1-epsilon)` and `C N^(1+epsilon)` eventually, with positive constants.
The maximum is attained. Thus its power exponent is exactly one. Any fixed
neighborhood contains a fixed circle, so the proposed uniform subpower
input is false.

The dependency-closed paper proof and Lean status are recorded in
[the formalized growth-law card](../3-formalized/edq-prime-count-complex-neighborhood.md).
The exact Lean theorem is
`RHTower.PrimeCountDamping.complexSource_circle_energy_growth` in
`EulerDeletionPrimeCountCircleGrowth.lean`; its leaf audit passed.

The proof retains the complete physical carrier, transports the proved
aperture lower bound by finite polynomial extrapolation, and controls that
transport by the divisor bound. It neither lower-bounds the value at `z=1`
nor rules out shrinking neighborhoods. An estimate directly at that
endpoint still requires the missing signed arithmetic cancellation.
