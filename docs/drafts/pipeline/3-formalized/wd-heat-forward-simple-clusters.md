# Forward simplicity of arbitrary heat-zero clusters

- **ID:** wd-heat-forward-simple-clusters
- **Stage:** 3-formalized
- **Source:** [Localized heat energy](wd-heat-localized-energy-flux.md)
- **Lean:** `RHTower/Heat/HeatForwardSimpleZeros.lean`
- **Declaration:** `RHTower.DeBruijn.exists_ball_simple_riemannHeat_zeros_forward`

## Statement

For every `t > 0` and arbitrary complex center `z0`, there is `r0 > 0`
such that for every `0 < r <= r0`, there is `delta > 0` for which every
zero of `H_s` in `|z-z0| < r` is simple whenever `t < s < t+delta`.
The theorem proves both nonvanishing derivative and multiplicity one.

The center need not be real. The initial zero may have arbitrary
multiplicity; if the center is not a zero, the sufficiently small disk
remains zero free. No uniform duration of simplicity is asserted.

## Proof

Let `k` be the multiplicity at the center. The forward local heat model
is the degree-`k` Hermite polynomial. Its `k` distinct real roots are
already formalized. Choose disjoint small circles around these roots,
on each of which the model has a positive minimum modulus.

The existing local expansion at an arbitrary complex center has error
`O(q^(k+1))`, while the model on each circle has size bounded below by
a positive constant times `q^k`. For every sufficiently small `q > 0`,
the minimum-modulus principle therefore produces one heat zero inside
each circle after scaling and translation. This gives `k` distinct
zeros of `H_(t+q^2)` within `O(q)` of the center. This intermediate
statement, `exists_distinct_riemannHeat_zeros_forward`, also holds at
initial time zero.

For positive initial time, stable local zero counts give total
multiplicity exactly `k` in the isolating disk. The `k` distinct zeros
exhaust that multiplicity. A zero with vanishing derivative would
contribute at least two, contradicting the total. Hence every zero in
the disk has nonzero derivative and multiplicity one.

## Verification and role

Final plain check passed without errors or warnings:

`lake --old env lean GaloisForLFunctions/RHTower/Heat/HeatForwardSimpleZeros.lean`

The module is wired into `RHTower.lean`; no umbrella compilation or new
olean generation was needed.

This supplies local simple intervals after collisions. It does not yet
establish weighted zero-sum continuity or integrate the localized energy
inequality. Those steps and the WD arithmetic upper estimate remain open.
