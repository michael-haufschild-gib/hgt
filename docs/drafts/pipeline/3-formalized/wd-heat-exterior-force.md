# Uniform exterior force on actual heat-zero packets

- **ID:** wd-heat-exterior-force
- **Stage:** 3-formalized
- **Source:** [Localized heat energy](../1-in-progress/wd-heat-localized-energy-flux.md)
- **Lean:** `RHTower/HeatExteriorForce.lean`
- **Declaration:** `RHTower.DeBruijn.exists_uniform_riemannHeat_exterior_force`

## Statement

There are absolute `C > 0` and `X0 >= 4096` such that for `X >= X0`,
`0 <= t <= 1/8`, and `t log X <= 1`, the zeros of `H_t` with
`|Re a-X| <= 2` form a finite packet `S` of total multiplicity at most
`C log X`. There is a field `Q`, real on the real axis, analytic at every
point of `|Re z-X| <= 1`, `|Im z| <= 1/2`, satisfying

`|Q(z)| <= C log X`, `|Q'(z)| <= C log X`,

`|Im Q(z)| <= C log X |Im z|`.

At every nonzero point in this inner rectangle,

`H_t'(z)/H_t(z) = sum_{a in S} mult(H_t,a)/(z-a) + Q(z)`.

The packet consists of actual heat zeros with actual multiplicities.
The theorem assumes neither simplicity nor separation and includes `t=0`.

## Proof

Use the Euler-anchored local cofactor at `X-16i`. Remove factors with
exponent zero, translate the factorization, and identify its exponents
with analytic multiplicities. The total degree is `O(log X)`.

All heat zeros for nonnegative time lie in `|Im z| <= 1/2`. Consequently
every zero in the horizontal packet lies in the anchored disk and is
one of its factors. The remaining factors have distance at least one
from the inner rectangle. Their pole sum and its derivative are bounded
by their total degree. The cofactor supplies the other `O(log X)` term;
the inner rectangle lies inside its derivative-control disk of radius
`67/4`.

Average this exterior field with its conjugate reflection. The heat
function and the complete local pole packet are conjugation symmetric,
so the logarithmic-derivative identity is preserved. The average is real
on the real axis, and averaging preserves both norm bounds. The mean
value estimate on a vertical segment gives the height factor in the
imaginary-part bound.

## Verification and scope

Final plain check passed without errors or warnings:

`lake --old env lean GaloisForLFunctions/RHTower/HeatExteriorForce.lean`

The module is imported by `RHTower.lean`; the umbrella was not compiled.
No olean was generated for this module because no new file imports it yet.

This supplies the exterior-force input to localized vertical-energy
transport. Internal pair forces, collision passage, and the arithmetic
upper estimate needed for WD extinction remain open.
