# Localized heat-zero energy evolution

- **ID:** review-2910-w17-localized-heat-energy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / integration
- **Source:** W17 of the obstacles summary.
- **Statement:** Combine the actual heat-zero velocity, gap-independent pair flux,
  exterior force and forward simplicity into a collision-compatible local energy estimate.

## Existing ingredients checked

`Heat/LocalizedHeatPairForce` bounds each pair by its negative vertical interaction
plus `2M(y²+y'²)`, where M is the Lipschitz constant of the cutoff derivative.
A nonreal conjugate pair contributes exactly `−4w(x)`.
`Heat/HeatExteriorForce.exists_uniform_riemannHeat_exterior_force` supplies the
actual packet `|Re z−X|≤2`, its degree at most `C log X`, and a real-symmetric
exterior field Q with `|Im Q(z)|≤C log X |Im z|`.
`Heat/HeatLocalizedEnergyEvolution` proves the velocity and local simple branches,
then compact-region forward simplicity after every positive time. It currently
ends before the energy derivative or evolution estimate.
`Heat/HeatZeroSumContinuity` proves collision-continuity of the weighted energy.

## Paper calculation and remaining proof obligations

For `E_X=Σ w(Re z−X)(Im z)²`, simple-zero velocity is
`z'=2Σ_{b≠z}(z−b)⁻¹+2Q(z)`. Pair symmetrization and conjugation give

`E'_X ≤ −2Σ_{Im z≠0}w(Re z−X)
        + C(2M+2V+4W) log X Σ_{|Re z−X|≤2}(Im z)²`,

for a nonnegative cutoff supported in `(-1,1)`, bounded by W, with derivative
bounded by V and Lipschitz constant M. The pair error is
`2M(m−1)Σ y²`; use `m≤C log X`. The exterior contribution is at most
`C(2V+4W) log X Σ y²`. No minimum zero gap appears.

The finite-packet identity, derivative of the actual weighted sum, and passage
through collisions must all be formalized. A finite configuration inequality alone
does not finish this task. For the integrated form, a continuous outer cutoff
majorizes the radius-two squared-height sum. Forward simplicity supplies each
short punctured time interval; continuity handles its initial collision.

## Gates

- [x] Corpus search and source statements read.
- [ ] Symmetrized finite-packet inequality with conjugate dissipation.
- [ ] Actual localized energy derivative on simple intervals.
- [ ] Collision-compatible local/integrated evolution theorem.
- [ ] Direct leaf checks, transitive axiom audit, umbrella wiring.
