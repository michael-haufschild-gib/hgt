# Sonin physical log-shell probe separation universality law

## Status

In progress — paper proof and Lean source complete; exact check deferred to final module build because
both terminal provenance modules currently lack cached `.olean` files.

## Theorem-first provenance

- `RHTower/SoninLogShellCocycle.lean`
  - `soninPrimePowerLogShellTraceDensity_eq_fluxCoefficient`
- `RHTower/SoninSemilocalProbeUniversalSourceSeparationLaw.lean`
  - `exists_finiteSoninSemilocalRelativeTrace_ne_everyHilbertSchmidtCyclicSourceGenerator`

## Universal law

One finite prime-power test separates the projection-correction relative trace from every nonzero
Hilbert--Schmidt cyclic tangent generator even after the abstract semilocal flux is replaced by the
actual intrinsic physical logarithmic-shell trace density.

## Lean status

Lean source is in
`formal/GaloisForLFunctions/RHTower/SoninPhysicalLogShellProbeSeparationUniversalityLaw.lean`.
Final exact and module checks remain pending under the mandated final audit.

## Novelty status

Pending post-discovery literature audit. Discovery used Lean statements only.
