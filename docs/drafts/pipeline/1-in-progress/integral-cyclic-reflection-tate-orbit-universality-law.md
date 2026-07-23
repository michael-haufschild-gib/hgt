# Integral cyclic/reflection Tate orbit universality law

## Status

- Stage: 1-in-progress
- Lean target: `GaloisForLFunctions.RHTower.IntegralCyclicReflectionTateOrbitUniversalityLaw`

## Theorem-generated route

Source statements were read before synthesis:

- `reflectionTateCocycle_is_boundary_iff_fixed_even`
- `fixedMirrorUnit_not_boundary`
- `freeMirrorPair_is_boundary`
- `integralUnitExtension_tate_separates_fixed_free`
- `cyclicTate_separates_fixed_regular`

The concrete integral norm/charge at a fixed orbit is definitionally the order-two cyclic model.
The abstract reflection classification then says the one-point fixed unit is nonboundary, while
the fixed-point-free two-cycle has no anomaly class at all.  This identifies the concrete
extension residue with the fixed-locus parity quotient rather than merely juxtaposing two
separation statements.

## Candidate law

Canonical integral unit-extension descent is exactly stabilizer support: its unit residue survives
on a fixed orbit, dies on a free orbit, and is the order-two instance of the corresponding
fixed/regular law for every nontrivial cyclic order.

## Open audits

- Exact Lean check
- Axiom audit
- Literature novelty audit
