# Coulomb/de Sitter zero-mode observability universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- CoulombPhaseIntensityObservability: Coulomb carrier, reflected carrier, unit intensity,
  orientation phase, and Wigner--Smith clock.
- DeSitterBogoliubovIntensityObservability: same observation tuple for arbitrary branch mass and
  angular mode, with lower and upper Gamma shifts.
- GammaIntegerShiftIntensityBlindnessUniversalityLaw: both sectors instantiate a generic
  integer-separated Gamma source law, but does not identify sectors with each other.

Whole-corpus research found no parameter map making Coulomb and de Sitter observable carriers
definitionally equal.

## Universal law

For every Coulomb partial wave ell, choose de Sitter angular mode zero and branch mass
2 ell + 3/2. Both de Sitter Gamma shifts become ell + 1. Consequently original carrier, reflected
carrier, intensity, orientation phase, and Wigner--Smith clock equal corresponding Coulomb
objects exactly; common intensity is one.

## Paper proof

Substitute branch mass 2 ell + 3/2 and angular mode zero into both de Sitter shifts:
1/4 + (2 ell + 3/2)/2 = ell + 1. All five observables are generic opposite-shift Gamma
constructions depending only on these two shifts, so equality follows by substitution. Coulomb
unit-intensity theorem transports to de Sitter sector. No numerical computation is used.

## Lean formalization

Module:
GaloisForLFunctions.HTGeometry.CoulombDeSitterZeroModeObservabilityUniversalityLaw.

Exact command:
lake env lean GaloisForLFunctions/HTGeometry/CoulombDeSitterZeroModeObservabilityUniversalityLaw.lean.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
