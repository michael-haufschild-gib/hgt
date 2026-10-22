# Finite affine cyclic moment-residue-character universality law

- **ID:** finite-affine-cyclic-moment-residue-character
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** whole-corpus theorem-generated closure
- **Statement:** Sharp finite cyclic moment vanishing simultaneously determines affine spectrum
  symmetry, characteristic-product character, central multiplicity congruence, signed local order,
  and logarithmic-residue charge.

## Goal

Join finite cyclic moment Torelli with meromorphic equivariant residue quantization on their actual
shared carrier: the centered characteristic product of a finite spectrum.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, proof generated from existing Lean theorems
- [x] 1 → 2 fully-proven: dependency-closed scratch proof
- [x] 2 → 3 formalized: repository exact check passed
- [ ] 3 → 4 publication-ready: deferred until global exhaustion and final audit

## Lean-generated inputs

- `GaloisForLFunctions.finiteAffineCyclicMomentCharacterOrderUniversalityLaw`
- `GaloisForLFunctions.finiteCenteredSpectralProduct_analyticOrderAt_zero`
- `GaloisForLFunctions.HTGeometry.meromorphicEquivariant_residueCharacterLaw`
- `AnalyticAt.meromorphicOrderAt_eq`

## Corpus gap

The RHTower capstone identifies moment vanishing, affine cyclic symmetry, characteristic-product
covariance, and central-multiplicity congruence. HTGeometry independently proves that an equivariant
meromorphic germ's signed order is simultaneously its character exponent and logarithmic-derivative
residue. No theorem applies the latter to the centered characteristic product and closes all five
faces into one equivalence.

## Proof

Use the existing moment-character-order equivalence to obtain cyclic covariance. The centered
characteristic product is analytic, and its analytic order at zero is the number of spectral points
at the affine center. Transport this equality to meromorphic order, then apply the meromorphic
residue-character law to rotation by the primitive root. The reverse implication forgets the two
new consequences.

No numerical computation is used.

## Novelty status

Post-proof searches found adjacent work on cyclic power sums, equivariant meromorphic functions,
logarithmic derivatives, divisor residues, and character sectors. No searched source stated the
exact equivalence joining the sharp finite centered-moment block, affine cyclic multiset symmetry,
the characteristic-product character, center-multiplicity congruence, signed order exponent, and
logarithmic-derivative residue. Novelty claim is restricted to this joint connector; Newton/Torelli
recovery, cyclic orbit counting, and residue-equals-order are classical ingredients.

## Lean result

`formal/GaloisForLFunctions/RHTower/FiniteAffineCyclicMomentResidueCharacterUniversalityLaw.lean`
proves `finiteAffineCyclicMomentResidueCharacterUniversality`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/FiniteAffineCyclicMomentResidueCharacterUniversalityLaw.lean`

## Log

- 2026-07-23 — theorem generated from the cyclic-spectrum and meromorphic equivariant-residue
  terminal modules; dependency-closed scratch proof passed.
- 2026-07-23 — repository exact check passed; post-proof novelty search found adjacent ingredients
  but no exact joint equivalence.
