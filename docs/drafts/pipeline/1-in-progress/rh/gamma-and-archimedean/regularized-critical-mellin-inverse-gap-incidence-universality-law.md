# Regularized critical-Mellin inverse-gap incidence universality law

## Status

Formalized in Lean and wired into the RHTower umbrella. Kept in progress until global exhaustion
and final audit complete.

## Lean sources

- `GaloisForLFunctions.RHTower.PrimeMellinInverseGapEnergy`
- `GaloisForLFunctions.RHTower.CriticalMellinFourCoordinateCollapseUniversalityLaw`
- `GaloisForLFunctions.HTGeometry.InverseGapCauchyCommutator`

## Conjecture

At every positive Lorentzian boundary scale, the universal Cauchy value commutator is the signed
sum of the resolved prime commutator, shifted-polar commutator, and the Gram commutator of the
pole-filled regularized critical-Mellin germ. Consequently finite inverse-gap commutator energy is
the squared entry norm of this same signed packet.

This upgrades the existing Laplace-coordinate incidence to the globally continued coordinate
whose half-plane analyticity is equivalent to RH.

## Corpus gap

The four-coordinate collapse module proves equality of the two critical-Mellin Grams. The
inverse-gap module proves the commutator and energy formulas using only the older
`criticalMellinDefectRightHalfPlaneGram`. Search found no theorem transporting those formulas to
`regularizedCriticalMellinRightHalfPlaneGram`.

## Proof plan

1. Prove positive boundary nodes lie in the right half-plane.
2. Rewrite the critical-Mellin Gram in the existing commutator incidence by the four-coordinate
   collapse.
3. Rewrite the existing squared-entry energy formula by the same matrix equality.

No numerical computation is used.

## Lean result

`formal/GaloisForLFunctions/RHTower/RegularizedCriticalMellinInverseGapIncidenceUniversalityLaw.lean`
proves:

- `cauchyBoundaryValueCommutator_eq_prime_sub_shiftedPolar_add_regularizedCriticalMellin`;
- `regularizedInverseGapCommutatorEnergy_eq_primePolarRegularizedCriticalMellinIncidence`.

Exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/RegularizedCriticalMellinInverseGapIncidenceUniversalityLaw.lean`

## Novelty status

Post-proof searches found literature on Mellin-convolution commutators, Fredholm regularization,
and inverse problems separately, but no match for this finite Cauchy-commutator identity coupling
von Mangoldt prime, shifted-polar, and pole-filled critical-Mellin Gram packets. Novelty claim is
limited to the exact source-resolved incidence/energy packaging; the coordinate equality used to
transport it is already a corpus theorem.
