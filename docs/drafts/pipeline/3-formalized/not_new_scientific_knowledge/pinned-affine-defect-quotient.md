# The universal quotient by pinned affine defects

- **ID:** pinned-affine-defect-quotient
- **Stage:** 3-formalized
- **Type:** new constraint object / universal quotient theorem
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

For a pinned torsion presentation `A`, the commutator-plus-two-sided-factor defects form an additive
subgroup of the matrix defect group.  Define the **pinned-affine defect quotient** by dividing all
defects by this subgroup.

The Fitting boundary homomorphism vanishes on the subgroup and therefore descends canonically to the
quotient.  Every defect with nonzero Fitting boundary has nonzero quotient class.  The quotient is
not vacuous: the existing one-slot presentation `A=X^2`, `Delta=1` supplies an explicit nonzero
class.

This quotient is the universal carrier-free meaning of intrinsic nonlocality at the presentation
level: every additive detector blind to pinned affine defects factors through it.

## Attack and verdict

- `[BRIDGE]` Quotienting by a subgroup and descending a homomorphism are standard algebra.
- `[PROVED NATIVE OBJECT]` The full pinned-affine family is closed under zero, addition, and
  negation, so it defines a canonical subgroup rather than an informal class of examples.
- `[PROVED NONTRIVIALITY]` The Fitting boundary factors through the quotient and detects a concrete
  nonzero class.
- `[HONEST LIMIT]` This constructs the correct recipient for a completed arithmetic obstruction but
  does not yet attach xi or distinguish zero location.

## Formal theorem surface

- `pinnedAffineDefects` is the additive subgroup of all commutator-plus-two-sided-factor defects.
- `PinnedAffineDefectQuotient` is the quotient by exactly that subgroup.
- `pinnedAffineBlindLift` is the generic descended homomorphism for every additive detector blind to
  pinned affine defects.
- `fittingBoundaryClassHom` bundles the Fitting boundary additively.
- `pinnedAffineDefects_le_ker_fittingBoundaryClassHom` proves the required annihilation without an
  extra blindness hypothesis.
- `pinnedAffineBoundaryHom` is the canonical descended Fitting boundary.
- `pinnedAffineClass_ne_zero_of_fittingBoundaryClass_ne_zero` proves every live boundary survives.
- `exists_nonzero_pinnedAffineDefectQuotientClass` proves explicit nontriviality.

The implementation is
`formal/GaloisForLFunctions/RHTower/PinnedAffineDefectQuotient.lean` and is registered in the
`RHTower` umbrella.

## New open core

`[OPEN CORE]` Construct a canonical class in `PinnedAffineDefectQuotient` from the completed
prime--archimedean datum, before mentioning a zero location.  The attachment must satisfy two hard
tests:

1. it is not defined from `analyticOrderAt xi`, fixed/free orbit shape, or a chosen cutoff;
2. its vanishing/nonvanishing forces a genuinely new compatibility statement rather than merely
   restating that a divisor germ is determinant-transverse.

The quotient is now a real recipient, but the arithmetic source map into it remains the live
scientific problem.

## Novelty and significance gates

- **BRIDGE INFRASTRUCTURE:** quotient groups and descended homomorphisms are standard algebra.
- **NOVEL NATIVE OBJECT:** the quotient by the full pinned affine realization subgroup is specific
  to the HGT seam/weld interface and had not existed in the tree.
- **SIGNIFICANT:** “intrinsically nonlocal” now means a nonzero class in a universal constraint
  quotient, not an appeal to a carrier.  Every live Fitting boundary supplies such a class.
- **HONEST LIMIT:** no completed-zeta attachment or RH implication is claimed.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  No root build or project-wide lint was run.
