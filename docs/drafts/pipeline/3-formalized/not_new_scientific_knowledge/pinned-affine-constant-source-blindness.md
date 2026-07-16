# Constant and prime sources activate the pinned-affine quotient everywhere

- **ID:** pinned-affine-constant-source-blindness
- **Stage:** 3-formalized
- **Type:** activation classification / RH-interface no-go
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

For the canonical one-slot torsion presentation `A=X^m` with `m>0`, every nonzero constant defect
`Delta=C(c)` has nonzero Fitting boundary and therefore nonzero class in
`PinnedAffineDefectQuotient`.

Specializing to the obvious prime evaluation `c=p^(-rho)`, the quotient class is nonzero for every
positive prime base and every complex point `rho`.  No zero hypothesis and no critical-line condition
enters.  Thus raw prime-to-quotient activation is position-blind and cannot serve as an RH detector.

## Attack and verdict

- `[PROVED]` The one-slot Fitting boundary is exactly the constant jet class `C(c) mod X^m`.
- `[PROVED]` Positive order and `c != 0` make that class nonzero, hence it survives the universal
  pinned-affine quotient.
- `[PROVED]` Complex powers of a nonzero positive integer never vanish, so prime evaluation activates
  at every point.
- `[HONEST LIMIT]` The quotient remains a valid universal obstruction recipient.  What fails is the
  naive use of nonvanishing prime evaluation as a location selector.

## Formal theorem surface

- `oneSlotTorsionPresentation`, `oneSlotConstantDefect`, and
  `oneSlotTorsionPresentation_det` define the canonical local model.
- `fittingBoundaryClass_oneSlotConstant_eq` computes the exact constant jet.
- `pinnedAffineBoundaryHom_oneSlotConstant_eq` computes its descended quotient boundary.
- `fittingBoundaryClass_oneSlotConstant_ne_zero` and
  `oneSlotConstant_pinnedAffineClass_ne_zero` prove generic nonzero activation.
- `primeEvaluationPinnedAffineClass_ne_zero` proves activation for every positive base and every
  complex point; the prime specialization adds no zero or location hypothesis.
- `finiteConstantSourcePinnedAffineClass_eq_zero_iff` proves that every finite constant-source
  family collapses to its single scalar sum; all labels are forgotten.
- `twoPrimeEvaluationPinnedAffineClass_eq_zero_iff` gives the exact two-source criterion.
- `twoPrimeEvaluation_tunedCancellation` proves that coefficients chosen from a target point can
  always cancel two nonzero prime sources there, so pointwise-tuned cancellation is circular.

The implementation is
`formal/GaloisForLFunctions/RHTower/PinnedAffineConstantSourceBlindness.lean` and is registered in
the `RHTower` umbrella.

## New open core

`[OPEN CORE]` The arithmetic source cannot be a pointwise nonzero prime evaluation or any finite
constant-source sum: the quotient forgets all labels and remembers only one scalar.  A surviving
completed compatibility must retain nonconstant germ data—at least higher prime-log jet
coefficients—or an infinite-support constraint before scalar collapse.  Its cancellation must be
derived before inserting a zero location; otherwise it is only pointwise interpolation,
susceptibility, or orbit parity again.

## Novelty and significance gates

- **BRIDGE INFRASTRUCTURE:** nonvanishing of complex powers and constant jets is standard.
- **NEW ACTIVATION NO-GO:** the newly constructed universal quotient is proved uniformly active
  under the most obvious prime source at every point.  This prevents its nonzero class from being
  misreported as an RH selector.
- **SIGNIFICANT:** any viable attachment must use a completed multi-source compatibility or
  cancellation law retaining higher-jet or infinite-support structure, not a one-prime incidence
  map or finite scalar sum.
- **NON-TAUTOLOGICAL:** the all-point theorem is stronger precisely because it assumes neither
  `xi rho = 0` nor `Re rho = 1/2`.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  No root build or project-wide lint was run.
