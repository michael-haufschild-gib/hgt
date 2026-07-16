# Pinned affine weld defects have zero Fitting boundary

- **ID:** pinned-affine-weld-boundary-no-go
- **Stage:** 3-formalized
- **Type:** theorem synthesis / local positive-order no-go
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

At a pinned torsion presentation `A` with `det A = X^m`, the natural affine realization of a weld
cochain has two pieces:

1. a positive-order action defect represented by a commutator `sigma*A - A*sigma`;
2. an order-zero scalar/basis correction factoring through `A`, possibly modulo `X^m`.

Every defect of the stronger two-sided combined form

`commutatorDefect A sigma + (A*Hr + X^m*Kr) + (Hl*A + X^m*Kl)`

has zero Fitting boundary class.  Consequently a nonzero boundary class cannot admit any such
affine pinned realization.

## Attack and verdict

- `[PROVED INFRASTRUCTURE]` `fittingBoundaryClass_commutatorDefect` kills the positive-order
  commutator piece.
- `[PROVED INFRASTRUCTURE]` `fittingBoundaryClass_add_right_factor_mod_X_pow` removes every scalar
  presentation-factor correction without changing the class.
- `[PROVED SYNTHESIS]` Combining them kills the full two-sided pinned affine defect and yields the
  converse nonrepresentation theorem for every live boundary class.
- `[HONEST LIMIT]` This classifies only pinned local realizations.  It does not construct or endorse
  a cutoff/carrier escape; any surviving datum must be genuinely nonlocal and constraint-defined.

## Formal theorem surface

- `pinnedAffineWeldDefect` packages the commutator, target-factor, source-factor, and local-ideal
  correction terms.
- `fittingBoundaryClass_pinnedAffineWeldDefect_eq_zero` proves their combined Fitting boundary
  vanishes over every finite square presentation and commutative coefficient ring.
- `nonzero_fittingBoundaryClass_not_pinnedAffineWeldDefect` proves that every live boundary class
  lies outside the entire pinned affine realization family.

The implementation is
`formal/GaloisForLFunctions/RHTower/PinnedAffineWeldBoundaryNoGo.lean` and is registered in the
`RHTower` umbrella.

## Consequence for the filtered-weld bridge

The previous theorem proves that any global weld primitive must have the positive principal symbol
`weldDerivSymbol`; this theorem proves that realizing that positive-order piece as a pinned
presentation commutator still gives zero local boundary.  Adding every possible scalar/source/target
factor correction cannot change the conclusion.

`[OPEN CORE]` A live completed obstruction must therefore be nonlocal in a mathematically intrinsic
sense: it cannot be the local commutator of an action with a divisor presentation, even after the
full affine gauge correction.  The next step is to characterize such nonlocality as a constraint
class, not to manufacture a carrier or cutoff evolution.

## Novelty and significance gates

- **DERIVABLE INFRASTRUCTURE:** each separate vanishing theorem already existed.
- **NEW SYNTHESIS:** the full two-sided affine defect and its universal nonrepresentation theorem
  were not present.  They show that the forced positive-order primitive cannot reach a live pinned
  Fitting boundary through any natural affine realization.
- **SIGNIFICANT:** both order-zero and positive-order pinned routes are now closed.  A future RH
  bridge must explain intrinsic nonlocality rather than merely choose a stronger local gauge.
- **NON-TAUTOLOGICAL:** no zero location, analytic order, or RH predicate is used.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  No root build or project-wide lint was run.
