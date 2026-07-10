# The weld class cannot canonically orient a scalar germ line

- **ID:** weld-germ-orientation-no-go
- **Stage:** 2-fully-proven
- **Type:** carrier-free naturality obstruction
- **Status:** `[PROVED ON PAPER + LEAN]`

## Claim

The scalar weld class canonically determines the alternating form `weldAreaForm theta` on the real
two-generator plane, but it determines neither a nonzero scalar reader nor a nonzero marked vector.
More precisely, any real linear functional `ell : R^2 -> R` invariant under every linear
equivalence preserving the weld area form is zero, and every vector fixed by all such equivalences
is zero.  Hence there is no natural scalar direction with which the weld class could orient a
rank-one divisor germ or restrict its full complex basis gauge.

The proof should require only the two unipotent symplectic shears.  Invariance under the upper shear
forces `ell(1,0)=0`; invariance under the lower shear forces `ell(0,1)=0`; linearity then gives
`ell=0`.  The result is independent of `theta`, including the degenerate zero class.

## Candidate moves and verdict

- `[BRIDGE / REJECT]` Use the common-gauge obstruction of a prime-indexed coefficient family.
  Pairwise ratios survive, but the natural analytic family is `p |-> p^(1-2 Re rho)`, which merely
  encodes the target location and is a continuous weld character—a hidden flow/RH reformulation.
- `[FALSIFIED ALREADY]` Use a projective FE/Schwarz square multiplier.  Exact commutation forces it
  to one in `FESchwarzGermGluingTrivialization`.
- `[FALSIFIED]` Use the weld area to supply a canonical scalar germ orientation.  The upper and
  lower unipotent shears force every invariant covector and marked vector to vanish.

## Formal theorem surface

- `weldLowerShear`, `weldLowerShear_preserves_area` complete the two-shear automorphism test.
- `weldNaturalMarkedVector_eq_zero` proves that the area form selects no natural generator-plane
  direction.
- `weldNaturalScalarReader_eq_zero` proves that every natural scalar reader is zero.
- `weldClassLineNaturalMarkedVector_eq_zero` and
  `weldClassLineNaturalScalarReader_eq_zero` remove the conversion-rate coordinate and state the
  result directly for an arbitrary weld class.
- `WeldClassLineNaturalScalarReaderFamily.reader_eq_zero` allows the reader to vary with the full
  class and still proves the entire family zero.
- `no_nonzero_weldClassLineNaturalScalarReaderFamily` is the resulting interface-level no-go.

The implementation is
`formal/GaloisForLFunctions/RHTower/WeldGermOrientationNoGo.lean` and is registered in the `RHTower`
umbrella.

## Combined consequence with scalar FE/Schwarz gluing

`FESchwarzGermGluingTrivialization` proves that the separate scalar FE and Schwarz arrows have no
gauge invariant beyond fixed/free orbit shape.  The present theorem proves that the scalar weld
class cannot canonically reduce that gauge by providing a reader or marked direction.  Therefore
the entire scalar route is exhausted from both sides: neither the local gluing coefficients nor the
global scalar weld area supplies the missing arithmetic orientation.

## New open core

`[OPEN CORE]` Retain genuinely marked arithmetic structure before passing to the scalar weld-area
line.  The smallest possible survivor is a prime-graded module carrying a gauge-restricting lattice,
filtration, or pairing whose preservation law is forced by the completed Euler datum.  It must not
be a freely chosen character of the prime-log lattice: continuous characters are exponential flow
parameters, and `p |-> p^(1-2 Re rho)` merely stores the desired zero location.  The next object must
therefore expose a non-character obstruction in the full prime-indexed weld, before the
class-to-area collapse forgets the labels.

## Novelty and significance gates

- **PROOF INFRASTRUCTURE:** absence of invariant vectors and covectors for the two-dimensional
  symplectic group is standard linear algebra.
- **NOVEL BRANCH CONSEQUENCE:** applying the full automorphism test to the actual injective
  class-to-area interface proves that no class-dependent scalar reader family can exist.  This
  answers the precise arithmetic-gauge escape left by the preceding gluing theorem.
- **SIGNIFICANT:** the surviving search space is no longer “some scalar attachment from the weld.”
  It must retain prime-marked non-scalar structure and derive its reduced gauge group arithmetically.
- **NON-TAUTOLOGICAL:** no zero, analytic order, orbit cardinality, or RH predicate occurs in the
  definitions or proof.

## Verification scope

The new module compiles directly and its exact module target builds.  The capstone axiom footprints
are `[propext, Classical.choice, Quot.sound]`.  No root build or project-wide lint was run.
