# The weld class cannot canonically orient a scalar germ line

- **ID:** weld-germ-orientation-no-go
- **Stage:** 1-in-progress
- **Type:** carrier-free naturality obstruction
- **Status:** `[CONJECTURE UNDER FORMAL ATTACK]`

## Claim

The scalar weld class canonically determines the alternating form `weldAreaForm theta` on the real
two-generator plane, but it determines no nonzero scalar reader of that plane.  More precisely, any
real linear functional `ell : R^2 -> R` invariant under every linear equivalence preserving the
weld area form is zero.  Hence there is no natural nonzero covector with which the weld class could
orient a rank-one divisor germ or restrict its full complex basis gauge.

The proof should require only the two unipotent symplectic shears.  Invariance under the upper shear
forces `ell(1,0)=0`; invariance under the lower shear forces `ell(0,1)=0`; linearity then gives
`ell=0`.  The result is independent of `theta`, including the degenerate zero class.

## Candidate moves and attack

- `[BRIDGE / REJECT]` Use the common-gauge obstruction of a prime-indexed coefficient family.
  Pairwise ratios survive, but the natural analytic family is `p |-> p^(1-2 Re rho)`, which merely
  encodes the target location and is a continuous weld character—a hidden flow/RH reformulation.
- `[FALSIFIED ALREADY]` Use a projective FE/Schwarz square multiplier.  Exact commutation forces it
  to one in `FESchwarzGermGluingTrivialization`.
- `[CONJECTURE]` Use the weld area to supply a canonical scalar germ orientation.  This card attacks
  that claim by the full area-preserving automorphism group.

## Promotion gate

Promote only if the lower shear and its area preservation are formalized, every natural scalar
reader is proved zero, and the resulting nonexistence theorem is integrated with the current scalar
gluing exhaustion.  The branch-level significance is closure of the last scalar arithmetic
reduction; the underlying invariant-covector fact is standard symplectic algebra and must be labelled
as proof infrastructure rather than novelty.

## Verification scope

Compile only the new module and its exact target.  Do not run the root build or project-wide lint.

