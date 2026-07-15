# Projective-horizon reversal-self-Legendre core

- **ID:** `projective-horizon-reversal-self-legendre-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN) / MULTI-MODULE CERTIFICATE
- **Scientific status:** `[FORMALIZED ALGEBRAIC CORE] [NOVELTY PROVISIONAL] [SIGNIFICANCE CANDIDATE]`
- **Paper parent:** `projective-horizon-reversal-self-legendre-tower`

## Formalized declarations

The exact cotangent and duality core is certified by:

- `criticalHorizonLegendrePairing`
- `criticalHorizonLegendrePairing_eq_reversedDotProduct`
- `criticalHorizonLegendrePairing_eq_zero_of_inverse`
- `criticalHorizonSymplecticPairing`
- `criticalHorizonSymplecticPairing_eq_reversedCotangentSum`
- `criticalReciprocalGraph_isotropic`
- `criticalHorizonSymplecticPairing_swap`
- `criticalReciprocalHessian`
- `criticalReciprocalHessian_transpose`
- `criticalReciprocalJacobian_eq_reverseRows_hessian`
- `criticalHorizonTopPairing_add_dual_eq_zero`

The polarization invariants are certified by the declarations in:

- `ProjectiveHorizonPageTransition.lean`
- `ProjectiveHorizonCriticalMultiplicity.lean`
- `ProjectiveHorizonSchurCaustic.lean`
- `ProjectiveHorizonCausticQSystem.lean`

## Certified content

Lean proves that the coefficient-residue pairing is exactly the canonical raw-coordinate dot
product with coefficient-reversed reciprocal momenta and that this pairing vanishes in positive
degree for compatible truncated inverse jets.  It identifies the residue symplectic form with the
canonical reversed cotangent sum, proves that it is antisymmetric, and proves that the reciprocal
tangent graph is isotropic.  It also proves that the symmetric reciprocal Hessian becomes the critical
raw-to-reciprocal Jacobian under exact row reversal.  The separate certified modules establish the
critical binomial degree, the rectangular Schur determinant, and the Q-system algebraic core.

Together these declarations certify the algebraic claims needed to regard every finite horizon as a
partial polarization of the reciprocal graph.  The identity that the reversed reciprocal packet is
the gradient of the coefficient of a formal logarithm is retained at paper level; this card does not
claim a fully bundled formal Legendre-transform API.

## Verification

The relevant targeted leaf checks pass.  No full build is run.  Scratch `#print axioms` for the new
cotangent identities reports only `propext`, `Classical.choice`, and `Quot.sound`; there are no
project axioms or placeholders.  Repository formal lint remains part of final lane verification.

## Scientific boundary

Formalization certifies the mathematics but not the literature novelty verdict.  The theorem gives
the current canonical physical/topological description of the source-pure constraint.  Generic
full-symmetric monodromy is now proved in the adjacent all-rank card.  The open high-significance
target is a classification invariant of the infinite source or an application not already inherited
from classical reciprocal, Schur, or Grassmannian geometry.
