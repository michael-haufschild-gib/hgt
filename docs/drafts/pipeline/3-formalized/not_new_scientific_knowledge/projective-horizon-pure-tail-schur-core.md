# Pure-tail factorization and rectangular Schur-caustic core

- **ID:** `projective-horizon-pure-tail-schur-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN)
- **Scientific status:** `[FORMALIZED] [BRIDGE]`
- **Paper parents:** `projective-horizon-pure-tail-fermionic-fiber`,
  `projective-horizon-rectangular-schur-caustic`

## Formalized declarations

In `ProjectiveHorizonPureTailFiber.lean`:

- `pureCritical_factorization_iff`
- `pureCriticalCyclicPolynomial_separable`
- `criticalHorizonOccupationStates`
- `card_criticalHorizonOccupationStates`

In `ProjectiveHorizonSchurCaustic.lean`:

- `criticalReciprocalInfinitesimal_tangent`
- `rectangularSchurToeplitz`
- `criticalReciprocalJacobian_apply`
- `criticalReciprocalJacobian_eq_neg_rectangularSchurToeplitz`
- `criticalReciprocalJacobian_det_eq_rectangularSchur`

## Verification

Both targeted leaf builds pass.  No full build was run.  The declarations contain no `sorry`,
`admit`, local axiom, `opaque`, or `unsafe` theorem.  A scratch `#print axioms` audit is recorded
after the final monodromy-lane edit.

## Scope

The Lean layer certifies the exact cyclic factorization identity, separability, binomial occupation
count, truncated tangent equation, Toeplitz Jacobian, and determinant sign.  It does not claim an
irreducibility theorem or a geometric monodromy group.
