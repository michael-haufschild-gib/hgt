# Projective-horizon Landau--Ginzburg duality core

- **ID:** `projective-horizon-landau-ginzburg-duality-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (LEAN)
- **Scientific status:** `[FORMALIZED CORE] [NOVELTY PROVISIONAL] [SIGNIFICANCE OPEN]`
- **Paper parent:** `projective-horizon-logarithmic-vacuum-duality`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ProjectiveHorizonLandauGinzburgDuality`

## Formalized declarations

- `criticalReciprocalHessian`
- `criticalReciprocalHessian_transpose`
- `criticalReciprocalJacobian_eq_reverseRows_hessian`
- `criticalHorizonTopPairing`
- `criticalHorizonTopPairing_add_dual_eq_zero`
- `criticalHorizonSymplecticPairing`
- `criticalHorizonLegendrePairing_eq_reversedDotProduct`
- `criticalHorizonSymplecticPairing_eq_reversedCotangentSum`
- `criticalReciprocalGraph_isotropic`
- `criticalHorizonSymplecticPairing_swap`

## Certified content

The Lean layer certifies that the critical reciprocal Hessian is symmetric, that reversing its rows
gives the previously formalized critical observation Jacobian exactly, and that the two top-degree
source-tail pairings cancel at a compatible factorization under the required low-degree and
tail-divisibility hypotheses.  The companion module `ProjectiveHorizonExactLagrangian.lean`
certifies antisymmetry of the coefficient-residue form and exact isotropy of the reciprocal tangent
graph at every truncation depth.

The paper-level formal logarithm and its gradient identity are not represented by a single Lean
potential object yet.  Consequently this card claims a formalized algebraic core, not complete
formalization of every displayed equation in the paper theorem.

## Verification

The targeted leaf builds

```text
lake build GaloisForLFunctions.HTGeometry.ProjectiveHorizonLandauGinzburgDuality
lake build GaloisForLFunctions.HTGeometry.ProjectiveHorizonExactLagrangian
```

pass.  No full build was run.  Scratch `#print axioms` for the new cotangent identities reports only
`propext`, `Classical.choice`, and `Quot.sound`; there are no project axioms or placeholders.  The
repository formal lint remains part of final lane verification.

## Scientific boundary

Formalization does not promote the provisional literature verdict or establish significance.  The
infinite-depth Q-system and generic full-symmetric-monodromy targets are now proved in adjacent
cards.  The remaining external-significance target is a classification of the infinite source or an
application not inherited from the universal reciprocal constraint geometry.
