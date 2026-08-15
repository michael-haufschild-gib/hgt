# Prime-choice descent for Artin local Euler polynomials

- **ID:** `artin-local-euler-prime-descent`
- **Stage:** 1-in-progress
- **Type:** THEOREM (local Artin infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** the local polynomial
  \(\det(1-T\rho(\mathrm{Frob}_Q)\mid V^{I_Q})\) is unchanged when `Q` is replaced by a
  conjugate prime above the same base prime.

## Goal

Build actual ideal-action transport, invariant-subspace conjugacy, and Frobenius transport needed
to index the existing upstairs polynomial by a base prime.  This is a mandatory prerequisite to a
global Artin Euler product.  It must use Mathlib's `Ideal.inertia`, decomposition stabilizers,
`IsArithFrobAt.conj`, and the concrete representation action—not a record postulating prime
independence.

## Paper proof

For `Q' = tau • Q`, conjugation by `tau` identifies decomposition groups and maps `I_Q` to
`I_Q'`.  The representation action of `tau` maps `V^{I_Q}` linearly and bijectively onto
`V^{I_Q'}`.  An arithmetic Frobenius at `Q` conjugates to one at `Q'`; the two induced maps on
invariants are conjugate.  Characteristic polynomials agree, and existing lift-independence
replaces that conjugated lift by the chosen `arithFrobAt` at `Q'`.  Galois transitivity of primes
over a fixed base prime then gives arbitrary prime-choice independence.

## Exact initial Lean target

```text
(Q.inertia (stabilizer G Q)).map
  (stabilizerEquivStabilizer (show tau • Q = tau • Q from rfl)).toMonoidHom
  = (tau • Q).inertia (stabilizer G (tau • Q)).
```

The first lemma is the nontrivial ideal-action transport.  It is a real obstruction boundary: the
fixed-`Q` lift-independence theorem does not establish it.

## Known APIs and non-routes

- `IsArithFrobAt.conj` transports a Frobenius lift to `tau • Q`.
- `Algebra.IsInvariant.exists_smul_of_under_eq` supplies `tau` when two primes lie over the same
  base ideal.
- `MulAction.stabilizerEquivStabilizer` transports decomposition groups.
- `LinearEquiv.charpoly_conj` can consume a concrete invariant-space equivalence.
- `isConj_arithFrobAt` alone is insufficient: its conjugator is not tied to the prime transport.
- `Ideal.inertiaEquiv` is inapplicable because it assumes a fixed ideal/action rather than
  simultaneous conjugation.

## Anti-theatre boundary

This does not define an Euler product, prove convergence or continuation, or establish any
continued-divisor effectivity.  It only removes an essential local choice.  A polynomial indexed
by a base prime cannot be honestly defined before this theorem.

## Formalized sublayer

`formal/GaloisForLFunctions/RHTower/ArtinLocalEulerPrimeTransport.lean` now proves the exact
ideal-action transport lemmas

```text
inertia_map_conj:
  map (conj tau) (Q.inertia G) = (tau • Q).inertia G,

inertia_map_stabilizer_conj:
  map (stabilizerEquivStabilizer tau) (Q.inertia D_Q) = (tau • Q).inertia D_(tau•Q).
```

These use no postulated equivariance: membership is transported directly through the pointwise
ideal action.  Targeted source check and leaf build passed; the axiom audit reports only
`[propext, Classical.choice, Quot.sound]`.  The leaf is wired into `RHTower.lean` without an
umbrella build.  The remaining invariant-space and Frobenius conjugacy steps are still open.

## Log

- 2026-08-15 — opened after audit identified exact Mathlib routes and verified that no existing
  Artin prime-choice theorem is present in the project.
- 2026-08-15 — formalized the inertia and decomposition-stabilizer conjugation transport.  This
  closes the initial target but not local-polynomial prime-choice independence.
