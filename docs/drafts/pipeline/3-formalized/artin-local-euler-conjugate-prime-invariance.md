# Conjugate-prime invariance of Artin local Euler polynomials

- **ID:** `artin-local-euler-conjugate-prime-invariance`
- **Stage:** 3-formalized
- **Type:** THEOREM (local Artin infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** replacing a prime ideal `Q` by `τ • Q` leaves the actual local Artin Euler
  polynomial unchanged.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerPrimeDescent.lean` proves

```text
frobeniusInertiaEulerPolynomial_eq_of_smul:
  frobeniusInertiaEulerPolynomial_smul (R := R) τ Q ρ
    = frobeniusInertiaEulerPolynomial (R := R) Q ρ.
```

The left side is the existing Frobenius--inertia polynomial at `τ • Q`, with primality and finite
residue quotient transported concretely from `Q`.  It is not a postulated prime-choice interface.

The proof supplies actual subgroup transport, an explicit linear equivalence
`inertiaInvariantConjLinearEquiv` between the two invariant spaces, conjugacy of the induced
Frobenius actions, and a reversed-characteristic-polynomial equality.

## Paper proof

Conjugation by `τ` maps the decomposition group and inertia subgroup at `Q` to those at `τ • Q`.
The map `v ↦ ρ(τ)v` is a linear equivalence of their inertia invariants, intertwining an element
of the first decomposition group with its conjugate.  An arithmetic Frobenius lift at `Q` conjugates
to one at `τ • Q`; fixed-prime lift independence replaces it with the chosen arithmetic Frobenius.
Conjugate endomorphisms have equal characteristic polynomials.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerPrimeDescent.lean` passed.
- `lake build GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPrimeDescent` passed; targeted leaf only.
- `/tmp/ArtinLocalEulerPrimeDescentAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for the invariant equivalence, conjugacy theorem,
  finite-quotient transport, and final polynomial equality.
- The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build was run.

## Anti-theatre boundary

This handles only conjugate primes.  It does not yet use prime transitivity to identify arbitrary
primes above a base prime, define a global Euler product, prove convergence or continuation, or
establish Artin holomorphy.

## Log

- 2026-08-15 — formalized from actual ideal actions, inertia invariants, arithmetic Frobenius, and
  characteristic polynomials; no synthetic local-data or prime-independence premise introduced.
