# Same-base-prime invariance of Artin local Euler polynomials

- **ID:** `artin-local-euler-same-base-prime-invariance`
- **Stage:** 3-formalized
- **Type:** THEOREM (local Artin infrastructure)
- **Status:** `[LITERATURE] [PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOT NEW]`
- **Statement:** local Artin Euler polynomials agree for any two finite-residue prime ideals with
  the same underlying prime ideal of the invariant base ring.

## Exact formal result

`formal/GaloisForLFunctions/RHTower/ArtinLocalEulerPrimeDescent.lean` proves

```text
frobeniusInertiaEulerPolynomial_eq_of_under_eq:
  Q.under R = Q'.under R →
  frobeniusInertiaEulerPolynomial (R := R) Q' rho
    = frobeniusInertiaEulerPolynomial (R := R) Q rho.
```

This is derived from `Algebra.IsInvariant.exists_smul_of_under_eq`, then the concrete
conjugate-prime theorem.  The prime, finite-residue, inertia, and Frobenius data are all actual
Mathlib objects.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/ArtinLocalEulerPrimeDescent.lean` passed.
- `lake build GaloisForLFunctions.RHTower.ArtinLocalEulerPrimeDescent` passed; targeted leaf only.
- `/tmp/ArtinLocalEulerPrimeDescentAxioms.lean` reports only
  `[propext, Classical.choice, Quot.sound]` for the final equality and all supporting public
  declarations.
- The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build was run.

## Anti-theatre boundary

This proves choice independence once primes above a base prime are supplied.  It does not yet
construct the number-field base-prime carrier or prove prime-above existence in the required
global setting, and says nothing about Euler-product convergence, continuation, or holomorphy.

## Log

- 2026-08-15 — formalized by combining actual Galois transitivity of prime ideals with the
  conjugate-prime local-polynomial theorem.
