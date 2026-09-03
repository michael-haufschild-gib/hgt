# Frobenius eigen-characters on integral lattices

- **ID:** F1-LEAN-LATTICE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `1-in-progress/f1-object-forced-shape.md` C1–C2
- **Statement:** a nonzero functional intertwining an endomorphism of a finite free ℤ-module with
  a scalar has an integral scalar (Cayley–Hamilton). Hence for nonreal `ρ` and distinct primes
  `p, q, r` no finite free ℤ-module carries three endomorphisms with a common nonzero
  eigen-functional of eigenvalues `p^ρ, q^ρ, r^ρ`; and a Frobenius on a finite free ℤ-lattice with
  unimodular spectrum has every eigen-character a root of unity.

## Lean
| module | declarations |
|---|---|
| `GaloisForLFunctions.RHTower.FrobeniusLatticeRigidity` | `eigenfunctional_aeval`, `isIntegral_of_eigenfunctional`, `isAlgebraic_of_eigenfunctional`, `not_exists_joint_eigenfunctional_three_primes`, `exists_pow_eq_one_of_eigenfunctional_of_unimodular_charpoly` |

Inputs: `LinearMap.aeval_self_charpoly`, `LinearMap.charpoly_monic`, `minpoly.dvd`,
`SixExponentials.not_all_three_prime_cpow_isAlgebraic`,
`exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one`. Axioms:
`propext, Classical.choice, Quot.sound`. Wired into `GaloisForLFunctions.RHTower`.

## Log
- 2026-09-03 — created at stage 3.
