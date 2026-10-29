# Primitive Gauss sums and the arithmetic dual Hecke character

- **ID:** hecke-primitive-gauss-sums-and-arithmetic-dual-character
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** [Hecke programme](hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Statement:** For primitive finite-order ray characters, identify the actual dual theta transform with the inverse-character Hecke series, with its conductor, discriminant and Gauss normalization, and derive the completed functional equation.

## Established analytic inputs

Actual ideal-lattice Poisson summation, trace-ideal duality and covolumes,
finite weighted theta inversion, parity factors, unit-domain integration,
Gamma factors, class-series Mellin identities, finite class recombination,
and global ordinary-L continuation are all formalized. The remaining
functional-equation input is arithmetic: the finite Fourier coefficients
must become the correctly normalized inverse-character coefficients.
Ordinary L-function entireness alone does not settle cancellation of the
raw completed-theta zero modes.

## Search leads checked

Corpus first: `RHTower/MultiplicativeLargeSieve.lean` proves
`normSq_gaussSum_of_isPrimitive` and
`conj_mul_gaussSum_of_isPrimitive`. Their source uses the full primitive
Gauss transform and finite Parseval. These are rational-modulus
`ZMod r` results; they do not establish the arbitrary ideal-quotient case.

The subsequent Mathlib search located
`NumberTheory/DirichletCharacter/GaussSum.lean`:
`gaussSum_mulShift_of_isPrimitive` is also specialized to `ZMod N`.
`NumberTheory/GaussSum.lean` has the general finite-ring
`gaussSum_mulShift_eq` for a unit shift. Its full statement and the
primitive nonunit argument still need source inspection before reuse.

## Candidate finite-ring mechanism

For a finite commutative ring, primitivity of a unit character can be
expressed by nontriviality on every congruence kernel attached to a
nonzero ideal. For a nonunit `a`, its annihilator is nonzero: multiplication
by `a` cannot be injective on a finite ring. A unit `u` congruent to one
modulo this annihilator fixes `a`, while its primitive character value can
be chosen nontrivial. Changing variables by `u` forces the Fourier
coefficient at `a` to vanish. Unit shifts give the inverse character.
Finite Parseval then determines the Gauss norm once the additive trace
pairing is proved nondegenerate.

This is a proposed mechanism, not a formalized theorem. For the actual
Hecke application, primitivity must be tied to the finite conductor and
the trace pairing must be constructed and audited. Neither may be left
as an unexplained analytic or arithmetic interface.

## Arithmetic obligations

1. Define the finite conductor and primitive characters, with the
   necessary quotient-unit descent and minimality statements.
2. Prove the primitive finite Fourier transform over the actual ideal
   quotient and its trace-dual module, including nonunit vanishing and
   Gauss norm.
3. Account for nonprincipal conductor and different ideals. A chosen
   additive generator or auxiliary ideal must be constructed; evaluating
   the Hecke character directly on conductor primes is invalid because
   those ideal coefficients are zero.
4. Reindex the actual dual fractional-ideal sums over ordinary classes,
   identifying every coefficient with the inverse Hecke character.
5. Assemble the completed reflection with the exact discriminant,
   conductor and parity factors, and audit the root number.

No new Lean scratch is written for this card. Finish the Mertens consumer
checks before starting this arithmetic formalization. Class field theory
still follows the completed Hecke programme.
