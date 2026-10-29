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
`gaussSum_mulShift_eq` for a unit shift. Both sources have now been read:
the general unit identity is finite reindexing; the rational primitive
argument derives quotient-character descent from a nonzero Gauss sum
and a congruence kernel. General norm identities in the Gauss-sum source
are field-specialized, so they do not supply the ideal-quotient result.

The corpus quotient-unit query did not locate a general finite-ring
lifting theorem. Subsequent Mathlib leads include the rational
`ZMod.unitsMap_surjective` and
`IsLocalRing.surjective_units_map_of_local_ringHom`. The latter lifts
units along a surjective local homomorphism; its proof is inspected.
Applying it to an arbitrary ideal quotient still requires an actual
local decomposition or a separate lifting proof. These search results
are leads, not an assertion that a general theorem is absent.

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

HL6, including both forms of the Mertens bounds, is now fully audited.
No new Lean scratch is yet written for this card. This arithmetic
functional-equation work is the next Hecke gate; class field theory
still follows the completed Hecke programme.

## Finite-ring unit-lifting route

For a finite commutative ring, a positive power `e=r^n` of every element
can be chosen idempotent. If a ring homomorphism sends `r` to a unit,
then it sends `e` to one. The element `r*e+(1-e)` is a unit lifting the
same image, with inverse `r^(n-1)*e+(1-e)`. Expanding the product and
using `e^2=e` proves the inverse identity. This would lift units along
every surjective ring homomorphism with finite source, avoiding a new
Chinese-remainder decomposition.

The corpus query on finite idempotent powers has been run; its leads
only concerned powers of elements already known idempotent. A Mathlib
search for the positive idempotent-power existence theorem is the next
step before implementing this lifting argument. The construction has
not yet been checked in Lean.
