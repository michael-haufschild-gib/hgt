# Primitive Gauss sums and the arithmetic dual Hecke character

- **ID:** hecke-primitive-gauss-sums-and-arithmetic-dual-character
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Hecke programme](../1-in-progress/hecke-l-functions-and-class-field-theory-2026-10-28.md)
- **Statement:** Actual finite conductors, primitive Gauss transforms, inverse-character Fourier coefficients, and unit root numbers give the primitive completed Hecke functional equation over every number field.

## Finite conductor and Gauss transform

Unit lifting through quotients of finite commutative rings follows from
an idempotent positive power of each element. Congruence-kernel
decomposition makes character descent closed under sums of ideals.
The sum of all descent ideals is the unique conductor, with a unique
primitive quotient character. These constructions specialize to the
actual finite residue component of each Hecke character.

Primitivity forces the Gauss transform to vanish at nonunit shifts:
a suitable congruence unit fixes the shift but changes its character.
Unit shifts give inverse-character covariance. Additive orthogonality
then gives the exact reciprocal Gauss product and squared norm.

- [Finite-ring unit lifting](finite-ring-units-lift-through-quotients.md)
- [Canonical conductors](finite-ring-characters-have-primitive-conductors.md)
- [Primitive finite-ring Gauss transforms](primitive-finite-ring-characters-have-gauss-transforms.md)
- [Actual finite Hecke conductors](hecke-finite-characters-have-primitive-conductors.md)

## Actual arithmetic dual coefficients

The finite Fourier coefficient on the trace-dual ideal is the Gauss sum
of the actual residue trace character. Ideal colon identities identify
primitive additive support with coprimality of the constructed frequency
ideal. Actual coprime representatives supply a primitive reference
frequency without assuming principal conductor or different.

Normalize the reference coefficient by its infinite sign and ideal
character value to obtain `Cψ`. Ray-residue covariance, transfer between
base ideals, and principal-ideal compatibility prove, for every nonzero
actual dual frequency `a`,

```
F_b(a) sign_psi(a) = C_psi psi(b) psi^-1(I_a),
I_a = (a) dual(mb)^-1,
||C_psi|| = sqrt(Norm(m)).
```

The identity includes unsupported ideals, where both sides vanish.
Conductor, infinite signs, parities, Gamma factors, and Mellin arguments
are invariant under inversion of the character.

- [Actual Gauss sums](hecke-finite-fourier-coefficients-are-gauss-sums.md)
- [Exact ideal support](hecke-fourier-support-is-ideal-coprimality.md)
- [Ray-residue covariance](hecke-fourier-coefficients-scale-by-ray-residues.md)
- [Actual Gauss constant and norm](hecke-primitive-gauss-constants-have-exact-norm.md)
- [Inverse Hecke coefficients](hecke-fourier-coefficients-are-inverse-hecke-values.md)
- [Inversion invariance](hecke-conductors-and-parities-are-invariant-under-inversion.md)

## Completed functional equation

[Actual dual unfolding](hecke-dual-theta-unfolding-over-fractional-ideal-classes.md)
identifies the inverse-character class series with the dual averaged
Mellin transform. The fractional trace-dual norm and actual Poisson scalar
cancel every base-ideal factor. With `delta=|disc K|Norm(m)` and parity
sum `d`, the remaining root number is
`Wψ=(Cψ/sqrt(Norm(m)))(-i)^d`, with `||Wψ||=1`.

The completed function uses entire divided differences to fill removable
values. The exact ordinary-class permutation and analytic uniqueness give
`Lambda_psi(1-s)=W_psi Lambda_(psi^-1)(s)`: globally after clearing both
possible poles, off zero and one for every primitive character, and at
every complex point for nontrivial primitive characters.

- [Arithmetic normalization](hecke-completion-factors-have-exact-arithmetic-normalization.md)
- [Completed removable values](hecke-gamma-completed-functions-have-removable-values.md)
- [Completed functional equation](primitive-hecke-l-functions-have-completed-functional-equation.md)

Every displayed result is formalized. Final direct source audits pass
without warnings; recorded transitive axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`. Modules are wired into
their umbrellas; no umbrella was compiled. All five arithmetic
obligations are closed. The larger programme remains paused before CFT.
