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

The finite-ring mechanism is now formalized, including the exact Gauss
norm. The proof uses additive orthogonality at one in place of Parseval:
the full transform gives the reciprocal Gauss product directly. For the
actual Hecke application, primitivity must still be tied to the finite
conductor and the trace pairing must be constructed and audited. Neither
may be left as an unexplained analytic or arithmetic interface.

## Arithmetic obligations

1. **Done for the actual finite Hecke residue character:** define its
   finite conductor and primitive quotient character, prove uniqueness,
   quotient-unit descent, and the exact conductor divisibility criterion.
2. **Done:** prove the primitive finite Fourier transform over the actual ideal
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

HL6, including both forms of the Mertens bounds, is fully audited.
This arithmetic functional-equation work is the next Hecke gate;
class field theory still follows the completed Hecke programme.

## Finite-ring unit-lifting route

For a finite commutative ring, a positive power `e=r^n` of every element
can be chosen idempotent. If a ring homomorphism sends `r` to a unit,
then it sends `e` to one. The element `r*e+(1-e)` is a unit lifting the
same image, with inverse `r^(n-1)*e+(1-e)`. Expanding the product and
using `e^2=e` proves the inverse identity. This lifts units along
every surjective ring homomorphism with finite source, avoiding a new
Chinese-remainder decomposition.

Both statements are now formalized and audited in
`HTGeometry/FiniteRingUnitsLiftThroughQuotients.lean`:
`FiniteRing.exists_pos_pow_idempotent`, `exists_unit_map_eq`, and
`units_map_surjective`. The proof uses a finite collision of powers and
the explicit complementary-idempotent construction above. Transitive
axioms are standard only; final direct source audit passed. Full proof:
[finite-ring unit lifting](../3-formalized/finite-ring-units-lift-through-quotients.md).

The consumer `HTGeometry/PrimitiveFiniteRingCharactersHaveGaussTransforms.lean`
is also finalized and audited. It defines pullback on unit characters,
proves quotient descent equivalent to triviality on the congruence kernel,
defines standard primitivity by absence of nonzero quotient descent, and
proves the full Gauss transform, reciprocal product, and exact squared
norm. All five main transitive audits have standard axioms only. Full
proof and exact declarations:
[primitive finite-ring Gauss transforms](../3-formalized/primitive-finite-ring-characters-have-gauss-transforms.md).

## Canonical finite-ring conductor

Unit lifting applies even to a ring map that is not surjective, provided
the chosen element has unit image. This gives a useful congruence
decomposition: if `u-1∈I+J`, write `u-1=x+y` with `x∈I`, `y∈J`.
The element `1+y` has unit image in `R/I × R/J`, namely `(u,1)`.
Lift that image to a unit `w`; then `w≡1 (mod J)` and
`u w⁻¹≡1 (mod I)`. Hence descent through both ideals implies descent
through their sum.

There are finitely many ideals, so the sum of all descent ideals is
itself a descent ideal and is their unique greatest element. The
character on that quotient is unique and primitive: any further
quotient descent pulls back to a larger descent ideal.

The construction is finalized in
`HTGeometry/FiniteRingCharactersHavePrimitiveConductors.lean`.
It includes the exact ideal criterion
`factorsThrough_iff_le_conductorIdeal`, the unique primitive character
`conductorCharacter`, and a transport theorem for every surjective ring
map whose kernel is the conductor ideal. All four main transitive
audits have standard axioms only; final source audit passed without
warnings. Full proof:
[finite-ring primitive conductors](../3-formalized/finite-ring-characters-have-primitive-conductors.md).

The Hecke consumer is now finalized and audited:
`HeckeLFunctions/HeckeFiniteCharactersHavePrimitiveConductors.lean`.
It pulls the canonical ideal back to `𝓞 K`, proves it nonzero and dividing
the original modulus, constructs the unique primitive character directly
on that integral quotient, and proves the exact descent criterion for
every divisor modulus. All four main transitive audits have standard
axioms only; final direct source audit passed without warnings. Full proof:
[actual finite Hecke conductors](../3-formalized/hecke-finite-characters-have-primitive-conductors.md).

## Actual trace-character bridge in progress

A scratch consumer now constructs the additive character associated to
each frequency in the actual trace-dual ideal. Representatives in the
coprime ideal differ by the modulus-product ideal, whose pairing with
the frequency has integral trace. This proves well-definedness and
additivity, and identifies the existing finite theta coefficient with
an actual Gauss sum. Multiplication of a frequency by an algebraic
integer should then give the inverse finite-character factor.

The general Gauss strengthening is now finalized in
`HTGeometry/PrimitiveGaussSumsDetectPrimitiveAdditiveCharacters.lean`:
for primitive multiplicative characters, Gauss nonvanishing is equivalent
to additive primitivity, with squared norm exactly zero or the ring
cardinality. It uses a principal ideal annihilated by an imprimitive
additive character and the congruence-unit argument. All three transitive
audits have standard axioms only; final source audit passed. Full proof:
[Gauss sums detect additive primitivity](../3-formalized/primitive-gauss-sums-detect-primitive-additive-characters.md).

The actual trace-character module passes all five main transitive
axiom audits with standard axioms only. It is finalized as
`HeckeLFunctions/HeckeFiniteFourierCoefficientsAreGaussSums.lean` and
wired into the Hecke umbrella; its final direct source audit passes
without warnings. Full proof:
[actual Hecke Fourier coefficients](../3-formalized/hecke-finite-fourier-coefficients-are-gauss-sums.md).
It constructs the trace character, identifies the actual theta
coefficient with its Gauss sum, proves inverse finite-character scaling,
and gives exact nonvanishing and squared-norm criteria.

It also proves the concrete intermediate kernel description:
the trace character attached to `a∈dual(𝔪₀𝔟)` is trivial exactly when
`a∈dual(𝔟)`. Consequently it is primitive exactly when every algebraic
integer `r` satisfying `ra∈dual(𝔟)` lies in `𝔪₀`.
The next arithmetic task is to convert this annihilator criterion into
coprimality of the associated integral ideal and then identify its
Hecke character value. The general Dedekind ideal-colon criterion below
is now finalized in `HTGeometry/DedekindIdealQuotientsDetectCoprimality.lean`.
Its transitive axiom audit is standard only, and its final direct source
audit passes without warnings. Full proof:
[ideal quotients detect coprimality](../3-formalized/dedekind-ideal-quotients-detect-coprimality.md).

Checked arithmetic sources for the next step:

- `HeckeThetaHasAFiniteFourierTransform.lean` defines the actual phase,
  residue coefficient, and dual-frequency sum. `residueIdealRemainder`
  proves that two representatives in a coprime ideal differ by the
  modulus-product ideal.
- `NumberFieldIdealTraceDuality.lean` proves actual lattice/trace-dual
  identification using a rational trace-dual basis.
- Mathlib `RingTheory/DedekindDomain/Different.lean`, read through the
  fractional-dual identities, supplies `FractionalIdeal.mem_dual`,
  `dual_eq_mul_inv`, `dual_mul_self`, `dual_dual`, and `dual_le_dual`.
  In particular `dual(I)=dual(1)*I⁻¹` is available for the arithmetic
  support calculation; it need not be reproved.
- `Complex.exp_eq_one_iff` and `exp_int_mul_two_pi_mul_I` identify the
  trace phase kernel with integral rational traces. Their sources are
  inspected, and the trace phase kernel equivalence now passes its
  verification in the actual trace-character module.

## Arithmetic support calculation formalized

Write `D=dual(1)` for the codifferent fractional ideal. For
`a∈dual(𝔪₀𝔟)`, the fractional ideal
`F=(a)𝔪₀𝔟D⁻¹` is integral, since
`dual(𝔪₀𝔟)=D(𝔪₀𝔟)⁻¹`. Let `I` be the corresponding integral ideal.
Then `ra∈dual(𝔟)` is equivalent to `rI⊆𝔪₀`. Thus the concrete
annihilator above is the ideal quotient `(𝔪₀:I)`.

For a nonzero ideal `m` in a Dedekind domain, `(m:I)=m` exactly when
`m+I=(1)`. One proof avoids a new prime-factorization calculation.
Put `J=m+I`, which is nonzero. The fractional ideal `N=mJ⁻¹` is
integral because `m≤J`, and `NI≤m`. If `(m:I)=m`, then `N≤m`;
cancelling the nonzero `m` gives `J⁻¹≤1`, forcing `J=(1)`.
Conversely, when `m+I=(1)`, any element sending `I` into `m` also
sends `m` into `m`, hence sends `m+I` into `m` and lies in `m`.

The relevant Mathlib leads are now inspected:
`FractionalIdeal.le_one_iff_exists_coeIdeal` converts an integral
fractional ideal to an ordinary ideal, and
`FractionalIdeal.not_inv_le_one_of_ne_bot` rules out `J⁻¹≤1` for
a nonzero proper ideal. The Dedekind criterion is formalized and audited.
The Hecke consumer is now finalized as
`HeckeLFunctions/HeckeFourierSupportIsIdealCoprimality.lean`. It constructs
the integral frequency ideal, identifies the actual annihilator with its
ideal quotient, and proves exact coprime support, Gauss mass, and vanishing
dual zero mode for a proper primitive finite modulus. It also constructs
a nonzero primitive frequency for every nonzero base ideal, including
unit modulus, using a coprime representative of the inverse ordinary
class of the trace-dual ideal. All five main transitive axiom audits are
standard only; final direct source audit passes without warnings. Full
proof: [arithmetic Fourier support](../3-formalized/hecke-fourier-support-is-ideal-coprimality.md).
The inverse Hecke coefficient and global root number remain open.

## Global coefficient comparison through unit fractions

The existing `exists_unit_fraction` and `reduce_eq` in
`ElementsPrimeToAModulusReduceModuloIt.lean` construct, for every
`α∈Kˣ` prime to the modulus, algebraic integers `r,s` invertible modulo
the modulus with `sα=r`. Consequently, for two valid frequencies
`a'=αa`, integer Fourier scaling applied to `sa'=ra` gives

```
F_b(a') = χ(reduce α)⁻¹ F_b(a).
```

No additive generator is assumed. To construct one for the unit base
ideal, choose a coprime integral ideal `I₀` in the inverse ordinary class
of `dual(m)`. Then `I₀ dual(m)` is principal, generated by a nonzero
`a₀`; since `I₀≤1`, this generator lies in `dual(m)`. Its associated
ideal is exactly `I₀`, so the support criterion gives a nonzero Gauss
coefficient `τ=F_1(a₀)` of squared norm `Norm(m)`.

For a general coprime base ideal `b`, choose a nonzero `x∈b` invertible
modulo `m`. Multiplication by `x` sends `a∈dual(mb)` into `dual(m)`.
Comparison of the actual residue representatives gives

```
F_b(a) = χ(x mod m) F_1(xa).
I_(xa) = (x) b⁻¹ I_a.
```

On the coprime support, `α=xa/a₀` is prime to `m`, because its principal
ideal is `I_(xa) I₀⁻¹`. The already proved principal ray-class formula
identifies `χ(reduce α)` with `ψ((α))/sgnψ(α)`, where
`sgnψ` is the actual infinite sign character. Since `sgnψ²=1`, this gives

```
F_b(a) sgnψ(a) = Cψ ψ(b) ψ(I_a)⁻¹,
Cψ = τ sgnψ(a₀) ψ(I₀),
|Cψ|² = Norm(m).
```

All ideals on which `ψ` is evaluated are coprime to `m`; neither the
conductor nor the different is silently treated as such. The constant
is independent of `b` and `a`. These are paper obligations for the next
Lean consumer, not yet claimed as formalized. Nonzero frequency is
required for the sign; the zero mode is handled separately. The
unit-modulus case requires choosing nonzero representatives explicitly,
since its singleton residue ring does not force a representative of one
to be nonzero.

The reference-frequency existence step is now formalized by
`exists_heckeDualFrequencyIdeal_coprime` in the finalized support module.
The next written consumers are:

- `/tmp/HeckeFourierFractionScalingScratch.lean`: unit-fraction covariance
  and transfer of actual trace characters and Fourier coefficients from
  a coprime base ideal to the unit base. Its first check is running.
- `/tmp/HeckeReferenceGaussConstantScratch.lean`: actual reference
  frequency and ideal, corrected Gauss constant, exact norm, and unit
  normalization; not yet checked.
- `/tmp/HeckeDualCoefficientCharacterScratch.lean`: principal-ideal
  transformation of associated ideals, prime-to-modulus multipliers,
  sign-corrected character invariance, and the actual inverse-Hecke-value
  formula for the unit base; not yet checked.

The support module's consumer olean has been built. The first scratch
imports the finalized actual Gauss module; the second imports the
finalized support module; the third awaits both pending consumers.
None of these scratch conclusions is yet counted as formalized.
