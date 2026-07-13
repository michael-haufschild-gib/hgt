# Infinite-support moment representation capstone to RH

- **ID:** `infinite-support-moment-representation-rh-capstone`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[COMMON CONSUMER] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/MomentHankelStrict.lean` and
  `formal/GaloisForLFunctions/RHTower/PrimeArchMomentMeasureRH.lean`
- **Consumers:** `../../1-in-progress/completed-seam-thorin-subordinator-rh.md`,
  `../../1-in-progress/prime-gamma-free-poisson-cumulant-rh.md`, and
  `../../1-in-progress/prime-arch-exchangeable-de-finett-rh.md`

## Theorem

Let `s : N -> R` be represented by a positive measure `mu`:

```text
s_k=integral x^k dmu(x).
```

Assume every monomial is integrable and `mu` charges the complement of every finite subset of `R`.
Lean proves that every finite Hankel matrix

```text
H_n(i,j)=s_(i+j)
```

is positive definite and therefore has strictly positive determinant.

Specializing to

```text
s_k=normalizedPrimeArchMoment(k)
```

gives the capstone

```text
PrimeArchInfiniteSupportMomentRepresentation -> RiemannHypothesis.
```

The proof uses the exact coefficient-vector identity

```text
a^T H_n a=momentFunctional(s,(Polynomial.ofFn n a)^2).
```

The existing moment-functional theorem rewrites the right side as the integral of a polynomial
square.  If it vanishes, the polynomial is zero outside a finite root set; the infinite-support
hypothesis forces the coefficient vector to vanish.  Hence the form is strict.  The already
formalized prime--arch determinant criterion then yields RH.

## Positive content and exact limitation

This closes a consumer-side gap shared by several outlandish detours.  A Thorin law, positive free
jump law, de Finetti mixture, planar path measure, or any other source construction no longer has
to reprove strict finite Hankel determinants.  It only has to produce one positive representing
measure for the exact canonical moment tower and prove that its support is not finite.

The theorem does not construct that measure.  Assuming
`PrimeArchInfiniteSupportMomentRepresentation` is an RH-strength input unless the measure is built
independently from theta--Euler--Gamma source data.

## Formal certificate

The general module proves:

- `momentHankelMatrix_isHermitian`;
- `dotProduct_mulVec_momentHankelMatrix`;
- `momentHankelMatrix_posDef_of_infiniteSupport`;
- `det_momentHankelMatrix_pos_of_infiniteSupport`.

The RH module proves:

- `primeArchSourceMomentHankelDeterminantsPositive_of_infiniteSupportRepresentation`;
- `riemannHypothesis_of_primeArchInfiniteSupportMomentRepresentation`.

Both exact modules build.  Axiom audits of the strict determinant theorem and both RH capstones
report only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] moment-functional quadratic form identified with the finite Hankel form
- [x] infinite-support nondegeneracy upgraded to matrix positive definiteness
- [x] strict determinant theorem proved
- [x] canonical prime--arch moment specialization proved
- [x] RH capstone composed with the existing determinant equivalence
- [x] exact module builds
- [x] accepted-axiom audit
