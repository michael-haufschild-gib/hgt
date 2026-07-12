# Hedenmalm pointed analytic-moment determinacy

- **ID:** `hedenmalm-pointed-analytic-moment-determinacy`
- **Stage:** 3-formalized
- **Type:** BRIDGE / POSITIVE SOURCE-RIGIDITY LAW
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [POSITIVITY OPEN]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmMomentDeterminacy.lean`

## Unconditional theorem

Let

```text
G(z)=normalizedPrimeArchMomentGerm(z),
T(z)=continuedPrimeArchSourceRelativeTrace(z),
A(z)=XiC(z).
```

The normalized moment germ is not an unpointed formal moment sequence. It has the exact global odd
lift

```text
T(z)=-zG(z).                                               (1)
```

If `g` is analytic at the center and every iterated derivative of `g` there equals the
corresponding derivative of `G`, then

```text
g=G as analytic germs,                                    (2)
oddTracePreimage(g)=T as analytic germs.                  (3)
```

The fixed theta trace obeys the source differential constraint

```text
A'(z)+zG(z)A(z)=0                                         (4)
```

near the center. Consequently the Hedenmalm--de Branges candidate has the pointed-moment
presentation

```text
E(z)=A(z)+iA'(z)=A(z)(1-i zG(z)).                          (5)
```

For sufficiently central distinct nodes `z` and `v`, its removable derivative Bezoutian satisfies

```text
B_A(z,v)
 =A(z)A(v) dslope(w |-> wG(w),z,v)
 =A(z)A(v)(vG(v)-zG(z))/(v-z).                            (6)
```

The normalization `A(0)=XiC(0)` makes `(4)` globally determinate in the entire category:

```text
F entire,
F(0)=XiC(0),
F'(z)+zG(z)F(z)=0 near 0
  ==> F=XiC on C.                                         (7)
```

The proof applies analytic-order comparison to the difference of two solutions and then the
identity theorem. Equations `(1)`--`(7)` contain no Xi-zero enumeration and require no RH
assumption.

## Hilbert--Polya consequence

The complete prime--archimedean moment jet is rigid because it belongs to a pointed analytic-germ
category with an exact nonflat source lift. Therefore the indeterminate-moment-fiber ambiguity does
not survive in this local carrier.

This does not orient the carrier. Neither analytic determinacy nor the algebraic reconstruction
`(6)` proves that `B_A` is a positive kernel. The remaining theorem is a global source-defined Gram
factorization, contraction, or canonical extremal selection whose positivity is not imported from
the Xi divisor.

## Parent-theory collision and score

Analytic germs are determined by their complete Taylor jets, normalized divided differences invert
multiplication by the centered coordinate, and a first-order logarithmic-derivative identity gives
`(5)`--`(6)` by algebra. The result is a useful exact seam between the moment, Euler--Gamma,
Hedenmalm, and de Branges coordinates, but the mechanism is classical.

Honest score: **52/100**. It closes a real logical gap in the route but is not publication-level new
scientific knowledge and supplies no new positivity mechanism.

## Formal theorem surface

- `analyticAt_eventuallyEq_of_all_iteratedDeriv_eq`;
- `oddTracePreimage_normalizedPrimeArchMomentGerm_eq_source`;
- `normalizedPrimeArchMomentGerm_allOrder_determinate`;
- `normalizedPrimeArchMomentGerm_allOrder_determines_sourceTrace`;
- `continuedPrimeArchSourceRelativeTrace_eq_neg_pointedMomentFlux`;
- `deriv_XiC_eventuallyEq_neg_pointedMomentFlux_mul`;
- `analyticAt_eventuallyEq_zero_of_deriv_eq_mul`;
- `XiC_unique_entire_solution_of_pointedMomentConstraint`;
- `xiHedenmalmDeBrangesE_eventuallyEq_pointedMomentE`;
- `xiHedenmalmBezoutian_eq_pointedMomentBezoutian_of_deriv_eq`;
- `xiHedenmalmBezoutian_eventuallyEq_pointedMomentBezoutian_offDiagonal`.

The exact module build passes. The headline declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No RH, positivity, zero-reality, moment-determinacy, or
source-lift hypothesis is introduced for the instantiated identities `(1)`, `(4)`, `(5)`, and
`(6)`.

## Gates

- [x] exact odd source lift
- [x] analytic all-order jet determinacy
- [x] local theta-trace differential constraint
- [x] global normalized entire-solution uniqueness
- [x] local Hedenmalm candidate reconstruction
- [x] local off-diagonal Bezoutian reconstruction
- [x] exact build
- [x] axiom audit
- [ ] global pointed source Gram factorization
- [ ] positivity without divisor input
- [ ] RH
