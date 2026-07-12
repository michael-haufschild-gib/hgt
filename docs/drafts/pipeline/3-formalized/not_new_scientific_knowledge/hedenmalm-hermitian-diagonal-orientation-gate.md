# Hedenmalm Hermitian-diagonal orientation gate

- **ID:** `hedenmalm-hermitian-diagonal-orientation-gate`
- **Stage:** 3-formalized
- **Type:** BRIDGE / EXACT HILBERT--POLYA ORIENTATION GATE
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [SIGN OPEN]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/XiHedenmalmOrientationGate.lean`

## Unconditional theorem

Let `B_A` be the removable Hedenmalm--de Branges Bezoutian for `A=XiC`, and let

```text
T(z)=continuedPrimeArchSourceRelativeTrace(z).
```

At every regular point `z` of the centered upper half-strip,

```text
0<Im z<1/2,
```

one has the exact Hermitian-diagonal identity

```text
B_A(z,conj(z))
 =|A(z)|^2
   *[(T(conj(z))-T(z))/(z-conj(z))].                       (1)
```

The continued source obeys Schwarz conjugation on this domain, so the second factor is real and
equals

```text
-Im T(z)/Im z.                                             (2)
```

Moreover `A(z)` is nonzero on the stated source domain. Hence the positive norm-square factor in
`(1)` may be cancelled without losing sign, and the following are equivalent:

```text
B_A(z,conj(z)) has nonnegative real part
  at every regular upper-strip point;

Im T(z)<=0
  at every regular upper-strip point;

RH.                                                        (3)
```

No Xi-zero enumeration and no RH assumption enters the identity or the equivalence.

## Hilbert--Polya consequence

Full positive definiteness of `B_A` is sufficient to build a de Branges Hilbert space, but it is
stronger than needed for the implication to RH. Scalar Hermitian-diagonal orientation on the
cofinal upper-strip family already excludes every off-line zero.

Thus the direct source target has two levels:

1. prove the scalar source sign `(2)` to prove RH;
2. prove full Gram positivity to obtain the intended positive Hilbert--Polya realization.

The module completes neither sign theorem. It prevents the construction problem from being
mistaken for a missing moment reconstruction or a need for arbitrary off-diagonal test packets.

## Parent-theory collision and score

Equation `(1)` is the usual logarithmic-derivative congruence for a Hermite--Biehler Bezoutian.
Equation `(2)` is elementary complex algebra, and `(3)` reuses the classical one-Cauchy
anti-Herglotz criterion already formalized in the corpus.

Honest score: **48/100**. This is exact route compression, not new scientific knowledge and not an
orientation proof.

## Formal theorem surface

- `xiHedenmalmBezoutian_conj_eq_normSq_mul_sourceDiagonal`;
- `XiHedenmalmUpperHermitianDiagonalNonnegative`;
- `xiHedenmalmUpperHermitianDiagonalNonnegative_iff_source`;
- `xiHedenmalmUpperHermitianDiagonalNonnegative_iff_riemannHypothesis`.

The exact module build passes. The headline declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact Hermitian-diagonal identity
- [x] positive norm-square congruence factor
- [x] source-sign equivalence
- [x] exact RH equivalence
- [x] exact build and axiom audit
- [ ] source proof of the scalar sign
- [ ] full source Gram factorization
- [ ] RH
