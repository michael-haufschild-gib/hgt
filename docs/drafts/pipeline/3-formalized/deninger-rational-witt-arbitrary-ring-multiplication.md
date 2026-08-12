# Deninger rational-Witt multiplication over arbitrary rings

- **ID:** `deninger-rational-witt-arbitrary-ring-multiplication`
- **Stage:** 3-formalized
- **Route:** L — rational-Witt source foundation
- **Status:** closed in Lean 4 (2026-08-12)
- **Primary source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1, Section 1 background preceding Proposition 1.1.

## Exact theorem

For every commutative ring `A`, including rings with nilpotents, the literal normalized rational
power-series carrier `W_rat(A)` is closed under canonical big-Witt multiplication. It therefore
inherits a canonical commutative-ring structure as a subring of `W(A)`, with literal
rational-function multiplication as Witt addition and

```text
[a] * [b] = [ab].
```

No field, domain, reducedness, torsion-freeness, characteristic, or splitting hypothesis occurs in
the arbitrary-ring closure theorem.

## Construction

For normalized polynomials `P,Q`, define their Witt tensor polynomial by the fixed-degree
resultant

```text
(-1)^(mn) Res_U(P(U), U^n Q(T/U)).
```

Fixed degree bounds are part of the definition; this prevents specialization into a ring with
nilpotents from invalidating the formula when leading coefficients collapse.

The proof has four dependency-closed layers:

1. Over a field, split normalized polynomials into finite multisets of unit Teichmüller factors and
   prove the resultant formula gives all pairwise products.
2. Prove compatibility with literal big-Witt multiplication over an algebraically closed field.
3. Descend through a universal integer polynomial ring and its algebraically closed fraction field.
4. Evaluate universal coefficients into an arbitrary commutative target ring.

For fractions `P/Q` and `R/S`, closure is witnessed explicitly by

```text
((P ⊙ R)(Q ⊙ S)) / ((P ⊙ S)(Q ⊙ R)).
```

The image of the literal carrier is then a `Subring` of the canonical big-Witt ring. An injective
carrier equivalence transports its `CommRing` structure back to literal rational functions.

## Formal certificate

Module:

```text
GaloisForLFunctions.RHTower.DeningerRationalWittCanonicalMultiplication
```

Headline declarations:

- `deningerWittTensorPolynomial_bigWitt_mul_arbitrary`
- `deningerWittTensorPolynomial_coeff_zero_arbitrary`
- `deningerRationalBigWittElement_mul_closed`
- `deningerCanonicalRationalWittSubring`
- `DeningerCanonicalRationalWittRing`
- `deningerCanonicalRationalWittEmbedding`
- `deningerCanonicalRationalWittRing_additiveVal_add`
- `deningerCanonicalRationalWittTeichmuller_mul`
- `deningerCanonicalRationalWittMap`

Direct foreground Lean check passed. Exact-module build, axiom audit, and formal lint are recorded in
the closing audit. Module is imported by the `RHTower` umbrella.

## Novelty boundary

The mathematical closure theorem is classical. New contribution is first in-corpus unconditional
Lean proof on the literal localized-polynomial carrier, including nilpotent coefficient rings and
without target ghost injectivity. This closes prerequisite that previously blocked formal statement
of Deninger Proposition 1.1 as a ring-localization isomorphism. Proposition 1.1 itself remains next
primary-source obligation.
