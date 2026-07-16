# Coprime prime-residue anchored interaction law

- **ID:** `coprime-prime-residue-anchored-interaction-law`
- **Stage:** 3-formalized
- **Type:** NATURAL ARITHMETIC HT THEOREM / CANONICAL RELATIVE INTERACTION
- **Scientific status:** `[UNCONDITIONALLY FORMALIZED] [NOVELTY PROVISIONAL]`
- **Parent:** `finite-quotient-interaction-cohomology-law.md`
- **Statement:** For coprime positive moduli `m,n`, the actual joint unit-residue profile of the
  primes is tail-complete.  Inside its joint observable field, the identity-anchored mixed
  differences form a canonical complement to all separate-modulus observables, of exact rank
  `(phi(m)-1)(phi(n)-1)`; their prime carriers are relatively differentially independent over the
  two marginal fields and adjoining them generates the full joint residue field.

## Theorem

Put

```text
A = (Z/mZ)^x,  B = (Z/nZ)^x,
y(p) = (p mod m, p mod n),
```

with the finitely many nonunit primes assigned the identity.  Dirichlet's theorem and the Chinese
remainder theorem give tail completeness: every element of `A x B` occurs at arbitrarily large
primes.

Let `I_A` and `I_B` be the row- and column-observable spaces in `C^(A x B)`.  Define the canonical
anchored interaction space

```text
Q_(m,n) = {f : A x B -> C | f(a,1)=0 and f(1,b)=0 for all a,b}.
```

Every joint observable has the unique decomposition

```text
f(a,b)
 = f(a,1)
 + (f(1,b)-f(1,1))
 + (f(a,b)-f(a,1)-f(1,b)+f(1,1)).
```

Consequently

```text
C^(A x B) = (I_A + I_B) direct_sum Q_(m,n),
dim Q_(m,n) = (phi(m)-1)(phi(n)-1).
```

The quotient interaction cohomology is canonically linearly equivalent to `Q_(m,n)`.  If
`q_1,...,q_delta` is the formal canonical finite basis selected from this named space, its prime
carriers satisfy

```text
carrier(q_1),...,carrier(q_delta)
  are differentially independent over K_m K_n,

(K_m K_n)<carrier(q_1),...,carrier(q_delta)>_diff = K_(m,n),

delta = (phi(m)-1)(phi(n)-1).
```

Here `K_m`, `K_n`, and `K_(m,n)` are the embedded differential fields of the two marginal residue
observables and all joint residue observables, respectively.

## Positive law

> **Coprime residue coupling has an exact irreducible HT capacity.**  Two separate modulus fields
> omit a canonical mixed-difference sector.  That sector contains exactly
> `(phi(m)-1)(phi(n)-1)` relative hypertranscendental directions, and adjoining precisely those
> directions reconstructs the joint residue field.

## Formal declaration ledger

| Clause | Declaration |
|---|---|
| prime unit-residue profile | `primeUnitResidueProfile` |
| every unit residue recurs infinitely | `recurringValueSet_primeUnitResidueProfile` |
| prime residue tail completeness | `cofiniteTailDenseOn_primeUnitResidueProfile` |
| unit-group CRT equivalence | `coprimeUnitChineseRemainderEquiv` |
| actual joint coprime profile | `coprimePrimeUnitResidueProfile` |
| joint tail completeness | `cofiniteTailDenseOn_coprimePrimeUnitResidueProfile` |
| anchored interaction space | `productAnchoredInteractionSubmodule` |
| closed mixed-difference part | `productAnchoredInteractionPart` |
| unique row-column-interaction decomposition | `product_decompose_row_column_anchored` |
| canonical complement law | `productAnchoredInteractionSubmodule_isCompl` |
| exact finite-set interaction rank | `productFiniteQuotientInteractionDefect_eq` |
| arithmetic relative-HT capstone | `cofiniteTailDenseOn_coprimePrimeResidueAnchoredInteraction` |

Formal module:

- `formal/GaloisForLFunctions/HTGeometry/CoprimePrimeResidueInteraction.lean`.

The leaf module and direct file check pass.  The capstone axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Novelty boundary and anti-theatre gate

Classical inputs carrying no novelty claim are Dirichlet's theorem, CRT, finite-dimensional
row/column interaction decompositions, Euler-totient counts, and differential-transcendence-basis
machinery.  The candidate new statement is their exact arithmetic-field synthesis: the actual
prime residue profile realizes the named mixed-difference quotient as a relative HT extension of
exact totient-product rank and exact joint-field generating power.

The theorem is stronger than the preceding arbitrary finite-quotient existence result because the
arithmetic unit groups select the interaction representative by their identities.  It remains a
pairwise theorem.  The proposed all-orders conductor-support tower, character-support
identification, Euler-fusion compatibility, and analytic Dirichlet-germ realization remain open.

## RH pressure test

This theorem does not identify its carrier with zeta or prove an RH criterion.  It gives a positive
obligation for multi-conductor proof architectures: coupling two coprime residue systems requires
control of an exact mixed sector of totient-product rank.  Separate-modulus differential identities
alone cannot reconstruct the joint residue field.

## Antagonistic score

- **Correctness / rigor:** 100/100 on the stated surface.
- **Novelty:** 88/100 provisional; the exact arithmetic relative-HT bridge has not been located in
  targeted literature searches, but specialist priority review remains necessary.
- **Scientific significance:** 91/100 inside finite prime-supported HT geometry.  The all-orders
  spectrum and analytic transfer are required for a field-defining theorem.
- **Anti-theatre:** pass.  The exact relative differential independence and exact field
  reconstruction survive after removing the elementary rank formula and all physical language.
