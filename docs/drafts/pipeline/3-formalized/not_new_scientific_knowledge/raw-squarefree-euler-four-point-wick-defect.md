# Raw squarefree Euler coefficients fail the four-point Wick law

- **ID:** `raw-squarefree-euler-four-point-wick-defect`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NO-GO] [POSITIVE FOUR-INTERACTION RESIDUE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/EulerSquarefreeWickDefect.lean`
- **Consumer:** `../../1-in-progress/prime-source-monomer-dimer-matching-limit-rh.md`

## Theorem

For four local coefficients `a_0,a_1,a_2,a_3`, the finite Euler expansion gives the squarefree
four-index coefficient

```text
A_0123 = a_0 a_1 a_2 a_3.
```

If the two-index coefficients are declared to be dimer edge weights, the three Wick pairings give

```text
A_01 A_23 + A_02 A_13 + A_03 A_12
  = 3 a_0 a_1 a_2 a_3.
```

Lean proves that the defect is exactly

```text
D_0123 = -2 a_0 a_1 a_2 a_3.
```

Over the complex numbers, the proposed four-point Wick law holds if and only if at least one local
coefficient vanishes.  Hence a genuine four-local-factor Euler packet cannot be the moment packet
of the pairwise matching model obtained by using its raw two-index coefficients as edges.

## Positive residue

The nonzero defect is a canonical four-interaction coordinate.  A surviving monomer--dimer route
must do one of two precise things:

1. construct a new completed prime--Gamma pair kernel whose matching sums reproduce the completed
   source, rather than use raw Euler products; or
2. retain `D_0123` as a higher interaction and prove that the resulting source specialization lies
   in a particular stable hypergraph-matching class.

Arbitrary hypergraph matching polynomials do not inherit Heilmann--Lieb real-rootedness, so the
second repair requires its own stability theorem.

## Formal certificate

The module uses the existing formal `squarefreeMonomial` from
`RHProofLab/EulerProductArithmetic.lean` and proves:

- `eulerSquarefreeWickFourDefect_eq`;
- `eulerSquarefreeWickFourLaw_iff`;
- `not_eulerSquarefreeWickFourLaw_of_nonzero`.

The exact module builds.  Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] raw four-point Euler coefficient expressed in the existing finite source language
- [x] three pairing sum computed
- [x] exact defect proved
- [x] vanishing locus classified
- [x] direct raw-Euler matching proposal retired
- [x] completed-kernel and stable-hypergraph positive successors isolated
- [x] exact Lean build
- [x] accepted-axiom audit
