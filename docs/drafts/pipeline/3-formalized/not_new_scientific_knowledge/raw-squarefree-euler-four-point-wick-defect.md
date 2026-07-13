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

The nonzero defect is a canonical four-interaction coordinate, and it now has an exact positive
realization.  Let one shared Rademacher spin `epsilon` take the values `+1,-1` with equal weight and
put `X_i=a_i epsilon`.  For every even subset `S`,

```text
E product_(i in S) X_i=product_(i in S) a_i.
```

Hence the raw two- and four-index Euler squarefree coefficients are exactly the even moments of
this rank-one spin packet, and

```text
D_0123=E[X_0X_1X_2X_3]
  -E[X_0X_1]E[X_2X_3]
  -E[X_0X_2]E[X_1X_3]
  -E[X_0X_3]E[X_1X_2]
```

is its fourth joint cumulant.  Thus the no-go retires the Gaussian/dimer interpretation but
positively selects a shared-spin/higher-cumulant interpretation.

For the ordered noncrossing partition lattice, Lean also proves that the fourth free cumulant is

```text
kappa_4^free(X_0,X_1,X_2,X_3)=-a_0a_1a_2a_3.
```

The classical Wick defect is this free cumulant minus the excluded crossing pair product
`E[X_0X_2]E[X_1X_3]`.  Thus the positive successor is exact on both sides: the raw packet is a valid
shared-spin moment law, but for positive `a_i` it is not itself a positive compound-free-Poisson
jump packet.  Any free-probability successor needs completion-sensitive block coupling before
scalarization.

A surviving monomer--dimer or stability route must now do one of three precise things:

1. construct a new completed prime--Gamma pair kernel whose matching sums reproduce the completed
   source, rather than use raw Euler products; or
2. retain `D_0123` as the shared-Rademacher higher interaction and prove that the resulting source
   specialization lies in a particular stable hypergraph-matching or ferromagnetic class; or
3. treat the all-order shared-spin cumulants as input to a noncrossing/free-cumulant assembly, where
   higher interactions are structural rather than defects.

Arbitrary hypergraph matching polynomials do not inherit Heilmann--Lieb real-rootedness, so the
second repair requires its own stability theorem.

## Formal certificate

The module uses the existing formal `squarefreeMonomial` from
`RHProofLab/EulerProductArithmetic.lean` and proves:

- `eulerSquarefreeWickFourDefect_eq`;
- `sharedRademacherMoment_eq_of_even_card`;
- `eulerSquarefreeWickFourDefect_eq_sharedRademacherCumulant`;
- `sharedRademacherFreeFourCumulant_eq`;
- `eulerSquarefreeWickFourDefect_eq_freeCumulant_sub_crossing`;
- `eulerSquarefreeWickFourLaw_iff`;
- `not_eulerSquarefreeWickFourLaw_of_nonzero`.

The exact module builds.  Axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] raw four-point Euler coefficient expressed in the existing finite source language
- [x] three pairing sum computed
- [x] exact defect proved
- [x] vanishing locus classified
- [x] direct raw-Euler matching proposal retired
- [x] raw even squarefree packet identified with a positive shared-Rademacher moment law
- [x] exact negative fourth free cumulant and crossing-pair correction formalized
- [x] completed-kernel, stable-hypergraph, and free-cumulant positive successors isolated
- [x] exact Lean build
- [x] accepted-axiom audit
