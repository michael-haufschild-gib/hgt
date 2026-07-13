# Support-cardinality boundary jets do not determine matching incidence

- **ID:** `prime-word-matching-incidence-boundary-germ-blindness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / `[NO-GO] [POSITIVE MULTIVARIATE REPAIR] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeWordMatchingIncidenceNoGo.lean`
- **Consumer:** `../../1-in-progress/prime-source-monomer-dimer-matching-limit-rh.md`

## Theorem

Consider two unit-weight ensembles of two-letter words on four labels:

```text
A = {[0,1], [2,3]},
B = {[0,1], [0,2]}.
```

Every word in either ensemble has support cardinality two.  Lean proves that their one-variable
marked ensemble deformations are identical, hence every boundary jet at the cancellation point is
identical.  Nevertheless the two supports in `A` are disjoint and form a two-edge matching, while
the two supports in `B` intersect and do not.

Thus the complete support-cardinality germ cannot determine even the first nontrivial matching
incidence number.

## Positive repair

Lean also sums the squarefree multivariate support markers over the two ensembles and proves that
the resulting polynomials differ.  A specialization supported on labels `2` and `3` reads `1` on
`A` and `0` on `B`.

The matching-polynomial input is therefore precise:

```text
prime word
  -> squarefree multivariate support monomial
  -> disjoint-support incidence sums
  -> matching polynomial.
```

The scalar boundary germ may be retained as a grading, but it cannot replace the multivariate
incidence packet.

## Formal certificate

The module proves:

- `disjointTwoEdgeEnsemble_deformation_eq_intersecting`;
- `matchingEdge01_edge23_disjoint`;
- `matchingEdge01_edge02_not_disjoint`;
- `multivariateMarker_separates_twoEdgeMatchingIncidence`;
- `boundaryGerm_blind_to_twoEdgeMatchingIncidence`.

The exact module builds.  Axiom audits of the equality, positive repair, and capstone report only
`propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] equal complete scalar boundary germs proved
- [x] differing two-edge matching incidence proved
- [x] multivariate support repair proved
- [x] exact Lean build
- [x] accepted-axiom audit
