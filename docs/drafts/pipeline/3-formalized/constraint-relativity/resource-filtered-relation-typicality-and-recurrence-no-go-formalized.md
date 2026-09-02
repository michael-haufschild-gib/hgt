# Resource-filtered relation typicality and recurrence no-go — formalized

- **ID:** `resource-filtered-relation-typicality-and-recurrence-no-go-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `resource-filtered-relation-typicality-and-recurrence-no-go.md`
- **Status:** `[LEAN COMPLETE] [NO SORRY] [NO PROJECT AXIOMS]`

## Lean modules

| Module | Formal content |
|---|---|
| `HTGeometry/AnalyticMatrixRankStratification.lean` | analytic determinant/minor infrastructure, generic rank stratum, null exceptional locus, one-parameter discreteness/finiteness |
| `HTGeometry/ConstraintRelativity/ResourceFilteredRelations.lean` | transported relation rank, structural defect, soft visibility, recurrence no-go, exact tidal acceleration, bipartite classifier |
| `HTGeometry/ConstraintRelativity/HaarTypicalResourceRank.lean` | literal unitary Haar-null nontransverse locus and exact intersection-rank coordinates |
| `HTGeometry/ConstraintRelativity/AggregateTidalTomography.lean` | commutator Casimir identity and full aggregate coefficient `(5.7)` |
| `HTGeometry/ConstraintRelativity/InteractionCrossFibre.lean` | interaction/locality classifier and two-qubit witness reused by this card |

All are wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

1. `finrank_transportedRelation`, `accessibleRelationRank_lower_bound`, and
   `genericAccessibleRank_eq_lowerBound_of_exists_transverse` prove Theorem 2.1(1),(5).
2. `analytic_matrixRankDefect_generic_open_dense_fullMeasure` and
   `analyticRelationGenericStratum_open_dense_exceptional_volume_zero` prove Theorem 2.1(2),(3)
   uniformly in every finite-dimensional real analytic coordinate chart.
3. `analyticRelationExceptionalSet_discreteTopology` and
   `analyticRelationExceptionalSet_inter_compact_finite` prove Theorem 2.1(4).
4. `accessibleRank_eq_lowerBound_add_structuralDefect` and `structuralDefect_pos_iff` prove
   `(2.11)` and its exact rank-certificate criterion.
5. `finiteUnitaryHaar_framedAccessibleRelationRank_eq_grassmann` proves Corollary 2.2 for arbitrary
   complex relation and observer frames. `framedRelationEquivIntersection`
   identifies the matrix kernel with the literal moving-subspace intersection.
6. `continuous_softVisibility` formalizes the continuous visibility distinction.
7. `recurrence_no_go` proves Theorem 4.1 for an exact additive `NNReal` semiflow action.
8. `normalAcceleration`, `visibleAcceleration`, and `reporterTidalForm` prove `(5.2)`--`(5.4)`.
9. `all_matrixReporterTidalForms_eq_zero_iff_localForm` proves the finite bipartite classifier.
10. `aggregateBoundaryHiddenAcceleration_full_eq` proves `(5.7)` for every bipartite Hermitian
    Hamiltonian, including exact removal of local and scalar components.
11. `twoQubit_ZZ_exposure` supplies Example 5.4.

## Infrastructure

The analytic engine constructs a nonzero maximal-rank normal-form minor, proves its determinant
analytic, contains every exceptional point in its zero set, and derives openness, density,
Lebesgue-nullity, discreteness, and compact finiteness. The Haar proof constructs an explicit
transverse unitary witness and transfers Euclidean analytic nullity to Haar measure through finite
unitary exponential words. Aggregate tomography proves the matrix commutator Casimir identity
rather than assuming it.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/AnalyticMatrixRankStratification.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ResourceFilteredRelations.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/HaarTypicalResourceRank.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/AggregateTidalTomography.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.HaarTypicalResourceRank
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.AggregateTidalTomography
```

`#print axioms` for the principal declarations returns only `propext`, `Classical.choice`, and
`Quot.sound`.
