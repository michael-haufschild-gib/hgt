# Allocation equality on every boundary stratum

- **ID:** biscale-allocation-boundaries-1810
- **Stage:** 3-formalized
- **Type:** CLASSICAL REDUCTION
- **Parent:** [classical-boundary audit](../3-formalized/biscale-classical-boundaries-1810.md), checklist item 2

For arbitrary real `W,A,a,q`, equality in the two-dimensional support bound is exactly

`Wa+Aq = sqrt(W²+A²)sqrt(a²+q²)`

`↔ Aa=Wq and Wa+Aq≥0`.

The Lagrange identity identifies the difference of the squares with `(Aa−Wq)²`. Equality implies zero determinant and nonnegative dot product. Conversely those two conditions give equal squares of two nonnegative quantities, hence equality. No positive-total or nonzero assumption is needed.

For any finite set of pairs `(a_i,q_i)`, put `W=Σa_i`, `A=Σq_i`, `S=sqrt(W²+A²)` and `C=Σsqrt(a_i²+q_i²)`. Then

`C=S ↔ if W=A=0 then every (a_i,q_i)=(0,0)`

`else every i satisfies Aa_i=Wq_i and Wa_i+Aq_i≥0`.

When `S=0`, equality is a sum of nonnegative lengths equal to zero, so every vector vanishes. When `S>0`, each support deficit

`S sqrt(a_i²+q_i²)−(Wa_i+Aq_i)`

is nonnegative and their sum is exactly `S(C−S)`. Equality of the costs is therefore equivalent to zero deficit at every index; apply the pair criterion above.

For the actual allocation problem use `q_i=|b_i|`. This includes negative total origin weight, zero total origin weight, zero transverse mass and an empty index set. If transverse mass is zero and `W>0`, every nonnegative allocation with sum `W` is a minimizer; uniqueness is false. If `W=0` and transverse mass is positive, the unique minimizing origin allocation is identically zero. If both totals vanish, only the zero allocation minimizes. These are the exact boundary qualifications to the existing positive-total uniqueness theorem.

Corpus query `origin allocation equality zero total boundary Lagrange` returned the positive-total uniqueness theorem, the unconditional exact-minimum construction and the norm lower bound. It did not supply the all-strata equality statement among its returned inventory. Coverage was a source snapshot with unmeasured semantic completeness. This is elementary norm geometry, not a novelty claim.

- [x] Exact all-strata statement and dependency-closed symbolic proof.
- [x] `AllocationBoundaryClassification.lean` contains the pair and finite allocation criteria with no mathematical premise binders.
- [x] Final artifact-producing named-source `lake --old env lean -j 1` audit exits 0 without diagnostics. Scratch axiom audit of both proofs reports only `propext`, `Classical.choice`, and `Quot.sound`.
- [x] Leaf wired without compiling the umbrella.
- [x] Corpus index refreshed. Formal lint checked: no owned wiring or proof-placeholder errors. The global gate reports three concurrent BezoutValuationIncidence wiring errors and package-root `TransHorizonIncidenceMechanics.lean` placement, outside this component's scope.
