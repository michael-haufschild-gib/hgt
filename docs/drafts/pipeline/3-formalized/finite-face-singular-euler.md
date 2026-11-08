# Singular Euler characteristic of finite face realizations

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Arithmetic signed localization](riac-prime-vertex-signed-localization.md)

For every finite downward-closed family `K` of faces on a finite vertex set,
its actual barycentric realization has finite-dimensional rational singular
homology, vanishing in sufficiently high degrees, and

`χ(H_*(|K|;ℚ)) = Σ_(∅≠S∈K) (−1)^(|S|−1)`.

The positive-coordinate vertex stars form a finite open cover. An intersection
indexed by a nonempty face contracts to that face's barycenter; other
intersections are empty. Relative singular-chain excision and the long exact
sequence prove two-set Euler additivity and homology finiteness. Induction
on the cover gives inclusion-exclusion and the displayed formula. No
simplicial-to-singular comparison or finiteness premise is assumed.

[FiniteFaceSingularEuler.lean](../../../../formal/GaloisForLFunctions/HodgeTheoryWithoutVarieties/FiniteFaceSingularEuler.lean)
formalizes `finiteCover_homology_euler`, `faceStarIntersectionContraction`
and `finiteFace_singular_euler`. The production file passed its direct Lean
check; twelve capstone audits use only `propext`, `Classical.choice` and
`Quot.sound`. This is classical finite-polyhedral topology, supplying the
actual singular-homology comparison for the arithmetic application.
