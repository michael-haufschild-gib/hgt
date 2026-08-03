# Claim trace audit

Internal audit; not part of submission.

Primary formal module:

`formal/GaloisForLFunctions/RHTower/PreQuasiGelfandTwoSidedSingularDefect.lean`

Umbrella:

`formal/GaloisForLFunctions/RHTower.lean`

## Abstract classification

| Manuscript claim | Lean declaration |
|---|---|
| Hilbert pre-quasi pair hypotheses are represented explicitly | `HilbertPreQuasiPair` |
| Quasi condition is adjoint-domain/range equality | `HilbertQuasiCompatibility` |
| Canonical negative partner is inverse adjoint | `canonicalNegativeEmbedding` |
| Dense range of positive embedding kills adjoint kernel | `adjoint_ker_eq_bot_of_denseRange` |
| Canonical inverse adjoint is injective | `canonicalNegativeEmbedding_injective` |
| Canonical partner satisfies pivot pairing | `canonicalNegativeEmbedding_pairing` |
| Every compatible negative embedding lies below canonical inverse adjoint | `compatible_le_canonicalNegativeEmbedding` |
| Necessity: pre-quasi graph lies in canonical graph | `preQuasi_graph_le_canonical_graph` |
| Canonical negative range equals positive-adjoint domain | `canonicalNegativeEmbedding_range_eq_adjointDomain` |
| Quasi compatibility iff canonical saturation | `preQuasi_quasi_iff_eq_canonicalNegative` |
| Sufficiency: closed bi-dense canonical graph subspace yields pre-quasi pair | `preQuasi_of_closed_biDense_canonicalGraphSubspace` |

## Sharp criterion

| Manuscript claim | Lean declaration |
|---|---|
| Adjoint surjective iff bounded inverse estimate | `adjoint_surjective_iff_antilipschitz` |
| Dense range makes adjoint injective | `adjoint_injective_of_denseRange` |
| Hyperplane image is dense when normal misses adjoint range | `dense_image_orthogonal_hyperplane` |
| Two-sided singularity definition | `IsTwoSidedSingular` |
| Proper closed bi-dense subspace definition | `HasProperClosedBiDenseSubspace` |
| Two missing lower bounds produce one bi-dense hyperplane | `exists_biDense_hyperplane_of_twoSidedSingular` |
| One lower bound forces closed bi-dense subspace to be top | `closed_biDense_eq_top_of_antilipschitz` |
| Sharp iff criterion | `twoSidedSingular_iff_hasProperClosedBiDenseSubspace` |

## Explicit model

| Manuscript claim | Lean declaration family |
|---|---|
| Two-channel Hilbert model and reciprocal weights | `PQIndex`, `PQHilbert`, `pqInv`, `pqPWeight`, `pqQWeight` |
| Bounded graph coordinate maps | `pqP`, `pqQ` |
| Coordinate maps injective and densely ranged | `pqP_injective`, `pqQ_injective`, `pqP_denseRange`, `pqQ_denseRange` |
| Hyperplane normal is square summable | `pqVWeight_summable_sq`, `pqV` |
| Normal misses both coordinate ranges | `pqV_not_mem_range_pqP`, `pqV_not_mem_range_pqQ` |
| Hyperplane coordinate images are dense | `pqDefectDomain_dense`, `pqDefectRange_dense` |
| Defect graph is closed | `pqDefectGraph_eq_kernels`, `pqDefectGraph_isClosed` |
| Defect graph is single-valued | `pqDefectGraph_vertical_unique` |
| Closed negative restriction has dense domain/range and is injective | `pqDefectNegativeEmbedding_isClosed`, `pqDefectNegativeEmbedding_dense_domain`, `pqDefectNegativeEmbedding_dense_range`, `pqDefectNegativeEmbedding_injective` |
| Positive and canonical negative maximal diagonals | `pqPositiveEmbedding`, `pqCanonicalNegativeEmbedding` |
| Maximal diagonal operators are self-adjoint | `pqPositiveEmbedding_isSelfAdjoint`, `pqCanonicalNegativeEmbedding_isSelfAdjoint` |
| Pairing identity | `pqDefect_pairing` |
| Exact pre-quasi hypotheses | `pqDefect_is_preQuasi` |
| Quasi compatibility fails | `pqDefect_not_quasi` |
| Existential counterexample | `exists_hilbertPreQuasiPair_not_quasi` |

## Verification evidence

- Direct foreground elaboration:
  `lake env lean GaloisForLFunctions/RHTower/PreQuasiGelfandTwoSidedSingularDefect.lean` — pass.
- Targeted module build:
  `lake build GaloisForLFunctions.RHTower.PreQuasiGelfandTwoSidedSingularDefect` — pass.
- Axiom audit for five headline declarations — only `propext`, `Classical.choice`, `Quot.sound`.
- Forbidden-token scan in module — no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`.
- Umbrella import present in `GaloisForLFunctions.RHTower`.
- Global `scripts/formal_tools.py lint` reaches unrelated pre-existing `HTGeometry` umbrella
  reachability errors. None names this module. This repository-wide gate is not falsely reported
  as green.

## Claim exclusions

- Lean formalizes standard Hilbert same-space model used for counterexample and abstract
  classification; manuscript does not claim a formal Banach-space theorem.
- Paper’s operator-language equivalence “coordinate two-sided singular iff canonical operator is
  unbounded and not bounded below” is proved on paper from graph norm. Formal exact sharp theorem
  is stated at more primitive coordinate-map level.
- No numerical or finite-dimensional evidence is used as proof.
