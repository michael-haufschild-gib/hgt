# Claim trace audit

Status: active strict ledger. Manuscript may not retain a mathematical claim without a compiled unconditional Lean witness below.

## Universal observer law

| ID | Manuscript claim | Lean declaration |
|---|---|---|
| O1 | One-observer dense-image/adjoint-range equivalence | `dense_image_iff_orthogonal_inf_adjointRange_eq_bot` |
| O2 | Arbitrary-family observer–annihilator law | `dense_images_iff_orthogonal_avoids_adjointRanges` |
| O3 | Closed subspaces below a common normal yield dense orthogonal defects | `dense_orthogonal_image_of_le_countableWovenNormalSpace` |
| O4 | Nonzero normal gives a proper orthogonal defect | `orthogonal_ne_top_of_ne_bot` |
| O5 | Arbitrary nonempty-family normal rigidity iff adjoint ranges cover source pointwise | `closed_common_avoidance_rigid_iff_adjointRanges_cover` |
| O6 | Arbitrary nonempty-family dense-image rigidity iff adjoint ranges cover source pointwise | `closed_common_dense_image_rigid_iff_adjointRanges_cover` |

## Coercivity and weaving

| ID | Manuscript claim | Lean declaration |
|---|---|---|
| W1 | Injective bounded operator has nonclosed range iff it is noncoercive | `hilbertRangeSingular_iff_no_antilipschitz` |
| W2 | Singularity persists after restriction to orthogonal complement of finite-dimensional subspace | `hilbertRangeSingular_domRestrict_orthogonal` |
| W3 | Singular operator has arbitrarily small unit vectors | `exists_unit_norm_map_lt_of_hilbertRangeSingular` |
| W4 | Countable simultaneous orthonormal small-vector array | `exists_countable_singular_orthonormalArray` |
| W5 | Weight sequence tends to zero | `tendsto_pqInv_zero` |
| W6 | Countable woven coefficient weights are square-summable | `countableWovenNormalWeight_summable_sq` |
| W7 | Countable woven coefficient space is closed | `countableWovenNormalSubspace_isClosed` |
| W8 | Countable woven normal avoids each selected adjoint range | `countableWovenNormalSpace_inf_adjointRange_eq_bot` |
| W9 | Woven normal contains a countably indexed linearly independent family | `countableWovenNormalSpace_has_countable_independent_family` |
| W10 | Coercive observer forces every closed common dense-image defect to be full | `countable_coercive_observer_forces_trivial_common_defect` |
| W11 | Countable coercivity–wildness dichotomy, exact manuscript surface | `countable_observer_coercivity_wildness_law` |
| W12 | Finite-family wild branch | `finite_noncoercive_observer_wild_lattice` |
| W13 | Finite-family coercive rigidity branch | `finite_coercive_observer_forces_trivial_common_defect` |

## Two-marginal relations

| ID | Manuscript claim | Lean declaration |
|---|---|---|
| R1 | Proper closed bi-dense subspace exists iff both observers are noncoercive | `twoSidedSingular_iff_hasProperClosedBiDenseSubspace` |
| R2 | Hyperplane witness in singular branch | `exists_biDense_hyperplane_of_twoSidedSingular` |
| R3 | Infinite woven common-normal lattice in singular branch | `twoSidedSingular_has_common_woven_normal_lattice` |

## Pre-quasi graph classification

| ID | Manuscript claim | Lean declaration |
|---|---|---|
| G1 | Compatibility places negative graph inside canonical inverse-adjoint graph | `preQuasi_graph_le_canonical_graph` |
| G2 | Quasi compatibility iff negative map equals canonical partner | `preQuasi_quasi_iff_eq_canonicalNegative` |
| G3 | Every closed bi-dense canonical graph subspace produces a pre-quasi pair | `preQuasi_of_closed_biDense_canonicalGraphSubspace` |

## Explicit diagonal model

| ID | Manuscript claim | Lean declaration |
|---|---|---|
| M1 | Diagonal observers injective and densely ranged | `pqP_injective`, `pqQ_injective`, `pqP_denseRange`, `pqQ_denseRange` |
| M2 | Model normal is square-summable and nonzero | `pqVWeight_summable_sq`, `pqV_ne_zero` |
| M3 | Model normal misses both observer ranges | `pqV_not_mem_range_pqP`, `pqV_not_mem_range_pqQ` |
| M4 | Hyperplane images are dense | `pqDefectDomain_dense`, `pqDefectRange_dense` |
| M5 | Explicit Hilbert pre-quasi pair is not quasi | `exists_hilbertPreQuasiPair_not_quasi` |
| M6 | Universal Hilbert automaticity statement is false | `not_every_hilbertPreQuasiPair_is_quasi` |

## Formal gates

- Source modules:
  - `formal/GaloisForLFunctions/RHTower/PythagoreanObserverBlindness.lean`
  - `formal/GaloisForLFunctions/RHTower/PreQuasiGelfandTwoSidedSingularDefect.lean`
- Final checks:
  - direct `lake env lean` on modified module: PASS;
  - `scripts/formal_tools.py lint`: PASS;
  - scratch-file `#print axioms`: PASS, only `propext`, `Classical.choice`, `Quot.sound`;
  - targeted `lake build GaloisForLFunctions.RHTower.PythagoreanObserverBlindness`: PASS;
  - umbrella import present in `GaloisForLFunctions/RHTower.lean`: PASS.

## Exclusions

- No Banach-space annihilator theorem is claimed.
- No abstract spectral weaving theorem is claimed.
- No stability, commutation, self-adjointness, compactness, or joint lower-bound hypothesis is claimed or used in countable theorem.
- No uncountable-family theorem is claimed.
- No PDE trace counterexample is claimed.
- Bibliographic priority is not a Lean proposition and remains independently uncertified.
