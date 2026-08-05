# Arbitrary-graph quantum temporal-curvature law — closing item 6

Card: `docs/drafts/pipeline/2-fully-proven/arbitrary-graph-quantum-temporal-curvature-law.md`

## Audit of the card's six "still required" items (verified against the repo, not the card text)

1. all-vertex-good graph induction — DONE
   (`exists_physicallyRealizedTensorTree_leafExtension`,
    `exists_physicallyRealizedTensorTree_completeOneSiteSeed`,
    `exists_physicallyRealizedTensorTree_twoQubitGraphSeed`,
    `exists_completeOneSiteSeed_tensorTreeSchedule_maximal`,
    `exists_twoQubitSeed_tensorTreeSchedule_maximal`)
2. heterogeneous relation-erasure capstone — DONE (same file + `LocalTwoLayerSpectralResponse`,
   `LocalSelectedLayerSpectralResponse`)
3. spanning-tree lift — DONE
   (`PhysicallyRealizedTensorTreeSystem.hermitianSuperspaceMaximalSet_dense_residual_fullMeasure`,
    `exists_rootedSpanningTreePhysicalSystem`, `exists_binarySpanningTreePhysicalSystem`)
4. disconnected module equality + rational-transverse scaling — DONE
   (`DisconnectedProjectiveGapModuleLaw`: `anchoredTemporalRank_finiteComponentSumEnergy_eq_sum`,
    `exists_scales_componentProjectivelyIndependent`)
5. temporal partition-curvature capstone — DONE
   (`FiniteGraphTemporalCurvatureLaw`: `finiteGraphPartitionTemporalCurvature_eq_zero_iff`,
    `connected_iff_all_nontrivial_partitionTemporalCurvature_pos`,
    `finiteGraphPairTemporalCurvature_eq`, `adj_iff_finiteGraphPairTemporalCurvature_pos`)
6. simultaneous subsystem atlas + infinite product capstone — THE REMAINING ITEM.

## Why item 6 needs new infrastructure

The tree architecture (`RootedTensorTree`) carries the physical carrier as a *nested product*
`((F v1 × F v2) × F v3) × …`.  Corollary 2 needs, for one fixed ambient Hamiltonian, the induced
restriction to **every** vertex subset `S`.  That requires the carrier as a **site product**
`∀ v, F v` so that `S` is an actual tensor factor.  The corpus already owns the site-product tensor
layer (`LocalMatrixTensorFactorization`: `LocalConfiguration`, `liftLocalMatrix`,
`configurationSplitEquiv`, `reindex_liftLocalMatrix_eq_kronecker_one`;
`FiniteLocalInteractionFamily`, `DisconnectedLocalAffineFactorization`), but had no graph-local
Hamiltonian *space* on that carrier.

## Built so far (all compile clean, wired into `GaloisForLFunctions.HTGeometry`)

- `HTGeometry/SubsystemAtlasProjectiveGenericityLaw.lean` — the abstract Section-9/infinite-network
  mechanism:
  * `coefficientRestrict` / `coefficientExtend`, `isOpenMap_coefficientRestrict`,
    `preimage_mem_residual_of_isOpenMap`;
  * `restrictedPolynomialHermitianMaximalSet_dense_residual_fullMeasure` — pulls a subsystem's
    maximal set back to the ambient coefficient space.  Trick: `MvPolynomial.rename` the subsystem
    variables into the ambient ones, so the pullback *is* a polynomial-family maximal set and
    `polynomialHermitianMatrixMaximalSet_dense_residual_fullMeasure` applies directly — no
    measure-theoretic pullback needed;
  * `simultaneousRestrictedMaximalSet_dense_residual_fullMeasure` — countable atlas; density comes
    from Baire (finite intersections of dense sets are not dense, residual ones are);
  * `ambientRestrictedMaximalSet_residual` and
    `measure_compl_ambientRestrictedMaximalSet_eq_zero` — infinite countable coefficient product.
- `HTGeometry/SiteSupportedLocalHamiltonian.lean` — `IsSiteSupported S H` (acts as identity off `S`),
  its subspace/monotone/conjTranspose closure, `exists_liftLocalMatrix_of_isSiteSupported`,
  `siteFactorLocalSubmodule A G`, `IsGraphLocalTerm`,
  `mem_siteFactorLocalSubmodule_of_hermitian_sum` (Hermitian part of each term has the same
  support, so non-Hermitian pieces of a Hermitian local Hamiltonian are harmless).
- `HTGeometry/SiteFactorLeafTransport.lean` — `leafSiteEquiv A v : (∀ w ≠ v, A w) × A v ≃ ∀ w, A w`,
  `leafTransport`, and the three support lemmas
  (`isSiteSupported_leafTransport_id`, `isSiteSupported_leafTransport`,
   `isSiteSupported_leafTransport_newSite`) plus
  `leafTransport_mem_siteFactorLocalSubmodule`.

## Remaining plan

Stage 3: a `SiteFactorRealizedSystem V A` structure = a `GoodObserverSpectralSystem.PhysicalRealization`
whose `PhysicalState` **is** `∀ v, A v`, plus `probe_oneSite` and `hamiltonian_local`.  Mirror the
seeds and the leaf step by calling
`exists_maximallyProjective_physicalLocalGoodObserverFamily_leafExtension` directly (it exposes
`physicalLeafHamiltonian oldH parentOp shift edge = oldH ⊗ 1 + 1 ⊗ diag shift + parentOp ⊗ edge`),
then mirror the `exists_rootedSpanningTreePhysicalSystem` recursion (delete a degree-one vertex of a
spanning tree) to get a maximally projective element of `siteFactorLocalSubmodule A G` for every
connected `G` with all `2 ≤ card (A v)`.

Stage 4: for `S ⊆ V`, `H_S` = the `S`-supported part; `anchoredTemporalRank` of a lift equals that of
its block (`anchoredTemporalRank` only depends on `Set.range energy`; use
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` and
`reindex_liftLocalMatrix_eq_kronecker_one`), and across components of `G[S]` use
`anchoredTemporalRank_finiteComponentSumEnergy_eq_sum`.  Feed the witnesses into
`simultaneousRestrictedMaximalSet_dense_residual_fullMeasure`.

Stage 5: infinite network via `ambientRestrictedMaximalSet_residual` +
`measure_compl_ambientRestrictedMaximalSet_eq_zero`.

## Traps hit

- `Matrix.IsHermitian` needs `import Mathlib.LinearAlgebra.Matrix.Hermitian`; without it dot
  notation reports `Function.IsHermitian`.
- `Hᴴ` needs `open scoped Matrix`.
- The formal lint gate fails on warnings: every `theorem` that does not use a section instance needs
  an explicit `omit … in`, and the `omit` line must come **before** the docstring.
- `intro` does not accept `-`; use `_`.
