# Arbitrary-graph quantum temporal-curvature law — closing item 6

Card: `docs/drafts/pipeline/2-fully-proven/arbitrary-graph-quantum-temporal-curvature-law.md`

Items 1–5 of the card's "still required" list are **already done** in the pre-existing corpus (the
card now records the exact declaration names per item).  Item **6** (simultaneous subsystem atlas +
infinite product capstone) is the open one.

## Why new infrastructure was needed

`RootedTensorTree` stores the carrier as a *nested product*, in which a vertex subset `S` is not a
tensor factor.  Corollary 2 needs one fixed ambient Hamiltonian restricted to every `S`, so the
carrier must be the **site product** `∀ v, A v`.

## Built, compiling, wired into `GaloisForLFunctions.HTGeometry`

1. `SubsystemAtlasProjectiveGenericityLaw.lean` — abstract §9 + infinite-network mechanism
   (`restrictedPolynomialHermitianMaximalSet_dense_residual_fullMeasure` via `MvPolynomial.rename`,
   `simultaneousRestrictedMaximalSet_dense_residual_fullMeasure`,
   `ambientRestrictedMaximalSet_residual`, `measure_compl_ambientRestrictedMaximalSet_eq_zero`,
   `isOpenMap_coefficientRestrict`, `preimage_mem_residual_of_isOpenMap`).
2. `SiteSupportedLocalHamiltonian.lean` — `IsSiteSupported`, closure lemmas incl. `of_forall_mem`,
   `exists_liftLocalMatrix_of_isSiteSupported`, `siteFactorLocalSubmodule`, `IsGraphLocalTerm`,
   `siteFactorTermSpan`, `mem_siteFactorLocalSubmodule_of_mem_termSpan`.
3. `SiteFactorLeafTransport.lean` — `leafSiteEquiv`, `leafTransport`, three leaf support laws,
   `leafTransport_mem_siteFactorTermSpan`, `isGraphLocalTerm_leafTransport_newSite/_edge`,
   `twoSiteEquiv` + its two support laws.
4. `PhysicalRealizationCarrierTransport.lean` — `reindex_hamiltonian_maximallyProjective`
   (relabelling the physical carrier keeps the spectral system; requires the new carrier in the
   **same universe** as the spectral system, which is why the site-product theorems live at `Type`).
5. `SiteFactorGraphWitness.lean` — `PhysicallyRealizedTensorTreeSystem.tree`, `SiteFactorChart`,
   seeds (one-site, two-site), charted leaf step, charted rooted/binary spanning-tree inductions,
   and the capstone **`exists_maximallyProjective_mem_siteFactorLocalSubmodule`**: every connected
   finite graph with all local dims ≥ 2 has a Hermitian onsite-plus-edge Hamiltonian on `∀ v, A v`
   with maximal projective rank.  (Single binary site handled directly: no good observer family
   exists for two states.)
6. `SiteFactorLiftedSpectrum.lean` — `mem_range_hermitianEigenvalues_iff`,
   `anchoredGapSubspace_eq_of_range_eq`, `anchoredTemporalRank_eq_of_range_eq`,
   `isHermitian_liftLocalMatrix`, `reindex_scalarSub_liftLocalMatrix`,
   `range_eigenvalues_liftLocalMatrix` (= spectrum of the block),
   `anchoredTemporalRank_liftLocalMatrix`.
7. `KroneckerSumSpectrum.lean` — `isHermitian_kroneckerSum`, `kroneckerSum_eq_conj_diagonal`,
   **`range_eigenvalues_kroneckerSum`**: eigenvalues of `X ⊗ I + I ⊗ Y` are exactly the pairwise
   sums.  (`kroneckerSum`/`kroneckerSum_diagonal` already existed in `ParametricSpectralBranch`.)
8. `DisjointPacketSpectrum.lean` — `isHermitian_reindex`, `reindex_scalar`,
   `range_eigenvalues_reindex`, `outsideSplitEquiv`,
   `range_eigenvalues_liftLocalMatrixOutsideDisjoint`, and
   **`range_eigenvalues_add_liftLocalMatrix_disjoint`**: the spectrum of a sum of two operators on
   disjoint site packets is the set of pairwise sums.

## Surgery on existing files (additive, all call sites fixed)

`IsPhysicalLeafChart` (4th conclusion of `exists_physicallyRealizedTensorTree_leafExtension`) and
`IsTwoQubitSiteChart` (4th conclusion of `exists_physicallyRealizedTensorTree_twoQubitGraphSeed`)
expose the carrier factorization the constructions already build definitionally.  Watch out: in
`ConnectedGraphSpanningLocalWitnessLaw` the one-site and two-qubit seeds are destructured with the
same variable names — only the two-qubit one takes the extra component.

## Also done (2026-08-05, later)

- `DisjointPacketSpectrum.lean` now carries the **full** component decomposition `(18)`:
  `liftLocalMatrix_injective`, `isHermitian_of_isHermitian_liftLocalMatrix`,
  `isHermitian_sum_liftLocalMatrix`, `isSiteSupported_sum_liftLocalMatrix`,
  `range_eigenvalues_sum_liftLocalMatrix` (Finset induction: split off one packet, repackage the
  rest with `exists_liftLocalMatrix_of_isSiteSupported`), `exists_reference_sum_liftLocalMatrix`,
  and `anchoredTemporalRank_sum_liftLocalMatrix` = `Σ_c (card (LocalConfiguration A (S c)) − 1)`
  under `ComponentProjectivelyIndependent`.
- `SubsystemAtlasProjectiveGenericityLaw.lean` gained `simultaneousMaximalSet` +
  `simultaneousMaximalSet_dense_residual_fullMeasure`: several Hermitian families over ONE shared
  real parameter space are simultaneously maximally projective on a dense residual full-measure
  set.  **Design consequence**: the subsystem coordinates need not be a literal subfamily — write
  each `S`-subsystem as its own generator family on `LocalConfiguration A S` indexed by the *same*
  ambient parameters (zero generator when the packet is not inside `S`).  This kills all the
  `S`-vs-`V` coordinate bookkeeping.

## Next steps

1. Ambient coordinate family: for each admissible packet `P` (singleton or edge of `G`) take
   `Module.finBasis ℝ (selfAdjoint.submodule ℝ (Matrix (LocalConfiguration A P) … ℂ))`; index by
   `Σ P, Fin (dim P)` and transport to `Fin m` by `Fintype.equivFin`.  Ambient generator
   `liftLocalMatrix P (basis i)`; `S`-block generator `liftLocalMatrixToSuperset hPS (basis i)`
   when `P ⊆ S`, else `0`.  Compatibility is `liftLocalMatrix_liftLocalMatrixToSuperset`.
2. Assemble `(5)`–`(8)` with `FiniteGraphTemporalCurvatureLaw`, and `(20)` with
   `ambientRestrictedMaximalSet_residual` + `measure_compl_ambientRestrictedMaximalSet_eq_zero`.
   For disconnected `G[S]` the transversality genericity of card §8 is still needed (the witness
   exists: `exists_scales_componentProjectivelyIndependent`).

## Traps

- `Matrix.IsHermitian` needs `import Mathlib.LinearAlgebra.Matrix.Hermitian`; `Hᴴ` needs
  `open scoped Matrix`.
- `R.PhysicalState` needs an ambient `Fintype X.State` even when `R`'s type pins the instances —
  use `letI` in the statement type, or a `@[reducible]` accessor.
- `Matrix.sub_kronecker` does not exist in this mathlib; prove `(X - Y) ⊗ₖ Z` entrywise.
- The lint gate fails on warnings: `omit … in` before the docstring; watch unused simp args.
- `rcases`/`obtain` `_` tries to case-split an opaque `def`; use `-`.
- 2026-08-05: another session created untracked `HTGeometry/QuantileCoupling.lean` (not wired into
  the umbrella yet) — the resulting `formal_tools.py lint` failure is theirs, not this work's.
