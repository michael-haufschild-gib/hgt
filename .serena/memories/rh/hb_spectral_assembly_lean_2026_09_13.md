# HB-SPEC-001: spectral assembly of the modular surface in Lean (2026-09-13)

Card: `docs/drafts/pipeline/1-in-progress/hb-modular-laplacian-spectral-assembly.md` (input (ii)(b) of the
on-line sign law, ledger row 40). All abstract content B1–B4 is CLOSED IN LEAN, standard axioms:

- `HTGeometry/CfcEigenvectorRankOneAssembly`: `cfc_apply_eigenvector` (g(A)x = g(c)x, Stone–Weierstrass
  on the closed subalgebra), `re_inner_cfc_self_ge_rankOne`.
- `HTGeometry/FormEmbeddingCovarianceSpectrum`: `C = J J†` positive, `σ(C) ⊆ [0,1]` for contractive J,
  form-harmonic vectors fixed; `re_inner_cfc_formEmbeddingCovariance_ge`.
- `HTGeometry/ModularDirichletFormDomain`: `ModularL2` (a `def`, NOT abbrev — abbrev broke the ℝ-cfc instance
  search), `formPreDomain` (C¹ SL(2,ℤ)-invariant, gradient in L²), `formDomainClosure ⊆ L²(𝒟)³`,
  `formInclusion` (contractive), `modularCovariance`, `modularCovariance_one`, `modular_spectral_assembly`,
  `inner_modularOne`, `norm_modularOne_sq`.
- `HTGeometry/ModularDirichletFormIntegrationByParts`: `setIntegral_fd_eq_chart`, `setIntegral_fd_testWeight_chartDeriv`.
- `HTGeometry/ModularDirichletFormClosable`: `InteriorTest`, `eq_zero_of_forall_interiorTest`, `formInclusion_injective`.
- `HTGeometry/ModularDirichletFormPeriodization`: proper discontinuity of SL(2,ℤ) (from `𝒮ℒ`), `periodize`,
  `isChartC1_periodize`, `toModularL2_mem_range_formInclusion`.
- `HTGeometry/ModularDirichletFormSmoothApprox`: `exists_smooth_cutoff`, `exists_contDiff_uniform_approx`.
- `HTGeometry/ModularDirichletFormDense`: `exists_interior_approx`, `dense_range_formInclusion`,
  `modularCovariance_injective`, `modularFriedrichsOperator` (self-adjoint, dense domain) = Friedrichs `1−Δ`.

Still open for (b): HB kernel module (`skewPlateauCov` in the covariance variable r = 1/(1+l),
`hb_online_clock_spectral_assembly : t¹¹/2176·|∫F|²/vol − t⁹‖F−P₀F‖² ≤ Re⟪(Im K̂)(C)F,F⟫`), written in the
session scratchpad `CovKer.lean` but blocked: `…SkewUniformBound.olean` is stale (new imports) and
`ThetaCuspHawkingBMScalarStreamJet.olean` is missing after other agents' edits; rebuilding needs the whole
HB chain (forbidden: no long rebuilds). Also open: the source `F = Λ¹(E*(·,½+it)²)` as an `L²(𝒟)` element.

Lean tricks used: `exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ,ℂ)` gives smooth cutoffs on ℂ;
fundamental lemma `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero` works for ANY measure, so apply it
on `(ℂ, map coe μ)` and pull back with `measurableEmbedding_coe.ae_map_iff`; `ContDiffOn.div` over ℝ needs
ℝ-valued functions — do it over ℂ and `restrict_scalars ℝ`; RCLike vs Complex real casts differ
syntactically: finish with `simp`/`rfl`, not `ring`.
