# A rank-two theta boundary defect with infinitely many off-real source modes — Lean certificate

- **Paper card:** `stc-universal-boundary-pontryagin-countermodel.md`
- **Lean modules:** `GaloisForLFunctions.RHTower.STCUniversalBoundaryPontryaginCountermodel`
  (namespace `RHTower.UniversalBoundaryCountermodel`), `GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCompactSourceEigenmode`
  (compact source inverse, metric commutator and divisor eigenvectors for any positive density),
  `GaloisForLFunctions.HTGeometry.PontryaginNeutralEigenvectorBound`; inputs from the corpus
  quantile/Hilbert--Schmidt layer (`PositiveDensityQuantile`, `HedenmalmQuantileNormalForm`,
  `HedenmalmHilbertSchmidtNorm`, `HedenmalmPinnedVolterraBoundaryDefect`, `HedenmalmQuantileMetric`,
  `HedenmalmPrimeTranslationAnomaly`)
- **Umbrellas:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`
- **Verification:** `lake --old build`; `lake --old env lean` clean; `#print axioms` of all 91
  theorems = `propext`, `Classical.choice`, `Quot.sound`; no `sorry`.

| Card item | Lean theorem |
|-|-|
| parameters `0<a<1/2`, `cosh A = 1/(2a)`, `L>2A`; existence for every `a` | `Params`, `exists_params` |
| `g` positive, even, smooth, dominated by every Gaussian | `density_pos`, `density_neg`, `contDiff_density`, `density_le_gaussian`, `integrable_density_mul_exp` |
| (1) `F(z) = H(z)(1+2a cos Lz)` | `xiC_source` |
| (2) `F(z_n^±) = 0`, `0 < Im z_n^+ < 1/2` | `xiC_upperZero`, `xiC_lowerZero`, `upperZero_im_mem` |
| tail envelope `g(y) ≤ g(x) e^{-4(x-L)³(y-x)}` and tail integrals | `density_tail`, `density_tail_integral`, `density_tail_integral_left` |
| (3) `B = i M_q C` on `L²(0,1)` (kernel form) | `sourceInverseOp`; pointwise form `pinnedKernelOperator_ae`, `pinnedKernelField_apply_eq_pinnedVolterraFun` |
| (4) HS energy identity; `(1-G)/g ≤ [4M(x-L)³]⁻¹` and mirror; finiteness | `sourceInverseOp_energy`, `tailEnergyDensity_le_right`, `tailEnergyDensity_le_left`, `integrable_tailEnergyDensity`, `hasFiniteKernelEnergy_source` |
| (3) `B` Hilbert--Schmidt and compact | `sourceInverseOp_hilbertSchmidt` |
| (5) `D = M_{1/q}` bounded, self-adjoint, positive, injective; `DB - B*D = iP` | `metricOp_commutator` (generic `metricOperator_commutator_compactSourceInverse`, `re_inner_metricOperator_nonneg`) |
| (5) `P` rank two, `P1 = -v`, `Pv = -1/12`, one positive and one negative direction | `boundaryDefect_rankTwo` |
| (6) `A_z(1) = F(z)/M` | `rootA_one` (corpus) |
| (6) endpoint control `|R_z| ≲ g` at both tails; `R_z → 0` | `norm_sourceModeU_le_right`, `norm_sourceModeU_le_left`, `exists_norm_sourceModeU_le`, `tendsto_sourceModeU` |
| (6) `f_z ∈ L²`, `∫ f_z` = full mass, `B f_z = (-1/z) f_z`, `f_z ≠ 0` | `memLp_sourceModeF`, `integral_sourceModeF`, `sourceInverseOp_eigen`, `upperEigenvector_spec` (generic `compactSourceInverse_divisorEigenvector`, `divisorEigenvector_ne_zero`) |
| eigenvalues `-1/z_n^+` distinct, in the upper half-plane | `neg_inv_upperZero_injective`, `neg_inv_upperZero_im_pos` |
| `(λ_i - λ̄_j)[v_i,v_j] = 0`: upper eigenvectors span a neutral subspace | `sesq_eq_zero_of_upper_eigenvectors` |
| neutral subspace dimension ≤ κ; first `N` modes need `κ ≥ N` | `card_upper_eigenvalues_le`, `realization_card_le` |
| no finite-index realization retains the whole divisor | `no_finite_index_realization` |
