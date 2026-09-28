# Physical-ordinate topology forces singular source-to-seam transport — Lean certificate

- **Paper card:** `stc-physical-ordinate-transport-singularity.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.WeightedDirichletReadout`,
  `GaloisForLFunctions.HTGeometry.WeightedDirichletZeroCount`,
  `GaloisForLFunctions.HTGeometry.WeightedDirichletAlgebra`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateTransportNoGo`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateExactExtractor`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateFinitePacketInterpolation`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateGraphCollapse`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateRiggedRecovery`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateZeroDensityRigidity`,
  `GaloisForLFunctions.RHTower.PhysicalOrdinateObservationAlgebra`; inputs
  `STCPhysicalOrdinateSourceOrthogonality` (Gram (3)), `InfiniteMobiusSignedChannel` (source weights,
  `Q(σ)`), `SquarefreePartitionPole` (`(σ-1)Q(σ) → 6/π²`), `XiPrimeSeamCoherenceCollapse` /
  `XiPrimeSeamPairAsymptotics` (seam charge and energy), `BohrExponentialSeriesCoefficient` (Bohr
  coefficients), `UniformZeroCountBound` + mathlib Jensen formula, `Zeta23SimpleCriticalDensity`
  (`T log T/(72π)` simple critical ordinates, via the pinned Zeta23 formalization of the Alpöge–Furman
  two-thirds theorem), `XiSimpleCriticalSuperlinearConsumer`, `LpTwoMatrixOperators`, mathlib `LSeries`
- **Umbrellas:** `GaloisForLFunctions.HTGeometry`, `GaloisForLFunctions.RHTower`
- **Verification:** `lake --old build` of every module; `lake --old env lean` clean (no warnings);
  `#print axioms` of all 231 declarations of the ten modules = `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry`; lint gate has no finding in these modules.

Notation: `x_{σ,γ} = ordinateSource σ γ`, `y_{σ,γ} = ordinateSource σ (-γ)`,
`v_{β,γ} = seamVector β hβ γ`, `b_β = seamAmplitude β`, `Q(σ) = squarefreeMobiusTotal σ`,
`m_{σ,β} = extractorMultiplier σ β`, `D_{σ,β} = extractorOp`, `C_β = seamLogConst β`,
`R_min = minimalRelation` in `WithLp 2 (ℓ²(ℕ) × ℓ²(P))`.  `H_{-a}` is represented by its isometric
`ℓ²` coordinates `f̃(n) = n^{-a} f(n)` (as in the card): `z̃_{σ,γ} = riggedSource a σ γ`,
`B_{σ,β} = riggedOp a σ β`.  A bounded functional on `H_{-a}` is a bounded functional on `ℓ²(ℕ)`.

| Card item | Lean theorem |
|-|-|
| `x_{σ,γ}` is the unit source with coordinates `μ(n) √prob_σ(n) n^{-iγ}` | `ordinateSource_apply`, `norm_ordinateSource` |
| `v_{β,γ} ∈ ℓ²(P)`, `‖v‖²` = `orbitwisePrimeSeamWeightedNormSq (β+iγ)`, independent of `γ`, positive for `β ≠ 1/2`, norm-continuous | `seamVector`, `memℓp_seam`, `norm_sq_seamVector`, `norm_sq_seamVector_eq_orbitwise`, `seamVector_ne_zero`, `continuous_seamVector` |
| (3) Gram `Q(σ+i(δ-γ))/Q(σ)` → identity | `physicalOrdinateMobiusSource_inner`, `tendsto_inner_ordinateSource`, `tendsto_norm_sq_packet` |
| (2) no uniformly bounded landing on a set with nonempty interior: `‖T_σ‖ → ∞`; any nonzero norm-continuous target | `tendsto_norm_atTop_of_seam_landing`, `tendsto_norm_atTop_of_ordinate_landing` |
| (4) finite Bessel inequality; countable support in a separable target | `sum_norm_inner_sq_le_of_bounded_landing`, `countable_setOf_inner_ne_zero`, `countable_support_of_bounded_landing` |
| sharpness: `Σ a_j x_{σ,γ_j}` functionals, limits supported exactly on `{γ_j : a_j ≠ 0}` | `exists_bounded_landing_supported`, `tsum_ite_conj_ne_zero_iff` |
| the first prime coordinate already contradicts (4) | `not_bounded_landing_seam_coordinate`, `not_bounded_seam_landing` |
| (5) `D_{σ,β} y_{σ,γ} = v_{β,γ}` at every height | `extractorOp_ordinateSource`, `extractorMultiplier_mul_sourceWeight` |
| (6) bounded iff `1 < σ < 1 + 2 min(β,1-β)` (Euclid only) | `bddAbove_extractorMultiplier_iff`, `exists_exact_landing_iff` |
| rigidity: exact landing on an open interval = `D_{σ,β}` on squarefree coordinates | `coord_eq_of_exact_landing` (readout `coord_landing_eq_readout`, identity theorem `dirichletReadout_eq_of_eqOn_Ioo`, Bohr coefficients `coeff_eq_of_dirichletReadout_eq`) |
| (7) least norm `M_{σ,β} = ‖D_{σ,β}‖ = √Q sup_p log p p^{(σ-1)/2}|…|` | `abs_extractorMultiplier_le_norm`, `norm_extractorOp`, `iSup_abs_extractorMultiplier_eq` |
| (8) `√(σ-1) M_{σ,β} → C_β/√ζ(2)` | `tendsto_sqrt_mul_leastCost` (`tendsto_iSup_seamLogProfile`, `tendsto_sub_one_mul_squarefreeMobiusTotal`) |
| (9) uniform-in-height approximate landing: `liminf ‖T_σ‖/√Q(σ) ≥ C_β` | `eventually_le_norm_div_sqrt_of_uniform_landing` |
| finite zero-selected packets: finite-rank exact interpolants with `‖S_σ‖ ≤ √2‖Z‖` | `eventually_exists_packet_interpolation`, `half_sum_sq_le_norm_sq` |
| (10) `y_{σ_j,γ} ⇀ 0`; seam span dense; source span dense in `ℓ²(squarefree)`; `R_min ≤ R`; `R_min` least; vertical fibre `= ℓ²(P)` | `tendsto_inner_ordinateSource_zero`, `eq_zero_of_inner_seamVector_eq_zero`, `coord_eq_zero_of_inner_ordinateSource_eq_zero`, `minimalRelation_le`, `isLeast_minimalRelation`, `graphPair_zero_mem_of_closed` |
| (11) `z̃_{σ,γ} → z̃_{1,γ}` in `H_{-a}`; no critical vector at `a = 0` | `tendsto_riggedSource`, `not_memℓp_critical_unrigged` |
| (12) `B_{σ,β}` bounded with exact norm, `B_{σ,β} z̃_{σ,γ} = v_{β,γ}`, `B_σ → B_1` in norm, `B_1 z̃_1 = v` | `norm_riggedOp`, `riggedOp_riggedSource`, `tendsto_riggedOp`, `riggedOp_one_riggedSource` |
| sharp window `0 < a < κ` for any bounded all-height landing on `H_{-a}` | `coord_eq_of_rigged_landing`, `norm_riggedMultiplier_le_of_rigged_landing`, `exists_rigged_landing_iff`, `bddAbove_seamLogProfile_iff` |
| (13) weighted summability `Σ|c_n|n^η < ∞`, strip holomorphy, readout dichotomy `≡ 0` or `O(1+T)` zeros | `weightedAbsSummable_rigged_mul`, `differentiableOn_dirichletReadout`, `rigged_reader_dichotomy`, `exists_zero_count_linear` |
| (13) vanishing at all positive simple critical ordinates ⇒ `L = 0` on `ℓ²(squarefree)`; Hilbert-valued; every safe level `σ > 1` | `rigged_reader_vanishes`, `rigged_map_vanishes`, `source_reader_vanishes`, `coeff_eq_zero_of_readout_vanishes_on_simpleCritical` |
| (14) cofinal divisor reader: `‖L_j‖ → ∞` | `tendsto_norm_atTop_of_divisor_reader` |
| `A_η` Banach algebra (Dirichlet convolution, `(mn)^η = m^η n^η`, completeness); readout ring hom | `weightedDirichletSubring`, `weightedNorm_mul_le`, `exists_limit_of_weightedCauchy`, `readoutHom`, `readoutHom_det`, `norm_dirichletReadout_sub_le` |
| observations in `A_η`; finite determinants / ring expressions / fixed-aperture limits cannot carry the simple critical divisor | `observationCoeff_mem`, `det_observations_eq_zero`, `closure_observations_readout_eq_zero`, `limit_readout_eq_zero`, `readout_limit` |

Proof-mechanism differences from the paper (same conclusions): the `O(1+T)` real-zero count is
obtained from Jensen discs centred at height `Y` above the real line, where the least nonzero
Dirichlet term dominates the readout uniformly in the real part, instead of the translation-hull
compactness and argument-principle argument; the readout is realized as `LSeries c (-iz)`, which is
holomorphic on the whole half-plane `Im z > -η`; the weak closedness of the relation in (10) is used
through `R = Rᗮᗮ`; the finite-packet interpolation bound uses the lower Riesz bound
`‖Σ cᵢ xᵢ‖² ≥ ‖c‖²/2` instead of the operator norm of `G⁻¹`.
