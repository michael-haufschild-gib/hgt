# Top-level `2-fully-proven` → stage 3 — formalization ledger

Scope: the **top-level** `.md` cards of `docs/drafts/pipeline/2-fully-proven` only
(subfolders `computations/`, `constraint-relativity/`, `new_scientific_knowledge/`,
`nomological-geometry-and-dynamics/`, `not_new_scientific_knowledge/`, `universal-law-field/`
are out of scope — other agents own them).

Rules in force: unconditional Lean only (no `sorry`, no added axiom, no hypothesis standing for an
analytic input); never full builds nor umbrella builds — `lake env lean <file>` to check, `lake build
<module>` only for oleans a scratch needs; wire new modules into the area umbrella import list
without building it; search the corpus (`scripts/formal_tools.py research`) before writing anything.

## Start state (2026-08-21): 22 cards

Unblocked by the fixed-shell promotion: `stabilizer-seeded-static-local-double-exponential-plateau-law`,
`cubic-phase-seeded-static-local-full-scale-plateau-law`,
`capacity-compatible-fast-forwardable-incubation-law`,
`onset-recurrence-dimension-independence-law`,
`weak-cut-complexity-onset-capacity-separation-law` (Theorem C),
`circuit-complexity-selection-synthesis-divergence-law` (§6),
`capacitary-observer-sector-excision-law` (Corollary I.3, Theorem K),
`all-replica-static-centralizer-planar-separation-law` (also needs Kargin).

## Promoted

| date | card | evidence |
|---|---|---|
| 2026-08-21 | `codimension-forced-complexity-onset-moment-divergence-law` | Theorem C in full: `coupled_shortcut_tube`, `coupled_tail_lower` `(23)`, `lintegral_coupled_onset_pow_eq_top` / `lintegral_coupled_onset_rpow_eq_top` `(24)`, on top of the Davis--Kahan-free collision bound `spectralCollision_le_of_near_diagonal` and the near-uniform separating direction — 6 new modules (`NearDiagonalOverlapFlatness`, `PathDiagonalCarrier`, `BaseThreeSignSeparation`, `PathCarrierSeparatingDirection`, `NearUniformSeparatingCarrier`, `CoupledShortcutCollision`, `CoupledShortcutOnsetMoments`), all axiom-clean, wired |
| 2026-08-21 | `circuit-complexity-selection-synthesis-divergence-law` | the composition `(22)`--`(26)` with the now-formal plateau: `exists_plateau_codebook_split`, `exists_late_plateau_codebook_split`, `recurrence_row`, on top of the padding law `exists_length_eq_prod_map_eq` and the depth-`S` complexity bound `lt_wordComplexity_of_forall_notMem` — 1 new module (`PlateauSelectionSynthesisSplit`), axiom-clean, wired |
| 2026-08-21 | `computable-static-local-exponential-state-complexity-law` | Theorems A and B in full, including the uniform-computability clause: `half_mul_one_sub_le_liminf_quenchedWindowAverage_pauliEnsemble` `(8)`, `le_limsup_quenchedFixedTimeProb_pauliEnsemble` `(9)`, `exists_restricted_goodSet_common_time_hardness` `(8a)`, `exists_rational_common_time_witness` `(17)`--`(20)`, `exists_integer_coefficient_witness`, and the executable rational certificate `HardCertificate` / `exists_certifiedIndex` / `hard_searchIndex` — 7 new modules (`GateWordDictionary`, `CommonTimeCircuitHardness`, `GateWordCommonTimeHardness`, `RationalCommonTimeWitness`, `GaussianIntegerPauliModel`, `ExponentialFactorialRemainder`, `RationalOrbitCertificate`), all axiom-clean, wired |
| 2026-08-21 | `suzuki-v2-spherical-atlas-convergence` | `RHTower/SuzukiV2SphericalConvergence.lean` — 3 theorems, axiom-clean, wired |
| 2026-08-21 | `suzuki-v2-actual-projective-characteristic` | `RHTower/SuzukiTaV2ProjectiveCharacteristic.lean` — Theorems A/B/C, axiom-clean, wired |
| 2026-08-21 | `stabilizer-seeded-static-local-double-exponential-plateau-law` | Theorems A/B/C and the low--plateau--recurrence corollary: `exists_stabilizer_family_collision_eq`, `limsup_sphereLaw_seedCapture_le`, `limsup_sphereLaw_stabilizerSeeded_sum_le`, `exists_time_forall_interval_hard_of_speed`, `ae_exists_late_seed_recurrence_chainShell` — 4 new modules |
| 2026-08-21 | `determinant-defect-completion-law` | `(DC)` in several variables as one set equality: `pencilGraphClosure_eq_pencilCompletionFibre`, with the polarization bridge `eval_homogeneousComponent_mem_span_clmPow`, the line-jet extraction `exists_lineJet_of_locallyUniform`, and the low-trace jet `lowTraceMv` — 2 new modules (`PencilLowTraceJet`, `PencilDeterminantCompletion`) plus the coefficient-carrying necessity in `DeterminantGraphLocallyUniform` |
| 2026-08-21 | `capacity-compatible-fast-forwardable-incubation-law` | Theorem B `(20)` and clauses 1--5, 7 at one seed on the tube over the diagonal cap: `exists_incubating_cubicSeed`, on top of `pathPatchIsometry` (the shell *is* the patch space of its diagonal splitting), `toSphere_preimage_crossSphereMap`, `sphericalCap_coord_ge`, `density_patchGood`, `edgeCoupling_lower` — 5 new modules (`CrossSphereIsometryTransport`, `PathShellPatchTransport`, `DiagonalPatchConstruction`, `PatchChainPullback`, `CapacityIncubationInstantiation`), all axiom-clean, wired |
| 2026-08-21 | `weak-cut-complexity-onset-capacity-separation-law` | Theorem C `(14)` at one fixed pair: `exists_weakCut_delayed_plateau`, on top of `exists_late_hardWindow` (single-orbit plateau), `exists_prodPolyEval_collision_le_four_div` (bipartite eighth-root transfer), `pathShellProb_pathBadSphere_eq_zero` and `norm_pathHamiltonian_le_sqrt` — 5 new modules (`SingleOrbitPlateauWindow`, `PathChainLabelIdentification`, `PathShellProjectiveGenericity`, `BipartiteEighthRootTransfer`, `WeakCutDelayedPlateau`), all axiom-clean, wired |
| 2026-08-21 | `cubic-phase-seeded-static-local-full-scale-plateau-law` | Theorem A, Theorem B `(8)`/`(9)` in both normalizations, Theorem C `(17)`/`(24)`, and both corollaries: `card_filter_phaseCollision_polyEval_gt_le`, `limsup_sphereLaw_cubicSeeded_le`, `exists_fixed_cubicSeed_sphereLaw_le`, `exists_fixed_cubicSeed_plateau_and_recurrence`, `card_monLe` — 4 new modules (`CubicSeedCollisionTail`, `CubicSeedPlateauLaw`, `CubicFixedSeedSelection`, `CubicSeedFullScalePlateau`), all axiom-clean, wired |
| 2026-08-21 | `fixed-shell-angular-dephasing-static-local-plateau-law` | Theorems A/B/C on the card's own nearest-neighbour Pauli shell: `exists_shell_energy_witness_pauliChain`, `tendsto_integral_exp_sortedSpectralAction_zero_pauliChain`, `limsup_sphereLaw_chainCapture_le`, `eventually_sphereLaw_chainCapture_le` — 20 new modules, all axiom-clean, wired |

## In progress

**`capacitary-observer-sector-excision-law`** — 2026-08-21: Theorems G, H, I, `(11aa)`, `(11ab)`
closed with four new modules (`CapacitySoftMinLaw`, `CompletedPhaseAccessibilityPlateau`,
`PartitionDivergenceBounds`, `CapacityEntropyBudget`).  Corollaries I.2 and J.1 closed the same day
with `GeometricCircuitCollision`.  Remaining: Corollary I.1's physical-time transfer (unique
ergodicity + the phase-coherence target bound), Corollary A.3, `(8c)`, `(11be)`, and — gated on the
fixed-shell card — Corollary I.3 and Theorem K.

**`computable-static-local-exponential-state-complexity-law`** — 2026-08-21: `(5)`, `(12)`, `(13)`,
`(14)`, the completed-time circuit bound behind `(6)` and the eigenbasis coordinate change are
closed with `CompletedTimeCircuitDensity`, `GaussianGoodCoefficientSet`, `CircuitDictionaryCounting`
(plus a strengthening of `GaussianBoxMass`).  One-sided Kronecker--Weyl closed the same day
(`OneSidedCaptureDensity`), so the window transport is no longer a gap.  `(6)` itself is now closed in physical time
(`ClockPhaseEvolutionBridge`, `PhysicalTimeCircuitCapture`:
`limsup_oneSided_physicalCapture_le`).  It is now also instantiated at the Gaussian Pauli
ensemble (`GaussianEnsembleCircuitDensity.ae_limsup_physicalCapture_le_of_gaussianGoodSet`).
The window/time-fraction bridge is closed too
(`WindowTimeFractionBridge`).  The single remaining brick for Theorem A is joint measurability of
the hard event in `(J,t)` — which needs the matrix operator-norm topology reconciled with the
entrywise topology so that `NormedSpace.exp_continuous` composes.  Then `(8)`/`(8a)`/`(9)` are
`QuenchedFixedTimeTransfer` verbatim.  Theorem B (Duhamel, rational density, dovetailed search) is
untouched.  **Not gated on the
fixed-shell card** — it lives on the Gaussian Pauli ensemble, where `(23)`/`(26)` are available.


## Shared infrastructure landed (2026-08-21)

**`HTGeometry/SingleOrbitPlateauWindow.lean`** — *the single-orbit continuous plateau*
(`exists_late_hardWindow`, axiom-clean, wired).  The shell-averaged plateau laws bound the measure
of the Hamiltonians that are easy at a late time; this one bounds, at *one fixed* Hamiltonian with
maximally projective spectrum and one seed of small collision, the long-time **density** of the
times whose forward window of length `W` meets the dictionary, and concludes that windows of length
`W` that are hard at every instant occur arbitrarily late as soon as
`plateauGridCount W ((ε₊−ε₋)/speed) · 2^{-r/2} < 1`.  Route: one-sided Kronecker--Weyl
(`oneSided_closedTarget_limsup_le_volume`) applied to the union of the mesh translates of the closed
capture target, whose Haar volume is `N_W` times `measure_projectiveAmpCaptureTarget_le_two_rpow`.
Supporting declarations: `shiftTarget`, `gridTarget`, `metricEasySet`,
`metricEasySet_subset_physicalCaptureSet`, `metricEasySet_mesh`, `badWindowSet`,
`limsup_windowProb_badWindowSet_le`, `windowProb_Ioc`,
`exists_notMem_of_limsup_windowProb_lt_one`, `finiteComplexInner_unitaryEvolution_self`.

This is the tool every cluster-A card needs for the clause "**one fixed pair** `(H, χ)` is hard at
every instant of a long window", as opposed to the shell-measure clause the parents already had.

**`HTGeometry/PathChainLabelIdentification.lean`** — the path shell *is* the numbered chain shell.
`pathWord` sends a path label (site+axis, or edge+axis pair) to a Pauli string; it is injective,
lands in `ChainLabel (n+2)`, and `exists_pathWord_eq` shows every nonidentity label of support
diameter at most one is a path label -- so `pathLabelEquiv : PathLabel n ≃ ChainLabel (n+2)`, and
`reindex_pathHamiltonian` identifies `pathHamiltonian u` with
`spectralEnsembleMatrix (chainPauliFin (n+2))` at the relabelled coefficients.

**`HTGeometry/PathShellProjectiveGenericity.lean`** — maximal projectivity is generic on the path
shell.  `volume_notMaximallyProjective_eq_zero` generalizes the chain argument to any Hermitian
family with one maximally projective witness; transported through `pathCoeffEquiv` (pi-Lebesgue
reindexing) and the cone/`toSphere` step it gives `pathShellProb_pathBadSphere_eq_zero`.  The payoff
is `exists_pathHamiltonian_orthoEigenBasis` (an orthonormal eigenbasis of `pathHamiltonian v` with
maximally projective eigenvalues, at every direction outside the null set) and
`exists_mem_notMem_pathBadSphere` (selecting one inside a positive-measure sector, e.g. the delay
sector of `pathShellProb_delayEvent_pos`).  Also `MaximallyProjectiveEnergy.comp_equiv`.

**`HTGeometry/CrossSphereIsometryTransport.lean`** — `crossSphereMap` and
`toSphere_preimage_crossSphereMap`: the spherical measure transports along a linear isometry
equivalence of finite-dimensional inner product spaces (cone presentation + `LinearIsometryEquiv.measurePreserving`).

**`HTGeometry/PathShellPatchTransport.lean`** — `IsDiagLabel`, `diagLabelEquiv`, `card_diagLabel`
(`= 2n+3`), `offDiagLabelEquiv`, `card_offDiagLabel` (`= 10n+12`), and
**`pathPatchIsometry : PatchSpace (2n+3) (10n+12) ≃ₗᵢ[ℝ] PathShell n`**; also `pathHamiltonianLM`
(the shell map as a real-linear map), `norm_pathHamiltonian_le` and `norm_pathHamiltonianLM_sub_le`
(Lipschitz constant `√(12(n+2)-9)`), and `toSphere_preimage_pathBadSphere_eq_zero`.

**`HTGeometry/DiagonalPatchConstruction.lean`** — `uniformDir`, `sphericalCap`,
`isCompact_embedPatch_sphericalCap`, `sphericalCap_coord_ge` (**`(16)`**), and
`volume_patchAnnulus_sphericalCap_pos` (the carrier factor `a_P > 0`).

Together with `exists_late_hardWindow` these are the missing ingredients of the clause
"one fixed pair `(H, χ)` is hard at every instant of a long window, at a Hamiltonian inside a
prescribed positive-measure sector".

## Per-card blocker survey (2026-08-21)

The 14 open cards, with the *exact* remaining item.  Read this before choosing a card.

**Cluster A — the static-local complexity cards.**  Both plateau parents *and* the cubic-phase
keystone are now at stage 3, so the shared collision bound is available:
`card_filter_phaseCollision_polyEval_gt_le` (seed normalization),
`card_filter_finCollision_gt_le` (unnormalized), and at one fixed seed
`exists_fixed_cubicSeed_sphereLaw_le`.

| card | remaining |
|---|---|
| ~~`weak-cut-complexity-onset-capacity-separation-law`~~ (promoted) | Theorem C's late-time clauses.  The chain is now: (a) **the bipartite eighth-root transfer** — `exists_prodPhaseSeed_collision_le_four_div` is stated for *continuous* product phases, but Theorem C needs a *finite* seed family to cover the delay sector, so the mean `4/D` must be transported to the product cubic ensemble `(MonLe ιA 3 → ZMod 8) × (MonLe ιB 3 → ZMod 8)`; only the **first** moment is needed, and the collision is a `trigLift` on `α ⊕ β` with support `≤ 4` and entries in `[-2,2]`, so `average_trigLift_eighthPhase_eq_integral_box` applies once a product-ensemble uniformity lemma (a character of `α ⊕ β` splits, and each factor kills its own nontrivial part) is in place; then (b) `exists_fixed_seed_on_delay` selects one seed on a positive-measure part of the delay sector, (c) `exists_mem_notMem_pathBadSphere` selects a nondegenerate direction inside it, (d) `exists_pathHamiltonian_orthoEigenBasis` supplies the eigenbasis, and (e) `exists_late_hardWindow` gives the continuous hard window at that one pair.  Clauses (b)--(e) are all owned |
| ~~`capacity-compatible-fast-forwardable-incubation-law`~~ (promoted) | Theorem A is closed; the transport blocker is **now closed too** (`CrossSphereIsometryTransport`, `PathShellPatchTransport`, `DiagonalPatchConstruction` below).  What is left is one module and one assembly.  **The module**: pull the chain-shell genericity and the *gauge-invariant* collision back to the patch sphere along `patchCoeffIsometry k : PatchSpace f d ≃ₗᵢ EuclideanSpace ℝ (Fin (card (ChainLabel (k+3))))` — the composite of `pathPatchIsometry` with the `pathCoeffEquiv` reindexing.  The pullback must use `crossCollision` (continuous on `simpleLocus`, hence **measurable**) rather than `pathEigenBasis`, because `exists_seed_measureReal_ge` requires `MeasurableSet (G q)` and eigenvector measurability is not available; `crossCollision_eq` converts back to the eigenbasis collision on the simple locus, and `sortedEigenBasis` is the eigenbasis to use (its eigenvalues are a permutation of the canonical ones, and `MaximallyProjectiveEnergy.comp_equiv` transports maximal projectivity).  **The assembly**: `hdensity` from `card_filter_phaseCollision_polyEval_gt_le` (bad fraction `≤ β = 96/(κ²D)`), then `exists_seed_measureReal_ge` + `measureReal_inter_conull` for `(8)`, `toSphere_patchThickening_ge` + `incubation_tail_lower` for `(20)`, `approxComplexity_le_of_mem_patchThickening` for clause 1, `exists_late_hardWindow` for clause 4, `exists_late_seed_recurrence` for clause 5, `norm_ge_half_of_perturbation` + `sphericalCap_coord_ge` for clause 7 |
| ~~`codimension-forced-complexity-onset-moment-divergence-law`~~ (promoted) | Theorem C (the coupled `10n-8` shortcut law) and the uniform split synthesis certificate `(16)`.  **`(22)` is closed** by an elementary route that replaces Davis--Kahan: `spectralCollision_le_of_near_diagonal` (`NearDiagonalOverlapFlatness`) bounds the collision of any constant-modulus seed by `(c+2δ/γ)²` for every eigenvector of a `δ`-nearby operator with `γ`-separated diagonal.  **The carrier data is closed too**: `pathHamiltonian_eq_diagonal` (`PathDiagonalCarrier`), the explicit base-three direction `sepCarrier` with its quantitative separation `abs_sub_pathDiagEnergy_sepCarrier_ge` and neighbourhood gap `gap_near_sepCarrier` (`PathCarrierSeparatingDirection`, `BaseThreeSignSeparation`).  **All closed**: `coupled_shortcut_tube` (incubation + `(22)` + `(25)` on the tube), `coupled_tail_lower` `(23)`, `lintegral_coupled_onset_pow_eq_top` and `lintegral_coupled_onset_rpow_eq_top` `(24)`.  The base-three direction had to be replaced by a near-uniform one (`nearUniformDir`) because base-three weights make the edge couplings exponentially small and so violate `(25)`; evenness of the unperturbed energy difference is what still separates.  `(16)` is the alphabet's compiler certificate, carried as `hcert` exactly as in the promoted sibling incubation card |
| `onset-recurrence-dimension-independence-law` | its parent `capacity-compatible-fast-forwardable-incubation-law` is now at stage 3, so clauses 1, 3, 4, 6, 7 and the measure bound `(3)` are `exists_incubating_cubicSeed` verbatim; what is left is clause 5, the recurrence *exponent* `(D-2)/2`, which is `relationPhaseEnsemble_temporalDimension_eq_projectiveRank` plus the fidelity reading of `(2)`.  Previously: the same path-shell apparatus as the weak-cut card (clauses 1, 3, 4, 6, 7, 8 of its Theorem); the recurrence-dimension clauses 2 and 5 are already corpus laws (`relationPhaseEnsemble_temporalDimension_eq_projectiveRank`, `lbitTemporalRank_eq_maximal_iff_maximallyProjectiveEnergy`) |
| `capacitary-observer-sector-excision-law` | Corollary I.1's physical-time transfer, Corollary A.3, `(8c)`'s transitive action, `(11be)`; Corollary I.3 and Theorem K are now ungated and need the Choi-trajectory instantiation of the fixed-shell Portmanteau |
| `all-replica-static-centralizer-planar-separation-law` | Theorems B–E from one replica to all finite `r`; also Kargin's matrix Dyson equation |
| ~~`computable-static-local-exponential-state-complexity-law`~~ (promoted) | joint measurability is **closed** (`measurableSet_hardPairEvent`, `JointHardEventMeasurability`): `NormedSpace.exp_continuous` applies directly on the matrix C⋆-algebra and `M ↦ M *ᵥ ψ` is continuous by `LinearMap.continuous_of_finiteDimensional`, so no topology reconciliation was needed.  Left: Theorem A's dictionary packaging (gate action on the seed, `CircuitDictionaryCounting`, unit norms), then `(8)`/`(8a)`/`(9)` are `QuenchedFixedTimeTransfer` verbatim; and Theorem B's three layers (Duhamel to a rational time and a rational coefficient vector -- both owned -- rational density in the positive-measure hard fibre, and the dovetailed search, which is the only part with no corpus antecedent).  **All closed.**  Theorem A: `half_mul_one_sub_le_liminf_quenchedWindowAverage_pauliEnsemble`, `le_limsup_quenchedFixedTimeProb_pauliEnsemble`, `exists_restricted_goodSet_common_time_hardness`, and at the circuit ball `le_limsup_quenchedFixedTimeProb_gateWord`; Theorem B: `exists_rational_common_time_witness`, `exists_integer_coefficient_witness`, and for uniform computability the decidable rational certificate `HardCertificate` with `hardCircuitEvent_of_hardCertificate`, `exists_hardCertificate_of_hard`, `exists_certifiedIndex`, `hard_searchIndex` |
| ~~`circuit-complexity-selection-synthesis-divergence-law`~~ (promoted) | Theorem B's measurable selection and the continuum joint layer — both closed, and so is item 6 of its own Lean plan: `exists_plateau_codebook_split` and `exists_late_plateau_codebook_split` give `(22)`--`(24)` on a plateau segment of an autonomous orbit, `recurrence_row` gives `(25)` and the second row of `(26)`.  The one prerequisite was the encoder's Borel fibres, now part of `exists_curve_codebook` |
| `algebraic-two-local-instant-exact-complexity` | §1's specialisation argument (the last content of Hilbert irreducibility) |
| `arithmetic-static-local-hardness-recurrence-window-law` | Castillo--Dietmann quantitative Hilbert irreducibility |

**Cluster B — assembly-only.**

| card | remaining |
|---|---|
| ~~`determinant-defect-completion-law`~~ (promoted) | package the two several-variable halves as one set equality.  `opSchattenDet_pencil_line` absorbs the `z` variable (`det_p(pencil A (z·v)) 1 = det_p(pencil A v) z`), so both halves can be stated at `z = 1` over the star-shaped set of parameters; the common definitions are a `PencilGraphClosure`/`PencilCompletionFibre` pair keyed on lines through the origin.  Two gaps remain inside the packaging: the sufficiency half `exists_finiteRankPencil_tendsto_plainDet` gives **pointwise** convergence in `z`, while the necessity half needs **locally uniform** convergence -- the bridge is Vitali/Montel from the uniform Schatten bound (`exists_uniform_schattenNorm_bound`) -- and `exists_mvPoly_of_line_closures` needs its `hQc` (line-restriction coefficient convergence) discharged from the one-variable necessity `exists_poly_of_tendstoLocallyUniformlyOn_opSchattenDet` |

**Cluster C — named external theorems.**

| card | imported input |
|---|---|
| `cusp-spectrum-radius-law` | Kaczorowski--Perelli standard-twist theory |
| `local-chain-metric-recurrence-exponents` | Kleinbock--Margulis extremality (plus Lemma 2, nondegeneracy) |
| `route-e-cofactor-amplified-e3-token-supply` | Matomäki--Teräväinen all-interval `E₃` |
| `route-e-forbidden-support-e3-stability` | same |
| `schanuel-defects-algebraic-coefficient-independent` | the algebraic-group/Kähler layer |
| `schanuel-stage-two-defect-slope-normal-form` | Kirby's exponential-algebraic closure |

## The state-synthesis cap is no longer a hypothesis (2026-08-21)

Three promoted cards (`weak-cut-…`, `codimension-forced-…`, `capacity-compatible-…`) carried the
gate model as a hypothesis: a finite alphabet with a uniform compiler certificate for the carrier
orbit.  Two-level (Givens) synthesis now proves it on **every** finite register:
`exists_synthesis_alphabet` (model register), `exists_universal_synthesis_certificate` (arbitrary
finite register, via `transportAct`), `exists_orbit_synthesis_certificate` (uniformly in
Hamiltonian, seed and time), and `exists_weakCut_delayed_plateau_synthesized` (the delayed plateau
with the alphabet supplied).  Cap `2\cdot\dim`, matching the cards' `(2)`.  New modules:
`TwoLevelStateSynthesis`, `SynthesisWordApproximation`, `UniversalSynthesisCertificate`,
`WeakCutUnconditionalPlateau` — all axiom-clean, umbrella-wired.

## `capacitary-observer-sector-excision-law` promoted (2026-08-21)

The three remaining items are theorems.  **Corollary A.3**: on a group with a left-invariant
probability measure, translations act transitively and invariance of the integral forces the
coefficient matrix of an orthonormal family to be orthogonal, so `(8c)` needs no hypothesis; the
copy representation `U ↦ U^{⊗k} ⊗ \bar U^{⊗k}` is built with its multiplicativity and dimension
`D^{2k}`, and a *centred* orthonormal family in its matrix-coefficient sector has at most `2D^{4k}`
members (`CopySectorTranslationSymmetry`).  **Corollary I.1**: an upper semicontinuous statistic is
squeezed from above by continuous majorants with almost the same Haar mean, so the physical-time
transfer needs no word truncation (`UpperSemicontinuousMajorant`,
`PhaseFlowSemicontinuousTransfer`); the syndetic clause is the dense-orbit law at the open strict
sublevel set.  **Corollary I.3 and Theorem K**: the same majorant argument along any weakly
convergent family, plus Markov, gives `(11az)`--`(11bb)`, instantiated unconditionally at the
nearest-neighbour Pauli chain (`AnnealedPortmanteauBound`, `AnnealedAccessibilityPlateau`);
Theorem K is that bound plus the elementary hardening-cone containment.

## Open (10)

algebraic-two-local-instant-exact-complexity, all-replica-static-centralizer-planar-separation-law,
arithmetic-static-local-hardness-recurrence-window-law,
cusp-spectrum-radius-law,
local-chain-metric-recurrence-exponents, onset-recurrence-dimension-independence-law,
route-e-cofactor-amplified-e3-token-supply, route-e-forbidden-support-e3-stability,
schanuel-defects-algebraic-coefficient-independent, schanuel-stage-two-defect-slope-normal-form
