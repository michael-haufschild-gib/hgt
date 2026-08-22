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

| 2026-08-22 | `harmonic-matching-choi-laboratory-ramp` | the boxed shell theorem at the **sharp** radius `ε⋆ = √((1-2^{-1/2})/2)` (the corpus already had it at the rational `√(1/8)`): `harmonicMatching_twoGateCount_shell_lower_sharp`, the `⌈K/2⌉` complexity floor `ceil_half_le_choiTwoGateComplexity_harmonicMatchingEvolution`, the Duhamel tube `perturbed_harmonicMatching_twoGateCount_shell_lower_sharp` and the positive Gaussian mass `measure_ordinaryTwoLocalGaussianHarmonicChoiSharpRampEvent_pos` — 3 new modules (`SharpControlledPhaseChoiCutGap`, `HarmonicMatchingChoiSharpRamp`, `OrdinaryTwoLocalGaussianHarmonicChoiSharpRamp`), axiom-clean, wired.  The sharpening is the Gram largest eigenvalue `N(1+|cos(φ/2)|)`: `‖1+z‖ ≤ √2` on the closed left half-circle replaces the corpus's `3/2`, so the fidelity ceiling `7/8` becomes `(2+√2)/4` |

## Kleinbock--Margulis extremality is no longer an import (2026-08-22)

`local-chain-metric-recurrence-exponents` declared Kleinbock--Margulis extremality as an **imported
theorem**.  It is now unconditional Lean in this repository:
`KleinbockMargulis/TheoremA.lean` (`theoremA`, `theoremA_allOrders`, and the mathlib gap
`summable_pow_sum`), `KleinbockMargulis/Transference.lean` (`vwma_of_vwa` — the pigeonhole half of
Khintchine transference, which converts strong extremality into the *simultaneous* Diophantine
exponent the first-return law needs), and `KleinbockMargulis/Extremal.lean`
(`theoremA_simultaneous`, `theoremA_simultaneous_allOrders`, `measure_exists_dioph_exponent_eq_zero`).
All axiom-clean and umbrella-wired.

The residue on that card, and on its dependent `onset-recurrence-dimension-independence-law`
(clause 5), is **Lemma 2 only**: nondegeneracy of the spectral manifold.  With `theoremA_allOrders`
the requirement is exactly "the set where some nonzero `w` kills every positive-order derivative of
the gap-ratio map is null", which for an analytic chart is *empty* once no nonzero real traceless
constant-coefficient relation among the eigenbranches holds identically.  That statement is Lemma 2
of `../3-formalized/nearest-neighbor-qudit-projective-spectral-maximality.md` (real constants, not
rational); the corpus already owns the algebraic end of it
(`SpectralMonodromyRelationRigidity.centeredRoot_linearRelation_iff_coefficients_constant`,
`coefficients_eq_of_all_permuted_relations`) and the whole `LocalExtensionEigenbranchChart` stack.
Homogeneity `E_i(λx) = λE_i(x)` removes the constant term for free.

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

## The generic two-local Galois group is the shared blocker of three cards (2026-08-22)

`algebraic-two-local-instant-exact-complexity` (§1) and
`arithmetic-static-local-hardness-recurrence-window-law` (Theorem C's selection) both reduce, after
the now-closed `HilbertIrreducibility.gal_card_of_specialisation`, to one theorem:

> `Nat.card Gal = D !` for the generic two-local characteristic polynomial over `ℚ(Y)`.

The parent card `generic-two-local-spectral-monodromy` is at stage 3 but its Lean conclusion is
about **balanced integer** relations, obtained from *topological* monodromy.  "Geometric monodromy
⟹ Galois group" is Riemann existence and is not formalized.  An elementary replacement -- the
single-transverse block decomposition, Kummer independence of the block discriminants over `ℚ(i)`
(`A_z² + u² = (A_z+iu)(A_z−iu)`, distinct degree-one irreducibles), and transport to the full family
by a genuine *field embedding* `ℚ(i)(Y) ↪ Frac(F[[t]])` plus one-variable Hensel -- is written out
on the algebraic-two-local card.  First brick built and wired:
`HTGeometry/SquareInQuadraticExtension.lean`.

`local-chain-metric-recurrence-exponents` and `onset-recurrence-dimension-independence-law` need the
*analytic* sibling of the same phenomenon (real relation rigidity for the nearest-neighbour path
family); see the local-chain card.  So four of the ten open cards are downstream of one construction
in two flavours.

## Infrastructure landed 2026-08-22 (18 new modules, all axiom-clean and umbrella-wired)

**Kleinbock--Margulis** (4): `KleinbockMargulis/TheoremA` (`theoremA`, `theoremA_allOrders`,
`summable_pow_sum`), `/Transference` (`vwma_of_vwa`), `/Extremal`, `/AnalyticNondegeneracy`
(`exists_nondegAt_of_no_constant_combination`, `theoremA_analytic`).

**Sharp Choi ramp** (3): `SharpControlledPhaseChoiCutGap`, `HarmonicMatchingChoiSharpRamp`,
`OrdinaryTwoLocalGaussianHarmonicChoiSharpRamp` — the promoted card.

**Toward the generic two-local Galois group** (5):

* `SquareInQuadraticExtension` — one quadratic step creates one square class (`Algebra` language).
* **`QuadraticTowerSquareClasses`** (~880 lines) — the multiquadratic Kummer machinery, which
  mathlib does not have, in `Subfield L` language: `isSq_or_isSq_mul_of_span`,
  `mem_closure_insert_iff`, `span_unique`, the tower and its square-class statement in both
  structure and *partial-hypothesis* form (the latter is the one that breaks the circularity
  between `span` and `notMem`), the concrete tower `radicalStage` / `independentTower`, the
  conjugation `quadConj` / `quadConjEquiv` / `quadConjAlgEquiv`, and
  **`exists_algEquiv_neg_index`** — every block flip is realized by an algebra automorphism.
* `GalPermutationRealization` — `mem_range_galActionHom_of_algEquiv`,
  `card_gal_eq_factorial_of_closure`: realizing a *generating* set of root permutations gives
  `Nat.card p.Gal = D !`.
* `SquarefreeNotSquareInFractionField` — `not_isSquare_algebraMap_of_squarefree`, the Kummer
  independence criterion via UFD integral closedness.
* `PowerSeriesSimpleRootLift` — simple-root Hensel lifting over `PowerSeries R` **with
  uniqueness** (uniqueness is what makes the lift equivariant).
* `BlockDiagonalCharpolyQuadratic` — `charpoly_blockDiagonal` (mathlib has only `det_blockDiagonal`)
  and the symmetric `2 × 2` block's quadratic and discriminant.
* `HypercubeSingleTransverseBlocks` — with a single transverse flip the hypercube Hamiltonian is
  block-diagonal in the pairs `{x, x ⊕ e₀}` (`reindex_singleTransverseHam`) and its characteristic
  polynomial is the explicit product of the block quadratics (`charpoly_singleTransverseHam`).
* `SumOfTwoSquaresNotSquare` — the Kummer independence, which needs **no** multivariate
  irreducibility: `∏_z ((X + c_z)² + w²)` splits into `2|S|` distinct linear factors over a field
  containing `√(−1)`, so it is separable, squarefree and not a square in `K(X)`
  (`not_isSquare_prod_sq_add_sq`).
* `MonicDistinctRootFactorization` — a monic polynomial of degree `d` with `d` distinct roots over a
  domain is the product of the linear factors (`eq_prod_X_sub_C_of_monic_of_injective_roots`).
* `QuadraticRootFlip` — the residue side: the roots `(s_z ± ρ_z)/2`, their product form, and
  **`map_quadRoot_of_flip`**: an automorphism negating exactly `ρ_{z₀}` acts as
  `Equiv.swap (z₀, true) (z₀, false)`.
* `PowerSeriesSimpleRootLift` (extended) — **`map_lift_eq`, `map_lift_eq_of_perm`**: uniqueness of
  the Hensel lift makes it equivariant, so a residue permutation transports to the deformed roots.

The route these serve, the three shortcuts that provably fail, and the root-labelling obstruction
with its fix (put every root in the single ring `F[[u₁,…,u_n]]`, labelled by
`r_x ≡ d_x mod (u)`, and run each site's analysis in the larger ring `F'_i[[u_{≠i}]]` that contains
it) are written out on `algebraic-two-local-instant-exact-complexity.md`.

## Open (10)

algebraic-two-local-instant-exact-complexity, all-replica-static-centralizer-planar-separation-law,
arithmetic-static-local-hardness-recurrence-window-law,
cusp-spectrum-radius-law,
local-chain-metric-recurrence-exponents, onset-recurrence-dimension-independence-law,
route-e-cofactor-amplified-e3-token-supply, route-e-forbidden-support-e3-stability,
schanuel-defects-algebraic-coefficient-independent, schanuel-stage-two-defect-slope-normal-form

## `local-chain-metric-recurrence-exponents` PROMOTED to stage 3 (2026-08-22)

The card's boxed theorems `(3)` and the winding form of `(6)` are unconditional Lean theorems:
`exists_quditPathChain_discreteRecurrenceExponent` and
`exists_quditPathChain_windingRecurrenceExponent` (`HTGeometry/QuditPathChainRecurrenceExponent`).
Sixteen new modules; the card carries the full table.  The three load-bearing pieces:

1. **`(L2)` and `(L2')`** — a nonzero balanced real combination of the energies cannot vanish, nor
   be constant, on any nonempty open set of parameters of a family whose spectra escape the
   relation.  The obstruction is the labelling-orbit polynomial `∏_σ (∑_i c_i X_{σ i} - t)`, which
   is symmetric, hence a polynomial in the characteristic coefficients, hence in the parameters.
2. **The escape witness** — one local extension of a maximally projective base with a connected
   nonbipartite interaction lift erases any prescribed constant relation.  For an open chain this is
   available because the chain is one leaf extension of the chain one site shorter, attached at its
   last site (`leafGraphExtension_comap_pathGraph`); for two sites the architecture is unrestricted
   and a real diagonal witness suffices.
3. **Lemma 1 as a limit** — `tendsto_log_firstHit_div_log`.  Its missing half was the divergence of
   the first hit time, which follows from "not very well approximable" a second time: such a vector
   has no positive integer multiple in the lattice.

The remaining open card that depends on this one is `onset-recurrence-dimension-independence-law`
(clause 5, exponent `(D−2)/2`), whose analytic input is now available.

## Open (9)

algebraic-two-local-instant-exact-complexity, all-replica-static-centralizer-planar-separation-law,
arithmetic-static-local-hardness-recurrence-window-law,
cusp-spectrum-radius-law,
onset-recurrence-dimension-independence-law,
route-e-cofactor-amplified-e3-token-supply, route-e-forbidden-support-e3-stability,
schanuel-defects-algebraic-coefficient-independent, schanuel-stage-two-defect-slope-normal-form

## `algebraic-two-local-instant-exact-complexity` PROMOTED to stage 3 (2026-08-22)

Both boxed theorems of the card are unconditional Lean theorems at one *explicit* traceless integer
two-local Hamiltonian: `TwoLocalWitness.exists_twoLocal_exact_complexity_and_finiteness`
(`HTGeometry/TwoLocalExactComplexityFull`).  Eleven new modules; the card carries the full table.
The three load-bearing pieces:

1. **§1's generic Galois group.**  `exists_twoLocal_symmetric_gal` — the characteristic polynomial
   of the hypercube transverse-field family has Galois group `S_D` over `ℚ(u)`, by single-direction
   block decomposition, Kummer independence of the block discriminants (with **no** `√−1`), and
   transport of every block flip to the deformed root family through a chain of power-series
   deformations.  `gal_card_of_specialisation` then produces a rational specialisation avoiding any
   prescribed nonzero polynomial condition, and clearing denominators makes it integral.
2. **The Lagrange coefficient matrix.**  The eigenbasis of a rational Hermitian matrix is neither
   canonical nor algebraic, but `ℓ_j(H) *ᵥ Ω = ⟨e_j,Ω⟩ • e_j` is, so the orbit is
   `∑_j exp(−itE_j)·(ℓ_j(H) *ᵥ Ω)` with an *algebraic* invertible coefficient matrix.  The whole
   transcendence comparison is then made over `algebraicClosure ℚ ℂ`, where
   `AlgebraicIndependent.algebraicClosure` upgrades Lindemann–Weierstrass for free.
3. **Equation (2) without o-minimality.**  A transcendence basis inside the generating set gives
   `D−1` algebraically independent orbit coordinates; `16 s` complex gate parameters are fewer, so
   one polynomial separates; composing it with the orbit gives a complex-valued real-analytic
   function with finitely many zeros on a compact set.  Keeping the parameters *complex* is what
   keeps the constant at the card's `16` rather than `32`.

## Open (8)

all-replica-static-centralizer-planar-separation-law,
arithmetic-static-local-hardness-recurrence-window-law,
cusp-spectrum-radius-law,
onset-recurrence-dimension-independence-law,
route-e-cofactor-amplified-e3-token-supply, route-e-forbidden-support-e3-stability,
schanuel-defects-algebraic-coefficient-independent, schanuel-stage-two-defect-slope-normal-form

## Hilbert irreducibility with an *unbounded* good set (2026-08-22)

`HTGeometry/HilbertIrreducibility/LargeSpecialisation.lean` (new, axiom-clean, umbrella-wired):
every statement of the corpus's Hilbert chain now has a form whose good specialisations are
**larger than any prescribed bound**, up to and including
`gal_card_of_specialisation_gt`.  The only mathematical change is `exists_int_not_root_gt` — a
nonzero complex polynomial has a non-root integer above any bound — because the corpus's good
rationals are `s₀ + 1/t` with `t` arbitrarily large, so pushing `s₀` up pushes the whole good set
up.  Everything else carries the extra conjunct through the existing proofs verbatim.

This is the tool that turns a Zariski-open avoidance condition into an **ordinary open** one: with
the birational substitution `Y = r + 1/Z`, good points of the substituted family with `Z > N` are
good points of the original inside `(r, r + 1/N)`.  It is what
`arithmetic-static-local-hardness-recurrence-window-law` needs for Theorem C's collision bound, and
it replaces the appeal to Castillo–Dietmann's *quantitative* Hilbert irreducibility on that card.

## Theorem C's selection is Lean (2026-08-22)

`arithmetic-static-local-hardness-recurrence-window-law`'s selection clause — an explicit traceless
*integer* two-local Hamiltonian with symmetric Galois group, cyclic all-zero product state and
spectral collision below `4(2/3)ⁿ` — is `TwoLocalWitness.exists_integer_twoLocal_theoremC`
(`HTGeometry/TwoLocalTheoremCWitness`), unconditional and axiom-clean.

Two devices did it, both reusable:

1. **Lacunary Hilbert irreducibility.**  Quantifying the lower bound *inside* the induction of
   `hilbert_several` lets each recursive call use a bound depending on the coordinate already
   chosen; `gal_card_of_specialisation_lacunary` therefore returns a specialisation with every
   coordinate above any prescribed bound *and* tripling from each coordinate to every later one.
   This converts an inequality side condition into something Hilbert irreducibility can deliver,
   with no birational substitution and no quantitative (Castillo–Dietmann) input.
2. **The Walsh frame.**  `HypercubeWalshDiagonalisation` diagonalises the transverse flips of the
   Boolean hypercube; a transverse-field Hamiltonian becomes near-diagonal with the separated
   diagonal `∑_i ± u_i`, and `|0⟩^{⊗n}` becomes the flat superposition — exactly the hypothesis of
   the corpus's `spectralCollision_le_of_near_diagonal`.  No eigenvector perturbation theory.

Remaining on that card: only the downstream window assembly `(36)` into Theorem B's
`half_mul_le_measureReal_hardWindow`, and Theorem D.

## Theorem C of `arithmetic-static-local-hardness-recurrence-window-law` is Lean (2026-08-22)

`TwoLocalWitness.exists_integer_twoLocal_hardWindow` (`HTGeometry/TwoLocalTheoremC`).  The card's
Theorems A and B were already closed; what was missing was the *selection* and the interface.  Both
are now built: `exists_integer_twoLocal_theoremC` (selection) and
`exists_algebraic_spectrum_package` + `half_mul_le_measureReal_hardWindow_physical` (interface).
Remaining on the card: `(38)`, the recurrence half, and Theorem D.

## `arithmetic-static-local-hardness-recurrence-window-law` PROMOTED to stage 3 (2026-08-22)

All four theorems are unconditional Lean theorems.  Theorems A and B were already closed; this
session added the selection, the interface and Theorem D:

* **selection** — `TwoLocalWitness.exists_integer_twoLocal_theoremC`: an explicit traceless integer
  two-local Hamiltonian with `|Gal| = D!`, cyclic `|0⟩^{⊗n}`, and collision below `4(2/3)ⁿ`.  Two
  new devices: *lacunary Hilbert irreducibility* (quantify the bound inside the induction so each
  recursive call may use a bound depending on the coordinate just chosen) and the *Walsh frame*
  (which turns a transverse-field Hamiltonian into the near-diagonal configuration the corpus's
  `spectralCollision_le_of_near_diagonal` already handles).
* **interface** — `exists_algebraic_spectrum_package` and
  `half_mul_le_measureReal_hardWindow_physical` / `_recurrenceWindow_physical`: the spectrum of a
  traceless integer matrix presented as algebraic integers of its splitting field with a
  distinguished embedding, and the orbit fidelity identified with the physical one.
* **`(36)`, `(38)`** — `TwoLocalWitness.exists_integer_twoLocal_hardWindow`.
* **Theorem D** — `RHTower.exists_integer_twoLocal_choiAlternation`.  One lemma away: the corpus's
  Choi alternation law needs only `MaximallyProjectiveEnergy`, which *is* the spectral rigidity.

Castillo–Dietmann's quantitative Hilbert irreducibility, the card's declared external blocker, is
not needed.

## Open (6)

all-replica-static-centralizer-planar-separation-law,
cusp-spectrum-radius-law,
onset-recurrence-dimension-independence-law,
route-e-cofactor-amplified-e3-token-supply, route-e-forbidden-support-e3-stability,
schanuel-defects-algebraic-coefficient-independent, schanuel-stage-two-defect-slope-normal-form
