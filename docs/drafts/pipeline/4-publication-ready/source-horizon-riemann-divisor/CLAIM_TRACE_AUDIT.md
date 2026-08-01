# Claim trace audit

Internal verification record. This file is not part of manuscript and must not be cited as novelty.

## Universal generator law

| Manuscript claim | Checked theorem |
|---|---|
| Factorially normalized coherent jets form exact Poisson packet | `coherentExponentialJet_poisson_conservation` in `formal/GaloisForLFunctions/HTGeometry/CayleyFockOrderSpaceConservation.lean` |
| Poisson drift normalization uniquely forces \(x=\tau/|b|^2\) | `coherentGenerator_observationTime_unique` |
| Forced clock sends \(b\) to \(\overline{b^{-1}}\) | `coherentGenerator_duality` |
| Canonical packet rate is \(2\operatorname{Re}(b^{-1})+1\) | `coherentGenerator_exponent_observationTime`, `coherentGenerator_poisson_conservation` |
| Fock growth factors as drift times dual rate | `cayleyFockExponent_eq_drift_mul_dualRate` |
| Neutral reciprocal line equals shifted-generator unit circle | `coherentGeneratorDualRate_eq_zero_iff_shift_norm_one` |

## Meromorphic source specialization

| Manuscript claim | Checked theorem |
|---|---|
| Residue transport before extraction gives \(m e^{x/(\rho-c)}\) | `cayleyPoleEvolvedResponse_residue_transport` in `formal/GaloisForLFunctions/HTGeometry/CayleyPoleResidueTransport.lean` |
| Source clock is the universal generator clock | `sourceCayleyObservationTime_eq_coherentGeneratorTime` |
| Source clock converts reciprocal displacement to conjugate displacement | `sourceCayley_inverse_observationTime`, `cayleyPoleResidueMode_observationTime_eq` |
| Source rate is \(2\operatorname{Re}(\rho-c)+1\), with stated horizon and sign | `coherentGeneratorDualRate_sourceCayley`, `sourceCayleyTransverseRate_eq_zero_iff`, `sourceCayleyTransverseRate_pos_iff` |
| Exact source-horizon Poisson channel law | `sourceCayleyResidueMode_horizon_conservation` |
| Height cancels in vertical parabolic family | `parabolicCayleyResidueMode_renormalization` |

## Finite-carrier localization

| Manuscript claim | Checked theorem |
|---|---|
| Finite transported divisor is differentially algebraic | `finiteCayleyResidueCarrier_differentiallyAlgebraic` in `formal/GaloisForLFunctions/HTGeometry/CayleyPoleResidueTransport.lean` |
| Explicit characteristic polynomial annihilates finite carrier | `expSumAnnihilator_ode` in `formal/GaloisForLFunctions/HTGeometry/ExponentialSumDA.lean`; specialized as `finiteCayleyResidueCarrier_ode` |
| Distinct finite source frequencies cannot have all first \(N\) jets vanish | `finiteCayleyResidueCarrier_jetFaithful`, based on `phaseJet_exists_ne_zero` |

## Riemann specialization

| Manuscript claim | Checked theorem |
|---|---|
| Actual completed prime–Gamma logarithmic response has stated arithmetic decomposition | `xiCayleyEvolvedLogDeriv_eq_arithmetic` in `formal/GaloisForLFunctions/RHTower/XiSourceCayleyOrderSpaceConservationLaw.lean` |
| Actual \(\xi\)-zero residue is transported with no simplicity assumption | `xiCayleyEvolvedLogDeriv_residue_transport` |
| Source mode is Poisson completion of inverse Li orbit | `xiCayleySourceResidueMode_eq_poissonCompletedLiOrbit` |
| Drift and exponent reconstruct real part and squared height | `xiSourceCayley_rho_re_reconstruction`, `xiSourceCayley_rho_im_sq_reconstruction` |
| Strict-right zero has positive source exponent | `xiSourceCayleyExponent_pos` |
| Riemann canonical-time packet is height-independent | `xiCayleySourceResidueMode_parabolic_conservation` |
| Packaged Riemann source law | `xiSourceCayleyOrderSpaceConservation_law` |

## Escape collision

| Manuscript claim | Checked theorem |
|---|---|
| Polynomial quartet perturbations are entire, symmetric, off-line, and hypertranscendental | `escapingQuartetGaugedXi_hypertranscendental`, `escapingQuartetGaugedXi_analyticAt`, `escapingQuartetGaugedXi_one_sub`, `escapingQuartetGaugedXi_conj`, `escapingQuartetGaugedXi_added_zero`, `escapingQuartetGaugedXi_added_zero_off_critical` in `formal/GaloisForLFunctions/RHTower/CompactOpenKolchinWardChargeEscape.lean` |
| Every holomorphic jet converges compact-open to \(\xi\) | `escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly` |
| Rational differential matroid is unchanged, including all scalar valuation layers | `escapingQuartetEvenShiftUpperEndCarrier_differentialMatroid_eq_raw`, `escapingQuartetEvenShiftUpperEndCarrier_allValuation_differentialMatroid_eq_raw`, and multiplicity analogues |
| Ward density vanishes uniformly on bounded windows | `escapingQuartetWard_window_tendstoUniformly`, `multiplicityEscapingQuartetWard_window_tendstoUniformly` |
| Total Ward mass is \(8\pi\), or \(8\pi N\) with multiplicity | `escapingQuartetWard_mass`, `multiplicityEscapingQuartetWardMass_eq` |
| Added divisor remains a simple logarithmic pole | `escapingQuartetGaugedXi_logDeriv_addedZero_simplePole`, `multiplicityEscapingQuartetGauge_logDeriv_addedZero_simplePole` |
| Packaged bounded and unbounded escape laws | `compactOpenKolchinWardChargeEscape_law`, `unboundedCompactOpenKolchinWardChargeEscape_law` |

## Capstone and audit status

- Combined endpoint: `sourceHorizonEscapeConservation_law` in `formal/GaloisForLFunctions/RHTower/SourceHorizonEscapeConservationLaw.lean`.
- Direct checks: all modified modules pass `lake env lean <file>`.
- Final module build: recorded separately after manuscript freeze.
- Axiom audit: capstones use only `propext`, `Classical.choice`, and `Quot.sound`; no project axioms.
- Repository lint: new modules are reachable from theorem-area umbrellas. Full lint remains nonzero only because unrelated pre-existing modules are still unreachable; no forbidden declaration was reported in this work.

## Fibre--character conservation and reflected geometry

| Manuscript claim | Checked theorem |
|---|---|
| Equivariant norm-conservative descent of a whole exponential source fibre gives \(T=0\) or \(\nu=0\) | `normConservative_sourceCharacterFibre_descent_dichotomy` in `formal/GaloisForLFunctions/RHTower/SourceCharacterFibreConservativeDescentLaw.lean` |
| Nonzero rate forces the complete descent map to vanish | `normConservative_sourceCharacterFibre_descent_eq_zero` |
| A nonzero exponential character in a conservative target has zero rate | `normConservative_expCharacter_forces_zero` in `formal/GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean` |
| Reflected nonzero rates have exactly hyperbolic invariant quadratic forms | `reflectedRealCharacter_invariantQuadratic_iff` |
| No nonzero positive-semidefinite invariant metric exists off horizon | `reflectedRealCharacter_no_nonzero_positiveInvariantQuadratic` |
| Centered Riemann character is unit norm exactly on critical line | `norm_centeredComplexModularCharacter_eq_one_iff` |

## Arithmetic transverse fibre and fusion

| Manuscript claim | Checked theorem |
|---|---|
| Positive exponent shells partition the nonunit integers and fuse to \(\zeta-1\) | `shellIndicator_mul_eq_zero_of_ne` in `HighExponentShellOrthogonalDivisorReplication.lean`; `tsum_complexShellIndicator` in `HighExponentShellHypertranscendence.lean` |
| \(S_m=\zeta H_m\) with stated quotient multiplier | `LSeries_shellIndicator` in `HighExponentShellZeroFree.lean`; carrier identity `zeta_mul_relativeShellMultiplierUpperEndCarrier` |
| \(H_m\) is zero-free on \(\operatorname{Re}s>1/2\) for \(m\ge12\) | `shellMultiplier_ne_zero` in `HighExponentShellZeroFree.lean` |
| Shells replicate the completed-zeta divisor with analytic multiplicity | `finiteHighShell_analyticOrderReplication` in `HighExponentShellFusionConservation.lean` |
| Shell multipliers are jointly relatively differentially independent over the zeta differential field | `relativeShellMultiplierUpperEndCarrier_differentialIndependent`; finite specialization `finiteHighShell_relativeDifferentialIndependent` |
| For \(K\ge12\), the complete high-exponent multiplier vector is analytic, absolutely summable, and has sum one on \(\operatorname{Re}s\ge1/2\) | `completeResolution_summable_conormalLanding` together with `analyticAt_completeResolutionMultiplier_of_re_ge_half` in `CompleteResolutionSummableConormalLanding.lean` |
| At every closed-right point the fixed complete resolution has a nonzero analytic channel preserving exact \(\xi\)-multiplicity | `analyticAt_completeResolutionMultiplier_of_re_ge_half`, `completeResolution_summable_conormalLanding` in `CompleteResolutionSummableConormalLanding.lean` |
| Every summable analytic resolution of one gives a nonzero \(\ell^1\) vector, a divisor-faithful channel, and the stable character-defect bound | `summableAnalyticResolution_conormalLanding`, `summableAnalyticResolution_sourceCharacter_stability` in `CompleteResolutionSourceCharacterSelectionLaw.lean` |
| Exact equivariance specializes the stable law to erasure-or-neutral-character | `summableAnalyticResolution_sourceCharacter_conservation` in the same module |
| For the actual complete Riemann resolution, every equivariant norm-conservative consumer erases the predeclared source vector or the point lies on the critical line | `completeResolution_sourceCharacter_selection` in the same module |
| Every approximate norm-conservative consumer has intertwining defect at least \(|e^\nu-1|\|T\mathbf m\|\), specialized to the complete Riemann source vector | `normConservative_sourceCharacter_defect_lowerBound`, `completeResolution_sourceCharacter_defect_lowerBound` in the same module |
| The complete source vector has \(\ell^1\)-norm at least one, so every \(\kappa\)-bounded-below consumer has defect at least \(\kappa|e^{2\operatorname{Re}\rho-1}-1|\) | `one_le_norm_summableSourceVector_of_hasSum_one`, `completeResolution_sourceCharacter_uniformFaithfulness_defect_lowerBound` in the same module |
| Off neutral rate, no uniformly source-faithful sequence of norm-conservative consumers can converge to equivariance | `no_uniformlyFaithful_normConservative_approximateIntertwiners` in the same module |
| Finite fusion splits reciprocal signature into fused and centered blocks | `reciprocalLabelQuadratic_fusion_conservation` in `formal/GaloisForLFunctions/HTGeometry/CommonCharacterFusionConservation.lean` |
| Countable unit-response codiagonal is not closable; constant nonzero Bessel response impossible | `shellCodiagonal_not_closable`; packaged with the Bessel no-go by `highShell_no_stableHilbert_unitFusion` and with the unitary locus by `highShell_infiniteFusionSingularity_and_unitaryLocus` |

## Global orientation and bounded capacity

| Manuscript claim | Checked theorem |
|---|---|
| Normalized Cayley source phase has unit norm | `norm_sourceCayleyPhase` in `CCMFirstClockCayleySourcePhaseOrientation.lean` |
| Cayley polarization converts every pair to the stated positive square | `sourceCayleyExteriorPair_re_eq` |
| Global finite-packet energy is nonnegative, and strict for an unequal-height positive pair | `sourceCayleyExteriorScalarEnergy_nonneg`, `sourceCayleyExteriorScalarEnergy_pos` |
| Calibrated Julia--Gamma specialization is literal | `gammaSewnMobiusJuliaCayleyExteriorHermitianEnergy_eq_calibrated` |
| Every bounded polarization obeys the universal diameter ceiling | `abs_re_boundedPolarizedExteriorHermitianEnergy_le` in `CCMFirstClockBoundedExteriorPolarizationNoGo.lean` |
| Every unit-bounded first-clock polarization is below certified bad-mass square beyond explicit threshold | `ccmFirstClockEulerDepthZeroBoundedExteriorEnergy_lt_badMass_sq`, `not_ccmFirstClock_badMass_sq_le_EulerDepthZeroBoundedExteriorEnergy_re` |
| Same Cayley chart is globally positive but cannot dominate the block bad mass | `ccmFirstClock_CayleyOrientationCapacity_dichotomy` in `CCMFirstClockCayleyOrientationCapacityDichotomy.lean` |
| A block polarization bounded by \(B\) has the exact \(B^2m^4/\log(2m^4)\) ceiling | `abs_re_ccmFirstClockEulerDepthZeroExteriorEnergy_le_of_norm_le` in `CCMFirstClockExteriorCapacitySingularity.lean` |
| Domination forces \(\log(2m^4)\le7200(\log4)^2B^2\), hence square-root-logarithmic blow-up | `ccmFirstClock_exteriorCapacity_forces_log_multiplier_sq` in the same module |

## Filtered, Calkin, Ward, and dense-radical specializations

| Manuscript claim | Checked theorem |
|---|---|
| Exact reflected valuation sewing costs beyond every physical aperture power | `reflectedHellingerSewingOperatorNorm_beyondEverySuzukiAperturePower` in `SuzukiApertureReesConditioningNoGo.lean` |
| No polynomially aperture-conditioned exact sewing exists | `reflectedHellingerSewingOperatorNorm_not_isBigO_suzukiAperturePower` |
| Two-clock character is quadrant bounded iff rate zero | `conjugateTwoClockQuadrantBounded_iff` in `HighExponentShellLeastAtomAsymptotic.lean` |
| Prime-seam Calkin compactness at one open-strip fibre is exactly critical-line location | `orbitwisePrimeSeamCalkinGramCompact_iff_re_eq_half` in `XiPrimeSeamCalkinGram.lean` |
| Strict-right Xi zero forces Ward response norm-square \(>4\) and negative Schur diagonal | `normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four`, `continuedXiWardFourUnitSchurDefect_eulerEdge_diag_re_neg` |
| Nonzero positive theta-null form has dense proper nonclosed \(L^2\) radical and is nonclosable | `universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw` in `HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean` |
| Theta-null sequential \(L^2\) closability occurs exactly for zero form | `universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero` |

## Current verification status

- Direct foreground checks passed:
  - `lake env lean GaloisForLFunctions/RHTower/CCMFirstClockCayleySourcePhaseOrientation.lean`
  - `lake env lean GaloisForLFunctions/RHTower/CCMFirstClockCayleyOrientationCapacityDichotomy.lean`
  - `lake env lean GaloisForLFunctions/RHTower/SourceCharacterFibreConservativeDescentLaw.lean`
  - `lake env lean GaloisForLFunctions/RHTower/CompleteResolutionSummableConormalLanding.lean`
  - `lake env lean GaloisForLFunctions/RHTower/CCMFirstClockExteriorCapacitySingularity.lean`
  - `lake env lean GaloisForLFunctions/RHTower/CompleteResolutionSourceCharacterSelectionLaw.lean`
- Final targeted `lake build` and updated axiom output are pending manuscript freeze.
