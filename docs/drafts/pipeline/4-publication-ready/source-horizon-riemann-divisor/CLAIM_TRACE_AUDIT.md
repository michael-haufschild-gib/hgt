# Claim trace audit

Internal verification record. Not part of manuscript; not novelty evidence.

## Current manuscript: prime-source distinction and charge conservation

| Manuscript claim | Checked declaration |
|---|---|
| Exact analytic iff: differential independence over coordinate plus every finite-prime Euler germ equals complete clock-orbit independence modulo finite prime rays | `differentialIndependent_finiteAbscissaPrimeProfiles_over_pulledCoordinate_iff_clock` in `PrimeClockAnalyticExactCorrespondence.lean` |
| Exact relative analytic iff: independence over an old analytic differential field equals clock independence modulo the complete old clock submodule | `differentialIndependent_finiteAbscissaPrimeProfiles_relative_iff_clockQuotient` in `PrimeClockAnalyticExactCorrespondence.lean` |
| Generic exact meet: two jointly free common/private differential fields intersect in precisely their common field | `differentialIndependent_threeBlock_differentialAdjoin_inf` in `RelativeShellExactCommonCore.lean` |
| Generic private tensor law: jointly free private differential extensions are linearly disjoint over their common differential field | `differentialIndependent_threeBlock_private_linearDisjoint` in `RelativeShellExactCommonCore.lean` |
| Exact Riemann private tensor law for arbitrary shell subsets | `relativeShellPrivateDifferentialField_linearDisjoint` in `RelativeShellExactCommonCore.lean` |
| Complete Riemann shell Boolean algebra: arbitrary nonempty families preserve intersections and composita exactly; complements are exact relative complements; every observable has finite shell support; field inclusion and equality reflect source inclusion and equality; the power-set realization is injective | `relativeShellSubsetDifferentialField_iInf`; `relativeShellSubsetDifferentialField_iSup`; `relativeShellSubsetDifferentialField_compl`; `relativeShellSubsetDifferentialField_exists_finset_support`; `relativeShellSubsetDifferentialField_inf`; `relativeShellSubsetDifferentialField_sup`; `relativeShellSubsetDifferentialField_le_iff`; `relativeShellSubsetDifferentialField_eq_iff`; `relativeShellSubsetDifferentialField_injective` in `RelativeShellExactCommonCore.lean` |
| A source nonzero at every prime on infinitely many private depths stays free over all-depth finite residue--valuation carriers and all finite-prime Euler germs | `analyticPrimeProfileCarrier_differentialIndependent_over_localEulerResidueFusionCompletion`; `analyticPrimeProfileCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion` in `PrimeResidueValuationExactSourceBoundary.lean` |
| Filtered von Mangoldt current and uncorrected completed \(+2\) Xi logarithmic shift are hypertranscendental over full local-Euler residue--valuation fusion completion | `filteredVonMangoldtUpperEndCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion`; `xiLogDerivShiftTwoUncorrectedCarrier_hypertranscendentalOver_localEulerResidueFusionCompletion` in `XiShiftResidueValuationFusionBarrier.lean` |
| Complete \(K\)-free head plus exact largest-exponent shells have disjoint \(0/1\) supports partitioning all positive integers | `completeResolutionIndicator_eq_zero_or_one`; `tsum_completeResolutionIndicator`; `completeResolutionIndicator_pairwiseDisjoint` in `CompletePositiveKolchinFreeRiemannResolution.lean` |
| Complete multiplier vector is absolutely summable on \(\operatorname{Re}s>0\) and has coordinate sum one | `summable_completeResolutionMultiplier`; `hasSum_completeResolutionMultiplier_one` in `CompleteResolutionSummableLanding.lean` |
| For \(K\ge12\), complete channels carry exact zeta divisor in the open right half-strip; at the closed boundary at least one channel preserves exact Xi order | `analyticOrderAt_riemannZeta_completeResolutionChannel`; `completeResolution_summable_conormalLanding` |
| Complete multiplier family has maximal countable differential rank over full zeta differential field | `completeResolutionUpperEndMultiplier_relativeDifferentialIndependent` |
| Complete source embedding and its zero-mass radical translate are injective | `completeResolutionSourceEmbedding_injective`; `completeResolutionSourceRadicalEmbedding_injective` |
| Unsquared source reflection displacement is zero exactly on the critical line | `completeResolutionReflectionSourceDisplacement_eq_zero_iff` |
| Every fixed source vector converges cofinally in \(\ell^1\) to the same point section, with an exact head-plus-tail norm formula | `norm_completeResolutionSourceVector_sub_pointSection`; `tendsto_completeResolutionSourceVector_pointSection` in `CompleteResolutionCofinalConditioningLaw.lean` |
| Distinct points remain separated at every finite shell base but their separation tends to zero and its reciprocal tends to infinity | `norm_completeResolutionSourceVector_sub_pos`; `tendsto_norm_completeResolutionSourceVector_sub_zero`; `tendsto_inv_norm_completeResolutionSourceVector_sub_atTop` in the same module |
| Every uniformly Lipschitz cofinal observer family, without linearity or label symmetry, loses all fixed spectral separation | `tendsto_uniformLipschitz_completeResolutionObserver_separation_zero`; `no_uniformLipschitz_completeResolutionObserver_fixedSeparation` in the same module |
| Off-line reflection displacement tends to zero cofinally while its inverse norm diverges | `tendsto_completeResolutionReflectionSourceDisplacement_zero`; `tendsto_inv_norm_completeResolutionReflectionSourceDisplacement_atTop` in the same module |
| Unit mass, finite-depth conormal landing, cofinal collapse, and inverse-conditioning divergence hold in one package | `completeResolution_cofinalConservationSingularity_law` in the same module |
| Canonical prime-two/prime-three projective normal chart converges despite source collapse and its limit is injective | `completeResolutionCofinalBlowupChart_fst_eq_sourceRatio`; `tendsto_completeResolutionCofinalBlowupChart`; `completeResolutionCofinalBlowupLimit_injective`; `completeResolution_collapseBlowup_duality` in the same module |
| For every distinct spectral pair, projective chart cannot satisfy any shell-independent Lipschitz estimate relative to collapsing source distance | `no_uniformLipschitz_completeResolutionCofinalBlowupChart_pair` in the same module |
| Every bounded vector-valued label-blind observer factors through the norm-one codiagonal | `sourceLabelBlind_factorization` in `CompleteResolutionLabelBlindObserverRigidity.lean` |
| Label blindness is exactly annihilation of zero-mass radical and makes observer constant on each mass fibre | `sourceLabelBlind_iff_annihilates_zeroMass`; `sourceLabelBlind_eq_of_sameMass` |
| Off line, actual reflection displacement is nonzero but every bounded label-blind observer annihilates it | `completeResolution_offlineReflectionDisplacement_labelBlind` |
| Norm-conservative consumer defect is at least \(|e^\nu-1|\|T E(\rho)\|\); exact non-erasing equivariance forces critical line | `completeResolution_sourceCharacter_defect_lowerBound`; `completeResolution_sourceCharacter_selection` |
| Positive largest-exponent shells have disjoint \(0/1\) supports and fuse as \(S_m=\zeta H_m\) | `shellIndicator_mul_eq_zero_of_ne`; `zeta_mul_relativeShellMultiplierUpperEndCarrier` |
| \(H_m\) is holomorphic and zero-free on \(\operatorname{Re}s>1/2\) for \(m\ge12\), so shell divisor order equals zeta divisor order | `shellMultiplier_ne_zero`; `finiteHighShell_analyticOrderReplication` |
| Complete \(H_m\)-frame is jointly differentially independent over \(\mathbb C(s)\langle\zeta\rangle\) | `relativeShellMultiplierUpperEndCarrier_differentialIndependent` |
| Zeta is hypertranscendental over differential field generated by complete countable zero-free \(H_m\)-frame | `zetaUpperEndMero_hypertranscendentalOver_relativeShellMultipliers` in `RelativeShellCommonDivisorHypertranscendence.lean` |
| Zeta logarithmic current is hypertranscendental over the same complete transverse shell field | `zetaLogCurrentUpperEnd_hypertranscendentalOver_relativeShellMultipliers` in `RelativeShellCommonCurrentHypertranscendence.lean` |
| Any two distinct high-shell test fields meet in exactly the zeta differential field; intersection of the complete countable test family is the same field | `relativeShellTestDifferentialField_inf`; `iInf_relativeShellTestDifferentialField` in `RelativeShellExactCommonCore.lean` |
| Every shell channel recovers the common current as exact relative logarithmic connection | `logDeriv_riemannZeta_mul_shellMultiplier` in `HighExponentShellZeroFree.lean` |
| Source-normalized adjacent transfer converges to \(2^{1/2-s}\) | `tendsto_sourceNormalizedShellAdjacentTransfer` |
| Prime-two-removed adjacent transfer converges to \(3^{1/2-s}\) | `tendsto_normalizedShellSecondAtomAdjacentTransfer` |
| Pair of transfer characters is injective and recovers complete complex spectral coordinate | `twoPrimeShellTransferSpectrum_injective` |
| Transfer modulus and reflected reciprocal product give signed horizontal charge | `norm_shellTransferCharacter`, `log_norm_shellTransferCharacter`, `shellTransferCharacter_reflection_pair` |
| Reflected shell-tail entropy equals Riemann source-horizon rate; canonical transported residue has exact Poisson order packet with that rate | `riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy`; `riemannSourceCayleyResidueMode_horizonConservation_shellTail` in `XiSourceBoundaryOrientationConservation.lean` |
| Nearby-cycle outer charge and centered Xi logarithmic-current residue both equal \(-m(\rho-\tfrac12)\) | `xiDepthNearby_sourceBoundaryOrientationConservation` in `XiSourceBoundaryOrientationConservation.lean` |
| Dyadic deck charges form a coherent root-of-unity tower and read every \(2\)-adic divisibility level of divisor multiplicity | `xiDeckCharge_pow`; `xiDeckCharge_succ_sq`; `xiDeckCharge_eq_one_iff_toNat_dvd` in `XiDeckCharge.lean` |
| Escaping off-line quartet is invisible to every fixed compact jet and bounded Ward window while retaining total Ward mass \(8\pi\) per quartet | `compactOpenKolchinWardChargeEscape_law`; multiplicity form `unboundedCompactOpenKolchinWardChargeEscape_law` |
| Scalar shell-label erasure is not sequentially closable | `shellCodiagonal_not_closable` |
| Full independent two-clock quadrant is bounded iff rate zero, while characteristic line cancels depth | `conjugateTwoClockQuadrantBounded_iff`, `conjugateTwoClockCharacter_characteristic` |
| Gaussian Hilbert-line log-determinant curvature is minus self-commutator energy and is reflection invariant | `hilbertLineGaussian_logDet_curvature_eq_selfCommutator`; `hilbertLineAnnihilationEnergy_reflection_invariant` in `HilbertMetric/HilbertLineCommutatorCurvature.lean` |
| Reflection-symmetric positive conserved quadratic is zero at nonzero rate | `no_nonzero_positive_boostInvariant_reflectionForm` in `ReflectionBoostPolarizationLaw.lean` |
| Conservative cross square, Fisher information, positive curvature, and reciprocal-square orientation are exactly equal | `reflectionInformationIdentity`, `reciprocalSquareReflectionInformationIdentity` |
| Xi reciprocal boost rate is actual reflected source entropy | `reflectionTransverseRate_xiSpectralPoint_eq_sourceEntropy` |
| At an off-line Xi divisor copy, every positive reflection-symmetric conserved quadratic is zero | `xiSourceEntropy_no_nonzero_positive_conservative_reflectionForm` |
| Xi Fisher mass equals orientation mass and positive curvature is eight times orientation mass | `xiSourceEntropyReflectionFisherMass_eq_measureMass`, `xiSourceEntropyPolarizationCurvatureMass_eq_eight_mul_measureMass` |
| Universal countable quartet-symmetric tomography law, including summability | `reciprocalSquareQuartetSymmetricCauchyTomographyLaw` in `XiSourceEntropyCauchyTomography.lean` |
| Local Cauchy variance is \(W_z(a)\operatorname{Im}(a^{-2})^2\), with \(W_z(a)>0\) | `cauchyQuartetVariance_eq_tomographyWeight_mul_orientationMass`, `xiSourceEntropyCauchyTomographyWeight_pos` |
| Reflection pairing of reciprocal-square orientation is negative total mass | `reciprocalSquareOrientationReflectionPairing_eq_neg_mass`; Xi Hilbert realization `xiWeilHilbertQuadratic_sourceEntropyOrientationVector_eq_neg_measureMass` |
| Reflection-even quotient erases every odd target | `oddTarget_eq_zero_of_factorsThrough_invariantCompletion` in `CompletionKernelPairTransversalityLaw.lean` |
| Orientation measure mass equals source energy; vector is reflection-odd; Weil square is negative mass | `xiSourceEntropyOrientationMeasureMass_eq_energy`, `xiWeilLineConjLp_xiSourceEntropyOrientationVector`, `norm_sq_xiSourceEntropyOrientationVector`, `xiWeilHilbertQuadratic_sourceEntropyOrientationVector_eq_neg_measureMass` |
| Endpoint constant is \(2+\gamma_E-\log(4\pi)<93/2000\); every zero has \(\gamma^2>41/2\) | `xiEndpointCompletedCurvature_eq_eulerMascheroni_log`, `xiEndpointCompletedCurvature_lt_ninetyThree_over_twoThousand`, `xiZeroCopy_fortyOne_div_two_lt_im_sq` |
| Off-line quartet height and global source energy bounds | `xiZeroCopy_offLine_sevenThousandNineHundredSeven_over_ninetyThree_lt_im_sq`, `xiThermalOrientationEnergy_le_exactCubicEndpointBudget`, `xiSourceEntropyOrientationEnergy_lt_one_over_oneHundredFiftyThousand` |
| Xi Cauchy defect is a positive tomogram and vanishes exactly under RH | `xiSourceEntropyCauchyTomographyLaw`, `xiSourceEntropyCauchyTomography_eq_zero_iff_riemannHypothesis` |
| Nonzero reflected character has only hyperbolic invariant quadratic forms and no nonzero PSD invariant form | `reflectedRealCharacter_invariantQuadratic_iff`, `reflectedRealCharacter_no_nonzero_positiveInvariantQuadratic` |
| Symmetric Gamma/co-Poisson common-test determinant is strictly negative | `gammaCoPoissonSymmetricPacketDeterminant_eq`, `gammaCoPoissonSymmetricPacketDeterminant_re_neg` |
| Critical rooted prime amplitude has divergent squared norm | `not_summable_sq_suzukiCriticalRootedBianchiPrimeAmplitude` |
| Finite-Rees operators preserve flat radical and cannot sew reflected Wold/Hellinger sectors | `no_finiteReesOperator_sews_flat_to_nonflat`, `no_boundedOperator_sews_reflected_Hellinger_sectors`, `primeWoldReesFiltration_law` |
| Reflected Hellinger sectors are all-orders flat versus half-normal, their scalar sewing cost dominates every inverse Rees power, and every exact sewing operator has the same essential norm lower bound | `primeValuationHellingerBelow_reesAllOrdersFlat_of_pos`; `primeValuationHellingerBelow_isTheta_halfNormal_of_neg`; `reflectedHellingerSewingCost_beyondEveryReesOrder`; `reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder` in `PrimeValuationHellingerReesReflectionFracture.lean` |
| Activation \(\zeta(s)/\zeta(2s)\) disintegrates into Bernoulli occupancy and geometric valuation; Fisher damping is exact | `woldActivationHolonomy_diagonal_eq_squarefreePartition`, `diagonalActivationPositiveValuationMass_factorization`, `diagonalActivationValuationMass_total`, `diagonalActivationOccupancyFisher_eq_variance`, `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation` |
| Gamma sewing preserves prime summability in both directions at positive aperture and has nonzero principal-symbol determinant at every finite prime rank | `summable_gammaSewnMobiusMultiplier_sq_mul_iff`; `gammaSewnMobiusReesPrincipalSymbolMatrix_det_ne_zero`; packaged as `gammaSewnActivationReesResolution_law` |
| No additive scalarization \(\mathbb N^2\to\mathbb N\) is injective, whereas two paired nonparallel scalar views recover the bidegree and unpaired marginals do not | `natProd_addMonoidHom_not_injective`; `transverseScalarDegrees_injective`; `transverseScalarMarginal_pairing_ambiguity` in `BifilteredScalarizationNoGo.lean` |
| Nonzero positive theta-null form has dense proper nonclosed \(L^2\) radical and is nonclosable | `universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw` |
| Paugam reciprocal operator preserves actual Meyer boundary and descends as an involution on rapid quotient | `deningerMeyerPaugamJ_boundary`, `deningerMeyerRapidCohomologyPaugamJ_sq` |
| Positive reciprocal cup--Hodge defect vanishes on genuine endpoint cycles | `deningerMeyerEndpointCycleReciprocal_cupSigma_self_zero` |
| Strict-right Xi fibre forces Calkin and Ward failures | `xiRightUpperHorizontalFailure_law` |

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/PrimeResidueValuationExactSourceBoundary.lean
lake env lean GaloisForLFunctions/RHTower/RelativeShellCommonCurrentHypertranscendence.lean
lake env lean GaloisForLFunctions/RHTower/RelativeShellExactCommonCore.lean
```

Exited successfully with no warnings. Final targeted module builds and axiom prints are complete:

```text
lake build GaloisForLFunctions.RHTower.RelativeShellExactCommonCore
lake build GaloisForLFunctions.RHTower.XiShiftResidueValuationFusionBarrier
```

Both builds succeeded. Axiom prints for arbitrary shell meets and joins, finite shell support,
relative complements, private-tensor independence, common-core, and Xi-shift capstones report
only `propext`, `Classical.choice`, and `Quot.sound`.

Repository lint reported no forbidden declaration in this work. It remains globally nonzero
because seven unrelated owned modules are not reachable from their theorem-area umbrellas:
`SourceCharacterFibreConservativeDescentLaw`, `StaticChoiQuantitativeRecurrenceUpperLaw`,
`GammaShiftRatioGeneral`, `PhysicalObserverSpectralLeafExtension`,
`PhysicalObserverSpectralRealization`, `PhysicalTwoQubitGraphSeed`, and `PiZeroNerve`.

---

Historical trace material for earlier manuscript iterations follows.

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
