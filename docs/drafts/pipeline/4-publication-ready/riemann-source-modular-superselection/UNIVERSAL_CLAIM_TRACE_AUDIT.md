# Claim trace: `main-universal.tex`

Internal audit only. Manuscript must not mention formalization.

## Universal law

| Manuscript claim | Declaration(s) | Module |
|---|---|---|
| factorization on attained range iff kernel refinement | `factorsThroughRange_iff_kernelRefines` | `HTGeometry/CompletionKernelPairTransversalityLaw.lean` |
| arbitrary heterogeneous family recovery | `observationFamilyRecovers_iff_factorsThroughRecordRange` | same |
| downstream postprocessing enlarges kernel | `mapKernelPair_mono_of_factorsThrough` | same |
| invariant completion kills an odd real target | `oddTarget_eq_zero_of_factorsThrough_invariantCompletion` | same |
| every repair separates a nonzero reflected pair | `transverseChannel_separates_reflection_of_oddCharge_ne_zero`, `reflectionOddPart_ne_zero_of_jointlyRecovers` | same |
| dense fibres force a one-point-continuous separated reporter to be constant | `downstreamReporter_constant_of_dense_completionFibers` | same |
| `(1-epsilon)(1+epsilon)=0` | `reflectionOrientation_mul_hyperbolic_eq_zero` | `HTGeometry/ReflectionOrientationSingularSupportLaw.lean` |
| regular symmetric channel forces trivial orientation | `reflectionOrientation_eq_one_of_hyperbolic_regular` | same |
| with regular `2`, nontrivial orientation iff symmetric channel is nonregular | `reflectionOrientation_ne_one_iff_hyperbolic_not_regular` | same |
| anti-invariant module vectors lie in symmetric-channel kernel | `hyperbolic_smul_antiInvariant_eq_zero`, `antiInvariant_eq_zero_of_hyperbolic_smul_injective` | same |
| scalar and operator sewing cost beyond every finite order | `reesEssentialSewingCost_beyondEveryFiniteOrder`, `reesExactSewingOperatorNorm_beyondEveryFiniteOrder` | `RHTower/AsymptoticTypeSuperselection.lean` |

## Riemann centered character

| Manuscript claim | Declaration(s) | Module |
|---|---|---|
| character law and real-ray norm | `centeredComplexModularCharacter_add`, `norm_centeredComplexModularCharacter_ofReal` | `RHTower/RiemannComplexModularCharacterLaw.lean` |
| exact charge recovery | `centeredComplexModularCharacter_weight_recovery` | same |
| reflection negates charge and norms multiply to one | `criticalLineReflectionPoint_weight`, `norm_centeredComplexModularCharacter_reflection_mul` | same |
| principal Hurwitz phase gives absolute centered charge | `centeredComplexModularCharacter_principalPhase` | same |
| shell transfer entropy gives negative charge | `shellTransferEntropy_eq_neg_xiRightSourceModularCharge` | `RHTower/XiSourceModularTypeSuperselectionLaw.lean` |
| normal-cone/current residue gives multiplicity times centered charge | `tendsto_re_xiExceptionalAffineDivisorCurrent_eq_neg_modularCharge` | same |
| complex residue `-m(rho-1/2)` | `tendsto_xiCenteredPoleResidueMode_eq` and capstone fields | `RHTower/XiHypertranscendentalModularResidueTransgression.lean`, `RHTower/XiDepthMobiusGammaOuterInnerWeld.lean` |

The manuscript also gives the elementary local logarithmic-derivative proof of the current residue, so its truth does not depend on terminology of the source-normal chart.

## Gamma--Stokes source factor

| Manuscript claim | Declaration(s) | Module |
|---|---|---|
| literal theta seed Mellin transform equals archimedean factor | `mellin_thetaCuspSeed_eq_archFactor` | `RHTower/EulerHedenmalmGammaStokesTransgression.lean` |
| causal minus anti-causal mode is `t^(-s) A(s)` | `thetaGamma_causal_sub_anti_eq_archFactor_character` | same |
| jump nonzero in open strip | `thetaGamma_stokes_jump_ne_zero` | same |
| Euler multiplication kills jump iff Xi zero | `thetaGamma_completedEuler_kills_stokes_iff_xi_zero` | same |
| character preserves analytic multiplicity | `analyticOrderAt_thetaGammaCompletedEulerOutput` | same |

## Infinite Hedenmalm divisor transgression

| Manuscript claim | Declaration(s) | Module |
|---|---|---|
| removable germ value equals translated multiplicity difference | `xiFluxShiftDifferenceFullResidueGerm_zero` | `RHTower/HedenmalmOrientationDivisorTransgression.lean` |
| multiplicity jump forces nonanalyticity | `not_analyticAt_xiFluxShiftDifference_of_order_ne` | same |
| every positive shift has infinitely many multiplicity jumps | `xiTranslationOrderJumpSet_infinite` | same |
| affine Hedenmalm multiplier has infinite singular carrier | `xiCanonicalOrientationOrderJumpFrequencySet_infinite`, `xiCanonicalOrientationOrderJumpFrequencySet_subset_singularSet`, `xiCanonicalOrientationSingularSet_infinite_via_orderTransgression` | same |
| affine current/multiplier identity | `xiFluxShiftDifference_eq_neg_canonicalOrientation` | `RHTower/HedenmalmInfiniteOrientationSingularities.lean` |

Sign audit: manuscript defines `G_h = logDeriv xi(s) - logDeriv xi(s-h)`, the negative of the corpus `xiFluxShiftDifference`. Therefore its removable center value is exactly `m(rho)-m(rho-h)`, as written.

## Escaping quartet

| Manuscript claim | Declaration(s) | Module |
|---|---|---|
| Xi hypertranscendental | `xi_hypertranscendental` | `RHTower/XiHypertranscendenceUnconditional.lean` |
| FE/Schwarz quartet, all-jet compact escape, bounded Ward escape, `8*pi` mass | `compactOpenKolchinWardChargeEscape_law` | `RHTower/CompactOpenKolchinWardChargeEscape.lean` |
| full continuum real-shift differential matroid blind | `escapingQuartetRealShiftUpperEndCarrier_differentialMatroid_eq_raw` | `RHTower/XiRealTransverseQuartetSurgeryMatroidInvariance.lean` |
| reciprocal-square energy formula and decay | `escapingModularTraceEnergy_eq`, `escapingModularTraceEnergy_tendsto_zero` | `RHTower/RiemannComplexModularCharacterLaw.lean` |
| fixed modular charge and fixed Hurwitz phase survive | `escapingModularPoint_weight`, `escapingModularPoint_principalPhase` | same |
| combined certificate | `escapingModularCharacterSeparation_law` | same |

Parameter audit: paper uses horizontal displacement `c`; Ward width is `c+1/2`, matching the formal `d`/`c=d+1/2` convention after renaming. Trace energy uses centered displacement `c`, matching `escapingModularTraceEnergy_eq`.

## Prime-valuation type fracture

| Manuscript claim | Declaration(s) | Module |
|---|---|---|
| local squared Hellinger factor | `primeValuationSquaredHellingerFactor` and its definitions | `RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| negative charge has exact Wold grade | `primeValuationSquaredHellingerBelow_isTheta_wold_of_neg` | same |
| positive charge flat beyond all Wold orders | `primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos` | same |
| no finite-Rees operator sews reflected sectors | `no_finiteReesOperator_sews_reflected_Hellinger_sectors` | same |
| scalar cost and operator norm beyond every order | `reflectedHellingerSewingCost_beyondEveryReesOrder`, `reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder` | same |
| actual Xi right-charge specialization | `xiRightModularSewingOperatorNorm_beyondEveryReesOrder`, `no_finiteReesOperator_sews_xiRightModularAffinities` | `RHTower/XiSourceModularTypeSuperselectionLaw.lean` |

## Explicit exclusions

Paper does not claim:

- RH or zero exclusion;
- every centered modular character is unitary;
- bounded Ward positivity makes off-line defect mass vanish;
- Hedenmalm dense-radical, Sonin--Calkin, or Wold--Poisson estimates follow from set-level kernel theory without their analytic hypotheses;
- the elementary kernel-pair or ring identities are standalone novelty;
- finite-Rees impossibility excludes singular graded correspondences;
- compact/local agreement controls global divisor orientation.
