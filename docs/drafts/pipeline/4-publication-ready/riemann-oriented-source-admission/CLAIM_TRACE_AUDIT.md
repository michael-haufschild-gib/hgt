# Claim trace audit

Internal verification record for `main.tex`. The manuscript does not mention the formal
certificate. This file distinguishes proved mathematical statements from explicitly open
producer obligations.

## Status vocabulary

- **PROVED**: exact declaration exists in the current corpus.
- **SYNTHESIS**: prose interpretation whose mathematical components are individually proved;
  manuscript does not assert a stronger implication.
- **OPEN, EXPLICIT**: stated only as an unproved route obligation.
- **EXCLUDED OVERCLAIM**: tempting stronger claim which the manuscript expressly denies.

## Main law and completed specialization

| Manuscript claim | Status | Exact certificate |
|---|---|---|
| All-prime Calderón–Witt oriented source has a canonical primary/secondary observer split | PROVED | `DeningerCalderonWittOrientationTransgressionCompleteness.lean`: `deningerCalderonWittGlobalOrientationConsumer_primary_add_secondary`, `deningerCalderonWittGlobalOrientationConsumer_primary_secondary_unique` |
| Secondary channel vanishes exactly for boundary-blind observers and exactly for unique factorization through Haar orientation | PROVED | Same module: `deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff`, `deningerCalderonWittGlobalOrientationConsumerSecondary_eq_zero_iff_factorization`, `deningerCalderonWittGlobalOrientationConsumer_factorization_unique_iff` |
| Relative class vanishes exactly when canonical Green primitive lies in admitted sector | PROVED | `DeningerCalderonWittRelativeBoundaryTransgression.lean`: `deningerCalderonWittGlobalRelativeBoundaryClass_eq_zero_iff`; packaged by `deningerCalderonWittGlobalOrientationTransgressionCompleteness` |
| Dense transport plus closed admission plus exact detector trace exists iff target proposition | PROVED | `RiemannDenseSourceClosedAdmissionLaw.lean`: `denseSource_closedAdmission_eq_univ`, `ClosedOrientedSourceAdmission`, `nonempty_closedOrientedSourceAdmission_iff` |
| Canonical completed incidence vector decodes to actual nonzero cross-prime witness | PROVED | `DeningerCalderonWittCompletedXiGreenIncidenceComparison.lean`: `deningerCalderonWittCrossPrimeGammaWitness_ne_zero`; `RiemannDenseSourceClosedAdmissionLaw.lean`: `deningerCanonicalCompletedIncidenceVector_sourceValue` |
| Completed-incidence admission exists iff modular displacement is zero | PROVED | `RiemannDenseSourceClosedAdmissionLaw.lean`: `exists_deningerCompletedXiClosedHodgeAdmission_iff` |
| Divisor-fibre admission iff critical-line placement; global admission iff RH | PROVED | Same module: `exists_deningerCompletedXiClosedHodgeAdmission_boundaryFracture_iff`, `xiCompletedGreenClosedHodgeLanding_iff_riemannHypothesis` |
| One conjunction contains both paper cores | PROVED | `RiemannOrientationTransgressionPaperCertificate.lean`: `riemannOrientationTransgressionPaperCore` |

## Oriented charge and source realizations

| Manuscript claim | Status | Exact certificate |
|---|---|---|
| Centered divisor charge, horizontal part, shell-tail entropy and Cayley escape rate agree | PROVED | `XiSourceBoundaryOrientationConservation.lean`: `reflectedShellTailLogRatio_eq_centeredHorizontalDisplacement`, `centeredDivisorCharge_real_eq_reflectedShellTailLogRatio`, `riemannSourceCayleyRate_eq_neg_reflectedShellTailEntropy`, `centeredDivisorCharge_real_eq_neg_half_sourceCayleyRate` |
| Cayley residue jets obey exact Poisson horizon conservation | PROVED | Same module: `riemannSourceCayleyResidueMode_horizonConservation_shellTail` |
| Two prime clocks determine full complex affine charge | PROVED | Same module: `twoPrimeSourceSpectrum_determines_xiAffineCharge` |
| Source entropy selects reflected valuation/Rees type | PROVED | Same module: `riemannSourceEntropy_selects_primeValuationReesType`, `sourceNormalRank_entropyType_productLaw` |
| Boundary neutrality is RH | PROVED | `XiSourceModularTypeSuperselectionLaw.lean`: `xiBoundaryCharacterNeutral_iff_riemannHypothesis` |
| No claim that every modular character is unitary | EXCLUDED OVERCLAIM | Manuscript asserts neutrality only for the source boundary character. `xiHurwitzOrientationEnergy_eq_zero_iff_unitaryCenteredCharacters` is used only as a typed equivalence, not universal unitarity. |

## Constructed sources

| Source statement | Status | Exact certificate |
|---|---|---|
| Mass-one complete resolution, finite-base injectivity, cofinal collapse, finite prime-normal Vandermonde blocks, and full vertical product closure | PROVED | `CompleteResolutionSourceEmbeddingReflectionLaw.lean`: `completeResolutionSourceEmbedding_injective`; `CompleteResolutionCofinalConditioningLaw.lean`: `tendsto_completeResolutionSourceVector_pointSection`, `finitePrimeNormalSpectrum_sampleMatrix_det_ne_zero`, `completeResolution_closedLinearRelation_countablePrime_affine_fullVertical`, `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod` |
| Diagonal activation disintegrates into occupancy and conditional valuation fibres; Fisher variance and Gamma coordinate identities | PROVED | `EulerActivationSquarefreeDisintegration.lean`: `diagonalActivationPositiveValuationMass_factorization`, `diagonalActivationValuationMass_total`, `diagonalActivationOccupancyFisher_eq_variance`, `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation`, `eulerActivationSquarefreeDisintegration_law` |
| Hellinger/KMS half-density and reflection finite-energy classification | PROVED | `EulerPrimitiveHellingerKMSReflectionLaw.lean`: `eulerPrimitiveBoundaryHellingerDensity_eq_KMSWightman`, `reflectionOrientationEquipartition_iff_finiteEnergy`, `gammaBoundaryGreenDescent_iff_reflectionFiniteEnergy` |
| Transverse source score is common-test invisible and canonical normalization has four-unit norm | PROVED | `EulerPrimitiveCommonTestTransverseOrientation.lean`: `eulerPrimitiveBoundaryPolarizedPairing_test_transverseScoreRaw`, `eulerPrimitiveBoundaryPolarizedPairing_transverseScoreRaw`, `eulerPrimitiveBoundaryTransverseFourUnit`, `eulerPrimitiveBoundaryPolarizedPairing_transverseFourUnit` |
| CCM crease recovers every von Mangoldt atom | PROVED | `CCMFirstClockCreaseCurrent.lean`: `ccmFirstClockArithmeticTrace_entry_recovers_vonMangoldt` |
| Theta completed-density relation exists at every divisor; Hurwitz circuit exactly on line | PROVED | `XiSourceMatroidCircuitFracture.lean`: `xiCompletedDensityReflectionRelationAt_all`, `xiHurwitzMonodromyCircuitAt_iff_re_eq_half`, `xiSourceCircuitComparisonPreserving_iff_riemannHypothesis` |
| Hypertranscendental source coherence, point-finite differential matroid, and summable orientation weights | PROVED | `HTGeometry/HypertranscendentalHochsterSourceCoherenceDuality.lean`: `hochsterSourceCoherenceExact`, `hypertranscendentalHochsterSourceCoherence_orientationProduct`; `HTGeometry/UniversalFacetSourcePhase.lean`: `UniversalFacetSource.differentialIndependent`, `UniversalFacetSource.summable_norm_orientationWeight`; `HTGeometry/UniversalFacetSourceCountablePointFiniteConstraintUniversalityLaw.lean`: `UniversalFacetSource.countablePointFiniteConstraintDifferentialMatroid` |
| Projective recurrence kernel/range/rank conservation | PROVED | `HTGeometry/UniversalProjectiveRecurrenceCapstoneLaw.lean`: `projectiveEnergyDetuning_ker_eq_relationSpace`, `projectiveEnergyDetuning_range_eq_gapSubspace`, `projectiveTemporalRank_add_relationRank`, `finiteProjectiveRecurrence_universalLaw` |

## Constructed transports and no-go boundaries

| Manuscript claim | Status | Exact certificate |
|---|---|---|
| Product topology makes retained countable prime-normal relation maximally vertical and output-free | PROVED | `CompleteResolutionCofinalConditioningLaw.lean`: `completeResolution_closedLinearRelation_countablePrime_affine_fullVertical`, `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod` |
| Reflected off-line sectors cannot be sewn by finite Rees order; exact sewing grows beyond every Rees order | PROVED | `XiSourceModularTypeSuperselectionLaw.lean`: `no_finiteReesOperator_sews_xiRightModularSectors`, `xiRightModularSewingOperatorNorm_beyondEveryReesOrder` and affinity variants |
| Canonical shifted cell carrier has actual reflection-odd Gamma coordinate and is excluded off zero displacement | PROVED | `CCMFirstClockPrimitivePromotedCellHodgeBoundaryRigidity.lean`: `reflectionOddCoefficient_eq_actualGammaHardyBoundary`, `shiftedCarrier_not_mem_actualCellGammaAdmittedHodgeSector`, `sourceNormalDepthSpreadCarrier_not_mem_actualCellGammaAdmittedHodgeSector` |
| Cofinal depth countertransport exists, lies in reflected Hodge sector, has bounded pretrace capacity and linear scalar gain | PROVED | `CCMFirstClockPrimitivePromotedCofinalDepthCountertransport.lean`: `doubledLandedDepthPairProfile_mem_reflectedDepthHodgeSector`, `reflectedHodgeCountertransportCapacity_le`, `reflectedHodgeCountertransport_readout_eq`, `scalarReadoutGain_linear_lower` |
| Completed Xi incidence comparison is coefficient-faithful, isometric, and dense | PROVED | `DeningerCalderonWittCompletedXiGreenIncidenceComparison.lean`: `deningerCalderonWittCrossPrimeXiIncidenceTestToJetHilbert_injective`, `deningerCalderonWittCrossPrimeXiIncidenceTestToJetHilbert_dense`, `norm_deningerArithmeticCompletedGreenToCrossPrimeIncidence`, `deningerArithmeticCompletedGreenToCrossPrimeIncidence_dense` |

## Route-atlas evidence and open-core discipline

The rightmost table column in the manuscript is explicitly unproved. Only the prefix and the
connector from the named open theorem to RH are mathematical claims.

| Route | Proved prefix/connector anchors | Open statement status |
|---|---|---|
| C1 singular Hedenmalm | `HedenmalmUniversalPositiveFormClassification.lean`: `universalPositiveForm_thetaNull_iff_canonicalMeasure_support_realDivisor`; `HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw.lean`: `universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw`; `HedenmalmSourceHilbertGramClosedGraphNoGo.lean`: `hilbertGram_l2PartialOperator_not_closable` | OPEN, EXPLICIT: source-selected singular boundary form |
| E critical Möbius | `MobiusBoundaryOppositeSignTransport.lean`: exact factor-replacement sign, Hall transport, proportional conductance, isolated/degree defect bounds, and window no-go declarations including `not_boundaryFactorReplacementWindowAdjacent_of_primeFactors_le_of_pow_mul_lt`, `completeBipartiteProportionalConductance_attains_signedImbalance`, `abs_truncatedMobiusLaplace_le_degreeNormalizedWindowedFactorReplacementDefect` | OPEN, EXPLICIT: strict-half all-prime seam cancellation |
| G Suzuki | `SuzukiSafeBoundaryThetaCumulantWall.lean`: exact Xi jets, safe minor/cumulant identity, positive Hankel carrier and sign chamber; finite carrier and source-category no-gos are imported by the current Route-G capstones | OPEN, EXPLICIT: pole-compatible source-selected two-angle continuation and identification |
| J Julia | `CCMFirstClockPrimitivePromotedCofinalDepthCountertransport.lean` plus the Julia capacity/no-go modules imported by it | OPEN, EXPLICIT: source-relative pretrace polarization or class-complete no-go |
| L Calderón–Witt/Hodge | Main-law and completed-incidence modules above; `RiemannGammaCoPoissonHodgeGreenDescentLaw.lean` classifies the labelled tail-energy condition | OPEN, EXPLICIT: source-derived graph-domain landing |
| N prime-normal | `HedenmalmPrimeNormalWickBoundaryEnergy.lean`: `hedenmalmPrimeNormalEnergy_eq_vertical_add_radial`, `riemannHypothesis_of_xiCZeroHedenmalmPrimeNormalSubLogSquare`; `HedenmalmPrimeNormalSubLogSquareClassification.lean`: `hedenmalmPrimeNormalSubLogSquare_iff_im_eq_zero` | OPEN, EXPLICIT: uniform source-domain sub-log-square estimate |
| O Connes/CCM | `CCMProlateRayleighGroundLock.lean`: `CCMProlateRayleighGroundData.riemannHypothesis_iff_rayleighExcess_tendsto_zero`, false-RH persistent separation; `CCMPublishedRestrictedWeilMatrix.lean` for finite matrices | OPEN, EXPLICIT: source proof of cofinal floor convergence |
| P Thorin/Markov | `PrimeArchXiCompactThorinRH.lean`: `primeArchCompactMarkovGermRepresentation_iff_riemannHypothesis`, `primeArchCompactThorinExponentRepresentation_iff_riemannHypothesis`; compact determinacy modules | OPEN, EXPLICIT: source-built positive carrier |
| Q theta–Cassini | `ThetaCuspCassiniHyperbolicSourceLaw.lean`: positive likelihood carrier; `SuzukiSafeBoundaryThetaCumulantWall.lean`: all Hankel blocks; `ThetaCuspCalibratedPowerReciprocalSecondMomentLaw.lean`: calibrated exponent/moments; `XiSquaredSeamCassiniResolventSourceLaw.lean`: `thetaCuspCassiniInwardBoundarySaturated_iff_riemannHypothesis` | OPEN, EXPLICIT: higher calibrated carrier control or saturation inequality |
| R primitive current | `EulerActivationSquarefreeDisintegration.lean`, `PrimitiveFibreModularRenormalizationLaw.lean`, `EulerPrimitiveHellingerKMSReflectionLaw.lean`, primitive-promotion and Ward boundary modules | OPEN, EXPLICIT: singular breadth/depth common-test continuation plus source Ward sign |
| Analytic–Hurwitz | `XiSourceMatroidCircuitFracture.lean` declarations listed above | OPEN, EXPLICIT: source relation comparison |
| HT/recurrence | `HypertranscendentalHochsterSourceCoherenceDuality.lean`, `DARelativeSourceConservativity.lean`, `UniversalProjectiveRecurrenceCapstoneLaw.lean` | OPEN, EXPLICIT: arithmetic reporter and source-allowed protection theorem |

## Claims deliberately not made

1. RH is not proved or assumed.
2. No global completed admission object is constructed.
3. The abstract set `K` is not credited as a producer when chosen after inspecting divisor
   displacement; `main.tex` explicitly rejects that circular use.
4. No assertion says all open routes reduce technically to Route L's incidence completion.
5. No assertion says all modular characters are unitary.
6. No retired bounded/finite submechanism is promoted to a route-wide impossibility theorem.
7. No equivalence to RH is credited as an independent source theorem.

## Verification commands

- `lake env lean GaloisForLFunctions/RHTower/RiemannDenseSourceClosedAdmissionLaw.lean`
- `lake env lean GaloisForLFunctions/RHTower/RiemannOrientationTransgressionPaperCertificate.lean`
- final audit: `lake build GaloisForLFunctions.RHTower.RiemannOrientationTransgressionPaperCertificate`
- `scripts/formal_tools.py lint`
- `tectonic --keep-intermediates main.tex`

## Final command results — 2026-08-02

- Direct elaboration of `RiemannDenseSourceClosedAdmissionLaw.lean`: passed.
- Direct elaboration of `RiemannOrientationTransgressionPaperCertificate.lean`: passed.
- Axiom audit of the observer split, completeness theorem, generic admission theorem,
  global RH specialization, and paper apex: exactly `propext`, `Classical.choice`, and
  `Quot.sound`.
- `scripts/formal_tools.py lint`: passed with no output.
- Final leaf audit
  `lake build GaloisForLFunctions.RHTower.RiemannOrientationTransgressionPaperCertificate`:
  passed, `10900/10900`; replayed style warnings occur in unrelated imported modules.
- `tectonic --keep-intermediates main.tex`: passed without TeX warnings.
- PDF: 13 A4 pages; all pages rendered to PNG and visually inspected; no clipping,
  overlap, missing glyph, or broken table continuation was found.
- Post-audit process check found no stale Lean process for either paper module or the
  axiom scratch file.
