# Claim trace for localization--recurrence rewrite

**Status:** internal truth-control document; not manuscript material

| Candidate manuscript claim | Formal declaration(s) | Status |
|---|---|---|
| l-bit temporal rank equals rational rank of nonconstant coefficients | `lbitGapSubspace_eq_coefficientSubspace`, `lbitTemporalRank_eq` | proved |
| temporal rank plus balanced relation rank equals \(2^N-1\) | `lbitTemporalRank_add_relationRank` | proved |
| noninteracting independent one-body model has \(\tau=N\) | `lbitCoefficientSubspace_eq_singletonSpan`, `lbitNoninteracting_temporalRank_eq` | proved |
| same model has exactly \(2^N-1-N\) independent projective relations | `lbitNoninteracting_relationRank_eq` | proved |
| full temporal rank has no nonzero rational projective relation | `lbitFullTemporalRank_relationRank_eq_zero`, `lbitFullTemporalRank_relationSpace_eq_bot` | proved |
| every finite-order diagonal l-bit model has a coefficient-count ceiling | `lbitTemporalRank_le_order` | proved |
| an arbitrarily close all-order diagonal model reaches \(2^N-1\) | `exists_lbitEnergy_maximal_uniformly_close`, `exists_localizedTemporalDimensionExplosion` | proved |
| every l-bit charge remains conserved and no off-diagonal configuration transport appears | `lbitChargeMatrix_commutes`, `lbitHamiltonianMatrix_offDiagonal`, clauses of `exists_localizedTemporalDimensionExplosion` | proved |
| fixed commuting range \(R\) gives \(\tau\le|\mathcal S_{n,R}|\) | `lbitTemporalRank_le_geometricSupports` | proved |
| rationally independent allowed coefficients saturate the support ceiling | `lbitTemporalRank_eq_geometricSupports_card` | proved |
| arbitrarily weak exactly range-\(R\) families saturate the allowed support ceiling | `exists_small_geometricLBit_maximalLocalRank` | proved |
| explicit fixed-range bound \(\tau\le n2^{R+1}\) | `card_lbitGeometricSupports_le_linear`, `lbitTemporalRank_le_geometric_linear` | proved |
| maximal rank is equivalent to rational independence of every nonempty-support coefficient | `lbitTemporalRank_eq_maximal_iff_linearIndependent` | proved |
| one exact coefficient collision or moved coefficient-preserving symmetry support forces strict rank loss | `lbitTemporalRank_lt_maximal_of_coefficient_collision`, `lbitTemporalRank_lt_maximal_of_permutation_symmetry_movedSupport` | proved |
| one countable coefficient field is rationally independent on every nonempty support | `quasiLocalInfiniteLBitCoefficient_linearIndependent` | proved |
| one explicit origin-dependent field obeys an exponential envelope and is absolutely summable | `abs_quasiLocalInfiniteLBitCoefficient_le_physical`, `summable_abs_quasiLocalInfiniteLBitCoefficient` | proved |
| every finite embedded restriction has rank \(2^{|I|}-1\) | `quasiLocalInfiniteLBitRestriction_fullRank` | proved |
| infinite energy series converges absolutely for every configuration | `summable_quasiLocalInfiniteLBitEnergyTerm` | proved |
| infinite energy is uniformly bounded and continuous | `abs_quasiLocalInfiniteLBitEnergy_le_mass`, `continuous_quasiLocalInfiniteLBitEnergy` | proved |
| the diameter-weighted absolute interaction mass \(\sum_S2^{\operatorname{diam}S}|J_S|\) is finite for the explicit infinite field | `summable_quasiLocalInfiniteLBitWeightedCoefficient` | proved |
| the double energy difference created by flips at \(x,y\) is bounded by \(4K2^{-|x-y|}\) | `abs_infiniteLBitEnergyDoubleFlip_le` | proved |
| the local-flip commutator obeys the volume-independent bound \(\min\{2,4K|t|2^{-|x-y|}\}\|\psi\|_\infty\) | `norm_quasiLocalInfiniteLBitFlipCommutator_le_min` | proved on continuous amplitudes with the sup norm |
| every finite environment \(F\) of a local flip has exact conditional flip-frequency rank \(2^{|F|}\) | `quasiLocalInfiniteLBitIncidentRestriction_localFlip_fullRank` | proved |
| the same infinite coefficient field simultaneously has maximal local-flip rank on every finite environment and the exponential commutator bound | `quasiLocalInfiniteLBit_fullRank_and_commutatorBound` | proved; exact l-bit model, not a microscopic random Anderson/XXZ ensemble |
| for every pair of distinct sites, an explicit positive time and normalized amplitude make the local-flip commutator attain its algebraic maximum \(2\) | `exists_quasiLocalInfiniteLBit_allPairsInfluenceSaturation` | proved; together with the universal upper bound this is exact operator-norm saturation for the current unbundled operator encoding |
| the explicit all-pairs saturation witness must pay the distance-dependent delay \(2\le 4Kt_{xy}2^{-\operatorname{dist}(x,y)}\) | `two_le_pairSaturationTime_mul_weightedInfluenceRate` | proved; division-free consequence of exact saturation and the same-field fixed-time locality bound |
| adding the next boundary site to an \(r\)-site environment doubles local-flip temporal rank from \(2^r\) to \(2^{r+1}\), and the new half is exactly the coefficient packet crossing that boundary | `quasiLocalInfiniteLBitIncidentRestriction_newEnvironmentSubset_eq_boundary`, `lbitBoundary_localFlipTemporalRank_doubles` | proved |
| the boundary-born packet obeys \(2^{r+1}\sum_S|b_{r,S}|\le K\) | `two_pow_mul_lbitBoundaryPacketAbsMass_le_weightedMass` | proved |
| at coefficient threshold \(\delta>0\), the boundary count obeys \(2^{r+1}\delta N_{r,\delta}\le K\); resolving all \(2^r\) new directions forces \(2\delta(2^r)^2\le K\) | `two_pow_mul_thresholdCount_le_weightedMass`, `two_mul_threshold_mul_sq_two_pow_le_weightedMass` | proved; coefficient-resolution law, not yet a device-noise or general finite-time spectral-capacity theorem |
| nested first-\(n\)-site energies converge uniformly to infinite energy | `tendstoUniformly_quasiLocalInfiniteLBitWindowEnergy`, `exists_quasiLocalInfiniteLBitWindow_uniformError` | proved |
| finite-window error is bounded by omitted absolute interaction mass | `abs_quasiLocalInfiniteLBitEnergy_sub_window_le_tail`, `tendsto_quasiLocalInfiniteLBitWindowTail_zero` | proved |
| full-cube character isolates the top interaction as \(2^N J_I\) | `lbitFullCubeCharacter_detuning` | proved |
| top interaction survives as a recurrence relation iff absent | `lbitTopInteraction_relation_iff`, `lbitTopInteraction_fracture_iff` | proved |
| minimum replica height is \(2^{N-1}\) | `lbitFullCubeCharacter_minimumReplica` | proved |
| finite symmetric response is \(\operatorname{sinc}(A2^N J_I)\) | `lbitFullCube_finitePhaseResponse` | proved |
| calibrated horizon gives exact zero, bounded by \(\pi/\delta\) under a certified detuning floor | `lbitFullCube_calibratedPhaseResponse`, `lbitFullCube_calibratedHorizon_le` | proved |
| in the calibrated ideal response model, additive complex errors below \(1/2\) keep present/absent outcomes algebraically disjoint | `lbitFullCube_measurementsSeparated` | proved; not device-noise robustness |
| every support \(S\) has a balanced integer full-configuration Walsh character extracting exactly \(2^N J_S\) | `lbitSupportIntegerCharacter_balanced`, `lbitSupportIntegerCharacter_detuning` | proved |
| for scaled coefficient \(g^{w(S)}J_S\), the support response at elapsed horizon \(T=\tau g^{-w(S)}\) is exactly independent of \(g\) | `lbitSupport_scaled_finitePhaseResponse_birth_exact` | proved in ideal scaled diagonal family |
| the actual support Fourier response converges to \(1\), its sinc crossover, or \(0\) below, at, or above its inverse-power birth horizon | `lbitSupport_scaled_finitePhaseResponse_wallCrossing` | proved |
| the uniform \(\lvert+\rangle^{\otimes N}\) l-bit product state sees the complete Hamiltonian gap space and temporal rank | `lbitUniformStateVisibleGapSubspace_eq`, `lbitUniformStateVisibleTemporalRank_eq` | proved |
| maximal rank is equivalent to every survival-fidelity moment of that state reaching its permutation floor | `lbitUniformState_all_survivalFidelityMoments_extremal_iff` | proved |
| maximal rank is generic in the complete finite tensor-local onsite-plus-edge extension slice once a connected transition witness exists | `hermitianLocalExtensionSliceMaximalSet_dense_residual_fullMeasure_of_family` | proved |
| a finite local survival packet with exponential spectral-weight decay and geometric shell growth has a positive return with quadratic error \(4\beta_R+2(2\pi/(Q+1))^2\) and deadline exponent equal to localization-ball cardinality minus one; the same budget has a never-exits/post-exit-return alternative | `exists_finiteAndersonLocalizedSurvival_quadratic_recurrence`, `finiteAndersonLocalizedSurvival_quadratic_neverExits_or_postExit_return`, `exists_finiteAndersonLocalizedSurvival_quadratic_volume_recurrence` | proved; deterministic localization-certificate interface, not a proof that every Anderson ensemble supplies the certificate |
| for a normalized countably infinite nonnegative pure-point packet, a finite visible head and certified tail bound give recurrence and escape--return deadlines depending on visible-head volume rather than countable ambient support | `exists_summableLocalizedSurvival_recurrence`, `exists_summableLocalizedSurvival_volume_recurrence`, `summableLocalizedSurvival_neverExits_or_postExit_return` | proved; pure-point summability boundary, no continuous-spectrum claim |
| for every finite Hermitian hopping matrix and prescribed finite horizon, one onsite-plus-hopping Hamiltonian has maximal projective rank while every site-survival loss stays below any prescribed positive tolerance | `exists_finiteAnderson_maximalProjective_finiteHorizon_survivalTarget` | proved |
| for every finite Hermitian hopping matrix and every prescribed positive off-diagonal envelope, one onsite potential at fixed hopping strength gives maximal projective rank while every transition amplitude stays below its assigned envelope for every real time; in particular this holds for every positive exponential envelope over any finite site metric, and the same Hamiltonian's completed relative phases are Haar on the full projective torus | `exists_finiteAnderson_fixedHopping_maximalProjective_allTimeBelow_any`, `exists_finiteAnderson_fixedHopping_maximalProjective_exponentialLocality_any`, `exists_finiteAnderson_fixedHopping_exponentialLocality_fullHaar` | proved; required onsite scale and decay constants need not be volume-uniform; external priority audit classifies this as a bridge, not a Nature-level standalone result |
| generic nearest-neighbour random-field XXZ/Anderson--Hubbard Hamiltonians have maximal rank in their localized regime | none | forbidden |
| infinite energy generates reversible strongly continuous norm-preserving evolution on continuous amplitudes | `quasiLocalInfiniteLBitEvolutionLinearIsometryEquiv`, `continuous_quasiLocalInfiniteLBitEvolution_time` | proved |
| spectral-jet resolution \(r\) has temporal dimension equal to the sum of rational ranks of coefficient birth layers below \(r\) | `temporalDimension_scaledLBitSpectralJet_eq_sum_layerRank` | proved |
| under layerwise independence, resolved dimension equals the number of supports born below \(r\), without cross-layer independence | `temporalDimension_scaledLBitSpectralJet_eq_card_bornBefore` | proved |
| every coefficient family at diameter birth resolution has explicit ceiling \(n2^{r+1}\) | `temporalDimension_diameterScaledLBitSpectralJet_le_linear_unconditional` | proved |
| spectral-jet resolution is physical elapsed time | none | forbidden |
| the full-configuration support character is a scalable support-local protocol | none | forbidden; current replica height remains exponential in ambient system size |
| a uniform bounded-height noisy classifier reconstructs the layer filtration at finite \(g,T\) | none | open |
| the exact layer-rank law is externally novel and experimentally distinct from known MBL dephasing | external priority audit | candidate novelty only; not established |

## Nonmathematical claim boundary

Formal proof establishes truth only. It does not establish novelty,
significance, experimental feasibility, microscopic MBL applicability or
Nature suitability. Those are separate literature and hostile-review gates.
