# Claim trace audit

Internal verification record for `main.tex`. Not part of manuscript. Formal verification is a
truth-control tool only and contributes nothing to novelty or significance.

Audit date: 2026-07-30.

## Policy

- Every mathematical claim in manuscript must be an unconditional consequence of declarations
  below.
- Main paper contains no mention of Lean, formalization, proof assistants, or machine checking.
- Literature priority is handled separately in `LITERATURE_AUDIT.md`.
- RH, zero exclusion, a source-derived defect bound, and existence of a global completely
  positive Rees correspondence are not claimed.

## Universal reflected critical-window law

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Exact squared Hellinger factor between reflected geometric valuation laws | `reflectedPrimeValuationSquaredHellingerFactor_eq_one_sub_defect` | `formal/GaloisForLFunctions/RHTower/PrimeValuationReflectedHellingerCriticalProfile.lean` |
| Exact local defect \(4p^{-1}\sinh^2(c\log p/\log N)/(1-p^{-1})^2\) | same theorem; `reflectedPrimeValuationHellingerDefect` | same |
| Vacuum-renormalized defect sum differs from prime-clock energy by \(o(1)\) | `reflectedPrimeValuationHellingerDefectSum_sub_energy_bound`; `tendsto_reflectedPrimeValuationHellingerDefectSum_sub_energy_zero` | same |
| Defect sum tends to \(\Phi(c)=4\int_0^1\sinh^2(cu)/u\,du\) | `tendsto_reflectedPrimeValuationHellingerDefectSum_critical_profile` | same |
| Every local defect vanishes uniformly in critical window | `reflectedPrimeValuationHellingerDefect_nonneg_le`; `tendsto_reflectedPrimeValuationHellingerUniformBound_zero` | same |
| Logarithmic product remainder tends to zero | `tendsto_reflectedPrimeValuationHellingerLogRemainderSum_zero` | same |
| Squared reflected affinity tends to \(e^{-\Phi(c)}\) | `tendsto_reflectedPrimeValuationSquaredHellingerLE_critical_profile` | same |
| Prime-clock energy tends to \(\Phi(c)\) | `tendsto_primeClockCutoffEnergy_critical_profile` | `formal/GaloisForLFunctions/RHTower/PrimeClockCriticalProfile.lean` |
| Symmetric prime-log Wick cumulant at \(2c/\log N\) tends to \(\Phi(c)\) | `tendsto_primeBoundaryWickCumulant_critical_profile`; exact real-axis identity `primeBoundaryWickCumulant_ofReal` | `formal/GaloisForLFunctions/RHTower/PrimeBoundaryWickCriticalProfileUniversalityLaw.lean`; `PrimeBoundaryDickmanWick.lean` |
| Hellinger partition times exponentiated prime-clock energy tends to one | `tendsto_reflectedHellinger_mul_exp_primeClockEnergy_one` | `PrimeValuationReflectedHellingerCriticalProfile.lean` |
| \(\Phi\) is even, positive off zero, analytic, and has expansion \(2c^2+c^4/3+O(c^6)\) | direct consequences of `primeClockUniversalProfile` and the entire power series of \(\sinh\); manuscript gives proof | `PrimeClockCriticalProfile.lean` |

## Hellinger–Rees phase law

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Exact local geometric Hellinger formula | `squaredHellingerAffinity`; `primeValuationSquaredHellingerFactor`; `primeRadialCrossMass_sq` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| Local affinity lies in \([0,1]\) | `squaredHellingerAffinity_nonneg`; `squaredHellingerAffinity_le_one` | same |
| Every finite-prime squared Hellinger sector is strictly positive in the open strip | `primeValuationSquaredHellingerBelow_pos` | same |
| Negative-face local lower bound \(1-p^{-1}\) | `one_sub_primeMass_le_squaredHellingerFactor_of_nonpos` | same |
| Negative-face explicit exponential correction bound | `inv_one_sub_sq_le_exp_six_mul`; `primeSquaredHellingerFactor_le_wold_mul_exp_of_nonpos`; `primeValuationSquaredHellingerBelow_le_wold_mul_correction_of_neg` | same |
| Real finite Euler partition tends to zeta for exponent \(>1\) | `realPrimeEulerPartitionBelow_tendsto` | same |
| Exact squared-affinity factorization into Wold volume and Euler correction | `primeValuationSquaredHellingerBelow_eq_wold_mul_eulerCorrection` | same |
| Euler correction is the exact finite partition midpoint ratio | `primeValuationHellingerEulerCorrectionBelow_eq_partitionRatio` | same |
| Exact negative-face limit \(H_N(c)/a_N\to\zeta(1-c)^2/\zeta(1-2c)\) | `tendsto_primeValuationSquaredHellinger_div_wold_of_neg` | same |
| Squared affinity is \(\Theta(a_N)\) for \(c<0\) | `primeValuationSquaredHellingerBelow_isTheta_wold_of_neg` | same |
| Affinity is exactly half-normal, \(\Theta(\sqrt{a_N})\), for \(c<0\) | `primeValuationHellingerBelow_isTheta_halfNormal_of_neg` | same |
| Critical local and global affinities equal one | `squaredHellingerAffinity_self`; `primeValuationSquaredHellingerFactor_zero`; `primeValuationSquaredHellingerBelow_zero`; `primeValuationHellingerBelow_zero` | same |
| Every positive twist is eventually below every prescribed local Wold power | `eventually_primeSquaredHellingerFactor_le_woldPower` | same |
| Positive squared affinity is \(O(a_N^L)\) for all \(L\) | `primeValuationSquaredHellingerBelow_isBigO_woldPower` | same |
| Positive squared and unsquared affinities are all-orders flat | `primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos`; `primeValuationHellingerBelow_reesAllOrdersFlat_of_pos` | same |
| Exact three-phase trichotomy | `primeValuationHellinger_reesType_trichotomy` | same |
| Flat iff \(c>0\) in strip | `primeValuationSquaredHellingerBelow_reesAllOrdersFlat_iff` | same |
| Reflection swaps flat/nonflat type for every \(c\ne0\) | `reflected_primeValuationSquaredHellinger_type_fracture` | same |
| Wold volume is positive and tends to zero | `primeWoldBoundaryVolumeBelow_pos`; `tendsto_primeWoldBoundaryVolumeBelow_zero` | `formal/GaloisForLFunctions/RHTower/PrimeWoldGammaGlobalBoundaryVolume.lean` |

## Universal transport claims

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Definition of all-orders-flat radical and finite Rees grade | `ReesAllOrdersFlat`; `ReesGradeAtMost` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesJetStability.lean` |
| Finite packet flat iff coordinatewise flat | `reesAllOrdersFlat_pi_iff` | same |
| Constant finite coordinate maps preserve flat radical | `reesAllOrdersFlat_finiteJetTransform` | same |
| Finite matrices with uniform finite Rees bound preserve flat radical | `reesAllOrdersFlat_finiteReesJetTransform` | same |
| Bi-moderate invertible finite changes of frame preserve and reflect flat radical | `reesAllOrdersFlat_finiteReesJetTransform_iff_of_inverse` | same |
| Arbitrary-dimensional bounded operators of fixed finite Rees order preserve flat radical | `reesAllOrdersFlat_apply_reesOperatorGradeAtMost` | same |
| For arbitrary asymptotic germs, scalar sewing from all-orders-flat source to finite grade \(d\) dominates every inverse scale power | `reesEssentialSewingCost_beyondEveryFiniteOrder` | `formal/GaloisForLFunctions/RHTower/AsymptoticTypeSuperselection.lean` |
| In arbitrary real normed source and target spaces, every exact bounded linear sewing from all-orders-flat source to finite grade has operator norm beyond every inverse scale power | `reesExactSewingOperatorNorm_beyondEveryFiniteOrder` | same |
| Universal flat-to-nonflat no-sewing | `no_finiteReesOperator_sews_flat_to_nonflat` | `formal/GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean` |
| Actual reflected Hellinger sectors cannot be sewn by a finite-Rees operator | `no_finiteReesOperator_sews_reflected_Hellinger_sectors` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| Prime-reflection scalar sewing multiplier dominates every inverse Wold Rees power | `reflectedHellingerSewingCost_beyondEveryReesOrder` | same |
| Every exact scalar prime-reflection sewing family has operator norm beyond every inverse Wold Rees power | `reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder` | same |
| Actual Wold irregular gauge is all-orders flat and half-normal sector is not | `norm_primeWoldReflectedIrregularGauge_reesAllOrdersFlat`; `primeWoldHalfNormalSector_not_reesAllOrdersFlat` | `formal/GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean` |

## Signed Fisher–Ward orientation carrier

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Pointed Fisher connection is rank at most two and every bounded sandwich has summable trace diagonal | `pointedFisherConnection`; `mul_pointedFisherConnection_mul`; `summable_inner_diag_mul_pointedFisherConnection_mul` | `formal/GaloisForLFunctions/HTGeometry/PointedFisherCutoffWardTrace.lean` |
| Bounded factors need not be Hilbert–Schmidt for trace evaluation | `opTrace_mul_pointedFisherConnection_mul` | same |
| Tangent reversal negates pointed Fisher connection | `pointedFisherConnection_neg_tangent` | same |
| Signed cutoff Ward trace is odd in source tangent | `pointedCutoffWardTrace_neg_tangent` | same |
| Signed trace equals pointed Fisher pairing with adjoint double-cutoff curvature | `pointedCutoffWardTrace_eq_opTrace_adjointCurvature` | same |
| Exact two-matrix-element value formula | `pointedCutoffWardTrace_eq_adjointCurvature_values` | same |
| Self-adjoint cutoff reduces adjoint curvature to ordinary double commutator | `pointedCutoffWardTrace_eq_opTrace_curvature`; `pointedCutoffWardTrace_eq_values` | same |

## Modular-retuning escape

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Rank-one complementary rational Weyl eigenvalue | `normalizedRankOneWeylComplementaryEigenvalue` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| Exact numerator/denominator norm-square defect \((p^2-1)(|z|^4-1)\) | `normalizedRankOneWeyl_normSq_numerator_sub_denominator` | same |
| Weyl complementary channel has norm one iff \(|z|=1\) | `norm_normalizedRankOneWeylComplementaryEigenvalue_eq_one_iff` | same |
| Outward face is strictly expansive | `norm_normalizedRankOneWeylComplementaryEigenvalue_gt_one` | same |
| Real radial Weyl cost is strictly larger than \(p^{2c}\) for \(0<c<1/2\) | `radialRankOneWeylModularCost_gt_rpow` | same |
| Scalar gauge cannot alter complementary/spherical ratio | `normalizedRankOneWeyl_scalarGauge_ratio` | same |

The parent scattering interpretation is cited, not claimed as new: Calegari–Venkatesh,
Theorem 6.6.1, give the two-channel block \(N(z,s)\) induced by the standard intertwiner. At
\(s=0\), direct characteristic-polynomial algebra gives eigenvalues \(1\) and the rational
function above. All new mathematical uses of that function are the checked algebraic
declarations listed here.

## Activation source

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Diagonal activation equals \(\zeta(s)/\zeta(2s)\) | `woldActivationHolonomy_diagonal_eq_squarefreePartition`; `squarefreePartition` | `formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeDisintegration.lean`; `SquarefreeFixedCurrentLocalization.lean` |
| Positive valuation atom factors as occupancy times conditional geometric mass | `diagonalActivationPositiveValuationMass_factorization` | `EulerActivationSquarefreeDisintegration.lean` |
| Positive atoms sum to occupancy; zero plus positive atoms total one | `tsum_diagonalActivationPositiveValuationMass`; `diagonalActivationValuationMass_total` | same |
| Occupancy Fisher coordinate is Bernoulli variance | `diagonalActivationOccupancyFisher_eq_variance` | same |
| Positive valuation atoms are Möbius Schur differences | `diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference` | same |
| Möbius atoms are Fisher-damped Gamma valuation coordinates | `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation`; `xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher` | same |
| Critical occupancy mass is \(1/(p+1)\) and nonsummable | `criticalActivationOccupancyMass_eq`; `not_summable_criticalActivationOccupancyMass` | `CriticalActivationReesSourceLaw.lean` |
| Critical depth-\(m\) tail formula and summability for \(m\ge2\) | `criticalActivationValuationTailMass_eq`; `summable_criticalActivationValuationTailMass` | same |
| Critical Gamma fibre is \((p-1)/(p(p+1))\) and nonsummable | `criticalActivationGammaFibreMass_eq`; `not_summable_criticalActivationGammaFibreMass` | same |
| No nonzero polynomial recurrence on infinitely many reciprocal-prime nodes | `polynomial_eq_zero_of_vanishes_on_infinite_prime_nodes` | same |

## Hypertranscendental depth–support grid

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Every finite depth × state rectangle is differentially independent | `cofiniteTailDenseOn_primeResidueValuationInteractionGrid_differentialIndependent` | `formal/GaloisForLFunctions/HTGeometry/PrimeResidueValuationInteractionSuperselection.lean` |
| Exact support sector is relatively HT over complete complement | `cofiniteTailDenseOn_primeResidueValuationSupportSector_relativeHT` | same |
| Exact support rank \(d\prod_{i\in S}(|A_i|-1)\) | `primeResidueValuationSupportCellIndex_card` and preceding theorem | same |
| Complete next layer relatively HT over complete finite prefix | `cofiniteTailDenseOn_primeResidueValuationNextLayer_relativeHT_over_completePrefix` | same |
| Polynomial degree cannot enlarge coordinate support | `polynomialObservable_mem_coordinateInvariant` | same |
| Fusion adds depth and unions source support | `primeResidueValuationObservableColumn_fusion`; `pointedSupport_pointedUnion` | same |
| Disjoint anchored supports fuse exactly to union sector | `primeResidueValuationAnchoredBasisColumn_fusion_of_disjoint` | same |
| Overlap strictly drops principal interaction degree | `coordinateInvariant_mul_interactionDegree_drop_of_overlap` | same |
| Fusion of prefix carriers escapes complete finite prefix | `cofiniteTailDenseOn_primeResidueValuationFusion_escapes_completePrefix` | same |

## Divisor grade and singular graph

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| PSD \(2\times2\) Gram cross bound | `divisorReesGram_posSemidef_crossBound` | `CriticalActivationReesSourceLaw.lean` |
| Differentiation drops one divisor grade and ratio is \(d^2/t^2\) | `monomialDivisorFisher_ratio` | same |
| Ratio is unbounded near divisor | `monomialDivisorFisher_ratio_unbounded` | same |
| No uniformly bounded positive Gram completion | `no_bounded_positive_divisorReesGram` | same |
| Squarefree moving overlap and Fisher numerator definitions | `squarefreeBoundaryOverlap`; `squarefreeFisherScore` | `formal/GaloisForLFunctions/RHTower/SquarefreeFixedCurrentLocalization.lean` |
| Exact division-free score identity | `squarefreeFisherScore_eq_fixedCurrent_difference` | same |
| Singular graph division reconstructs completed squarefree current | `squarefreeMobiusGammaCurrentTransportV_eq_completedCurrent` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardJuliaTransport.lean` |
| Strict-right correction gives continued Xi source current | `squarefreeMobiusGammaXiWardTransportV_eq_continuedSource`; `continuedPrimeArchSourceRelativeTrace_eq_completedSquarefree_add_correction` | same |
| Actual Hilbert Möbius tangent coefficient is Fisher numerator | `inner_fisherTangent_damped_eq_squarefreeFisherScore` | same |
| Actual four-unit tangent passes through singular graph to continued Xi trace column | `mobiusGammaFourUnitTangent_to_continuedXiTraceColumn` | same |

## Four-unit Ward boundary consumer

| Manuscript claim | Checked declaration(s) | Source |
|---|---|---|
| Canonical strict-right phase is the convergent Schwarz-paired Cayley product | `xiRightWardBoundarySourcePhaseCrossRatio_hasProd_cayley` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardHardyContraction.lean` |
| Phase norm is at most one; actual transport \(V=1-\Phi\) has norm at most two | `norm_xiRightWardBoundarySourcePhaseCrossRatio_le_one`; `mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase`; `norm_mobiusGammaXiAntiCausalWardTransportV_le_two` | same |
| \(V/2\) is a contractive Hardy multiplier on every finite packet | `xiWardNormalizedTransport_nonexpansive`; `xiWardTransport_fourUnit_nonexpansive` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardHardyNonexpansive.lean` |
| Boundary derivative of \(V\) is the continued anti-causal Ward response | `hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero`; packet form `hasDerivAt_mobiusGammaXiAntiCausalWardPacketTransportV_zero` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardHardyTransport.lean` |
| One strict-right pair contributes real part \(>2\) at its Euler-edge adapted node | `re_selected_xiAntiCausalWardSchwarzPairResponse_at_eulerEdge_gt_two`; `re_xiAntiCausalWardSchwarzPairResponse_le_continued` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardEulerEdgeCompleteness.lean` |
| One strict-right pair forces response norm square \(>4\) | `normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four` | same |
| Euler-edge scalar four-unit law is equivalent to RH | `riemannHypothesis_iff_continuedXiWardEulerEdgeScalarLaw` | same |
| Finite-aperture contraction saturates iff RH; strict contraction detects false RH | `xiWardHardyUnitarySaturationTrichotomy` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardHardySaturation.lean` |

## Scope controls

Claims deliberately excluded:

- RH proof or disproof.
- Any unconditional conclusion excluding a \(\Xi\)-zero; the exact four-unit Ward consumer is
  stated only as an equivalence and adapted-node violation theorem.
- A bound forcing an off-line defect index to vanish.
- A no-go for every Hilbert–Pólya, Connes–Consani, trace-formula, or co-Poisson construction.
- Existence of a global completely positive Rees reflection or a Pick contraction at the divisor.
- Any claim that Gamma completion alone sews the reflected valuation products.
- Priority based on formalization.

## Manuscript language audit

- No occurrence of “Lean,” “formalization,” “machine checked,” “proof assistant,” or equivalent.
- “New” is restricted to the conjunction isolated in `LITERATURE_AUDIT.md`.
- No open-problems or future-work section.
- Scope section distinguishes unconditional source/transport theorems from the explicitly
  labelled RH-complete Ward consumer.
