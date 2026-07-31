# Internal claim trace audit

This file is not part of manuscript. Formal verification is used only as truth
control. It contributes nothing to novelty or significance.

Audit date: 2026-07-31.

## Scope policy

- Every mathematical assertion in `main.tex` must be an unconditional
  consequence of declarations below.
- Manuscript contains no mention of formalization, proof software, or machine
  checking.
- RH is not assumed and not claimed.
- The paper does not claim zero exclusion, a defect-vanishing theorem, or a
  bounded positive reflection sewing.

## Universal normal-cone law

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Functional-equation endpoint charts glue | `endpointNormalChart_eq_reflected` | `formal/GaloisForLFunctions/RHTower/XiSourceNormalConeDivisorConservation.lean` |
| Endpoint chart tends to reciprocal exceptional section | `tendsto_endpointNormalChart_zero` | same |
| Depth successor differentiates to \(-u f'(u)/f(u)\) | `hasDerivAt_depthSuccessorTransport_zero` | same |
| Exceptional section reverses logarithmic connection | `logDeriv_exceptionalBoundarySection` | same |
| Exceptional section reverses meromorphic order | `meromorphicOrderAt_exceptionalBoundarySection` | same |
| Centered affine current is reflection invariant | `exceptionalAffineDivisorCurrent_reflection` | same |
| Its residue is \(-n(\rho-\tfrac12)\) | `exceptionalAffineDivisorCurrent_residue` | same |
| Reflection-odd affine weight is uniquely centered | `affineWeight_reflectionOdd_iff`; `affineWeight_eq_centered_of_reflectionOdd` | same |
| Completed Xi endpoint charts glue and tend to \(1/(2\xi)\) | `xiEndpointNormalChart_eq_reflected`; `tendsto_xiEndpointNormalChart_zero` | same |
| Xi exceptional section reverses divisor order | `meromorphicOrderAt_xiExceptionalBoundarySection` | same |
| Xi current residue law | `xiExceptionalAffineDivisorCurrent_residue` | same |

## Positive exponent-depth source

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Bounded-exponent source equals the \(m\)-free L-series | `boundedExponentEulerSource_eq_LSeries` | `XiSourceNormalConeDivisorConservation.lean` |
| Euler quotient \(\zeta(s)/\zeta((M+1)s)\) | definition `boundedExponentEulerSource`; `boundedExponentEulerSource_normal_coordinate` | same |
| Fixed-scale convergence to zeta | `tendsto_boundedExponentEulerSource_fixedScale` | same |
| Inverse-depth convergence to \(-1/(2\zeta(u))\) | `tendsto_boundedExponentEulerSource_normalScale` | same |
| Microscopic convergence to one | `tendsto_boundedExponentEulerSource_microscopicScale` | same |
| Bundled three-scale law | `zetaSourceScaleTransition_law` | same |
| Positive shell resolution and bulk-boundary duality | `positiveHTBulkBoundaryDuality_law` | same |
| Positive source is positive on its defining half-plane | `boundedExponentEulerSource_pos_of_one_lt` | same |

## Positive shell and relative hypertranscendence

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Shell is \(0/1\)-valued and exact largest-exponent support | `shellIndicator_eq_zero_or_one`; `shellIndicator_eq_one_iff` | `formal/GaloisForLFunctions/RHTower/HighExponentShellZeroFree.lean` |
| Distinct shells have disjoint supports | `shellIndicator_eq_zero_of_ne` | same |
| Shell factorization \(S_m=\zeta H_m\) | `LSeries_shellIndicator` | same |
| Prime-two head and tail bounds | `le_norm_shellHead`; `norm_riemannZeta_diff_sub_shellHead_le` | same |
| \(H_m\) holomorphic and zero-free on \(\Re s>1/2\), \(m\ge12\) | `shellMultiplier_ne_zero`; `analyticAt_shellMultiplier` | same |
| Lowest shell \(\Omega\)-grade and pure-prime equality case | `shellIndicator_cardFactors_lower`; `shellIndicator_eq_prime_pow_of_cardFactors_eq` | `formal/GaloisForLFunctions/RHTower/HighExponentShellHypertranscendence.lean` |
| Selected-prime derivative leading layer | `primeDeriv_rotatedShellJet_eq_zero_of_cardFactors_lt`; `primeDeriv_rotatedShellJet_eq_pointMass_of_cardFactors_eq` | same |
| Tail-immune determinant coefficient | `arithmeticFunction_det_apply_eq_of_cardFactors_lowerLayer_fintype` | same |
| Universal \(\Omega\)-leading finite-jet independence | `omegaLeadingJets_algebraicIndependent` | same |
| Joint zeta-plus-shell differential independence over \(\mathbb C(s)\) | `zetaPositiveShellUpperEnd_differentialIndependent` | same |
| Relative shell multiplier family independent over the full zeta differential field | `relativeShellMultiplierUpperEndCarrier_differentialIndependent_two` | same |

## Least-atom character and two-prime tomography

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Quantitative prime-two extraction | `norm_two_cpow_mul_riemannZeta_sub_one_sub_one_le` | `formal/GaloisForLFunctions/RHTower/HighExponentShellLeastAtomAsymptotic.lean` |
| \(2^{ns}H_n(s)\to1-2^{-s}\) | `tendsto_two_cpow_nat_mul_shellMultiplier` | same |
| Adjacent shell ratio tends to \(2^{-s}\) | `tendsto_shellAdjacentTransfer` | same |
| Normalized ratio tends to \(2^{1/2-s}\) | `tendsto_normalizedShellAdjacentTransfer` | same |
| Character modulus and entropy formula | `norm_shellTransferCharacter`; `log_norm_shellTransferCharacter` | same |
| Critical-line iff unit modulus | `norm_shellTransferCharacter_eq_one_iff` | same |
| Prime-three residual and normalized ratio | `tendsto_three_cpow_nat_mul_shellSecondAtomResidual`; `tendsto_normalizedShellSecondAtomAdjacentTransfer` | `formal/GaloisForLFunctions/RHTower/HighExponentShellPrimeSpectrum.lean` |
| Two-prime character spectrum is injective | `twoPrimeShellTransferSpectrum_injective` | same |
| Shell entropy equals \(1/2-\Re s\) | `shellTransferEntropy_eq` | `formal/GaloisForLFunctions/RHTower/XiHypertranscendentalModularResidueTransgression.lean` |
| Xi affine residue equals shell entropy times multiplicity | `re_centeredXiAffineResidue_eq_shellTransferEntropy`; `tendsto_re_xiExceptionalAffineDivisorCurrent_eq_transferEntropy` | same |
| Base-independent prime-two/prime-three charge | `xiModularCharge_prime_two_eq_prime_three` | same |

## BV prime windows and Hurwitz character

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Compact BV window and Mellin transform | `CompactBVPrimeWindow`; `mellinTransform` | `formal/GaloisForLFunctions/RHTower/BVPrimeWindowQuadrature.lean` |
| Moving-prime and prime-polar coefficients | `weightedPrimeWindow`; `polarCoefficient` | `BVPrimeWindowDirichlet.lean`; `BVPrimeWindowContinuation.lean` |
| Prime-polar L-series convergence and canonical continuation | `polarCoefficient_LSeriesSummable`; `LSeries_polarCoefficient_eq_continuedSource`; `meromorphicOn_continuedSource_rightHalf` | `BVPrimeWindowContinuation.lean` |
| Actual Laurent residue \(2m_\rho I_W(\rho+\tfrac12)\) | `tendsto_continuedSource_residue_of_zeta_zero` | `BVPrimeWindowDivisorTomography.lean` |
| Noncensoring gives a simple pole | `meromorphicOrderAt_continuedSource_eq_neg_one_of_mellin_ne_zero` | same |
| Forward/inverse Mellin characters | `mellinTransform_argumentDilation`; `mellinTransform_argumentExpansion` | `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDilationOrientation.lean` |
| Forward/inverse residue characters | `continuedSourceResidueValue_argumentDilation`; `continuedSourceResidueValue_argumentExpansion` | same |
| Weighted and polar coefficients obey square-index decimation | `weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul`; `polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul` | same |
| Residue norm ratio recovers horizontal displacement | `xiBVResiduePhaseCoordinate_eq_sourceModularCharge` | `formal/GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean` |
| Complex modular character is additive | `centeredComplexModularCharacter_add` | `formal/GaloisForLFunctions/RHTower/RiemannComplexModularCharacterLaw.lean` |
| Real ray equals Mellin character | `centeredComplexModularCharacter_real_cpow` | same |
| Imaginary period equals negative Hurwitz monodromy | `centeredComplexModularCharacter_hurwitzPeriod` | same |
| Principal phase is alias-free in open critical strip | `centeredComplexModularCharacter_principalPhase` | same |

## Valuation Hellinger-Rees fracture

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Diagonal activation is the squarefree partition \(\zeta(s)/\zeta(2s)\) | `woldActivationHolonomy_diagonal_eq_squarefreePartition` | `formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeDisintegration.lean` |
| Positive valuation mass factors into occupancy and conditional geometric depth | `diagonalActivationPositiveValuationMass_factorization` | same |
| Positive atoms sum to occupancy and total local mass is one | `tsum_diagonalActivationPositiveValuationMass`; `diagonalActivationValuationMass_total` | same |
| Occupancy Fisher coordinate is Bernoulli variance | `diagonalActivationOccupancyFisher_eq_variance` | same |
| Positive prime atoms are Möbius Schur differences | `diagonalActivationPositiveValuationMass_prime_eq_mobiusDifference` | same |
| Positive prime atoms are Fisher-damped Gamma valuation coordinates | `diagonalActivationPrimeMass_eq_fisherDampedGammaValuation` | same |
| Squared damping is exactly occupancy Fisher variance | `xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher` | same |

## Fisher–Gamma infinite Rees resolution

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Fisher-whitened Gamma fibre has exact mass \((p-1)/(p(p+1))\) | `criticalActivationGammaFibreMass_eq` | `formal/GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean` |
| Gamma-fibre mass is nonsummable over the primes | `not_summable_criticalActivationGammaFibreMass` | same |
| Gamma-sewn multiplier has the exact fourth-power law | `gammaSewnMobiusValuationContractionMultiplier_pow_four` | `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusValuationContraction.lean` |
| On positive aperture the multiplier lies strictly between \(1/2\) and \(1\) | `one_half_lt_gammaSewnMobiusValuationContractionMultiplier`; `gammaSewnMobiusValuationContractionMultiplier_lt_one` | same |
| Gamma sewing preserves summability of every nonnegative prime energy in both directions | `summable_gammaSewnMobiusMultiplier_sq_mul_iff` | same |
| Iterated valuation differences have exact geometric form | `gammaSewnMobiusContinuousApertureDepthDifference_eq_geometric` | same |
| Every normalized depth difference converges to its prime-log Rees symbol | `tendsto_gammaSewnMobiusContinuousApertureDepthDifference_div_pow` | same |
| First \(N\) symbols on \(N\) distinct primes form a weighted Vandermonde matrix of nonzero determinant | `gammaSewnMobiusReesPrincipalSymbolMatrix_factorization`; `gammaSewnMobiusReesPrincipalSymbolMatrix_det_ne_zero` | same |
| Bundled activation–Gamma–Rees resolution law | `gammaSewnActivationReesResolution_law` | `formal/GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean` |
| Exact geometric squared Hellinger formula | `squaredHellingerAffinity`; `primeRadialCrossMass_sq`; definition `primeValuationSquaredHellingerFactor` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesReflectionFracture.lean` |
| Negative face is \(\Theta(a_N)\) after squaring | `primeValuationSquaredHellingerBelow_isTheta_wold_of_neg` | same |
| Negative unsquared face is \(\Theta(\sqrt{a_N})\) | `primeValuationHellingerBelow_isTheta_halfNormal_of_neg` | same |
| Critical affinity equals one | `primeValuationSquaredHellingerBelow_zero`; `primeValuationHellingerBelow_zero` | same |
| Positive face is bounded by every Wold power | `primeValuationSquaredHellingerBelow_isBigO_woldPower` | same |
| Positive squared and unsquared faces are all-orders flat | `primeValuationSquaredHellingerBelow_reesAllOrdersFlat_of_pos`; `primeValuationHellingerBelow_reesAllOrdersFlat_of_pos` | same |
| Exact three-phase classification | `primeValuationHellinger_reesType_trichotomy` | same |
| Reflection swaps flat and nonflat type | `reflected_primeValuationSquaredHellinger_type_fracture` | same |

## Universal superselection and exact sewing cost

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Definition of all-orders-flat radical and finite Rees grade | `ReesAllOrdersFlat`; `ReesGradeAtMost`; `ReesOperatorGradeAtMost` | `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesJetStability.lean` |
| Finite packets are flat iff coordinatewise flat | `reesAllOrdersFlat_pi_iff` | same |
| Finite matrices with uniform finite Rees order preserve flatness | `reesAllOrdersFlat_finiteReesJetTransform` | same |
| Arbitrary-dimensional bounded finite-Rees operators preserve flatness | `reesAllOrdersFlat_apply_reesOperatorGradeAtMost` | same |
| Universal scalar essential sewing cost | `reesEssentialSewingCost_beyondEveryFiniteOrder` | `formal/GaloisForLFunctions/RHTower/AsymptoticTypeSuperselection.lean` |
| Universal operator-norm essential sewing cost | `reesExactSewingOperatorNorm_beyondEveryFiniteOrder` | same |
| Actual reflected squared sectors cannot be finitely sewn | `no_finiteReesOperator_sews_reflected_Hellinger_sectors` | `PrimeValuationHellingerReesReflectionFracture.lean` |
| Actual unsquared sectors cannot be finitely sewn | `no_finiteReesOperator_sews_xiRightModularAffinities` | `XiSourceModularTypeSuperselectionLaw.lean` |
| Unsquared exact sewing cost dominates every inverse Wold power | `xiRightModularAffinitySewingCost_beyondEveryReesOrder`; `xiRightModularAffinitySewingOperatorNorm_beyondEveryReesOrder` | same |
| Bundled right-Xi cross-chart superselection law | `xiRightSourceModularTypeSuperselection_law` | same |

## Escaping-quartet optimality

| Manuscript claim | Checked declaration | Module |
|---|---|---|
| Xi is unconditionally hypertranscendental | `xi_hypertranscendental` | `formal/GaloisForLFunctions/RHTower/XiHypertranscendenceUnconditional.lean` |
| Normalized quartet gauge and gauged Xi | `normalizedEscapingQuartetGauge`; `escapingQuartetGaugedXi` | `formal/GaloisForLFunctions/RHTower/CompactOpenKolchinWardChargeEscape.lean` |
| Gauged Xi is hypertranscendental and completed-symmetric | `escapingQuartetGaugedXi_hypertranscendental`; `escapingQuartetGaugedXi_one_sub`; `escapingQuartetGaugedXi_conj` | same |
| Added zero is off critical line | `escapingQuartetGaugedXi_added_zero`; `escapingQuartetGaugedXi_added_zero_off_critical` | same |
| Gauged Xi and every fixed jet converge locally uniformly to Xi | `escapingQuartetGaugedXi_tendstoLocallyUniformly`; `escapingQuartetGaugedXi_iteratedDeriv_tendstoLocallyUniformly` | same |
| Ward density vanishes uniformly on bounded windows | `escapingQuartetWard_window_tendstoUniformly` | same |
| Ward mass is exactly \(8\pi\) | `escapingQuartetWard_mass` | same |
| Modular weight and principal phase remain fixed | `escapingModularPoint_weight`; `escapingModularPoint_principalPhase` | `formal/GaloisForLFunctions/RHTower/RiemannComplexModularCharacterLaw.lean` |
| Reciprocal-square energy has exact formula and tends to zero | `escapingModularTraceEnergy_eq`; `escapingModularTraceEnergy_tendsto_zero` | same |
| Bundled separation theorem | `escapingModularCharacterSeparation_law` | same |

## Direct verification record

- `lake env lean GaloisForLFunctions/RHTower/RiemannComplexModularCharacterLaw.lean`
  passed.
- `lake env lean GaloisForLFunctions/RHTower/XiSourceModularTypeSuperselectionLaw.lean`
  passed after caching the checked dependency.
- `lake env lean /tmp/XiSourceModularAxiomAudit.lean` passed. Every audited
  theorem, including `gammaSewnActivationReesResolution_law` and the final
  capstone, depends only on `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build GaloisForLFunctions.RHTower.XiSourceModularTypeSuperselectionLaw`
  passed (`10110` jobs).
- `scripts/formal_tools.py lint` found no proof debt or reachability error in
  any module used by this paper. It exited nonzero only for 18 unrelated owned
  modules already absent from their theorem-area umbrellas.
- Final PDF: 20 A4 pages. Tectonic compilation passed with no overfull box,
  undefined-reference, or citation warning; all 20 rendered pages were
  inspected.
- Final process audit found no stale `lean`, `lake`, or `formal_tools.py`
  process.
