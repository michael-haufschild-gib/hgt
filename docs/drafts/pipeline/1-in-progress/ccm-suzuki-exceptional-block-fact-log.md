# CCM/Suzuki exceptional-block fact log

Scope: Codex `/root` research only. Facts and no-gos; no chronology or status diary.

## Facts

- The exact high-order first-atom enclosure discharges all five premises of the order-24 sector
  reduction.  Therefore the twenty-third normalized completed prime--Gamma moment is now closed
  unconditionally (`PrimeArchMomentTwentyThreeClosure.lean`,
  `normalizedPrimeArchMoment_twentyThree_pos`).  Whole-route consequence: one additional finite
  positive moment is available to exterior source windows; it does not supply the missing
  all-moment source weld or the source-selected mixed-incidence sign, each of which remains
  RH-strength.
- For every positive aperture, real-parameter movable Suzuki raw deficiencies have dense complex
  linear span in Suzuki energy space
  (`suzukiTaRawDeficiencySpan_closure_eq_top`).
- Literal CCM two-pole constraint is exactly orthogonality to deficiencies at parameters
  `-1/2` and `1/2` (`isPolarConstrained_suzukiTaToFormCLM_iff`).
- Orthogonally pole-corrected movable Suzuki CCM responses remain total in constrained CCM form
  sector (`suzukiTaPolarOrthogonalMovableCCMResponseSpan_closure_eq_top`).
- Restricted-Weil form has finite-dimensional reducing exceptional block, coercive exterior,
  and exactly zero mixed form (`CCMRestrictedWeilReducingBlockCertificate`).
- Projected actual movable Suzuki responses span constrained-visible exceptional range densely;
  finite dimensionality upgrades closure to exact algebraic span
  (`suzukiTaMovableReducingExceptionalSpan_eq_top`).
- A finite linearly independent subset of projected actual movable responses spans constrained-visible
  exceptional range (`exists_finite_suzukiTaMovableReducingExceptional_basis`).
- RH is equivalent to nonnegativity of restricted-Weil quadratic on constrained-visible finite
  exceptional range at every positive aperture
  (`riemannHypothesis_iff_movableReducingExceptional_nonnegative`).
- Restricted-Weil ground energy is antitone and continuous in aperture, and is strictly positive at
  sufficiently small aperture (`ccmRestrictedWeilGroundEnergy_antitone`,
  `continuous_ccmRestrictedWeilGroundEnergy`, `exists_suzukiSmallAperture_ccmGroundEnergy_pos`).
- If RH fails, first zero of unrestricted ground energy is attained by a nonzero completion-boundary
  vector not represented by any strict smooth interior source
  (`riemannHypothesis_or_ccmFirstContactBoundaryRoughness`).
- Projected raw movable Suzuki responses span every full reducing exceptional block exactly, with a
  finite linearly independent subfamily
  (`suzukiTaMovableFullReducingExceptionalSpan_eq_top`,
  `exists_finite_suzukiTaMovableFullReducingExceptional_basis`).
- At any nonnegative aperture, every zero-energy vector lies entirely in every reducing exceptional
  block (`mem_reducingExceptional_of_nonnegative_of_null`).
- Hence RH failure has an exact finite actual movable-source first-contact realization despite its
  exclusion from smooth interior core
  (`riemannHypothesis_or_firstContactFiniteMovableExceptionalCoordinates`).
- Literal diagonal and cross pole cutoffs are finite positive-part hinge superpositions on every
  bounded aperture neighborhood (`ccmWeilPoleDiagonal_eq_smooth_sub_sum_hinges`,
  `ccmWeilPoleCross_eq_smooth_sub_sum_hinges`). Each prime atom vanishes at entry.
- Full diagonal, cross, and fixed-parity prime--polar--Gamma energies are globally continuous across
  every prime-power entry (`continuous_ccmWeilPoleDiagonal`, `continuous_ccmWeilPoleCross`,
  `continuous_ccmRestrictedWeil_parityPoleSourceQuadratic`).
- If RH fails, one literal parity vector with fixed coefficients `(1, 1)` or `(1, -1)` has a first
  zero aperture and is strictly positive at every smaller aperture
  (`riemannHypothesis_or_ccmFixedParityPoleFirstContact`). No existential source coefficients or
  spectral projection remain in this witness.
- If RH fails, the entire literal two-pole compression has an earliest singular aperture: one fixed
  parity eigenvalue is zero, the companion is nonnegative, and both were strictly positive at every
  smaller aperture (`riemannHypothesis_or_ccmPoleCompressionFirstContact`). Equivalently, the exact
  arithmetic entries first reach `|ccmWeilPoleCross| = ccmWeilPoleDiagonal` from strict inequality
  (`riemannHypothesis_or_exists_ccmPoleCompression_exact_first_wall`).
- Every literal odd/even pole atom factors as critical-Mellin energy times an exact signed
  hyperbolic response, including entry delay and common age loss
  (`ccmWeilOddPrimeAtom_eq_criticalMellinWallEnergy`,
  `ccmWeilEvenPrimeAtom_eq_criticalMellinWallEnergy`). At a canonical prime power this carrier is
  exactly zero-height Suzuki wall-field energy
  (`criticalMellinAtomWeight_primePower_eq_wallFieldEnergy`).
- The complete finite odd and even prime--polar--Gamma pole sources are exact finite
  critical-Mellin wall-energy superpositions, not merely atomwise comparisons
  (`ccmWeilOddPole_eq_criticalMellinWallEnergySuperposition`,
  `ccmWeilEvenPole_eq_criticalMellinWallEnergySuperposition`).
- Odd and even pole responses solve one exact hyperbolic Green equation. Their normalized
  `(1 - d²/ds²)` residuals are respectively `2s - log n` and its negative
  (`ccmWeilOddWallEnergyResponse_normalized_green_triangle`,
  `ccmWeilEvenWallEnergyResponse_normalized_green_triangle`).
- At half aperture `s = H/2`, the odd residual is exactly the positive-lag rectangular FU triangle
  on every actual finite-head atom (`ccmPositiveLagRectangularTriangle_eq_oddPoleGreenResidual`).
  Multiplication by `32 / (H (log n)^3)` recovers the literal third-grade coefficient with no
  loss (`criticalMellinAtomWeight_mul_thirdGradeTriangularWeight_eq_oddPoleGreenResidual`).
- The complete RH-bearing anchored FU moment is exactly a signed finite sum of normalized odd-pole
  Green residuals minus the literal continuous polar window
  (`ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_oddPoleGreenResidual_sub_polar`).
  Thus the previously missing source-faithful Route O--CCM-FU bridge is an equality, not a bound.
- The literal triangular curvature transform has an exact critical Abel decomposition into a
  uniformly bounded Mertens--Gamma finite-part base term and a variation action of the vanishing
  critical ordered-prefix remainder
  (`suzukiCheckpointTriangularCurvatureTransform_eq_criticalFinitePart_add_remainderVariation`).
- That remainder separates exactly into source-free Gamma/harmonic error minus the actual signed
  Mertens deviation (`suzukiCheckpointCriticalOrderedRemainder_eq_sourceFree_sub_mertensDeviation`).
- Source-free Gamma/harmonic increments have a common summable envelope and hence a uniform moving
  variation-action budget
  (`summable_suzukiCheckpointCriticalSourceFreeIncrementMajorant`,
  `exists_uniform_bound_suzukiCheckpointCriticalSourceFreeVariationAction`).
- Uniform control of the remaining Mertens-deviation variation action is equivalent to the literal
  triangular curvature bound and to RH
  (`ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_riemannHypothesis`).
- For Suzuki's actual shift selector, the free endpoint is already strictly below the Xi
  calibration at every sufficiently large aperture
  (`eventually_freeDefectAngle_lt_primeArchSuzukiFirstDefectCalibration`).  Abstract continuity,
  free-limit, ground-residue, and greatest-root selection laws are complete; only actual
  source occurrence at the spectral endpoint is unresolved.
- Exact finite-aperture simple-even ground occurrence is proved only from positivity of
  `suzukiFiniteSignDefectCoefficient a = 1/2 - 4 a * suzukiOriginCurvatureUnitBound`, hence only
  on a punctured neighborhood of aperture zero.  This coefficient cannot yield cofinal
  large-aperture occurrence.
- A finite-Morse polynomial in one below-spectrum resolvent can cancel every negative affine
  Krein level while preserving positivity on positive levels
  (`suzukiFiniteMorse_operatorCompletion_nonneg`), and is a finite resolvent-shift jet
  (`suzukiFiniteMorseInterpolant_eq_resolventShiftJetSum`).
- G-CE singular-graph completion and finite self-adjoint boundary transport are complete.  The
  exact excess is `|continuedXiAntiCausalWardResponse (1/2)|²`, and its vanishing is equivalent
  to RH (`mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh`).
- A source-native marked Sonin producer exists before scalarization; it is contractive, conserves
  its two-port energy, and its odd commutator port vanishes cofinally
  (`canonicalMobiusClockSoninMarkedProducer_closed`).  A separate affine charge port retains the
  nonzero zero-clock prime--polar--Gamma coefficient and transports it coefficient-faithfully.
- The actual-head Route O source has a complete phase-preserving Fourier normal form: the literal
  restricted-Weil source quadratic is the spectral average of `correctedCCMSymbol` against the
  actual head density (`ccmActualHeadCoherentCompletedGammaProducer_eq_sourceQuadratic`).  On
  canonical Gamma--Slepian heads, reverse-prime control is exactly nonnegativity of this same
  signed average (`ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_correctedSymbolAverage_nonneg`).
- The source-horizontal adaptive class-law observer has no off-centre reserve: at each retained
  prime and scale ratio its certificate exists exactly at centred rate zero
  (`sourceHorizontalPrimeAdaptiveClassLawScaleOrbitCertificate_nonempty_iff`), while its global
  Xi-copy version is equivalent to RH
  (`sourceHorizontalAdaptiveFisherGlobalClassLawScaleOrbitProducer_iff_riemannHypothesis`).
  It is therefore a classified neutral observer, not an independent Route-O/G producer.
- Matched-phase Fock tomography has one global PSD carrier already: every finite source packet is
  a restriction of `ccmActualHeadMatchedPhaseGlobalFockKernel`, not a separately chosen Gram
  matrix (`ccmActualHeadMatchedPhaseGlobalFockKernel_isPSDKernel`,
  `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_globalPhaseFockKernel`).  Thus cofinal kernel
  selection and compactness are false subproblems; remaining datum is a signed estimate for its
  logarithmic anchor reporter after spectral integration.
- PSD/Jensen extraction from that carrier is excluded pointwise: each literal prime-power reporter
  takes strict opposite signs at its two phase probes while the projective Fock kernel is PSD at
  both (`ccmActualHeadMatchedPhaseGlobalProjectiveFockPrimePowerReporterSignStraddle`), and the
  negative probes recur cofinally in frequency.  Hence a continuous scalar source-to-Ward repair
  must have cofinal zero walls
  (`ccmActualHeadMatchedPhasePrimePowerContinuousScalarReporterFaithful_cofinal_zero`); a valid
  mechanism must be non-scalar and couple distinct frequencies before readout.
- Endpoint mismatch is a null aperture gauge, not arithmetic debt.  The completed quantile symbol
  and its endpoint-free representative have identical quadratic averages on every physical head
  (`integral_ccmActualHeadOutgoingQuantileEndpointFreeCosinePhaseSymbol_eq_completed`).
- Fixed finite exterior-measure gauges are automatically harmless in both frequency tails, so
  global representative positivity reduces exactly to one compact core
  (`exists_compactCore_nonneg_iff_correctedExteriorMeasureGaugeRepresentative_nonneg`).
- The canonical actual wall-light completion has the exact nonzero local affine datum that the
  homogeneous incidence lacks: at zero frequency it equals the critical Mellin atom, and its
  oriented imaginary coordinate has strictly positive first jet at every prime power
  (`ccmActualHeadWallLightCompletedPhase_zero`,
  `deriv_ccmActualHeadWallLightCompletedPhase_im_zero_pos`).  Hence any remaining Route-O/CCM-FU
  completion failure is global: it must concern a signed prime--polar--Gamma sewing of this
  already fixed two-channel phase, not construction of a free local reserve.
- The global sewing now closes exactly: the real deficit of the natural-indexed affine wall phase
  is the literal reflected-chord energy, its prime-power restriction is the completed Suzuki
  phase, and the finite signed affine producer equals the completed source quadratic
  (`ccmActualHeadPrimeWallAffinePhaseEnergy_eq_chordEnergy`,
  `ccmRestrictedWeilActualHeadWallAffinePhaseSignedProducer_eq_sourceQuadratic`).  Thus Route O
  and CCM-FU no longer lack a coefficient-faithful pre-scalar affine carrier.  Their sole shared
  hard core is a cofinal signed lower bound for this exact carrier; no local phase completion or
  source-identification modification can resolve it.
- Off-pole logarithmic phase integration has exact tail mass `1 / log U`; its remainder therefore
  obeys the unconditional outer-tail scale `1 / (|lambda| log U)`
  (`integral_Ioi_logTailWeight_eq`, `norm_integral_Ioi_oscLogRemainder_le`).  Hence every moving
  phase regime with `|lambda| log U → ∞` is analytically harmless before arithmetic transport.
  The only nonuniform phase zone is the scale-boundary layer `|lambda| log U = O(1)`.  This does
  not estimate the completed prime--polar source, so it narrows—rather than closes—the shared
  Route-O/CCM-FU hard core.
- The PNT error term has now been separated uniformly from that obstruction: for every fixed
  compact band `|lambda| ≤ R`, its Abel-summation tail is uniformly small
  (`exists_uniform_compact_oscLogKernelDeriv_thetaError_tail`).  This is a closed unconditional
  Lean theorem with only standard Lean axioms.  Combined with the exact phase tail, it proves that
  bounded-frequency arithmetic error cannot create the moving obstruction; only the explicit
  shrinking band `|lambda| log U = O(1)` remains.  This is still an analytic prime-phase result,
  not a completed prime--polar lower bound.
- The required relevance test is negative: no exact Lean map connects `primeCpowSum` or its
  oscillatory logarithmic phase to the literal third-grade CCM/FU completed prime--polar source.
  Therefore the uniform prime-phase theorem must not be presented as an RH-bearing CCM result.
  The real FU problem remains its triangular completed window; future work must start from that
  source rather than from an auxiliary one-line Euler phase.
- The natural central unit-Riesz barycenter is not a surviving FU producer despite its exact
  source landing: its uniform bound is unconditionally false
  (`not_ccmUnitRieszCentralBarycenterNaturalBound`).  Lean identifies the reason exactly: it is
  equivalent to RH plus the false square-root Chebyshev remainder bound
  (`unitRieszCentralBarycenterNaturalBound_iff_rh_and_normalizedErrorBounded`,
  `not_psiRemainderSquareRootBounded_of_riemannHypothesis`).  Thus every first-moment or
  central-barycenter compression loses the required scale cancellation.  A viable CCM-FU
  producer must remain higher-dimensional and pre-scalar through the triangular coupling.
- A cross-route transport test fails at the dictionary, not at an estimate: the proved
  squarefree-Möbius moving-boundary product cancellation
  (`squarefreeMobiusBoundaryLayerLaplace_mul_signed_eq`) has no Lean source map to either the
  actual-head Gamma autocorrelation or affine-wall producer (exhaustive symbol-file intersection:
  empty).  It cannot be used as a CCM positivity argument.  Its positive residue is structural:
  cancellation must occur before a singular moving-boundary limit; any prospective CCM carrier
  must provide that missing dictionary explicitly.
- The fixed physical divisor core `{2}` has no bound uniform over one new prime insertion and all
  later dilations: `not_exists_uniform_coreTwo_insert_dilationMean_bound` combines the exact
  inserted-prime negative `sqrt p` band with Bertrand primes.  Hence a one-step renewal induction
  cannot control CCM-FU/CCM-UR by a core-independent estimate.  Any viable producer must retain
  cancellation among multiple newly inserted prime coordinates before imposing uniform control.
- Cellwise positivity cannot exploit matched zero-mass transport: the literal matched Schur
  completion is nonnegative, but its prime value at zero has a divergent sum
  (`not_summable_ccmActualHeadMatchedPhaseSchurCompletionProfile_prime_zero`).  Thus a
  cell-by-cell Γ/graph-square completion necessarily loses the collective affine cancellation;
  only a full-block, phase-sensitive affine mechanism remains relevant.
- The locality obstruction is now orientation-complete for contiguous critical FU blocks.  If a
  block containing any prime `p ≥ 27` has nonpositive literal Mertens--polar mass, its left and
  right spans must together supply the exact logarithmic polar drift at least
  `log p / (2p)` (`suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_log_span`).
  Thus borrowing from earlier cells does not rescue bounded-memory transport.  This still leaves
  genuinely nonlocal, noncontiguous collective transport open.
- The orientation-complete obstruction has a cofinal fixed-radius form: for every fixed pair of
  left/right radii, the literal two-sided Mertens--polar block around every sufficiently large
  prime is strictly positive
  (`eventually_prime_suzukiCheckpointCriticalMertensDeviationCore_bidirectionalBlock_pos`).
  Hence no translation-invariant finite-memory signed transport can close CCM-FU; scale-growing
  collective transport is the first surviving class.
- **Contiguous bicausal cancellation needs logarithmic, not merely growing, support (new, Lean
  closed).** If `2*(L+1) ≤ p` and a block from `p-L-3` through `p-2+R` containing prime `p ≥ 27`
  has nonpositive literal Mertens--polar mass, then
  \(\log p/2\le 2L+R\)
  (`suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_bidirectionalBlock_forces_combined_log_radius`).
  Its cofinal scheduler corollary
  (`eventually_prime_suzukiCheckpointCriticalMertensDeviationCore_bidirectionalBlock_pos_of_eventually_combined_radius_lt_log`)
  rejects every schedule eventually satisfying \(2L(p)+R(p)<\log(p)/2\). Whole-route
  consequence: every contiguous bicausal producer with combined support \(o(\log p)\) is
  impossible on the actual source; the remaining collective class must use at least logarithmic
  reach or noncontiguous cross-scale pairing. This is a constraint, not a bound for the
  RH-bearing triangular action.
- **Sharp two-unit log-Haar transport is still conditional infrastructure, not an available
  cancellation estimate (Lean/literature audit).** `SuzukiMangoldtLogHaarTransport.lean` makes
  every sharp-cell result depend on `MangoldtLogHaarCapacity`, exactly
  \(\sum_{n\le N}\Lambda(n)/n\le\log N\); no corpus theorem proves it. Ramaré--Zuniga Alterman
  (arXiv:2312.05138v3, Appendix) prove it through a floor-kernel integral, Hanson’s global
  Chebyshev bound, and finite cutoff verification, none formalized here. Even after that
  prerequisite is formalized, `SuzukiBicausalNoFreeSplice.lean` charges the full duplicate seam
  back to the original capacity deficit. Whole-route consequence: capacity formalization would
  make a useful exact transport unconditional, but cannot by itself control the FU triangular
  action; a non-capacity, source-sensitive collective pairing remains required.
- The literal linear weighted-curvature first-moment route is false, not merely unproved: it is
  equivalent to RH plus the square-root Chebyshev remainder bound, and the latter contradicts the
  cofinal Deninger phase escape even under RH
  (`not_ccmFUSuzukiWeightedCurvatureFirstMomentLinearBound`).  Thus CCM-FU/UR/HG cannot pass
  through a separately bounded central first moment.
- The remaining scalar FU source is the normalized coupled half-order Abel action
  `coherentSelbergSquareRootAbelMoment M / M`; it equals the completed outgoing charge up to an
  explicit vanishing polar-lattice correction, and its uniform boundedness is exactly RH
  (`coherentCompletedOutgoing_eq_abel_add_latticeDefect_div`,
  `riemannHypothesis_iff_coherentSelbergSquareRootAbelBounded`).  Any viable producer must bound
  this coupled action directly rather than its terminal or interior pieces.
- The literal SP-E mass-error discrepancy from terminal normalized Chebyshev error is not an
  independent cancellation target: it is the negative completed outgoing charge plus a
  source-free polar--lattice residual uniformly bounded by
  `5 + |suzukiEulerianCoherentBoundaryAnchor|`
  (`SuzukiEulerianOutgoingChargeRigidity`).  Its uniform boundedness is therefore equivalent to
  RH.  This collapses SP-E into the same FU/O phase-preserving outgoing-charge frontier rather
  than providing a separate scalar producer.
- The resonant G-cap density has an exact potential-flow direction: writing
  `a = 51/100 + transverseLevel`, its coefficients multiply
  `∂_a log|XiC| - (2x/a) ∂_x log|XiC|`, whose characteristics satisfy `x*a^2 = constant`.
  This does not yet control the cap: the RH-bearing functional is a height integral at fixed
  transverse level, while the characteristic argument requires a joint transverse-height
  Green/coarea identity.  Exhaustive `XiWard*.lean` search finds no such source functional.
  Therefore transverse transport is a conditional new producer shape, not a valid bound or a
  substitute for the signed cap estimate.
- Factor-two-separated Suzuki reporter secants have coefficient-faithful negative Cauchy cross
  energy, including the literal prime pairs below the multiplicative hyperbola
  (`suzukiNaturalApertureFarHyperbolaCauchyEnergy_nonpos`), but removing all of that favorable
  sector still leaves a transition core with cofinal linear divergence
  (`tendsto_suzukiNaturalApertureTransitionCoreCauchyEnergy_eight_mul_atTop`).  Thus far-scale
  negativity cannot fund FU; a survivor must cancel the positive near-hyperbola core itself.
- On actual quantile Gamma heads, the higher-Gamma plus signed completed-error autocorrelation
  producer converges on canonical heads without splitting prime and polar channels
  (`tendsto_ccmCanonicalGroundHead_signedCompletedErrorGammaProducer`).  Its available lower
  bound cannot close the sign problem because it contains a reciprocal-Gamma chi-square cost
  proven to diverge on literal heads (`tendsto_ccmOutgoingQuantileGammaChiSquare_atTop`).  Hence
  convergence is closed; only a source-specific sign/coercivity law for the coupled current is live.
- Even the cross-prime coherent quantile-field chi-square cannot provide that coercivity: the
  post-cancellation scalar reserve `2 * gammaHardyPhaseRate 0 + 4` is strictly negative, so its
  nonnegative norm cost cannot be paid by any nonzero canonical head
  (`eventually_not_ccmRestrictedWeilCanonicalGroundHead_coherentChiSquare_le_centralBudget`).
  Therefore a viable O/CCM producer must retain the phase of the joint higher-Gamma/current
  bilinear block; every norm-square completion is excluded.

## No-gos

- Per-height scalar Suzuki/Schur contraction does not control cross-height terms, so it cannot prove
  quadratic nonnegativity on finite linear combinations of movable sources.
- Totality transfers coverage, not metric contraction; density alone cannot prove restricted-Weil
  positivity.
- Ordinary Hilbert Gram positivity of linearly independent source vectors is irrelevant to remaining
  sign problem: restricted-Weil quadratic is induced by `I - K`, not ambient inner product.
- Generic finite-negative-index reduction localizes all possible negativity but does not determine
  arithmetic sign of exceptional Hermitian matrix.
- Smooth-core aperture perturbation cannot exclude first contact: under RH failure, Lean forces the
  first null state to live outside every strict smooth interior source representation.
- Global positivity-preserving or Perron--Frobenius propagation is unavailable: beyond the proved
  threshold, the screw-regular form violates Beurling--Deny (`not_satisfiesBeurlingDeny_screwRegularForm_add_smul`).
- Prime-power entry cannot hide a discontinuous sign loss: exact entering atoms vanish, and full pole
  energy is continuous. Any boundary-jump escape mechanism is therefore false for these sources.
- Direct scalar transport of wall-chord orientation into the completed pole producer is impossible:
  completed producer is reflection-even while wall-chord jet current is reflection-odd, and any
  selector factoring through completed producer forces that current to vanish
  (`wallChordJet_zero_of_factors_through_completedProducer`).
- Positivity of each Suzuki wall-field carrier is insufficient: exact welded propagation responses
  are signed and retain common hyperbolic age loss. Local wall-field positivity cannot replace the
  global prime--polar--Gamma cancellation inequality.
- Differentiating the moving whole pole head as an ordinary smooth finite sum is invalid at entry
  clocks: support changes at `log n = 2s`. The lawful global bridge applies the Green residual
  atomwise before finite summation and retains entry boundary contributions through the FU triangle.
- Convergence of the critical ordered prefix is insufficient by itself: the critical triangular
  multiplier moves with aperture and grows before its reciprocal-log decay. A rate-sensitive signed
  variation action remains; taking absolute values of the arithmetic increments would erase the
  prime--polar cancellation and demand a stronger statement than RH.
- Limiting-log ground simplicity does not supply cofinal actual finite-aperture ground simplicity:
  the corpus contains no norm-resolvent or eigenspace-transport theorem between those operators,
  and the proved finite sign-defect estimate worsens linearly with aperture.
- Finite-Morse completion cannot be treated as an exact source-neutral negative projector.  Any
  finite resolvent polynomial paying a nonzero negative-level debt must overpay somewhere on the
  infinite positive spectral tail
  (`suzukiOperatorResolventJetSquare_exactProjector_impossible`).  A Suzuki selector based on this
  completion still needs a coefficient-faithful proof that its extra source jet leaves the Xi
  target readout unchanged or is physically cancelled.
- G-CE cancellation by a bounded scalar controller is either RH or universal source erasure
  (`mobiusGammaXiDebtController_cancellation_iff_rh_or_erasure`).  Lifting before scalarization
  does not rescue a diagonal contractive clock: every moving coordinatewise contraction
  asymptotically commutes with the cofinal Sonin pullback
  (`tendsto_norm_soninCofinalPositiveSourcePullback_commutator_lpCoordinatewiseContraction`), so
  its odd port cannot cancel the persistent affine charge.  Any surviving G-CE producer must be
  non-diagonal while preserving the positive energy wall.
- Unsigned absorption of the actual outgoing quantile current is terminal: the literal quantile
  Gamma chi-square diverges, and even coherent chi-square cannot fit the negative central
  Gamma--polar budget (`tendsto_ccmOutgoingQuantileGammaChiSquare_atTop`,
  `not_coherentChiSquare_le_centralBudget_of_ne_zero`).  Route O must combine higher-Gamma and
  arithmetic phases before absolute values or squares.
- Pointwise positivity of the unmodified completed symbol is false even before primes enter:
  `ccmCorrectedSymbol a 0 < 0` for every `a < ccmPrimeFreeAperture`.  Thus the sufficient
  pointwise-symbol criterion cannot be the proof target; positivity is only meaningful modulo the
  physical aperture's exterior-cosine annihilator.
- Universal exterior superoscillation is not a cofinal repair.  Any fixed-error approximation of
  the constant mode on expanding Sonin windows by arbitrary exterior finite measures has
  superpolynomially diverging Jordan mass
  (`tendsto_exteriorCosineMeasureGauge_mass_div_pow_atTop_of_constant_approximation`).  A viable
  exterior correction must be source-adapted and finite-aperture, not a universal constant-mode
  approximation.
- Moving the exterior support threshold with the aperture does not evade this wall: if the
  Sonin scale `delta N * H₀ N` diverges, every fixed-error constant-mode approximation by signed
  finite exterior measures has Jordan mass larger than every power of that moving scale
  (`tendsto_exteriorCosineMeasureGauge_mass_div_scalePow_atTop_of_variable_constant_approximation`).
  This removes only threshold-rescaled universal completions; source-adapted nonconstant
  corrections remain an open class.
- The exact Cauchy reporter route cannot start from its positive prime Gram energy.  Its
  transition-separated cross-block is favorable, but its exact positive transition core grows at
  least linearly; every bounded correction makes the rectangular Ward defect tend to `-∞`, and
  every successful correction must itself carry linear cofinal mass
  (`tendsto_suzukiRectangularWardDefect_transitionCore_sub_bounded_atBot`,
  `eventually_linear_le_correction_of_transitionCoreWardDefect_bddBelow`).  Hence a valid
  Cauchy mechanism must retain an unsummable signed atomic--continuous channel before forming the
  energy.
- The full Suzuki Cauchy wall is already exactly a positive prime wall minus a positive
  regular-screw continuum at every complex height
  (`suzukiUnitRieszGammaCompletedWardWall_eq_prime_sub_regular`); its lower-Hardy readout is
  Suzuki Green, whose uniform bound is RH-equivalent.  Replacing this difference by a positive
  Gram packet therefore erases, rather than controls, the decisive cancellation.
- Eventual odd chamber concavity does **not** exclude a smooth odd first zero.  It forces a
  negative value immediately to its right, but the exact checkpoint criterion only transfers
  that negative value to a later negative prime-power entry
  (`ccmWeilPole_primePower_gap_strict_shape`,
  `ccmWeilOddPole_negative_tail_iff_primePower_entry`).  Curvature alone is diagnostic; the
  unresolved datum remains aggregate signed checkpoint balance.
- Literal CCM pole diagonal is exactly `poleDiagonalExplicit` and hence eventually strictly
  positive.  At any late strict determinant failure (`D < |C|`), exactly one parity coordinate
  is negative.  This deletes the simultaneous-negative sector but does not bound the cross term,
  so it is a route-O reduction rather than an RH step
  (`exists_eventually_ccmWeilPoleDiagonal_pos`,
  `ccmWeilPoleCompression_parity_opposite_sign_of_diagonal_pos_of_cross_exceeds`).
- Each admitted even critical-wall response is nonpositive at its entry and strictly negative
  thereafter. Hence the literal finite even pole is at most its smooth prime--polar--Gamma
  carrier (`ccmWeilEvenPole_le_smooth`). There is no hidden cancellation within the even atomic
  source; remaining Route-O datum is dominance of its smooth carrier over accumulated losses,
  coupled to the sign-changing odd source. This is a reduction, not an orientation of first
  contact.
- Broad January--September 2026 arXiv probes (`Green`, `Tauberian`, `variation`) produced no
  eligible signed-kernel mechanism. Positive Tauberian routes would be structurally unsound here:
  they discard the prime--polar cancellation that constitutes the open datum.
- For every reflection-compatible causal operator, its self-adjoint phase coordinate maps an odd
  source into the even sector and has identically zero odd diagonal quadratic form
  (`inner_volterraPhase_apply_odd_eq_zero`). Therefore diagonal phase energy cannot orient the
  signed connection current. The surviving G/Suzuki class must be source-faithful and genuinely
  off-diagonal or affine; this is a sharp no-go, not a positivity result.
- The literal source-faithful off-diagonal Stokes current is already present: it equals centered
  zero-rate times a positive prime Green energy, and the completed polar current cancels only the
  neutral-wall jump (`gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_eq`,
  `gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm_eq_connection_pairing`). It detects
  orientation but cannot force the rate to vanish. Thus its missing producer is a lawful
  *constraint* on the signed current, not another representation or positive scalarization.

## Current exact frontier

- Exclude first singular wall of the explicit two-pole compression. The next useful law must orient
  its active null parity through the exact signed wall-energy superposition while retaining the
  smooth Gamma--polar term. Carrier identification, entry normalization, existential finite-basis
  coefficients, spectral projections, and ambiguity about an earlier companion-parity failure are
  gone.
- Hard datum is aggregate cancellation of signed hyperbolic responses against smooth Gamma--polar
  source. Odd atom cutoff/sign classification already exists, and even gap minima retain a missing
  logarithmic Mangoldt value moment; local positivity, curvature, or first jets cannot supply it.
- In CCM-FU coordinates, all finite-part, Gamma-tail, harmonic-tail, local Green, finite-head, and
  cubic-normalization debt is closed. Exact remaining datum is uniform moving variation control of
  the signed Mertens deviation against the critical triangular multiplier. This formulation keeps
  prime--polar cancellation intact and is equivalent to RH; pointwise or absolute control is not a
  lawful substitute.
- In actual-head Route O coordinates, all convergence, terminal-seam, first-Binet, and unsigned
  envelope questions are closed.  Exact remaining datum is nonnegativity of the completed CCM
  symbol averaged against cofinal canonical-head densities, equivalently the signed
  higher-Gamma-plus-quantile current threshold.  Pointwise symbol sign is too strong and false;
  generic exterior-gauge approximation is killed by the Jordan-mass wall.  Surviving mechanism
  must be a source-adapted positive completion in the aperture quotient.
- Suzuki-v2 finite self-adjoint realizations, all-angle real-zero laws, upper-half-plane Montel
  compactness, jet transport, and pole-free/spherical formulations are closed.  Remaining datum is
  source identification of the Montel limit with the Xi quotient on a uniqueness set; compactness
  alone cannot identify it, and that identification implies RH.
- The coefficient-only theta-stage asymmetry criterion is terminal for the actual corrected
  theta stages: its finite energies converge to a strictly positive anti-Hermitian
  Hilbert--Schmidt defect detected on the pinned coordinate vector.  Thus cofinally small ordinary
  skew-adjoint energy is false, not an available source estimate
  (`tendsto_thetaSourceSignedStageSkewAdjointEnergy`,
  `not_thetaSourceSignedStageSkewAdjointEnergyCofinallySmall`).
- The HCF prime--Gamma off-line lattice budget is an exact positive RH detector and its raw
  diagonal has unavoidable critical-line multiplicity.  The original Abel correction is
  divisor-dependent, but later source-only pole--Gamma Plemelj covariance already replaces the
  corrected translated budget modulo `o(N)` on canonical windows.  The live HCF obstacle is its
  quantitative source-only covariance ceiling, not construction of a pre-divisor replacement
  (`criticalFeaturePrimeGammaOffLineExcess_eq_zero_iff_rh`,
  `criticalFeaturePrimeGammaOffLineTranslatedLatticeBudget_eq_sourceCovariance_add_vm`,
  `tendsto_canonicalTranslatedCorrectedBudget_sub_sourceCovariance_div`).
- The connected third Suzuki tangent already lands coefficient-faithfully on the literal finite
  CCM prime--polar triangular window before scalarization
  (`ccmGuinandWeilPrimePolarTriangularWindow_eq_connectedSuzukiProducer`).  It cancels
  disconnected Euler composites, but supplies no inequality on the remaining signed
  prime--polar difference.  Therefore it is a completed representation, not the missing FU
  cancellation producer; a new law must constrain that completed difference locally.
- For every prime `p ≥ 27`, the literal Mertens-deviation cell increment is at least
  `log p / (2p)`: the prime atom exceeds its same-cell logarithmic continuum increment.
  Hence FU cancellation cannot happen within a prime cell; it must be a genuinely cross-cell
  signed transport.  This is the sharp target for any proposed ``local'' producer, and excludes
  any cellwise positivity/absolute-value argument before it starts
  (`suzukiCheckpointCriticalMertensDeviationCore_prime_cell_lower`).
- The exact Selberg coordinate does not evade this obstruction: it is a terminal normalized
  Chebyshev error minus a positive half-order Abel action, with only a source-free remainder
  (`weightedSignedCurvature_eq_normalizedErrorBoundary_add_squareRootAbel_arch`).  Existing
  harmonic-order Selberg control cannot land on this half-order pair; cancellation between its
  terminal and interior terms remains the FU datum.
- In the first half of a literal critical triangular aperture, each prime `p ≥ 27` has absolute
  weighted cell mass at least `8 √p / (p (log p)^2)`
  (`suzukiCheckpointCriticalPrimeCell_abs_weighted_lower`).  Independently, the prime weight in
  `(2Y,3Y]`, normalized by `√Y`, tends to `2(√3-√2)>0`
  (`tendsto_prefixPhaseWeight_triple_sub_double`).  These are unconditional pressure laws for
  an absolute-variation divergence argument; they cannot bound the signed reporter.  The whole
  FU route therefore requires cancellation across that growing prime pressure, not an absolute,
  one-sided, or cellwise estimate.
- The pressure argument is now closed on the canonical clock
  `H_N = 2 log(4N)`: its finite cutoff is exactly `(4N)^2`, the full `(2N,3N]` prime window lies
  in the first aperture half, and
  `suzukiCheckpointCriticalAbsoluteVariationCore(H_N) → +∞`
  (`tendsto_suzukiCheckpointCriticalAbsoluteVariation_schedule_atTop`).  Consequently every
  proof landing by triangle inequality, total variation, or independent prime-cell bounds fails
  unconditionally—even if RH were granted.  This removes an entire proof architecture, but does
  not bound the signed FU reporter: the sole viable hard core remains a source-faithful signed
  cross-cell transport law preserving the literal prime--polar cancellation.
- A quantitative local no-go is now closed for the same literal coordinate.  If a forward block
  of `L` cells starting at any prime `p ≥ 27` has nonpositive net Mertens--polar mass, then
  `log p / 2 ≤ L`
  (`suzukiCheckpointCriticalMertensDeviationCore_prime_nonpos_forwardBlock_forces_log_radius`).
  The proof retains every possible positive prime-power atom and bounds only accumulated polar
  drift.  Hence even signed bounded-memory transport is impossible: any surviving FU producer
  must couple cells across a range growing at least logarithmically with the prime scale.  This
  still leaves scale-adaptive, genuinely nonlocal signed transport open; it is not a reporter
  bound or an RH proof.
- The local obstruction is cofinal, not anecdotal: for every fixed forward width `L`, every
  sufficiently large prime begins a block with strictly positive net literal source
  (`eventually_prime_suzukiCheckpointCriticalMertensDeviationCore_forwardBlock_pos`).  Thus
  bounded-memory signed FU producers are eliminated outright.  The next possible class has a
  range that grows with scale (necessarily at least `log p / 2`); establishing or refuting a
  source-faithful weighted transport in that class is now the exact FU sub-frontier.
- The FU/O matched-cell route has an exact common hard core, not an unresolved convergence
  reduction: in polar-mass coordinate every matched cell is an equal-mass rigid translate of its
  quantile cell, and the completed source is the finite sum of those signed translates plus one
  terminal interval (`ccmActualHeadMatchedPolarCoverageSeam_eq_rigidCellTransports_sub_terminal`).
  Each displacement is the outgoing completed error modulo one atom
  (`ccmActualHeadMatchedQuantilePolarDisplacement_mem_errorCorridor`); de la Vallee Poussin only
  makes it small relative to polar mass, not summable.  Therefore pointwise, Lipschitz, or
  atomwise transport cannot close FU/O.  A surviving mechanism must prove collective signed
  spectral cancellation of this exact translate family.
- SCE is closed negatively at its stated source-independent level: a universal strictly convex
  event countermodel satisfies the complete checkpoint package while its restricted conjugate
  strictly exceeds the moment (`not_sceConvexEventSignPrinciple`).  Any revival must add a
  genuinely arithmetic invariant, rather than another convexity, Bregman, endpoint, or
  recurrence argument.
- F2 compact-fiber Hausdorff positivity is also insufficient: the formal compact interval model
  has matching zeroth moment and all scaled Hausdorff-difference inequalities but no parameter
  matching all moments (`f2HausdorffCompactFiberEscape`).  Compactness/positivity alone cannot
  supply source identification on that route.
- CSB low-moment matching is not an independent opening: the unconditional thermal second
  truncation converges to its own thermodynamic value, while convergence to the first nontrivial
  prime--archimedean source moment is already equivalent to RH
  (`tendsto_xiThermalTruncation_one_iff_rh`).  Thus frozen low-moment targets cannot supply a
  source-faithful cofinal comparison estimate; CSB still needs a genuinely degree-coupled signed
  packet mechanism.
- G’s pure marked-clock branch is exhausted: its actual two-port producer and finite
  self-adjoint transport are already closed, but the zero-clock odd port is identically zero
  (`mobiusClockSoninMarkedOddPort_zeroClock`).  Since the surviving G-CE coefficient is the
  nonzero-charge datum whose vanishing is RH, a commutator-only refinement cannot be the missing
  producer; it must alter the affine complement channel before scalarization.
- A proposed causal positive transport with a terminal flux is not a new FU mechanism: its exact
  prefix-flux accounting is already the discrete Abel identity
  `suzukiCheckpointCriticalVariationAction_eq_initial_add_incrementSum`.  Applied to the actual
  source, its sole non-source-free term is exactly the Mertens-deviation variation action
  (`ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_riemannHypothesis`).  Thus a
  transport construction helps only if it adds a new source-faithful *inequality* on that flux;
  repackaging the flux as a queue, matching, or terminal charge does not move the route.
- The apparent autocorrelation/spectral-factor bridge is also already closed at its strongest
  source-faithful level: the exact FU triangular weight is a positive marked direct mixture of
  literal interval-head autocorrelations
  (`ccmGuinandWeilThirdGradeCesaroTriangularWeight_eq_fixedRectangularMixture`), and Fubini keeps
  prime and polar terms coupled in the resulting marked rectangular current
  (`ccmThirdGradeCesaroMarkedRectangularPrimePolarCurrent_eq_fubini`).  Passing to one abstract
  spectral factor cannot add a sign inequality; it only hides this already exact signed direct
  integral.  Any advance must control the actual coupled rectangular current, not realize its
  positive kernel again.
- The candidate "retain a first-moment affine charge" is already subsumed by the literal
  central affine weld.  The exact FU source is a positive marked mixture of central affine
  remainders (`ccmGuinandWeilThirdGradeCesaroAnchoredErrorMoment_eq_neg_half_centralAffineMixture`);
  each remainder is a Xi-screw codiagonal plus a purely archimedean Lerch defect
  (`ccmFUCentralRectangularAffineRemainder_eq_two_mul_xiScrewCodiagonal_add_lerchDefect`), and
  that defect is uniformly bounded (`exists_nonnegative_uniform_bound_ccmFUCentralGammaLerchAffineMixture`).
  Uniform control of the surviving codiagonal mixture is equivalent to the FU moment bound and
  hence RH (`ccmGuinandWeilThirdGradeCesaroAnchoredMomentBound_iff_xiScrewCodiagonalMixtureBound`).
  Therefore an affine first-jet rewrite has no independent leverage: a valid new producer must
  impose a new signed inequality on this literal codiagonal mixture, not re-center its cells.
- **Scalar rectangular-Euler inversion is closed as a no-go (new, Lean closed).** The literal
  marked FU measure sends the unbounded affine-normalized quadratic source
  (q_b(t)=(t-b)^2) exactly to
  (32(1/b-1/H)^2) for every (0<b\le H)
  (`CCMFUSuzukiRectangularEulerNoGo.lean`,
  `rectangularMixDensity_quadratic_codiagonal`).  This response is uniformly bounded by the
  fixed lower wall even though (q_b) is unbounded. Whole-route consequence: no scalar
  Volterra/Euler inversion can obtain source control from the FU reporter bound alone; a
  surviving argument must exploit a literal prime--polar/divisor relation that excludes this
  quadratic invisible mode while preserving the signed cancellation.
- The corpus already has exact Vaughan decompositions and nonstationary exponential-sum envelopes,
  but their tested phase is `ndPhaseExp T r n = exp(2πi·T log(1+r/n)/(2π))` with the essential
  hypothesis `0 < r` (`exists_norm_sum_vonMangoldt_ndPhaseExp_le_secondThird_mixed_hybrid`).
  No CCM or Suzuki module contains an identity from the literal third-grade prime--polar window
  to this phase family.  Thus this sieve technology is not yet a FU producer: it lacks a
  source-faithful bridge and its derivative estimates exclude the nonoscillatory `r = 0` channel.
  Any attempt to import it must first prove that bridge while retaining the polar continuum;
  applying its norm bounds directly would change the problem.
- G-CE's finite source-native self-adjoint completion is not a debt-cancellation mechanism.  On
  one strictly cofinal depth schedule its actual source budget converges to
  `4 + mobiusGammaXiCoupledErrorSingularGraphDebt`
  (`exists_mobiusGammaXiCoupledErrorFiniteSelfAdjointBoundaryTransport`), and the debt vanishes
  iff RH (`mobiusGammaXiCoupledErrorSingularGraphDebt_eq_zero_iff_rh`).  Thus the positive
  singular graph leg faithfully transports, rather than removes, the obstruction.
- Scalar cancellation is fully exhausted in G-CE.  For every bounded complex-linear scalar
  controller, cancelling the actual charge is equivalent to `RH ∨ T = -I`
  (`mobiusGammaXiDebtController_cancellation_iff_rh_or_eq_opposite`).  The unconditional `-I`
  branch erases every scalar source and transfers twice the original debt to its hidden port
  (`mobiusGammaXiOppositeDebtController_exactPhysicalCancellation`).  It cannot be counted as a
  source-selective cancellation.
- The existing pre-scalar affine prime--polar--Gamma packet already lands coefficient-faithfully
  on the actual finite G-CE base response
  (`mobiusGammaXiPreScalarAffineBoundaryRenormalization_eq_sourceResponse_base`).  Its pure
  marked commutator port vanishes identically at zero clock
  (`mobiusGammaXiPreScalarAffineProducer_zeroClock_oddJet`), so no construction factoring through
  that port can provide the missing base-charge partner.  Contractive Sonin boundary transport
  lands on the same Ward coefficient, not a new signed term
  (`exists_soninContractivePreScalarAffineCriticalBoundaryRenormalization`).
- The apparent real-antilinear G-CE escape is now closed.  Schwarz pairing makes the literal
  completed Ward response real at every positive real node
  (`im_continuedXiAntiCausalWardResponse_of_real`).  Hence the reflection `z ↦ -conj z` cancels
  the entire physical real Ward ray, rather than selecting the critical charge; at that charge it
  pays one debt and puts exactly `2|d|²` in the hidden antisymmetric port
  (`mobiusGammaXiRealReflection_exactPhysicalRayErasure`).  This is a new no-go: real reflection
  cannot serve as a source-faithful pre-scalar G-CE producer.
- The scalar no-go is now exhaustive even for real-linear, not merely complex-linear, controllers:
  cancellation of the actual critical charge is exactly `RH ∨` erasure of every real physical Ward
  value (`mobiusGammaXiRealLinearDebtController_cancellation_iff_rh_or_physicalRayErasure`).
  Thus anti-linear mixing cannot supply the missing G-CE channel; a viable mechanism must be
  genuinely non-scalar before the Ward readout.
- The apparent non-scalar Euler lead is pointed-only.  The literal pre-scalar reporter splits
  orthogonally into radial and transverse four-unit records
  (`eulerPositivePreScalarGamma_orthogonal_four_plus_four_law`), but the transverse record reports
  only the normalized current difference and is exactly zero at the base node
  (`eulerPositivePreScalarGraphNormalizedCoefficient_transverse_zero`,
  `eulerPositiveTransverseGammaXiPointedReporter_eq_continued_sub_base`).  It cannot alter the
  absolute G-CE charge `d`; restoring the anchor necessarily reintroduces the radial record.
  Consequently, a G-CE advance needs a literal nonzero zero-clock complementary channel with an
  exact *signed cross-form* against the completed source, not another pointed reporter, positive
  completion, or scalar controller.
- Enlarging the transverse reporter to its full natural Hardy half-plane does not alter that
  conclusion.  At every admissible complex moving node its exact readout remains the pointed
  difference `trace(endpoint) - trace(base)`
  (`eulerPositiveTransverseGammaXiHardyPointedReporter_eq_continued_sub_base`), never an absolute
  base readout.  The only existing coefficient-faithful zero-clock completion adds the forced
  nonright-canonical-product correction
  (`mobiusGammaXiPreScalarAffineBoundaryCorrection_eq_forcedDifference`), hence is divisorial
  rather than a new literal pre-scalar channel.  Moving an anchor alone cannot supply the missing
  G-CE partner.
- Broad 2026 arXiv searches on `Krein`, `Schur`, `boundary`, `operator`, `spectral`, and
  `renormalization` yielded no transferable source-preserving cancellation theorem.  Search hits
  were either unrelated or positive/renormalization frameworks that would replace the signed
  prime--polar current.  No external mechanism was imported.
- The reduced first-clock Julia equilibrium Gram does restore literal cross-prime correlations,
  but only in the forward capacity direction: a negative attenuated packet forces its squared
  excursion into the coherent bad-prime energy
  (`ccmFirstClockJulia_negative_attenuatedCompletedPacket_forces_badCoherentEnergy`).  No Lean
  theorem bounds that energy from above by the continuous budget or identifies it with the
  third-grade/actual-head source.  Therefore PSD Julia coherence is a necessary certificate of a
  negative first-clock excursion, not a CCM-FU/O control mechanism.  Any reuse needs a new
  source-faithful reverse estimate; pointwise or Gram positivity cannot provide it.
- The source-selected complex-Dirac self-polarization is also not a positive completion: for
  every nonempty finite prime-power packet and positive shear time, its determinant response is
  strictly negative at every nonzero spectral frequency and vanishes only at the center
  (`ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse_neg_iff`).
  Thus lifting the two real phase coordinates and then scalarizing atomwise reverses the desired
  sign.  A phase-based producer would have to retain genuinely cross-frequency (not merely
  cross-prime or per-atom self-polarized) coupling through the source readout.
- On literal canonical Gamma--Slepian heads, the reverse-prime inequality is exactly the
  nonnegativity of the completed-error defect balance
  (`ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_completedErrorDefectControl`):
  full form energy plus the completed-error scalar and prime translation defect must dominate the
  polar autocorrelation defect.  That balance is also the ground floor times head mass plus the
  certified nonnegative vanishing truncation tail
  (`ccmRestrictedWeilCanonicalGroundHead_completedErrorDefectBalance_eq_ground_add_tail`).
  Thus improving head convergence cannot remove the obstacle; new work must sign the exact-ground
  balance itself while retaining the prime--polar coupling.
- The apparent endpoint-coefficient gap in coherent Suzuki transport is closed exactly, not
  asymptotically: outgoing minus incoming plus `Λ(X)/√X` is the normalized completed Chebyshev
  error (`unitRieszCoherentBoundaryJump_eq_normalizedChebyshevError`), and the induced cofinal
  transport is coefficient-faithful.  Its remaining boundedness demand is still the literal
  prime--polar source bound, so endpoint repair cannot be counted as an independent FU producer.
- [NO-GO] Position torque cannot control Suzuki's two-jet source sign away from exact
  parity-energy balance.  At fixed torque, the Schur numerator realizes every real value
  (`suzukiParity_twoJetSlack_surjective_at_fixed_torque`); the missing term is the local
  tilt-asymmetry.  Hence bounded actual boundary torque cannot supply the FU/O reverse-prime
  inequality without a new source cross-form that controls this independent coordinate.
- G's sliding source-rectangle construction is an exact finite source receiver: translation
  averaging produces the triangular Ward annulus and its full `3π` charge
  (`card_mul_three_pi_le_xiWardSlidingSourceRectangleAnnulusEnergy`).  Poisson dissipation reduces
  its obstruction to a uniform upper bound for literal narrow-line prime--polar--Gamma rectangle
  energy (`card_mul_three_pi_le_xiWardSlidingSourceRectangleNarrowEnergy`).  Rademacher cell signs
  prove only a zero-side randomized coercivity and are not source-realizable; this upper bound is
  therefore the genuine one-scale Ward frontier, not an already solved positivity statement.
- The sliding Ward receiver is not yet a canonical arithmetic producer.  Its narrow energy is a
  functional of four arbitrary maps `z₁ z₂ z₁' z₂' : ℝ → ℂ`, while the packet identities which
  give the `3π` charge are explicit hypotheses of
  `card_mul_three_pi_le_xiWardSlidingSourceRectangleNarrowEnergy`.  Exhaustive uses of that
  functional occur only in its receiver/budget modules; no source-defined moving rectangle family
  is present.  Thus an upper bound for arbitrary maps would be the wrong claim.  A valid G advance
  must first construct a zero-independent contour family that has the packet-realization law, then
  bound that particular source functional.
- The existing G-CE “coefficient-faithful source contour” cannot fill this producer gap: its
  integrand explicitly contains
  `xiFiniteCoefficientInterpolant (xiCClosedRectangleZeros z₁ z₂) target`
  (`normalizedXiFiniteCoefficientSourceContour`).  It is an exact finite divisor-adaptive
  interpolation device, and its proposed strict subquantum law is formally equivalent to RH
  (`xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum_iff_riemannHypothesis`).  Whole-route
  consequence: finite Lagrange lifting is a receiver/normalization theorem, not a lawful
  arithmetic cancellation mechanism; importing it into G would conceal the missing source
  producer rather than remove it.
- **Abel-boundary resonance (formalized in
  `HedenmalmExteriorCayleyAbelGreenLanding.lean`; direct check, `.olean` emission, and axiom
  audit passed).**  Direct substitution of
  `realCayley x = (x-i)/(x+i)` into
  `sourceCayleyAbelGreenMultiplier` gives
  \(M_R(x)=-4/((1+R)x+i(1-R))\), hence
  \(|M_R(x)|^2=16/((1+R)^2x^2+(1-R)^2)\).  For every `0 < |x| < 1`, the denominator has its
  strict interior minimum at \(R_*=(1-x^2)/(1+x^2)\); there
  \(|M_{R_*}(x)|^2=(1+x^2)|M_1(x)|^2\).  Thus the source-safe Abel family overshoots its
  exterior boundary energy before reaching it.  Whole-route consequence: no argument based on
  monotone transport of a safe-radius energy bound can close G/G-CE.  The usable new target is
  signed control of the explicit radius defect
  \((1-R)((3+R)x^2-(1-R))\), whose sign changes across the resonant scale; absolute estimates
  destroy exactly the cancellation needed for moving-boundary transport.
- **First-phase rigidity (formalized in
  `MobiusCriticalComplexPhaseHermitianGram.lean`).**  The centered infinitesimal imaginary
  source-phase coefficient is exactly `(I / 2)` times
  `infiniteMobiusCriticalFisherTangentWeight`
  (`infiniteMobiusCriticalCenteredImaginaryPhaseCoefficient_eq_i_half_fisher`); it is therefore
  not an independent source direction.  The audited complex source-to-Xi landing is for this
  Fisher tangent, while the generic packet Julia derivative accepts arbitrary target nodes and
  still requires their rectangle realization.  Whole-route consequence: neither first phase
  motion nor generic packet transport supplies G's zero-independent common-clock producer; a
  viable producer must introduce a nonseparable source operation with a new arithmetic landing.
- **Shared-ghost branch closed.**  The exact bilateral cubic completion reduces its indefinite
  packet to one shared rank-one ghost, but a source/Gamma-natural shared scalar satisfying the
  two retained prime labels `2,3` exists only at neutral grade
  (`primeGammaTwoThreeSharedInverseOrientedGhostWard_iff`); global descent is equivalent to RH
  (`everyFrankensteinSourceSelectedGammaWardSharedGhostDescends_iff_riemannHypothesis`).
  Whole-route consequence: a single Gamma/polar ghost cannot short the amplified bilateral
  cubic credit.  Any surviving pre-scalar producer must retain non-scalar primitive-index
  covariance through continuation.
- **Reflected radial Wirtinger law (scratch-certified).**  For the literal reflected conormal
  feature (M(\rho,r)=\overline{r\exp(- (\rho-\tfrac12)r)}), the unconditional Lean calculation
  gives \(\bar\partial_\rho M=-rM\).  It is the sole non-holomorphic leg of the pre-scalar
  quadratic source; the completed trace is holomorphic only in its initial zero-free half-plane,
  while its divisor poles lie beyond that boundary.  Whole-route consequence: the resulting
  oriented current reweights the already-positive residue form by `r`, but cannot by itself
  establish the missing signed completed-source bound.  The real remaining problem is a
  pole-crossing identity that retains the completed prime--polar cancellation.
- **A.e. literal-edge admissibility (formalized).**  The complete centered Xi divisor is
  countable, so each of its real and imaginary projections is countable.  Therefore every
  injectively moving vertical edge with fixed endpoints strictly in
  \((-\tfrac12,\tfrac12)\), and every injectively moving horizontal edge remaining in that
  strip, is `XiExplicitAdmissible` along its entire finite edge for almost every parameter
  (`XiWardAERectangleAdmissibility.lean`).  Whole-route consequence: a continuous
  source-defined transverse-band family need not select zero-free contour levels; the bad
  parameters are rigorously null.  This removes only the edge-selection obstruction.  It does
  not provide the two-parameter response identity, control moving height cutoffs, or bound the
  resulting source energy, which remain the RH-bearing G obstacles.
- **Canonical transverse coarea scan (formalized).**  The source-defined chart
  \(\theta(t)=\tfrac14+\arctan(t)/(2\pi)\) is a strict bijective coordinate from the scan line
  to \((0,\tfrac12)\).  For every strict-right transverse displacement \(a\), the literal lower
  spectral ordinate \(-a\) lies in the canonical lower-half band
  \([ -\theta(t+L),-\theta(t)]\) iff
  \(t\in[\theta^{-1}(a)-L,\theta^{-1}(a)]\); that selector has exact parameter length \(L\).
  The band endpoints are source-defined, strictly interior, and compatible with a.e. contour
  admissibility (`XiWardCanonicalTransverseScan.lean`).  Whole-route consequence: G now has a
  zero-independent transverse selector with equal scan-interval width, rather than only
  zero-adaptive slab widths.  The surviving hard core is height-direction closure: prove a source response for the
  all-height moving rectangles and a cofinal upper bound without losing prime--polar--Gamma
  cancellation at the moving horizontal cutoffs.
- **All-height source obstruction identified.**  The completed prime--archimedean trace is
  unconditionally the *full* relative resolvent, while the raw strict-right Ward response is that
  full trace minus `logDeriv xiNonrightCanonicalProduct` plus the Schwarz boundary symbol
  (`continuedXiAntiCausalWardResponse_eq_full_sub_nonright`).  Hence replacing finite rectangles
  by one scalar full-height source evaluation cannot select the strict-right divisor: it silently
  drops the complementary factor.  Whole-route consequence: the all-height producer must retain
  contour geometry (or an equivalent non-scalar projector); scalar source completion is not a
  valid shortcut.
- **Precise remaining cap datum.**  `exists_horizontal_xi_bound` proves only an *unweighted
  signed imaginary* horizontal integral of `logDeriv xi` is `O(log T)` on a zero-free height.
  It does not bound the complex Cauchy-weighted cap, nor its partial primitives.  A Cauchy factor
  supplies formal `O(1/T)` decay, but promoting that to a cap limit would require uniform signed
  control of the completed prime--polar trace on every subinterval before the Cauchy weight is
  varied.  Whole-route consequence: the genuine G height-closure lemma is a coefficient-faithful
  **weighted partial-horizontal cancellation** law; an absolute-value edge bound or the existing
  unweighted count bound cannot supply it.
- **Schwarz cap kernel exact law (formalized).**  On canonical lower cap points
  \(x-i\theta(s)\) and \(-x-i\theta(s)\), the literal Ward-weight difference is exactly
  \[
    \frac{-4i\tau}{(\frac{51}{100}+\theta(s)+i(\tau+x))
      (\frac{51}{100}+\theta(s)+i(x-\tau))}.
  \]
  At the moving resonance \(\tau=x\), its second denominator is the fixed positive transverse
  distance, not a large-height factor (`XiWardSchwarzCapKernel.lean`; direct check, `.olean`
  emission, and axiom audit passed).  Existing paired Hilbert/Schwarz source-vector results do
  not identify a completed prime--polar horizontal cap with this kernel.  Whole-route
  consequence: raw Schwarz pairing cannot supply the missing uniform pointwise cap decay; the
  only viable G height-closure target remains a literal source-level weighted partial-horizontal
  cancellation theorem, preserving the completed trace through the height integration.
- **All-height canonical cap admissibility (formalized).**  For every injective moving height
  level in the open centered strip, the *entire* horizontal line is `XiExplicitAdmissible` for
  almost every parameter, because the preimage of the countable set of Xi-zero imaginary
  coordinates is countable.  Applied to \(-\theta(s)\), this gives an a.e. source-defined
  lower cap line with no finite-height truncation (`XiWardAllHeightCapAdmissibility.lean`; direct
  check, `.olean` emission, and axiom audit passed).  Whole-route consequence: G no longer has
  a contour-selection barrier at all heights.  Any remaining failure to close the cap is
  necessarily an analytic signed-cancellation failure of the literal completed trace, not an
  unlicensed choice of zero-free edges.
- **Literal Schwarz source-pair factorization (formalized).**  On that same conull family of
  canonical cap levels, at every height and observation frequency, the actual reflected
  completed prime--polar--Gamma cap pair equals the two-pole Schwarz kernel times one *unaltered*
  `continuedPrimeArchSourceRelativeTrace` value
  (`XiWardSchwarzCapSourcePairing.lean`; direct check, `.olean` emission, and axiom audit
  passed).  The identity uses the exact source reflection, not a spectral sum.  Whole-route
  consequence: source-level pairing is no longer a missing bridge.  The one remaining G cap
  datum is now exact and irreducible: a cofinal signed bound for the height integral of this
  two-pole kernel against the literal completed trace.  The resonant kernel law precludes
  replacing that datum by pointwise two-pole decay.
- **Finite cap semantics completed (formalized).**  The factorized kernel is continuous at every
  height (both denominators have fixed positive real part), and every finite symmetric cap on
  the conull canonical family is interval-integrable against the literal completed trace.  The
  reflected source cap integral equals exactly that factorized integral
  (`XiWardSchwarzCapKernel.lean`, `XiWardSchwarzCapSourcePairing.lean`; direct checks, `.olean`
  emissions, and axiom audits passed).  Whole-route consequence: the remaining cofinal claim
  cannot be dismissed as undefined contour algebra or hidden non-integrability.  It is precisely
  the uniform signed behavior of these genuine finite source integrals as the cutoff and
  observation frequency move together.
- **Cap anti-Schwarz law (formalized).**  The literal paired Ward kernel satisfies
  `K_{tau,s}(-x) = -conj(K_{tau,s}(x))`
  (`XiWardSchwarzCapReflection.lean`; scratch check, isolated `.olean` emission, and axiom
  audit passed).  `XiWardSchwarzCapRealCharge.lean` then formalizes the source-pair and
  factor-density conjugate symmetry on the conull canonical-cap family, with its own `.olean`
  emission and standard-axiom audit.  Its factorized density is
  `K(-x) S(-x-i theta) = conj(K(x) S(x-i theta))`.
  Whole-route consequence: the symmetric cap is a real signed charge, not an odd integral that
  reflection can kill.  Thus parity is a closed no-go for the cofinal bound; any surviving
  height closure must control its real signed local mass near the moving resonance.
- **Half-cap reduction (formalized).**  The same module now proves, with no cutoff-sign or
  source-bound premise, that every factorized symmetric cap is exactly twice the real integral
  over its positive half.  This uses only finite interval-integrability and the literal
  conjugate-even source density (`ae_forall_xiWardSchwarzCapFactorIntegral_eq_two_re_half`; direct
  `.olean` emission and standard-axiom audit passed).  Whole-route consequence: cancellation
  between the two reflected cap halves is not available.  The precise G analytic problem is a
  uniform signed bound for one real positive-half current through its moving Cauchy resonance.
- **Pointwise source-control no-go (verified in existing Lean).**
  `continuedPrimeArchUpperImBoundedAbove_iff_riemannHypothesis` proves that merely imposing a
  finite global upper bound on the continued completed-source imaginary part throughout its
  pole-free upper half-strip is equivalent to RH.  Whole-route consequence: neither the G cap
  nor CCM-FU can obtain its required signed-window cancellation from a generic one-sided or
  pointwise completed-source estimate; that would conceal the desired theorem itself.  The
  estimate must use the exact observer/window geometry and preserve prime--polar--Gamma
  cancellation.
- **CCM-FU literal-cancellation boundary (verified in existing Lean).**
  `increment_rieszTail_eq_completedPrimePolarGamma_window` identifies the transported
  prime-free FU tail with the actual completed von-Mangoldt--polar--Gamma Riesz window before
  any estimate.  The subsequent first-moment Abel theorem proves that linear control of the
  *literal* weighted signed-curvature prefixes would bound the triangular FU reporter and hence
  imply RH.  Whole-route consequence: the literal cancellation bridge is already closed; the
  irreducible FU datum is the signed first-moment/barycenter control, not another transform or
  a separated prime/polar estimate.  It is distinct from G's cap current, so combining their
  conclusions without a source-faithful bridge would be invalid.
- **Two-dimensional transverse-current reframe is already exhausted by G (verified in existing
  Lean).**  The canonical transverse scan, a.e. moving-rectangle identities, and
  `card_mul_three_pi_le_xiWardSlidingSourceRectangleNarrowEnergy` already turn the full
  two-dimensional rectangle current into a coefficient-faithful `3*pi` charge for every
  strict-right finite packet.  Poisson dissipation reduces it to the narrow completed-source
  energy.  Whole-route consequence: promoting the transverse parameter does not create a new
  producer; that exact coarea construction is already the established G receiver.  Its remaining
  upper bound is genuinely new source information, not a missing contour or scan identity.
- **Resonant real/imaginary quadrature (formalized).**  Put
  \(a_s=51/100+\theta(s)>0\).  The literal Schwarz-paired cap kernel at its moving
  resonance has the exact coefficients
  \[
    \Re K_{x,s}(x)=-\frac{8x^2}{a_s(a_s^2+4x^2)},\qquad
    \Im K_{x,s}(x)=-\frac{4x}{a_s^2+4x^2}.
  \]
  Consequently the actual unaltered completed-source density is exactly
  \[
    \Re(K_{x,s}(x)S)=
    -\frac{8x^2}{a_s(a_s^2+4x^2)}\Re S+
    \frac{4x}{a_s^2+4x^2}\Im S,
  \]
  where \(S=\mathrm{continuedPrimeArchSourceRelativeTrace}(x-i\theta(s))\).
  The real coefficient is zero at the central height and strictly negative at every other
  height (`XiWardSchwarzCapResonantQuadrature.lean`; isolated source `.olean` emission and
  standard-axiom audit passed).  Whole-route consequence: the existing critical-locus
  imaginary-source reserve cannot by itself determine the moving-resonance G current.  A genuine
  G producer must establish a source-faithful cross-quadrature law or a signed bound on the real
  completed source in this exact geometry; replacing it with an imaginary-only estimate would
  leave an uncontrolled nonzero term.
- **Log-modulus transport (formalized).**  On the same conull canonical cap family,
  \[
    \Re\,\mathrm{continuedPrimeArchSourceRelativeTrace}(x-i\theta(s))
    =\frac{d}{dx}\log\lVert\Xi_C(x-i\theta(s))\rVert.
  \]
  Substitution into the resonant quadrature gives an exact actual-source current consisting of
  the explicit negative real coefficient times this Xi log-potential derivative, plus the
  explicit imaginary-source term (`XiWardSchwarzCapLogModulusCurrent.lean`; isolated source
  `.olean` emission and standard-axiom audit passed).  Whole-route consequence: G's residual
  real channel is now a coefficient-faithful divisor-potential transport problem.  This creates
  a lawful integration-by-parts target, but does not give its cofinal bound: available Xi decay
  is an upper bound and does not control the lower log modulus near the zero divisor.
- **Generic Hilbert/Cauchy recovery does not land (verified in existing Lean).**  The corpus gives
  local analyticity of `logDeriv XiC` on each admissible cap line, while
  `FokasLenellsCauchyExtension` is an arbitrary `SoninL2` Cauchy transform.  No theorem supplies
  a global pole-free strip, a Hardy/L2 boundary norm for this literal completed source, or an
  identification of that source with the generic Cauchy carrier.  Whole-route consequence: an
  imaginary-source reserve cannot be promoted to the required real-channel bound by importing
  Hilbert-transform theory alone; any such bridge must first prove new source-faithful global
  pole-distance or log-potential control.
- **Canonical divisor-detection law (formalized).**  For every `XiZeroCopy` with
  \(\Re\rho>1/2\), set \(a=\Re\rho-1/2\in(0,1/2)\) and take the canonical scan parameter
  \(s=\mathrm{xiWardTransverseCoordinate}(a)\).  Lean now proves
  \[
    \mathrm{xiWardLowerCapPoint}\bigl(s,\Re\,\mathrm{xiSpectralPoint}(\rho)\bigr)
      =\mathrm{xiSpectralPoint}(\rho),
  \]
  hence that literal lower-cap point is a zero of `XiC`
  (`XiWardSchwarzCapDivisorDetection.lean`; isolated source `.olean` emission and standard-axiom
  audit passed).  Whole-route consequence: the canonical source scan detects every possible
  RH-counterexample zero.  A uniform zero-free, positive-distance, or lower-log-modulus estimate
  over its full foliation is therefore RH-bearing; a valid G producer must instead exploit the
  exact moving signed geometry without silently imposing such a uniform avoidance condition.
- **CCM-FU has one irreducible arithmetic action (verified in existing Lean).** After exact
  critical rescaling and Abel summation, the third-grade Suzuki curvature transform differs from
  a uniformly bounded source-free Gamma/harmonic action by precisely
  `suzukiCheckpointCriticalVariationAction suzukiCheckpointCriticalMertensDeviation`.
  Its uniform bound is formally equivalent to RH
  (`CCMFUSuzukiCriticalRemainderVariation.lean`,
  `ccmFUSuzukiCriticalMertensDeviationVariationActionBound_iff_riemannHypothesis`). The
  deviation is exactly the compensated pair ψ-error-at-endpoint divided by endpoint minus its
  full future \(t^{-2}\) tail. Whole-route consequence: neither Gamma control, scalar critical
  convergence, nor another local prime--polar matching can close CCM-FU. A valid new producer
  must control this *coupled moving Abel action* without splitting its endpoint from its tail.
- **Cross-route landing is exact, but does not solve the action (verified in existing Lean).**
  `unitRiesz_center_eq_weightedSignedCurvature_add_arch` identifies the weighted signed-curvature
  prefix with the central CCM-UR/HG completed barycenter plus an explicit archimedean
  renormalization. A uniform natural-aperture barycenter bound would therefore close CCM-FU and
  imply RH (`SuzukiFirstMomentTriangularAbelTransfer.lean`). Whole-route consequence: CCM-FU and
  CCM-UR/HG share the same missing signed first-moment coherence; Route O's absolutely summable
  quadratic head current is not a lawful substitute because its damping removes this moment.
- **Bounded-memory cancellation is closed (verified in existing Lean).** A critical block
  containing a sufficiently large prime cannot have nonpositive mass unless its span grows at
  least \(\log p/2\); fixed one- or two-sided transport radii consequently fail cofinally
  (`CCMFUSuzukiCriticalTransportRangeNoGo.lean`,
  `CCMFUSuzukiCriticalBidirectionalTransportRangeNoGo.lean`). Whole-route consequence: any
  surviving CCM producer must be a genuinely growing-range, coefficient-faithful transport or
  phase-coherence law. Finite-window positivity, reordering, and fixed-light Suzuki cells are
  ruled out as closure mechanisms.
- **Every moving isometric carrier preserves the eight-unit Euler cost (new proof term; project
  audit pending restored dependency cache).** For any critical-parameter-dependent family of
  linear isometries, the literal squared full-Euler source norm is preserved pointwise, hence its
  limit remains \(8\); canonical cofinal Sonin embeddings are a specialization
  (`EulerPreScalarGammaCofinalSoninIsometryNoGo.lean`). Whole-route consequence: no isometric
  change of carrier can remove the four-unit debt. Any G-CE survivor must alter signed source
  incidence through a non-isometric relative channel before positive Gram energy is formed;
  carrier transport alone is closed.
- **Damping-Gram-faithful compression is also closed (new checked proof term; project audit
  pending restored dependency cache).** If a bounded same-carrier map preserves the complete
  source--damping Gram coefficients after acting on both source and every nonnegative critical
  damping state, totality forces \(T^*T\) to fix the literal source, so its squared norm is
  unchanged (`norm_sq_map_eulerPositivePreScalarGammaSource_of_dampedGram`). Whole-route
  consequence: a non-isometric reweighting is not enough when it preserves the full original
  incidence. A G-CE survivor must modify which source--test pairings enter the Gram formation,
  not merely compress their shared carrier.
- **Canonical two-leg source-normal repair is inadmissible (verified in existing Lean).** Its
  physical multiplier is exactly the prime, and already its exponent-zero restriction has
  divergent squared Gamma weight; hence it cannot enter the Hilbert graph domain
  (`SuzukiCausalDepthGammaTwoLegSourceNormalGraphDomainNoGo.lean`). Whole-route consequence:
  the sole algebraic escape from the damping-Gram no-go cannot be implemented by canonical
  source-normal deattenuation. Any surviving two-leg incidence must use a different,
  source-faithful unbounded-domain law and prove its graph admission rather than assume it.
- **Abstract pre-quasi two-leg geometry is not a new producer (verified in existing Lean).**
  `HilbertPreQuasiPair` already supplies closed, dense, pairing-preserving two-leg singular
  pairs, including a proper graph defect. But the actual full-source, momentum-symmetric
  Hedenmalm theta form has no ordinary-\(L^2\) pre-quasi realization
  (`PreQuasiGelfandTwoSidedSingularDefect.lean`,
  `HedenmalmThetaOrdinaryL2PreQuasiExclusion.lean`). Whole-route consequence: replacing a
  Hilbert carrier by an abstract two-leg graph does not land the arithmetic source. A valid
  distributional/finite-head arena must provide a new literal source map and cannot silently
  reuse ordinary \(L^2\) full-source Gram realization.
- **Fixed-affine SP-E compensation is closed (verified in existing Lean).** Once a constant
  affine correction cancels the transition-core scale, its residual is exactly a scalar multiple
  of aligned completed Gamma energy: negative coefficient is RH-equivalent, zero erases the
  source, and positive coefficient gives a vacuous nonpositive upper bound
  (`SuzukiFixedAffineSignedCompensationClassification.lean`). Whole-route consequence: no
  constant coefficient can provide missing cancellation; surviving SP-E/CCM-FU work must retain
  a non-affine, source-labelled relative term.
- **Growing-rank positive fission is closed as a cancellation mechanism (verified in existing
  Lean).** The Cartan logarithmic fission has a uniformly bounded cubic remainder, but its
  completed observable is the literal positive transition core plus a nonnegative remainder and
  still escapes cofinally (`SuzukiTransitionCoreGrowingRankCartanFission.lean`). Whole-route
  consequence: nonlinear finite-rank completion can regularize an error without changing signed
  source order; a genuine producer must introduce an exact signed cross-pairing with continuum
  increment and retained prime history before scalarization.
- **A scalar SP-E coboundary is only a renaming (verified from exact Lean identities).** The
  cumulative quarter-dilation increment is identically
  `unitRieszCoherentCompletedOutgoingCharge N - unitRieszCoherentCompletedOutgoingCharge 2`;
  its uniform bound is already equivalent to RH
  (`SuzukiCompletedOutgoingDilationBalance.lean`). Whole-route consequence: writing the
  increment as a bounded scalar causal state cannot be a new mechanism. Any valid reframe needs
  a genuinely non-scalar source observable whose boundedness does not collapse to this partial
  sum.
- **Canonical two-leg completed-source shorting is identically zero, even across distinct Xi
  labels (verified in existing Lean).**
  `suzukiTransitionCoreCompletedSourceEnvironmentBlock_short_eq_zero` has arbitrary `rho` and
  `tau`; it is not a same-fibre accident. Whole-route consequence: no bilinear two-leg residue
  Schur complement can supply the missing signed SP-E order. A surviving pre-scalar producer must
  be at least higher-relational than this canonical two-column environment and retain a literal
  prime--continuum source map.
- **The marked Volterra--Xi compound target is not yet source-faithful (Lean use audit).** The
  exact Bezoutian and midpoint theorems leave `x,X,y,Y,c` arbitrary; exhaustive Lean references
  occur only in those algebraic modules, with no map from `completedPrimePolarGammaAtom`, its
  Riesz window, or the completed outgoing charge. Whole-route consequence: its proposed
  prime--Gamma Gram factorization is presently an uninstantiated algebraic target, not a lawful
  producer. It must not be used to claim cancellation progress until a literal source map is
  constructed and verified.
- **Harmonic-to-Riesz second formation is fully classified and cannot be the missing bound
  (verified in existing Lean).** The literal completed source has absolutely summable zero
  harmonic charge, but the relative Riesz rate and its first difference are unbounded; only its
  second curvature is uniformly bounded. The resulting absolute drift-plus-history action is
  equivalent to RH (`SuzukiHarmonicRieszClockTransmutation.lean`,
  `SuzukiObserverJetFormationCompletion.lean`,
  `SuzukiObserverJetLinearActionClassification.lean`). Whole-route consequence: bounded clock
  curvature is kinematic only. Any survivor must use a source-specific signed relation not
  controlled by the absolute second-formation action; a generic clock-transmutation or Hardy--Green
  estimate cannot close CCM-FU/SP-E.
- **Third-grade Suzuki realization is already exact, not a remaining convergence gap (verified in
  existing Lean).** A common positive cofinal parameter schedule sends the connected finite
  Suzuki chord to the literal coupled third-grade prime--polar window with pointed error
  \(<1/(N+1)\) (`exists_suzukiConnectedChordThirdGradeLiteralCofinalSchedule`). At base wall
  one, uniform boundedness of the source-adaptive positive chord, matched-coverage seam, and
  completed quantile transport are pairwise equivalent (`CCMFUSuzukiHardCoreLanding.lean`).
  Whole-route consequence: another finite-head limit, cell-coordinate change, or quantile
  reassembly cannot be claimed as new CCM-FU control; all retain the same unbounded signed Abel
  datum.
- **Actual unbounded Suzuki resolvent has an exact positive graph-energy carrier (new, Lean
  closed).** `SuzukiTaActualResolventHerglotzEnergy.lean` proves that the normalized resolvent
  readout of `suzukiTaSelfAdjointExtension` has imaginary part
  \(\operatorname{Im}z(\|Ar\|^2+\|r\|^2)\), strictly positive for nonzero source in the upper
  half-plane. This uses the literal extension and its domain, not a finite spectral surrogate.
  Whole-route consequence: source-faithful Herglotz positivity is no longer blocked by absence of
  a resolvent carrier; the remaining hard datum is an exact comparison from this carrier to the
  finite Suzuki characteristic / completed prime--polar codiagonal that retains signed
  cancellation. Positivity alone cannot supply that comparison.
- **A nonreal self-adjoint deficiency resolvent has an exact Green-boundary quotient (new, Lean
  closed).** `DeficiencyResolventBoundaryQuotient.lean` proves
  \((A-z)^{-1}v=c-\langle w,v\rangle B(w,b)^{-1}b\), with `c` in the closure domain, whenever
  the adjoint eigenvector `w` has eigenvalue \(\bar z\) and its boundary pairing `B(w,b)` is
  nonzero. The literal Suzuki characteristic is already exactly this pairing in existing Lean.
  Whole-route consequence: a lawful resolvent-to-characteristic comparison can only fail through
  control of the closure component or of the source numerator; it cannot invoke an absent
  spectral-model bridge. Neither component has yet been related to the completed
  prime--polar codiagonal, so this does not furnish the CCM-FU bound.
- **Closure--spectral orthogonality is false on the literal Suzuki space (new, Lean closed).**
  `exists_suzukiTaMinimalClosure_inner_spectralVector_eq_one` constructs a vector in the minimal
  closure domain whose pairing with every spectral vector is exactly \(1\). Whole-route
  consequence: the Green-boundary quotient cannot be converted to a positive norm split by
  discarding its closure component. A surviving characteristic/resolvent argument must control
  the closure--source cross term while preserving prime--polar cancellation.
- **The Euler-deletion Möbius Gram cross criterion has no established CCM/G source transport
  (Lean use audit).** `EulerDeletionMobiusGramCancellation.lean` proves that a cofinally
  polynomial-log bounded raw Möbius Gram cross sum implies RH, after an unconditional logarithmic
  diagonal bound. Its sole open datum is that cross bound, and no Lean consumer identifies this
  raw Gram cross with the completed prime--polar codiagonal or the critical Ward response.
  Whole-route consequence: it is an auxiliary RH receiver, not evidence for signed cancellation
  on Route O, CCM-FU, or G; importing it as a producer would add an unproved source map.
- **Midpoint prime--polar positivity has no established Ward-debt transport (Lean use audit).**
  `criticalMellinMidpointCodiagonal_eq_completedError_sq` gives the exact nonnegative
  source-faithful midpoint codiagonal ½\(E(2a)^2\), with every non-midpoint readout retaining its
  explicit atom-square debt. Exhaustive joint searches find no declaration or consumer relating
  it to `continuedXiAntiCausalWardResponse` or its G singular-graph debt. Whole-route consequence:
  midpoint cancellation removes the *local atomic* debt only; it cannot be claimed to cancel
  G-CE's global \(|d|^2\) without a new literal transform identity.
- **Coupled-floor critical cancellation already lands coefficient-faithfully but does not bound
  the target (Lean use audit).** `CoupledFloorMobiusCriticalBoundaryCancellation.lean` proves
  strong critical-carrier convergence, and `CoupledFloorMobiusAffineRieszHandoff.lean` identifies
  its completed affine readout with the literal Möbius-divisor Abel source; the resulting uniform
  cofinal bound is proved equivalent to RH. `CoupledFloorMobiusTransitionCoreXiFission.lean`
  makes the remaining landing error inverse-square only after subtracting that same explicit
  error. Whole-route consequence: CFI solves convergence and source transport, not the signed
  bound. It cannot be reused as a new CCM-FU/G cancellation producer without a non-circular
  inequality for its literal readout.
- **Causal-depth Carathéodory positivity is not the sharp CCM trace block (Lean use audit).**
  `SuzukiRectangularWallGramGate.lean` gives literal von-Mangoldt diagonal cells and finite-packet
  PSD for the compact sharp wall kernel, while
  `xiGammaBoundary_fusedRectangle_ne_suzukiRectangularWallGramKernel_diagonal` proves the
  source-selected Gamma/fused rectangle remains nonzero outside that support. Its positive block
  also enters the assembled formula with coefficient \(-2\). Whole-route consequence: local
  Gamma--Euler positivity cannot supply the signed completed source inequality or be substituted
  for the sharp prime--polar trace; any compensation must be an exact global signed cross-form.
- **The Suzuki Weil--Robin connector is not yet source-instantiated (Lean use audit).**
  `SuzukiCausalWeilRobinGreenIdentity.lean` and
  `SuzukiAffineSewnWeilRobinFarTailFactorization.lean` quantify freely over endpoint jets
  `U,U'` and `weilExterior`; all three current consumers retain those variables. The file itself
  labels the integrations by parts and distributional identification as paper-level. Whole-route
  consequence: its exact denominator cancellation and far-tail no-go are valid algebraic
  constraints, but neither supplies an occurrence of the completed prime--polar source in the
  Robin/Gamma/holonomy carrier. The next lawful infrastructure task is an unconditional literal
  finite-hinge instantiation, followed by a separately proved cofinal distributional transport.
- **The completed restricted source already has an exact literal Xi-zero realization (Lean use
  audit).** `SuzukiCCMMixedScrewWeilBridge.lean` proves, for every strict interior complex test,
  `ccmRestrictedWeilForm_complexSmooth_eq_suzukiWeilDistribution`: the CCM restricted Weil form
  equals Suzuki's actual Hermitian-convolution Weil distribution, after an exact screw-form
  bridge. This is a stronger source-fidelity result than the real diagonal source identity, but
  it contains no causal endpoint/exterior map. Whole-route consequence: a successful Robin/Gamma
  producer may start from the literal Xi-zero/prime--polar source without any comparison premise;
  it still must construct a one-sided signed trace identity or lower bound. Repackaging the
  two-sided Weil form as a positive or spectral statement cannot discharge the Ward debt.
- **Mass-matched actual-head wall incidence is too small to pay the Ward debt (Lean use audit).**
  `CCMActualHeadMatchedOrientedWallLightIncidence.lean` gives a division-free, coefficient-faithful
  occurrence of each matched prime--polar cell as the signed Suzuki wall-light imbalance.
  `CCMActualHeadMatchedSignedControlProducer.lean` then proves its current has a quadratic-aperture
  gain and is absolutely summable, while
  `CCMActualHeadMatchedSuzukiTransitionCoreNoGo.lean` proves every range-block correction leaves
  the rectangular Ward defect tending to `-infinity`. Whole-route consequence: the source trace
  cannot be a fixed mass-matched cell sum. A valid assembly must preserve a genuinely
  unsummable atomic--continuous relative channel before quadratic matching; that relative
  boundedness is already RH-equivalent in the unit-Riesz representation, so it is a target, not
  an available estimate.
- **Direct negative-light payment leaves a forced divergent continuum residual (new, Lean
  closed).** `SuzukiWardCompletedLightResidualNoGo.lean` proves at spectral center
  
  \[
    \frac{\mathrm{regularWardMass}-\mathrm{negativeLightMass}}{\sqrt N}
      \longrightarrow \frac16,
  \]
  and hence this literal residual tends to `+infinity`, unconditionally. The exact unit-Riesz
  source is therefore positive light minus a still macroscopic regular residual, not positive
  minus negative light. Whole-route consequence: an FE-reflected light completion cannot be
  inserted by identifying its negative Gram with the regular continuum; any valid Robin/Gamma
  assembly must account for an additional signed relative channel of root scale before seeking a
  lower bound.
- **The literal all-gcd cross is irreducibly collective (Lean use audit).**
  `sum_mobiusDivisorGcdCross` identifies the sum over every common-divisor sector with the exact
  off-diagonal of the completed Möbius--divisor Abel source.  But
  `mobiusDivisorGcdCross_positive_unbounded` gives unbounded positive individual sectors, while
  `sum_mobiusDivisorGcdCross_eleven_lt_neg_oneHundredth` gives a negative total at the same
  finite cutoff where the coprime sector is positive.  Whole-route consequence: no componentwise
  gcd estimate, coprime-column estimate, or finite selection of sectors can be promoted to the
  required cancellation.  Any surviving CCM--FU producer must bound one simultaneous all-scale
  signed cross-form tied to the literal Abel source.
- **Prime-by-prime and independent-core control are excluded at their natural scales (Lean use
  audit).** `MobiusDivisorDilationMeanUniformCoreNoGo.lean` refutes a core-uniform one-step
  physical-renewal bound; `MobiusHalfSelectionGrowthObstruction.lean` refutes a fixed diagonal
  budget for independent half-subset averaging; and `MobiusDivisorCoareaOrderBarrier.lean` forces
  every complete one-prime order through a superquadratic coarea action.  Whole-route consequence:
  these statements do not rule out a raw endpoint-energy inequality, but they rule out proving it
  by uniform local insertion, independent randomization, or a bounded intermediate coarea
  potential.  The remaining mechanism has to preserve cancellation jointly before any
  intermediate norm or averaging operation.
- **The inclusive all-scale gcd PSD completion is superquadratic (new, Lean closed).**
  `MobiusDivisorInclusiveGcdGramNoGo.lean` factorizes its exact literal channel form into
  totient-weighted divisor sums of squares and proves
  \[
    \frac25\,\mathrm{latePrimeMass}(4N)^2\le G_{\gcd}(4N).
  \]
  `MobiusDivisorInclusiveGcdGramAsymptotic.lean` then proves
  \(G_{\gcd}(4N)/(4N)^2\to+\infty\), using the existing literal late-prime mass divergence.
  Whole-route consequence: no positive-semidefinite all-gcd preconditioner can be the missing
  CCM--FU signed-cancellation producer. Its positive survivor is an exact scale-resolved
  totient-square factorization; any viable global controller must retain signed cancellation or
  explicitly remove the late-prime diagonal by a source-faithful compensator.
- **Reflection-compatible scalar shorting cannot repair the opposite-radial source signature
  (new, Lean closed).** `XiWardCubicScalarShortingNoGo.lean` proves that every scalar multiplier
  covariant under functional-equation reflection and radial reversal preserves the exact negative
  norm-square of the signed completed conormal boundary product.  Whole-route consequence: the
  remaining polar--Gamma contraction cannot be a scalar boundary shorting; it must perform
  coefficient-faithful, nonlocal or matrix-valued oriented cancellation before continuation.
- **Literal outgoing quantile curvature has an exact signed-credit/debt law (new, Lean closed).**
  `CCMActualHeadOutgoingQuantileBarycentricDebt.lean` proves that every actual mass-quantile cell
  has quadratic Fourier curvature equal to its signed barycentric displacement credit minus its
  nonnegative squared-displacement debt, and that a finite block has nonnegative curvature only
  if its total signed credit pays the entire accumulated debt.  Whole-route consequence: neither
  Γ-head energy nor absolute transport work can close Route O; the missing cofinal producer must
  establish this precise unshorted signed credit inequality.  The next source-faithful bridge is
  a finite Stieltjes crossing identity between mass-clock cells and log-height atoms, retaining
  both intrusion and overshoot corrections.
- **Mass-clock/time-clock crossing is favorable and exact (new, Lean closed).**
  `CCMActualHeadOutgoingQuantileStieltjesCrossing.lean` proves, at every literal outgoing cutoff
  \(b_N\), that its finite quadratic moment is exactly
  \[
    \mathrm{completedSignedAction}_N-\mathrm{inwardArchimedeanLeakage}_N+
    \mathrm{crossingCredit}_N,
    \qquad \mathrm{crossingCredit}_N\ge0.
  \]
  The crossing credit is the explicit sum of log-time atoms intruding past the mass cutoff and
  the negative quadratic profiles of mass-clock atoms overshooting the log-time cutoff; neither
  is discarded or bounded absolutely. The same expression is the literal outgoing Fourier
  curvature, and nonnegative moment is equivalent to completed action plus crossing credit
  paying the full inward leakage. Whole-route consequence: Route O now has a source-faithful
  finite landing rather than a clock mismatch. The remaining hard datum is the cofinal signed
  inequality for this exact completed-action-plus-crossing expression; no Gamma-head or
  time-clock proxy can replace it.
- **The apparent inward archimedean leakage is exactly removable by source centering (new,
  Lean closed).** `CCMActualHeadOutgoingQuantileStieltjesCrossing.lean` now proves, for every
  real \(H\),

  \[
    \int_0^H e^{-h/2}(H^2-h^2)\,dh
      =2\int_0^H h\,2(1-e^{-h/2})\,dh.
  \]
  It also proves that the literal complex Stieltjes action is
  \(2\int_0^{b_N}hE(h)\,dh\), using only established local integrability of the actual prime
  staircase. Consequently the literal outgoing moment is exactly
  \[
    2\int_0^{b_N} h\bigl(E(h)-2(1-e^{-h/2})\bigr)\,dh+
      \mathrm{crossingCredit}_N,
    \qquad \mathrm{crossingCredit}_N\ge0.
  \]
  Whole-route consequence: the prior task “pay archimedean leakage” was a false decomposition;
  Route O's open core is solely a cofinal lower bound for this one threshold-centered, signed
  prime--polar action on actual quantile endpoints. This is neither a separate-prime estimate
  nor a Gamma-clock comparison.
- **The centered action and barycentric debt are now one exact literal invariant (new, Lean
  closed).** The terminal-mass action is pointwise an oriented polar tail from the quantile
  boundary of \(\lfloor e^h\rfloor+1\) to \(h\).  Lean proves
  \[
    \mathrm{terminalMassAction}_N+\mathrm{crossingCredit}_N
      =\mathrm{barycentricCredit}_N-\mathrm{squaredDisplacementDebt}_N.
  \]
  Consequently its nonnegativity is equivalent, at each finite actual head, to signed
  barycentric credit paying the complete squared displacement debt. Whole-route consequence:
  Route O has no residual mismatch between source, crossing, and geometry. The remaining
  cofinal producer must control this single signed invariant; independent Γ-head positivity,
  absolute terminal-mismatch bounds, and model-clock replacement cannot supply it.
- **Actual matched polar coverage has a finite adjacent codiagonal normal form (new, Lean
  closed).** `CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal.lean` proves
  \[
    \delta_{n+1}-\delta_n=U_n-L_{n+1}
  \]
  for the literal matched-to-quantile displacement, and rewrites every finite matched-minus-
  quantile block exactly as the signed sum of the oriented adjacent windows
  \(\int_{L_{n+1}}^{U_n}\) plus its two endpoint windows.  The proof works solely on strictly
  positive polar-mass intervals; it assumes neither continuity at the logarithmic coordinate
  singularity nor a sign/order for any matched cells. Whole-route consequence: the CCM--FU
  coverage problem is now a marked von Mangoldt--polar codiagonal pairing with the actual
  translation-defect profile.  A cellwise displacement corridor, absolute transport estimate, or
  proxy graph energy cannot control this pairing; a valid advance must bound its signed aggregate
  while retaining every overlap, gap, and boundary term.
- **Bare adjacent codiagonal has no scalar zero-clock charge (new, Lean closed no-go).** The
  same module proves that its profile-level codiagonal annihilates the constant function exactly:
  \(\mathcal C_K[1]=0\) for every finite literal head.  This follows from exact equality of
  each matched polar-cell mass and its quantile-cell mass, with telescoping rather than an
  asymptotic cancellation. Whole-route consequence: the requested zero-clock prime--polar--Γ
  charge cannot be supplied after scalarizing through the bare codiagonal. The positive survivor
  is precise: only its nonconstant actual autocorrelation/commutator profile can carry the
  residual source information, so a viable higher-dimensional producer must preserve that marked
  profile before any scalar zero-mode readout.
- **The mass-coordinate first codiagonal mode has a forced endpoint contaminant (new, Lean
  closed no-go and survivor).**
  `CCMActualHeadMatchedQuantilePolarAdjacentCodiagonal.lean` proves exactly
  \[
    \mathcal C_K[y]=-
      \sum_{n\le K}\Lambda_{\rm crit}(n+2)\,\delta_{n+2}
    =\sum_{n\le K}\Lambda_{\rm crit}(n+2)
      \bigl(E_{\rm out}(n+2)+\mathrm{upperExcess}_{n+2}\bigr).
  \]
  The upper excess is the literal nonnegative displacement of the raw matched upper endpoint
  from the prime-centre mass coordinate. Whole-route consequence: the unmarked linear
  codiagonal is not a cancellation-faithful completed-source reporter. The exact positive
  survivor is its endpoint-renormalized two-channel readout, which Lean identifies with
  \(\sum\Lambda_{\rm crit}(n+2)E_{\rm out}(n+2)\). This is a source extraction only, not a
  bound; it does not close the CCM--FU triangular transform, whose irreducible signed curvature
  current is separately RH-bearing.
