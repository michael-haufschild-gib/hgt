# CCM/Suzuki exceptional-block fact log

Scope: Codex `/root` research only. Facts and no-gos; no chronology or status diary.

## Facts

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
