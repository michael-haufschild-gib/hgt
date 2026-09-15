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
