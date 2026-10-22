# HB core-bridge viability: facts and no-gos

Owner: current HB viability investigation. Separate from other researchers' logs.
Evidence: current Lean source inspection and corpus search; no fresh kernel audit in this
investigation. `source_only` search metadata is not a compiler certificate.
Scope: complete physical-action identification and an independent extinction selector.

Paths below are relative to `formal/GaloisForLFunctions/RHTower/`.

| ID | Fact / no-go | Exact source evidence | Meaning for the whole route |
|---|---|---|---|
| V01 | The completed spin-two vertex is `XiC(z)^2 * U(z)`. The canonical amputated `U` is nonzero throughout the open critical strip; the first live jet divided by its external leading jet equals `U`. | `ThetaCuspHawkingBMCanonicalSpinTwoAmputation.lean`: `d4BMCompletedSpinTwoVertex_eq_XiC_sq_mul_canonicalSource`, `d4BMCanonicalSpinTwoAmputatedSource_ne_zero`, `d4BMFirstLiveSpinTwoJet_div_externalJet_eq_canonicalSource`. | The arithmetic zero of the unamputated vertex is not extinction of the retained source. Any selector must explain which observable vanishes while preserving this nonzero information. |
| V02 | No returned profile tested against the old minus source can reproduce the first live angular jet on every Xi copy. It also cannot reproduce universal full AIME incidence. Both global nonexistence statements discharge the critical-copy witness using Hardy. | `ThetaCuspHawkingBMSourceProbeRangeClassification.lean`: `not_exists_hbXiPeierlsSourceProbe_firstLiveAngularJet`, `not_exists_hbXiPeierlsSourceProbe_fullAIMEIncidence`. | These specific identifications are excluded, even with arbitrary returned profiles. This does not exclude every physical pairing or a diagnostic that itself vanishes on critical copies. |
| V03 | The old source probe represents exactly the profiles vanishing on critical-line copies. A fitted weighted skew response realizes every such profile. | Same module: `exists_hbXiPeierlsSourceProbeProfile_iff`, `hbXiPeierlsSourceProbeRealizingWeight_profile`. | Abstract representability of an RH diagnostic establishes no physical identification. The equations must determine the response without fitting it to the desired diagnostic. |
| V04 | The actual original current is an exact parameter divergence with a retained bulk term; the finite-rectangle identity retains all four oriented boundaries. | `ThetaCuspHawkingBMOriginalGreenBoundary.lean`: `original_current_boundary`, `original_rectangle_boundary`, `original_metric_boundary`. | Boundary bookkeeping is available. A divergence identity alone does not set the completed action or any individual boundary contribution to zero. |
| V05 | FE invariance of the explicit skew constant kernel is equivalent to `sigma=1/2` on `0<=sigma<=1`, `92<=t`. Its theorem is stated for arbitrary spectral parameters, without a Xi-zero hypothesis. | `ThetaCuspHawkingBMEvenSectorSkewConstantFE.lean`: `skewConstantKernel_fe_invariant_iff`. | This is a selective receiver. Its physical identification and the source-derived FE invariance needed to activate it are separate obligations. |
| V06 | A fixed finite-support Peierls model has an exact orbit cut `K=-Sigma*normSq(D_clock)`, with `Sigma>0` and no division by tilt. Its quadratic residual is pointwise multiplication; the displayed full-cut split uses the model propagator and zero advanced map. | `ThetaCuspHawkingTargetIndependentFullCokernelPeierlsRealization.lean`: `hbXiPeierlsCanonicalFullCokernelCausalCutAt`; `ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence.lean`: `hbXiPeierlsQuadraticResidual`; `ThetaCuspHawkingBMTotalCokernelClockDefectTransduction.lean`: `hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut_eq_neg_clockDefectEnergy`. | An algebraic identification exists. These definitions are not an identification with the complete physical PDE inverses. A cut depends on the response difference, so the zero-advanced presentation alone is not an impossibility proof. |
| V07 | The common direct third Taylor term cancels exactly from the full retarded-minus-advanced cut. In a cyclic/skew Peierls realization the stationary mixed contribution also vanishes; the survivor is the polarized pairing of the two quadratic radiation sources. | `ThetaCuspHawkingTotalThirdOrderCausalCut.lean`: `d4GaugeFixedTeukolskyTotalPlusPlusMinusCausalCut_eq_resolventJump`; `ThetaCuspHawkingCubicPeierlsPolarization.lean`: `d4GaugeFixedTeukolskyPhaseNormalizedPeierlsCubicCut_eq_polarized`. | No independent computation of the common cubic contact can repair this cut. The second reduction has explicit cyclicity/skewness hypotheses; their complete physical realization is still required. |
| V08 | Swapped source branches in one cyclic/skew Peierls theory give a reflection-odd cut. Matching both reflected BM candidates then forces the copy onto the critical line. | `ThetaCuspHawkingBMSourceFixedPeierlsReflectionRigidity.lean`: `d4GaugeFixedTeukolskySourceFixedPeierlsCubicCut_reflection_odd`, `d4BMXiSourceFixedPeierls_BM_incidence_forces_criticalLine`. | There is a precise conditional selection mechanism. It must not be reported as premise-free physical extinction: the theorem explicitly takes the common pairing, propagator, cyclicity, skewness, source exchange and both incidences. |
| V09 | Literal physical metrics and every nonlinear source coefficient exchange under FE reflection. Actual projected action transports with the reader held fixed. Reflecting both source and reader leaves an exact reader-change term. The reflected reader differs from the original at every Xi copy. | `ThetaCuspHawkingBMLiteralSourceReflection.lean`: `physicalPerturbation_reflect`, `physicalSource_coefficient_reflect`; `ThetaCuspHawkingBMSourceReflectionTransport.lean`: `physicalProjectedModeAction_reflect`, `physicalProjectedModeAction_diagonal_defect`, `physical_reader_reflect_ne`. | Source symmetry does not establish the required diagonal action covariance. The two source/reader indices cannot be silently identified during transport. |
| V10 | The original source parameter is `rho-1/2`; the physical reader parameter is `(rho-1)/2`. Reader-current divergence is `i*(Re rho-1)*Im rho*normSq(reader)`, with a nonzero value somewhere for every Xi copy. Source half-square divergence minus its gradient contact has coefficient `8*i*(Re rho-1/2)*Im rho`. | `ThetaCuspHawkingBMSourceHermitianCurrent.lean`: `divergence_eq_spectral_density`, `not_divergence_free`, `square_divergence_sub_gradient_contact`, `square_oriented_contact_balance`. | A divergence-free Hermitian reader would exclude known critical zeros. The source has the right spectral center, but its gradient work cannot be removed to manufacture conservation. |
| V11 | For a strict-right Xi copy, the complete evaluated angular source is `Lambda(5rho/2-1)*Lambda(rho/2)^2*Lambda(1-3rho/2)/2`. Its zero condition is exactly an affine Xi collision at `5rho/2-1`, `rho/2`, or `3rho/2`. | `ThetaCuspHawkingBMPhysicalAngularSourceValue.lean`: `physicalSelfSourceCoefficient_fourLambda`; `ThetaCuspHawkingBMPhysicalAngularSourceXi.lean`: `physicalSelfSourceCoefficient_zero_iff_xi`. | The actual source coefficient is not simply `xi(rho)`. This strict-right theorem supplies neither nonvanishing of every physical coupling nor its value on the critical line. |
| V12 | Local physical cubic symmetry retains the differentiated Einstein boundary term. Exchange with an inhomogeneous correction retains the changing weight, independent test residual and boundary defect. | `ThetaCuspHawkingBMOnShellCyclicSource.lean`: `physical_quadratic_with_boundary_cyclic`; `ThetaCuspHawkingBMInhomogeneousCorrectionBoundary.lean`: `correction_exchange`. | Local symmetry does not discharge the global cyclic pairing in V07--V08 after source insertion and limiting operations. |
| V13 | Physical ingoing/outgoing frequency-domain Green blocks have a nonzero diagonal difference on every Xi copy, witnessed by an interior point source. | `ThetaCuspHawkingBMSecondHarmonicPhysicalHorizonGreenNoncollapseNoGo.lean`: `exists_d4BMXiPlusPlusIngoing_sub_outgoingRightEndpointGreenKernel_diag_ne_zero`. | Equality of these entire Green blocks cannot select RH. This point-source result does not prove nonzero pairing for the actual theta source or exclude extinction of a projected orbit. |
| V14 | The canonical model's radial weight has imaginary part `-Im rho`, so its weighted propagator is not odd under its prescribed channel-Schwarz map. Generic finite-KMS passivity exactly realizes the model orbit's existing nonpositive sign. | `ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction.lean`: `hbXiPeierlsRadialWeight_propagator_not_channelSchwarzOdd`; `ThetaCuspHawkingHBFullCokernelKMSPassivityPolarityNoGo.lean`: `neg_I_mul_hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_eq_orbitCut`. | The model's successful detector and the desired causal symmetry cannot simply be combined. Passivity supplies no opposite sign. Scope is the displayed Schwarz map and passive realization, not every physical completion. |
| V15 | The source-derived density dual reproduces the opposite-branch forcing with the actual half-square Laplacian. Subtracting any constant multiple of an independent physical fundamental QNM leaves its fourth-order AdS residue unchanged. | `ThetaCuspHawkingBMSourceDensityDual.lean`: `densityDual_originalForcing`, `densityDual_physicalMode_ads_residue`. | The exact forcing transpose does not identify the physical dual state. A nonzero displayed residue obstructs this specific identification; an augmented pairing must retain the port. No pointwise universal nonvanishing is asserted. |
| V16 | The density-dual radial flux has an explicit value independent of radius and source branch, retaining `sourceAngularK * retainedSpinTwo`. | Same module: `dualRadialFlux_exact`. | Conservation does not imply an individual endpoint is zero. Orientation must be checked before interpreting a retained port as an obstruction or a selector. |
| V17 | The actual literal scalar and native causal response are horizontally even. The cross-eigenvalue/coexact physical work has zero integral on every symmetric finite slice; all four oriented rectangle edges cancel. | `ThetaCuspHawkingBMSpatialReflectionCurrent.lean`: `full_response_reflection`, `physical_cross_work_integral_zero`, `rectangle_boundary_flux_zero`. | An actual physical sector cancellation is available without an extinction premise. Its identification with the complete selective radiative action is not supplied by this result. |
| V18 | The distinct coexact/coexact work is horizontally even. | Same module: `causal_coexact_work_reflection`. | The odd-current cancellation cannot be extended to this channel by parity alone. Evenness proves neither zero nor nonzero complete action. |
| V19 | The original causal double time primitive has an exact finite-time Green balance: complete source work equals a retained final-time Hermitian current. Spatial cancellation uses the admitted original operator domain. | `ThetaCuspHawkingBMPhysicalPrimitiveCurrent.lean`: `physicalPrimitiveCurrent_source_hasDerivAt`, `physicalPrimitiveCurrent_balance`. | Physical domain control and a source-work identity exist. The final-time value, action phase and identification with the complete metric Peierls coefficient remain separate obligations. |
| V20 | The actual incoming SV--SV radial clock coefficient obeys a finite-cusp boundary-minus-work law with both endpoints, differentiated reader work, and full response/local-square work. The local square-work coefficient is nonzero on every Xi copy. | `ThetaCuspHawkingBMQuarticTestedCurrentCusp.lean`: `physical_radial_finite_cusp_balance`, `physical_clock_finite_cusp_balance`; `ThetaCuspHawkingBMQuarticResponseWork.lean`: `squareWorkCoefficient_ne_zero`. | The common clock factor does not remove source work. Nonzero coefficient alone proves neither nonzero total work nor failure of a complete orbit cancellation. |
| V21 | The original angular problem has a unique finite-energy remainder; its smooth response represents the actual lifted weak solution almost everywhere. | `ThetaCuspHawkingBMGlobalAngularWeakResponse.lean`: `exists_full_forcing_weak_response`, `full_forcing_weak_response_unique`; `ThetaCuspHawkingBMGlobalSmoothResponse.lean`: `globalResponse_ae_lift`. | Transport of the prescribed full forcing can use uniqueness. This is not uniqueness of arbitrary non-L2 solutions, nor a full-action identification. |
| V22 | Reflected radial readers at one unchanged physical frequency share leading normalization but have unequal first Gauss coefficients on every Xi copy. Their relative derivative current has no finite raw horizon limit. | `ThetaCuspHawkingBMRelativeReaderHorizon.lean`: `gauss_first_difference`, `gauss_first_difference_ne_zero`, `radialGreen_actual`, `radialGreen_no_finite_horizon_limit`. | Equal leading radial values do not remove the physical reader mismatch. This is an obstruction for this relative radial current, not a no-go for the complete renormalized action. |
| V23 | For that current, the unique leading-power subtraction permitting a finite limit has coefficient `center(q)/(4*(1+w))`; subtracting it leaves limit zero. | Same module: `normalized_radialGreen_tendsto`, `radialGreen_sub_source_counterterm_tendsto_zero`, `radialGreen_finite_subtraction_iff`. | Finiteness fixes a nontrivial positive survivor independently of RH. Its equality with the original full-action boundary prescription remains unestablished; arbitrary extra finite counterterms are outside this uniqueness statement. |
| V24 | After common radial normalization, the full reflected left-stream difference converges to the difference of its coexact angular readers. | Same module: `normalized_stream_difference_tendsto`. | Repairing the relative radial current does not remove the angular reader contribution. The theorem states an exact limit, not pointwise nonvanishing of that difference. |

## Search coverage limits

- `/tmp/hb-bridges-research.json`: interrupted/partial deep search; useful source hits only.
- `/tmp/hb-arithmetic-selection-research.json`: complete deep search, no reported errors;
  57,500 indexed files / 747,597 declarations. Most compiler metadata is pending/source-only.
  Retrieved suggestions do not establish applicability or absence of other mechanisms.
- Subsequent complete/error-free deep searches: `/tmp/hb-full-action-target-research.json`,
  `/tmp/hb-reader-selection-research.json`, `/tmp/hb-source-square-selector-research.json`,
  `/tmp/hb-critical-physical-incidence-research.json`. All ranked candidate and source-argument
  sections were inspected. Claims above use direct source reads, not generated proof suggestions.
- Current mechanism/method searches: `/tmp/hb-orbit-boundary-methods.json` and
  `/tmp/hb-radiation-pair-methods.json` completed without reported errors;
  `/tmp/hb-defect-budget-methods.json` was partial (reranking deadline).
  `/tmp/hb-dual-reflection-methods.json` completed without reported errors.
  Candidate, source-argument and available method/ingredient sections were inspected.
  The index reported 57,502 files / 747,614 declarations around generation 897277;
  most compiler metadata remained pending. Generated ingredient sets were unverified.
  Deep mode includes method discovery; the documented CLI has no separate method mode.
- `/tmp/hb-native-quadratic-dual-methods.json` was partial (malformed model judgment,
  interrupted retrieval/deadline); `/tmp/hb-spatial-null-selector-methods.json` was
  partial (malformed judgment and semantic deadline); their useful source hits were
  retained. `/tmp/hb-spatial-polarization-methods.json` completed without reported
  errors. All returned candidate/method sections were inspected; none establishes
  the missing full-action correspondence.
- `/tmp/hb-native-reciprocity-attack-methods.json` was partial (reranking
  deadline); `/tmp/hb-physical-primitive-orbit-methods.json` was partial
  (malformed judgment and reranking deadline). All candidate and source-method
  sections were inspected. Direct reads confirmed V19 and the assembled causal
  source definitions; no generated reciprocity proposal was treated as a proof.

- Further complete deep/method searches: `/tmp/hb-even-resolvent-sign-methods.json`,
  `/tmp/hb-quartic-fe-orbit-attack.json`, `/tmp/hb-quartic-reader-orbit-methods.json`,
  `/tmp/hb-half-square-observability-attack.json`. Latest reported generation
  897428. `/tmp/hb-source-field-nonzero-methods.json` was partial (malformed
  model judgment and decomposition deadline); `/tmp/hb-quadratic-pair-reader-identification.json`
  was partial (semantic deadline). All candidate, source-argument and available
  method/ingredient sections were inspected. Lexical searches confirmed actual
  response names and `radialGreen_finite_subtraction_iff`; direct reads support
  V20--V24. New derivations P5--P7 remain paper-only in the attack card.
- `/tmp/hb-relative-reader-counterterm-methods.json` was partial (reranking
  deadline), generation 897441. All returned candidate and source-method
  sections were inspected. The exact lexical hit and a direct read of the
  full relative-reader module confirmed the subtraction's restricted uniqueness
  and zero remainder. No generated action-identification suggestion was accepted.

## Scope boundaries established by the evidence

- Recovering a nonzero first live source and constructing a critical-line-vanishing diagnostic
  are different mathematical targets (V01--V03).
- Neither the receiver (V05) nor a completed Green identity (V04) supplies an extinction law.
- No impossibility theorem for every possible HB mechanism has been established here.
- V08 supplies a conditional algebraic mechanism; V09 and V12 supply concrete local physical
  inputs. A theorem assembling them with the physical global pairing and detector identification
  was not established by this investigation.
