# Route HB ledger (status quo)

Route HB: theta-cusp Hawking causal scattering. Chain as stated on the cards:
literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal
radial/left-QNM action → common Hawking-clock extinction → RH.

Verdict: no step proves or disproves RH. Steps 1–30 are built infrastructure; steps 31–40 are the
live radiative core; 42–44 are the static alternative. Four items are unknowns rather than merely
unproved: 34 (one residual collision factor), 38, 40, 44.

Status key. FULL = Lean, committed, audited. PART = Lean covers a sector or an abstract form; the
physical application is open. PAPER = paper derivation only. OPEN = statement known, unproved.
UNKNOWN = no mechanism or statement identified. DEAD = proven no-go.

## 1. Step ledger

| # | Step | Content | Status | Lean anchor |
|---|---|---|---|---|
| **A. Source and occurrence** | | | | |
| 1 | Literal theta-cusp source | Complete theta half-square, Fourier–Bessel/Eisenstein families, joint C∞ regularity, scalar and vector cusp equations | FULL | `ThetaCuspHawkingBMAngularScalarEquation`, `…EisensteinCuspJointSmooth` |
| 2 | Xi occurrence | Every Xi zero is a modular topological-AdS pole with shadow zero and two opposing QNM branches | FULL | `thetaCuspHawkingXiDivisor_topologicalBlackHoleQNM_incidence` |
| 3 | Causal excitation and Jost zeros | Hardy wavepacket excites each resonance; Jost descendants are simple boundary zeros with nonzero chiral AIME residue | FULL | `ThetaCuspHawkingCausalHardy*`, `ThetaCuspHawkingAIMECrossBranchTeukolskyResidue` |
| 4 | Canonical spin-two source | First live order-2m angular jet nonzero; unique factorization V = XiC²·U, U a unit on the strip | FULL | `ThetaCuspHawkingBMCanonicalSpinTwoAmputation` |
| 5 | Physical angular source value | Source = Λ(5ρ/2−1)Λ(ρ/2)²Λ(1−3ρ/2)/2 on the strict-right representative; zero iff one affine Xi value vanishes | FULL (formula) | `physicalSelfSourceCoefficient_fourLambda`, `…_zero_iff_xi` |
| **B. Einstein and metric algebra** | | | | |
| 6 | Metric jets and Einstein tensor | KI gauge-invariant reconstruction, full coordinate Einstein tensor, B/C multilinear source, Bianchi, linearized scalar+vector equations at both branches | FULL | `CoordinateEinsteinComplexLinearization`, `ThetaCuspHawkingBMFullLinearEinsteinEquation` |
| 7 | Quadratic mixed correction | Explicit second-order correction for the scalar/vector mixed block at doubled rate, all 16 components, amplitude identified | FULL (this sector) | `ThetaCuspHawkingBMQuadraticMixedSource`, `…Amplitude`, `forcedMetricField_einstein` |
| 8 | Mixed ++− cubic coefficient formula | L·l + B(p,k₊₋) + B(m,k₊₊) + C(p,p,m)/2; extra terms drop only when both quadratic corrections are solved | FULL (formula) | `cubic_mixed_coefficient`, `mixedPairedCoefficient_of_quadratic_zero` |
| 9 | Angular polarization obstruction | Scalar data cannot determine the source (defect −sech(1)²/16); spin-two must be retained | FULL (no-go) | `ThetaCuspHawkingBMFullPoincareDerivativePullback` |
| 10 | Global angular inverse | Unconditional modular gluing, H²/L² regularity, cusp mean, indicial branch | FULL | card `hb-global-angular-resolvent` |
| **C. Causal Green and QNM continuation** | | | | |
| 11 | Time-domain source and Laplace admission | Onset switching, transform admission, source-pole preservation | FULL | `ThetaCuspHawkingBMJointSourceTimeField` |
| 12 | Native causal inverse | Legendre kernel, Goursat/Volterra, all three principal channels equal the physical L² responses | FULL | `ThetaCuspHawkingBMFullNativeWave` |
| 13 | Residual energy and Friedrichs identification | Joint L², modular germs, global energy identity, mollification, W = JJ*(W+G), AW = W+G | FULL | card `hb-native-radial-form-admission` |
| 14 | Native = physical response | Physical Volterra response equals the native residual a.e. via Bochner covariance | FULL | card `hb-joint-causal-laplace-identification` |
| 15 | Full causal Green-band landing | Response ≪ (t+1)³e^{B(q)t}; on B(q) < Re w < 2 the projection equals the Green profile with Dirichlet trace | FULL | `ThetaCuspHawkingBMNativeGreenBand`, `…PhysicalCausalGreenBand` |
| 16 | Fixed horizon domain, QNM occurrence | Both fundamental Xi QNMs have zero connection coefficient, Wronskian −w, normalizable solution | FULL | card `hb-qnm-parameter-continuation` |
| 17 | Meromorphic QNM continuation, Laurent factorization | Residue = angularSource · fundamentalSourceMoment · clearedOnset / denominatorSlope, slope nonzero | FULL (factorization) | `physicalSelfResidueCoefficient_fundamental_value`, `continuedPhysicalSelfResponse_nonremovable_iff_elementary` |
| **D. Action and current** | | | | |
| 18 | Einstein action boundary and stream-master current | Local boundary identity, radial symplectic density, all four current components | FULL | cards `hb-einstein-action-boundary-current`, `hb-mixed-complete-current` |
| 19 | Projected physical mode action | A⁰, A¹ explicit on 3/2 < Re w < 2; A², A³ vanish for the projected SS/SV pair only | PART | `ThetaCuspHawkingBMModeActionReconstruction`, `…PhysicalModeAction` |
| 20 | Temporal QNM residue | Temporal current continues to both QNMs; residue = field residue × left mode × angular square | FULL (local) | `ThetaCuspHawkingBMPhysicalTimeActionContinuation` |
| 21 | Radial residue finite part | Horizon-subtracted mode square = Γ(w)Γ(3/2)/(2Γ(w+3/2)) ≠ 0; integrated finite part = 0 iff K = 0 | FULL | `normFinitePart_ne_zero`, `physicalRadialResidueFinitePart_eq_zero_iff` |
| 22 | Incoming horizon expansion | endpoint(w) + slope(w)·z + O(z²), frequency-uniform, nonzero Gauss factor | FULL | `ThetaCuspHawkingBMIncomingHorizonExpansion` |
| 23 | Temporal contact horizon factor | Cutoff commutators sum to horizonCoordinate × …; the extra horizon pole cancels | FULL (committed) | `ThetaCuspHawkingBMTemporalContactHorizonFactor` |
| 24 | Pulse horizon, contact clock, retarded history | Contact moment zero at every radius, yet the retarded pulse retains its history; contact vanishing is not extinction | FULL | `ThetaCuspHawkingBMPulseContactClock`, `…RetardedPulseClock` |
| 25 | Late two-source clock | W_V(h) = A e^{2sh} − B_V e^{(2s+6)h}, terminal coefficient nonzero; dropping it is invalid | FULL (negative) | `ThetaCuspHawkingBMLateSourceClock` |
| 26 | Fixed-clock source translation | Moment h·e^{vh}·A ≠ 0; raw switched-source covariance unavailable even on the line | FULL (negative) | `sourceAndContact_clockMoment` |
| 27 | Incoming current and clock moments | Four incoming components, exact translation and late-slab masses, radial mass balance | FULL | `ThetaCuspHawkingBMIncomingClockTranslation`, `…FullIncomingCurrent` |
| 28 | Full angular circle propagation | Circle Green law, Darboux, closed-cone Goursat/Volterra, Legendre kernel nonzero | FULL | `ThetaCuspHawkingBMFullAngularCircleAction` |
| 29 | Source-contact rigidity | Coefficient (λ−2)(λ−6)(3λ−2) ≠ 0 at every Xi occurrence; bilinear, not a positivity | FULL | `ThetaCuspHawkingBMSourceContactRigidity` |
| 30 | Spin-two contact balance | Quartic-period Green balance with cutoff-commutator cancellation; Re(13λ−6−μ) < −23/4 | PAPER | card `hb-source-contact-spin-two-balance` |
| **E. Open radiative core** | | | | |
| 31 | Laurent/horizon interchange | Horizon-mode leg (`outer = false`) closed: the cutoff radial integral of the temporal current plus the two counterterms of the cleared density's horizon jet converges near each fundamental QNM; the limit is meromorphic with a simple pole and its order −1 Laurent coefficient is `physicalRadialResidueFinitePart`. The normalizable-mode leg (`outer = true`) is not done | FULL (horizon-mode leg) / OPEN (normalizable leg) | `continuedPhysicalTimeAction_horizon_radial_laurent`, `radial_cutoff_package`, `clearedTemporalDensity_eq_current` |
| 32 | Radial contact and QNM-boundary traces | Horizon Wronskian-bracket finite part vanishes off the QNM (`continuedResponse_horizon_current_finite_part_zero`); germ at the QNM closed: the bracket equals the horizon source phase on the punctured neighbourhood, the phase is analytic through the connection zero (the Wronskian cancels the horizon-mode component), and its endpoint-subtracted horizon limit is zero at both fundamental QNMs (`physicalResponse_horizon_current_qnm_germ`). Derivative traces and cusp faces open | PART | `ThetaCuspHawkingBMHorizonSourcePhaseQNMGerm` |
| 33a | Cleared onset nonzero | clearedOnset s w = ∫₀¹χ′(u)e^{(2s−w)u}du; equals 1 at the source rate, positive at real exponents, nonzero for all but isolated onset durations. A universal duration exists: one positive `L` with `clearedOnsetDuration s w L ≠ 0` at both fundamental QNMs of every Xi copy on both branches (`exists_universal_onset_duration`, Baire over the countable copy set). The fixed unit duration itself is not proved nonzero; the pipeline is derived at unit duration and its re-derivation at duration `L` (`u ↦ χ(u/L)`) is not done | PART (nonvanishing closed at a universal duration) | `clearedOnset_eq_onsetPulseTransform`, `exists_universal_onset_duration` |
| 33b | Fundamental source moment nonzero | After u = √(1−z): 2a²∫₀¹(1−u)^w(1+u)^{2s}u²(A+Bu²)du, a Beta·₂F₁(−1) combination with no Kummer constellation | OPEN | only the different object `d4FundamentalQNMContinuedRadialMoment_xi_ne_zero` |
| 34 | Affine Xi collision control | ξ(3ρ/2) ≠ 0 for Re ρ ≥ 2/3 with a one-step ascent otherwise; ξ(ρ/2) collisions removed by half-descent to the real point 2/3; ξ(5ρ/2−1): five-half ascent above 2/3 and reflection `2 − 5ρ̄/2` below 8/15 give, for every strict-right zero with Re ρ ∉ [8/15, 2/3], a descendant strict-right zero with ξ(5ρ'/2−1) ≠ 0 and ξ(3ρ'/2) ≠ 0 simultaneously; inside the band the collision orbit either escapes, lands on Re = 3/5 (partner on the line), or stays trapped in [8/15, 2/3] forever (`xiFiveHalf_trapped_orbit_dichotomy`). Residual: simultaneous control of all three factors with the half-descent, and the trapped/3/5 cases; these are statements about the zero set no zero-density input reaches | PART / UNKNOWN residual | `XiAffineCollisionControl`, `XiFiveHalfCollisionOrbit`, `ThetaCuspHawkingBMAngularSourceCollisionControl` |
| 35 | ++ and +− quadratic corrections | ++ scalar/vector mixed block and ++ radial reduced Green with uniqueness solved; the stationary +− arm of the causal cut is a vanishing Peierls self-pairing; ++ SS and VV blocks open; k₊₋ still needed for the integrated action coefficient. Exact missing pieces for SS: (i) the scalar–scalar quadratic tensor `B(h_S,h_S)` of the fundamental scalar jet in simplified form (the general quadratic Einstein tensor exists, `CoordinateEinsteinComplexQuadratic.einstein`; the SV analogue is `QuadraticMixedSource.tensor`, 800 lines); (ii) the Kodama–Ishibashi scalar-sector reduction with source, from the four scalar-type components to the doubled-rate master equation (the vector analogue is the constrained vector operator on the card); (iii) then the existing ++ Green `d4BMPlusPlusContinuousGreenResponse_forcedEquation` gives the response. VV needs (i)–(ii) for the vector–vector product. This is the physical side of the third-order coefficient that rows 37, 39 and 40 consume | PART | `forcedMetricField_einstein`, `d4BMPlusPlusRadialBoundaryProblem_eq_green`, `ThetaCuspHawkingHBPeierlsStationaryChannelElimination` |
| 36 | Angular/cusp integration, nine-channel current | Pointwise hyperbolic Green identity, cusp flux limit, rapid-decay product algebra, and the truncated modular Stokes theorem exist, the latter only for the absolute-convergence Eisenstein family | OPEN | `angular_current_green` (private), `limitingFlux`, `D4BMCuspRapidDecay`, `…EisensteinActualFirstStokesFubini` |
| 37 | Corrected mixed action coefficient | Evaluate the integrated ++− coefficient and radial boundary current | OPEN | `mixed_complete_action_current`, `mixedPairedCoefficient_of_quadratic_zero` |
| 38 | Left-QNM / retarded-advanced data | The original BM testing leg vanishes on critical copies; no replacement probe retaining the first live jet is identified | UNKNOWN | `ThetaCuspHawkingBMSourceProbeRangeClassification` (no-go) |
| 39 | Spin-two/AIME coefficient match | Target C_phys = −Σ·|D|², Σ > 0; the model period P_ret = FP_conservative + i‖Radiation‖² fixes the shape but takes the conservative finite part as a free parameter | OPEN | `hbXiPeierlsClockDefectToFullCokernelSusceptibility`, `ThetaCuspHawkingBMTotalRenormalizedAngularPeriod` |
| 40 | ++ extinction before divisor selection | A source-derived law forcing D = 0. Every scalar, meromorphic, finite-rank, finite-energy Hilbert, bounded/Krein, passive, Schwarz-odd, finite-variation, and perturbative-clock mechanism is DEAD; a survivor must be nonscalar, singular, or infinite-energy. The corpus has Rellich identities only for Maass eigenforms and no unique-continuation or Carleman estimate | UNKNOWN | 38 no-go cards `5-failed/hb-*` |
| 41 | Extinction ⇒ RH | Universal extinction, standard-clock mixing, Ward cancellation, centralizer rigidity are each equivalent to RH | FULL (receivers) | `riemannHypothesis_iff_hbXiPhaseSensitiveChiralWardAmplitudeCancellation`, `…_FullMirrorStandardClockMixing` |
| **F. Static front** | | | | |
| 42 | All-replica graph-local completion | Hall rank, no zero atom, Dyson boundary equation, fourth-moment near-action law | FULL | `hawking-total-plus-plus-minus-cokernel-schur-section` |
| 43 | Static RH receivers | Centralizer rigidity, KMS Cayley mixing, Friedrichs mixing are each equivalent to RH | FULL | `riemannHypothesis_iff_thetaCuspHawkingTiltedResonanceCentralizerRigid`, `…_KMSCayleyScatteringMixing` |
| 44 | Phase-sensitive theta–Hawking KMS law | Producer needed; generic positivity fails because dark centralizer modes evade KMS dissipation yet keep positive Wigner delay | UNKNOWN | — |

## 2. Lean toolkit for the open core

All theorems are unconditional: no `sorry`, `axiom`, `opaque`, `unsafe`, or premise beyond the
stated real/complex variables; `#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`. Each module is clean under `lake env lean` (no errors, no warnings), has its olean
published, and is wired into its umbrella.

| Module | Namespace | Main declarations | Audit |
|---|---|---|---|
| `RHTower/ThetaCuspHawkingBMOnsetPulseTransform` | `RHTower.D4BMModularCore` | `onsetPulseTransform z = ∫₀¹χ′(u)e^{zu}du`; `onsetPulseTransform_sub : onsetPulseTransform (v−w) = 1 + (w−v)·onsetCorrection v w`; `onsetPulseTransform_zero`; `differentiable_onsetPulseTransform`; `onsetPulseTransform_ray_eventually_ne_zero`; `exists_real_near_onsetPulseTransform_ne_zero`; `onsetPulseTransform_ofReal_re_pos`, `_ne_zero` | `lake build` green |
| `RHTower/ThetaCuspHawkingBMClearedOnsetPulseTransform` | `RHTower.D4BMJointSource` | `clearedOnset_eq_onsetPulseTransform`; `clearedOnset_source_rate`; `clearedOnset_ne_zero_of_im_eq_zero`; `clearedOnsetDuration s w L := onsetPulseTransform (L(2s−w))` with `_one`, `_zero`, `differentiable_`, `clearedOnsetDuration_eventually_ne_zero`, `exists_real_duration_clearedOnsetDuration_ne_zero` | `lake build` green |
| `RHTower/XiAffineCollisionControl` | `RHTower` | `xi_three_half_ne_zero_of_re`; `xi_five_half_sub_one_ne_zero_of_re`; `xi_three_half_collision_partner`; `xiHalfDescent` with `_eq`, `_re`, `_im`, `_tendsto`; `exists_xiHalfDescent_half_ne_zero`; `exists_xi_zero_half_ne_zero`; `exists_strict_right_representative` | `lake build` green |
| `RHTower/ThetaCuspHawkingBMAngularSourceCollisionControl` | `RHTower.D4BMJointSource` | `physicalSelfSourceCoefficient_zero_iff_of_two_thirds_le`; `physicalSelfSourceCoefficient_zero_iff_half_of_four_fifths_le`; `physicalSelfSourceCoefficient_ne_zero_of_four_fifths_le`; `exists_strict_right_zero_half_ne_zero_of_copy` (copies with Re ≠ 1/2) | `lake build` green (13004 jobs, stale dependency oleans of the `PhysicalAngularSourceXi` cone rebuilt on the way) |
| `HTGeometry/FirstEndpointMellinLaurentInterchange` | `GaloisForLFunctions.HTGeometry` | `firstEndpointMellin_differentiableAt`; `firstEndpointMellin_analyticAt`; `firstEndpointMellin_const_mul`; `firstEndpointMellin_div_sub`; `laurentCoeff_firstEndpointMellin_div_sub` | `lake build` green |
| `RHTower/ThetaCuspHawkingBMUniversalOnsetDuration` | `RHTower.D4BMJointSource` | `goodOnsetDurations` open and dense per copy; `exists_universal_onset_duration` | `lake build` green |
| `RHTower/ThetaCuspHawkingBMHorizonSourcePhaseQNMGerm` | `RHTower.D4BMJointSource` | `continuedHorizonSourcePhase_frequency_analyticAt`; `continuedHorizonSourcePhase_finite_part_zero` (no connection hypothesis); `continuedResponse_horizon_current_analytic_germ`; `physicalResponse_horizon_current_qnm_germ` | `lake build` green |
| `HTGeometry/CoordinateEinsteinDiagonalCollapse`, `RHTower/ThetaCuspHawkingBMBackgroundDiagonalJet` | `GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet`, `RHTower.D4BMBackground` | `IsDiagonalJet`; index-collapsed closed forms, for an arbitrary perturbation over a diagonal background, of the linearized inverse, Christoffel, inverse-derivative, spatial inverse and spatial Christoffel variations and of the quadratic inverse, Christoffel, spatial inverse and spatial Christoffel variations (`linearization_connection_eq`, `linearization_connectionSpatial_eq`, `quadratic_inverse_apply`, `quadratic_connection_eq`, `quadratic_inverseSpatial_apply`, `quadratic_connectionSpatial_eq`), plus the background Christoffel closed form `christoffel_eq`; `jet_isDiagonalJet` for the BM background. Heartbeat-efficient route to the ++ SS/VV sources of row 35; curvature/Ricci collapse and the scalar-jet block specialization are next | `lake build` green |
| `HTGeometry/CoordinateEinsteinQuadraticPolarization` | `GaloisForLFunctions.HTGeometry.CoordinateMetricTwoJet` | `MixedQuadratic.einstein_self` and companions: the same-jet mixed quadratic Einstein coefficient is the quadratic coefficient (definitional), so scalar–scalar and vector–vector sources are the mixed coefficient with equal slots | `lake build` green (2691 jobs) |
| `RHTower/XiFiveHalfCollisionOrbit` | `RHTower` | `xiFiveHalfAscent` (orbit `ρ ↦ 5ρ/2−1`, real parts `2/3 + (5/2)^n(Re ρ − 2/3)`); `exists_xi_zero_five_half_ne_zero_of_two_thirds_lt`; `xiFiveHalfReflect` (`2 − 5ρ̄/2`); `exists_xi_zero_five_half_three_half_ne_zero_of_not_mem_band`; `xiFiveHalfStep`, `xiFiveHalfOrbit`, `xiFiveHalf_trapped_orbit_dichotomy` | `lake build` green |
| `HTGeometry/SecondEndpointMellinLaurentInterchange` | `GaloisForLFunctions.HTGeometry` | `dividedDifference`; `secondEndpointMellin`; `secondEndpointMellin_cutoff_tendsto`; `secondEndpointMellin_analyticAt`; `secondEndpointMellin_const_mul`; `laurentCoeff_secondEndpointMellin_div_sub` | `lake build` green (13103 jobs) |
| `HTGeometry/UniformSecondOrderJet`, `HTGeometry/ElementaryHorizonJets`, `HTGeometry/AnalyticJetGerm`, `HTGeometry/JetCoefficientUniqueness` | `GaloisForLFunctions.HTGeometry` | `HasUniformJet2` algebra (`add`, `sub`, `mul`, `const_mul`, `pow_three`, `of_deriv2_bound`, `closedBall_of_punctured`); jets of `√(1−z)`, `(1+√(1−z))^α`, `(√(1−z))⁻¹`; `AnalyticJet2At` germs closed under ring operations, `polynomial_eval`, `cpow_one_add_sqrt`; `eq_zero_of_norm_add_mul_le_mul_sq` (jet coefficients are unique) | `lake build` green (13103 jobs) |
| `RHTower/ThetaCuspHawkingBMHorizonCoordinateJets`, `…BMSelfChannelHorizonJet`, `…BMPrincipalChannelHorizonJet`, `…BMTemporalCurrentHorizonJet` | `RHTower.D4BMJointSource` | `exp_mul_tortoise`; `sourceAmplitude_eq_profile`; `selfClearedProfile_jet` (jet of the cleared self channel through the QNM, per-frequency analytic); `principalProfile_jet`; `clearedDensityProfile_germ` (analytic horizon-jet germ of the cleared density at the QNM) | `lake build` green (13103 jobs) |
| `RHTower/ThetaCuspHawkingBMHorizonModeOuterUniformBound` | `RHTower.D4BMJointSource` | `tortoiseMode_hasDerivAt_continued`, `tortoiseMode_equation_continued` (homogeneous tortoise ODE off the real axis); `tortoiseMode_outer_uniform_bound`: one constant bounds the continued horizon mode on a frequency ball and on every `[T, 0)`, up to spatial infinity (Grönwall, no Gauss summation at the disc boundary) | `lake build` green (13103 jobs) |
| `RHTower/ThetaCuspHawkingBMTemporalCurrentClearedDensity`, `…Bound` | `RHTower.D4BMJointSource` | `clearedTemporalDensity`; `clearedTemporalDensity_eq_current` (clearing factor × radius Jacobian × current = `z_t^u`·core); `_continuousOn`; `_frequency_analyticAt` (at the QNM too); `clearedTemporalDensity_outer_uniform_bound` | `lake build` green (13103 jobs) |
| `RHTower/ThetaCuspHawkingBMTemporalCurrentRadialCutoff`, `…Package`, `…Laurent` | `RHTower.D4BMJointSource` | `patchedProfile`; `compactPart_analyticAt` (Cauchy domination); `cutoff_integral_split` (change of variables `t → z`); `radial_cutoff_package` (cutoff limit with the profile's own counterterms, eventually on the punctured neighbourhood); `clearingSlope` (dslope of the clearing factor, value `physicalFundamentalDenominatorSlope`); `clearedTemporalDensity_fundamental` (density at the QNM = slope × residue density); `jet_coefficients_fundamental`; `mellin_fundamental`; `continuedPhysicalTimeAction_horizon_radial_laurent` | `lake build` green (13103 jobs) |

Scope limits of the toolkit. The stretched-onset pipeline is identified with the fixed one only
through `clearedOnsetDuration s w 1 = clearedOnset s w`; re-deriving the fixed-duration modules
with `u ↦ χ(u/L)` is not done. The Laurent interchange is now applied to the actual
horizon-mode temporal current (step 31, `outer = false`); the normalizable-mode leg
(`outer = true`, a second horizon branch weighted by the connection coefficient) is not assembled.
The counterterm coefficients are existential in the final statement but pinned by the horizon jet
clause (they are unique). Nothing here evaluates a physical current, proves extinction, or selects
the critical line.

## 3. Attack order

1. Step 39 first. If the physical residue is identified with the reduced cokernel −Σ|D|² through
   a nowhere-zero transducer, then off-line D ≠ 0 forces every Laurent factor nonzero, and steps
   33a, 33b, 34 follow. Lean effort on 33/34 before 39 is wasted.
2. Step 31: horizon-mode leg done. Remaining: the normalizable-mode leg (`outer = true`), same
   assembly with `normalizable` in place of `horizon`; needs a uniform outer bound of the
   normalizable mode up to spatial infinity (it decays there) and its horizon jet.
3. Step 36: generalize the Eisenstein Stokes modules from the absolute-convergence family to the
   actual theta fields at Xi parameters; this is also what step 30 needs.
4. Step 35: the ++ SS and VV blocks (the KI scalar-sector reduction with source is the blocker; it is symbolic GR at the scale of the SV module and is the prerequisite of 37, 39, 40).
5. Steps 38, 40, 44 have no candidate mechanism in the corpus.

## 4. Bookkeeping

- Pipeline card: `docs/drafts/pipeline/3-formalized/hb-onset-collision-laurent-toolkit.md`
  (ID `HB-ONSET-COLLISION-LAURENT-TOOLKIT`); cross-reference on
  `docs/drafts/pipeline/1-in-progress/hb-fundamental-radial-source-moment.md`.
- Step 31 card: `docs/drafts/pipeline/3-formalized/hb-radial-laurent-interchange-assembly.md`.
- Umbrella imports: all modules of §2 are wired into `RHTower.lean` / `HTGeometry.lean` in
  place next to alphabetical neighbours. No umbrella build.
- Final audit of the step-31 chain: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMTemporalCurrentRadialLaurent`
  green, 13103 jobs, no warnings in the new modules; `#print axioms` on the final theorem shows
  `propext`, `Classical.choice`, `Quot.sound` only.
- Static lint: the five modules pass; the only reported error is another agent's untracked
  `ThetaCuspHawkingBMQuarticCutoffMellin`, not wired into `RHTower`.
- Frontier map is read-only and unchanged.
- Corpus search coverage: the semantic index reported partial coverage on several deep queries;
  lexical `rg` sweeps confirmed the absence of unique-continuation, Carleman-estimate, Morawetz,
  and Laurent-of-integral theorems.
