Route HB: theta-cusp Hawking causal scattering

Chain (as stated on the cards): literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → common Hawking-clock extinction → RH.

Status key: FULL = Lean, committed, audited. LEAN-WT = Lean written, working tree only, not build-verified by the last map update. PART = Lean for a projected/special sector only. PAPER = paper derivation, no Lean. OPEN = statement known, unproved. UNKNOWN = no mechanism or statement identified yet. DEAD = the sub-approach is a proven no-go.

| # | Step | Short explanation | Status | Lean anchor |
|---|---|---|---|---|
| A. Source and occurrence | | | | |
| 1 | Literal theta-cusp source | Complete theta half-square, Fourier–Bessel/Eisenstein families, joint C∞ regularity, scalar and vector cusp equations | FULL | ThetaCuspHawkingBMAngularScalarEquation, ...EisensteinCuspJointSmooth |
| 2 | Xi occurrence | Every Xi zero is a modular topological-AdS pole with shadow zero and two opposing QNM branches | FULL | thetaCuspHawkingXiDivisor_topologicalBlackHoleQNM_incidence |
| 3 | Causal excitation and Jost zeros | Hardy wavepacket excites each resonance; Jost descendants are simple boundary zeros with nonzero chiral AIME residue | FULL | ThetaCuspHawkingCausalHardy*, ThetaCuspHawkingAIMECrossBranchTeukolskyResidue |
| 4 | Canonical spin-two source | First live order-2m angular jet nonzero; unique factorization V = XiC²·U with U a unit on the strip | FULL | ThetaCuspHawkingBMCanonicalSpinTwoAmputation |
| 5 | Physical angular source value | Assembled source = Λ(5ρ/2−1)Λ(ρ/2)²Λ(1−3ρ/2)/2, zero iff one affine Xi value vanishes | FULL (formula) | physicalSelfSourceCoefficient_fourLambda, ..._zero_iff_xi |
| B. Einstein / metric algebra | | | | |
| 6 | Metric jets and Einstein tensor | KI gauge-invariant reconstruction, full coordinate Einstein tensor, B/C multilinear source, Bianchi, linearized scalar+vector equations at both branches | FULL | CoordinateEinsteinComplexLinearization, ThetaCuspHawkingBMFullLinearEinsteinEquation |
| 7 | Quadratic mixed (+−) correction | Explicit second-order correction, all 16 components, mixed amplitude identified | FULL (this sector) | ThetaCuspHawkingBMQuadraticMixedSource, ...Amplitude |
| 8 | Mixed ++− cubic coefficient formula | L·l + B(p,k₊₋) + B(m,k₊₊) + C(p,p,m if both quadratic corrections are solved | FULL (formula) |cubic_mixed_coefficient, mixedPairedCoefficient_of_quadratic_zero |
| 9 | Angular polarization obstruction | Scalar data cannot determine the sourcpin-two must be retained | FULL (no-go) |ThetaCuspHawkingBMFullPoincareDerivativePullback |
| 10 | Global angular inverse | Unconditional modular gluing, H²/L² regularity,h | FULL | hb-global-angular-resolvent card |
| C. Causal Green and QNM continuation | | | | |
| 11 | Time-domain source and Laplace admission | Onset switching, transform adrvation | FULL | ThetaCuspHawkingBMJointSourceTimeField |
| 12 | Native causal inverse | Legendre kernel, Goursat/Volterra, all three principal channels = physical L² responses | FULL | ThetaCuspHawkingBMFullNativeWave |
| 13 | Residual energy and Friedrichs identification | Joint L², modular germs,ollification, W = JJ*(W+G), AW = W+G | FULL | hb-native-radial-form-admissioncard |
| 14 | Native = physical response | Physical Volterra response equals native revariance | FULL | hb-joint-causal-laplace-identification card |
| 15 | Full causal Green-band landing | Response ≪ (t+1)³e^{B(q)t}; on B(q)<Re w<2 the projection equals the Green profile with Dirichlet trace | FULL |
ThetaCuspHawkingBMNativeGreenBand, ...PhysicalCausalGreenBand |
| 16 | Fixed horizon domain, QNM occurrence | Both fundamental Xi QNMs have zero connection coefficient, Wronskian −w, normalizable solution | FULL | hb-qnm-parameter-continuation card |
| 17 | Meromorphic QNM continuation, Laurent factorization | Residue = angularSoment · clearedOnset / denominatorSlope, slope nonzero | FULL (factorization) |fundamentalSourceMoment_eq_original, ThetaCuspHawkingBMFundamentalGreenFactor |
| D. Action and current | | | | |
| 18 | Einstein action boundary and stream-master current | Local boundary identity, radial symplectic density, all four current components | FULL | hb-einstein-action-boundary-current,
hb-mixed-complete-current |
| 19 | Projected physical mode action | A⁰, A¹ explicit on 3/2<Re w<2; A², A³ vanish for the projected SS/SV pair only | PART | ThetaCuspHawkingBMModeActionReconstruction,
...PhysicalModeAction |
| 20 | Temporal QNM residue | Temporal current continues to both QNMs; residue = field residue × left mode × angular square | FULL (local) |
ThetaCuspHawkingBMPhysicalTimeActionContinuation |
| 21 | Radial residue finite part | Horizon-subtracted mode square = Γ(w)Γ(3/2)/(2Γ(w+3/2)) ≠ 0; integrated finite part = 0 iff K = 0 | FULL | normFinitePart_ne_zero,
physicalRadialResidueFinitePart_eq_zero_iff |
| 22 | Incoming horizon expansion | endpoint(w) + slope(w)·z + O(z²), frequency-uniform, nonzero Gauss factor | FULL | ThetaCuspHawkingBMIncomingHorizonExpansion |
| 23 | Temporal contact horizon factor | Cutoff commutators sum to horizonCoordole cancels | LEAN-WT (0 sorry, umbrella-registered, uncommitted) |ThetaCuspHawkingBMTemporalContactHorizonFactor |
| 24 | Pulse horizon, contact clock, retarded history | Contact moment zero at rded pulse retains its history; contact vanishing ≠ extinction | FULL |ThetaCuspHawkingBMPulseContactClock, ...RetardedPulseClock |
| 25 | Late two-source clock | W_V(h) = A e^{2sh} − B_V e^{(2s+6)h}, terminal cng it is invalid | FULL (negative) | ThetaCuspHawkingBMLateSourceClock |
| 26 | Fixed-clock source translation | Moment h·e^{vh}·A ≠ 0; raw switched-source covariance unavailable even on the line | FULL (negative) | sourceAndContact_clockMoment |
| 27 | Incoming current and clock moments | Four incoming components, exact trases, radial mass balance | FULL | ThetaCuspHawkingBMIncomingClockTranslation,...FullIncomingCurrent |
| 28 | Full angular circle propagation | Circle Green law, Darboux, closed-conee kernel nonzero | FULL | ThetaCuspHawkingBMFullAngularCircleAction |
| 29 | Source-contact rigidity | Coefficient (λ−2)(λ−6)(3λ−2) ≠ 0 at every Xi occurrence; bilinear, not a positivity | FULL | ThetaCuspHawkingBMSourceContactRigidity |
| 30 | Spin-two contact balance (eqs 6, 9) | Quartic-period Green balance with tion; Re(13λ−6−μ) < −23/4 | PAPER | hb-source-contact-spin-two-balance card |
| **E. Open radiative core** | | | | |
| 31 | Laurent/horizon interchange | Pass Laurent extraction through the full rular current | OPEN | — |
| 32 | Radial contact and QNM-boundary traces | Retain radial source contact, derivative/current traces, integrated horizon and cusp limits | OPEN | — |
| 33 | Source factors nonzero | Prove fundamentalSourceMoment ≠ 0 and clearedOndifferent object d4FundamentalQNMContinuedRadialMoment_xi_ne_zero exists |
| 34 | Affine Xi collision control | Show ξ(5ρ/2−1), ξ(ρ/2), ξ(3ρ/2) are all nonzero at an actual zero ρ | UNKNOWN (needs arithmetic input; no statement) | — |
| 35 | Solve ++ and +− quadratic corrections | Required to remove the changing-8 | OPEN (mixed sector only, step 7) | hypotheses hpp, hpm in step 8 |
| 36 | Angular/cusp integration, nine-channel current | Integrate retained flux; compare complete Einstein four-current across independent SS/SV/VV | OPEN | — |
| 37 | Corrected mixed action coefficient | Evaluate the integrated ++− coefficurrent | OPEN | — |
| 38 | Left-QNM / retarded-advanced data | The original BM testing leg vanishes on critical copies; a replacement probe retaining the first live jet is not identified | UNKNOWN |
ThetaCuspHawkingBMSourceProbeRangeClassification (no-go) |
| 39 | Spin-two/AIME coefficient match | Target known: C_phys = −Σ·|D|², Σ > 0; need Re C_phys ≥ 0 from the source | OPEN | hbXiPeierlsClockDefectToFullCokernelSusceptibility |
| 40 | ++ extinction before divisor selection | A source-derived law forcing D scalar, meromorphic, finite-rank, finite-energy Hilbert, bounded/Krein, passive,Schwarz-odd, finite-variation, and perturbative-clock mechanism is DEAD; survivor must be nonscalar, singular, or infinite-energy | UNKNOWN (the producer) | 38 no-go cards in
5-failed/hb-* |
| 41 | Extinction ⇒ RH | Universal extinction, standard-clock mixing, Ward cancellation, centralizer rigidity are each ⟺ RH | FULL (receivers) |
riemannHypothesis_iff_hbXiPhaseSensitiveChiralWardAmplitudeCancellation, ..._Fug, orbit cut = −(PW imbalance)² |
| F. Static front (alternative) | | | | |
| 42 | All-replica graph-local completion | Hall rank, no zero atom, Dyson bounnt near-action law | FULL | hawking-total-plus-plus-minus-cokernel-schur-section|
| 43 | Static RH receivers | Centralizer rigidity, KMS Cayley mixing, FriedrichmannHypothesis_iff_thetaCuspHawkingTiltedResonanceCentralizerRigid,..._KMSCayleyScatteringMixing |
| 44 | Phase-sensitive theta–Hawking KMS law | Producer needed; generic positivtralizer modes evade KMS dissipation yet keep positive Wigner delay | UNKNOWN | — |

Reading of the table. Steps 1 through 30 are the built infrastructure: 27 fully in Lean, one working-tree leaf, one projected sector, one paper balance. Steps 31 through 40 are the live
core. Of those, four are unknowns, not just unproved: the affine collision contleft probe (38), the extinction producer (40), and the static KMS law (44). Noroute step proves or disproves RH.

Evidence.
- Read: frontier map lines 1563–1754 in full, plus lines 44, 74, 86, 88, 218, 2203, 2496, 2518, 2727, 2765–2776, 2879–2906, 2958–2998, 3009, 3032. Cards read:hb-source-contact-spin-two-balance.md, hb-physical-mode-action-contact.md, hb-fixed-clock-source-translation.md, hb-source-contact-rigidity.md.
- Corpus searches run (--no-refresh, hybrid): route overview, fundamentalSourcenel, BM QNM occurrence, affine Xi collision, ++/+− quadratic corrections.Semantic index reported partial coverage on three of six.
- Greps: 13 anchor theorem names confirmed present in formal/GaloisForLFunction endpoint theorems across 73 Hawking modules; 1008 ThetaCuspHawking* modules; the three working-tree leaves contain no sorry/admit.
- Pipeline counts: 48 HB cards in progress, 273 formalized, 38 failed, 0 fully-y.

### review
Per-step findings (numbers follow the earlier table)

| # | Open step | Existing code found | Effect | What remains |
|---|---|---|---|---|
| 31 | Laurent/horizon interchange | normalizedFirstEndpointMellin_uniform_bound and _tendsto (uniform in w for Re w ≥ β > −2, given a Lipschitz constant C at z = 0); incomingResponseEndpoint_meromorphic and continuedResponse_horizon_quadratic_expansion (supply that C on a frequency neighbourhood); laurentCoeff_analytic_div_sub (residue of A(s)/(s−p) is A(p)); the parametric-analyticity recipe in memory | Simplify to a recipe: write the radial density as z^w·G(w,z) with G uniformly Lipschitz, get the cutoff finite part as a locally uniform limit of analytic functions, then read the residue off the analytic numerator | Assemble the recipe for the projected temporal current. The angular/cusp half of the interchange is not covered |
| 32 | Radial contact and horizon traces | continuedResponse_horizon_current_finite_part_zero: the horizon Wronskian bracket minus its counterterm tends to 0 for every w with nonzero connection coefficient | Simplify: the horizon-face finite part is identically zero on a punctured neighbourhood of each QNM, so its Laurent coefficient is zero once step 31's interchange holds for that face | The germ at the QNM itself, and the cusp faces |
| 33a | clearedOnset ≠ 0 | onsetCorrection is ∫₀¹(χ−1)e^{(2s−w)u}du with χ = smoothTransition. One integration by parts gives clearedOnset(s,w) = ∫₀¹ χ′(u)·e^{(2s−w)u}du, the Laplace transform of the derivative pulse | Circumvent: this transform is an entire, nonconstant function of the onset duration L (value 1 at L → 0), so it vanishes only for a discrete set of durations. Choosing a generic onset removes the factor | The physical point has Im(2s−w) = ±(7/2)τ or ±(9/2)τ, so no sign argument works for the fixed onset. Circumvention needs the onset duration threaded as a parameter through the onset modules |
| 33b | fundamentalSourceMoment ≠ 0 | fundamentalSourceCore and sourceRemainder are explicit. Substituting u = √(1−z) turns the moment into 2a²∫₀¹(1−u)^w(1+u)^{2s}u²(A+Bu²)du, a two-term Beta·₂F₁(−1) expression; SecondHarmonicGaussEulerSummation gives the closed forms | Simplify the statement only | No Kummer constellation, so no Gamma-ratio closed form. TransferCollisionRigidity shows the digamma log-slope method, but it applies to Gamma ratios, not to this ₂F₁ value |
| 34 | Affine Xi collisions | xi_ne_zero_of_one_le_re (RHLadderTheory); xi_divisor_support_im_ne_zero; continuedPhysicalSelfResponse_nonremovable_iff_elementary names the three factors ξ(ρ/2), ξ(3ρ/2), ξ(5ρ/2−1) for Re ρ = σ > 1/2 | Partially circumvent. 3ρ/2 is zero-free for σ ≥ 2/3 and for σ < 2/3 the partner is a strict-right zero with σ ≥ 3/4 whose own 3ρ/2 partner is zero-free. ρ/2 collisions descend by halving the ordinate toward the real point 2/3 where ξ ≠ 0, so discreteness ends the chain. 5ρ/2−1 is zero-free for σ ≥ 4/5 | The 5ρ/2−1 factor for σ ∈ (1/2, 4/5). At σ = 3/5 the partner lies on the critical line, so no descent can proceed, and the reflection map σ ↦ 2−5σ/2 has a repelling 2-cycle at σ = 4/7, so chains need not terminate |
| 33/34 | Both together | The residue factorization physicalSelfResidueCoefficient_fundamental_value versus the reduced cokernel K = −Σ|D|² (hbXiPeierlsClockDefectToFullCokernelSusceptibility) | Circumvent by ordering: if step 39 identifies the residue with K through a nowhere-zero transducer, then off-line D ≠ 0 forces every factor nonzero, and 33/34 follow for free | Attack 39 before 33/34; do not spend Lean effort on 33/34 first |
| 35 | ++ and +− quadratic corrections | forcedMetricField_einstein solves the doubled-rate (++) correction for the mixed scalar/vector block in all 16 components; d4BMPlusPlusRadialBoundaryProblem_eq_green gives existence and uniqueness of the ++ radial reduced Green action; d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq shows the +− correction enters the causal cut only through the retarded-minus-advanced jump of the +− response | Circumvent half of it: the +− frequency is the real, nonresonant value −3, so its response has no causal jump and the +− arm drops from the cut. Only the ++ jump matters in the cut formulation | ++ SS and VV blocks (card lists them as open). The integrated-action formulation (step 37) still needs k₊₋ |
| 36 | Angular/cusp integration | angular_current_green (pointwise hyperbolic Green identity for arbitrary smooth fields, currently private), angularCurrent_integral, limitingFlux with responseFlux_tendsto, D4BMCuspRapidDecay product lemmas, the two Eisenstein Stokes modules (truncated modular domain, side cancellation, paired cusp top) | Simplify: the truncated-domain Green theorem with translation/inversion cancellation exists, but only for D4BMnceParameter fields | Generalize the Stokes modules from theabsolute-convergence Eisenstein family to the actual theta fields at Xi parameters. This is also exactly what step 30 (spin-two balance) needs |
| 37 | Mixed action coefficient | mixed_complete_action_current, mixed_radial_aCoefficient_of_quadratic_zero | None new | Unchanged |
| 38 | Left-QNM probe | Canonical left covectors (d4BMXiPlusPlusComplementaryLeftConnectionCovector), ThetaCuspHawkingBMCanonicalLeftResponseWard, sourceJet; everything else returned is
a no-go module | None | Still unknown |
| 39 | Residue ↔ clock-defect identification | ThetaCuspHawkingBMTotalRenormalizedAngularPeriod: P_ret = FP_conservative + i‖Radiation‖² with the radiation flux decomposed as two squared
norms | None. This fixes the target shape but takes the conservative finite par | Derive that finite part from the literal action |
| 40 | ++ extinction producer | Rellich identities on the modular core for Maass cusp forms (SelbergMaassDilationRellich.core_rellich_identity,
SelbergMaassPhaseRellich.phase_rellich_identity); Krein/rigged interfaces (Denie, SecondHarmonicOuterResponseKrein); DirichletHilbertRiggingBarrier is a no-gofor diagonal riggings | Template only: the dilation-stress Rellich identity is the shape of the sign-definite estimate the spin-two card asks for, but it needs an eigen-equation, and the
theta half-square obeys ΔQ = 2λQ + E instead | No unique continuation, Carlemanntity exists anywhere in the corpus |
| 44 | Phase-sensitive KMS law | finiteKMSDissipativeMoment, scalarWignerSmithDelay, thetaCuspHawkingDavies_detailedBalance, thetaCuspHawkingFullMirrorKMSDetailedBalance | None; all
receivers or no-gos | Still unknown |

Cheapest wins, in order

1. clearedOnset identity. One integration-by-parts lemma proves clearedOnset eq of the derivative pulse. Cheap in Lean and it exposes the onset-durationfreedom.
2. Two of three collision factors. The 3ρ/2 and ρ/2 cases need only xi_ne_zero_upport_im_ne_zero, and continuity of ξ. The 5ρ/2−1 factor stays open below σ =4/5.
3. Drop the +− correction from the cut. Prove the +− response has no retarded/a−3, then only the ++ correction is needed for extinction in the cut formulation.
4. Step 31 recipe. All ingredients exist; the work is assembly.
5. Reorder 33/34 after 39. Both are consequences of a nonzero transducer identi
### implementation record (2026-09-11)

Implemented from the "cheapest wins" list. Every theorem below is unconditional (no `sorry`,
`axiom`, or extra premise beyond the stated real/complex variables); each module passed
`lake env lean` with zero errors and zero warnings; oleans published with `lake env lean -o`.

1. **clearedOnset identity and onset-duration genericity.**
   - `GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOnsetPulseTransform.lean`
     (namespace `RHTower.D4BMModularCore`): `onsetPulseTransform z = ∫₀¹ χ'(u) e^{z u} du`;
     `onsetPulseTransform_sub : onsetPulseTransform (v - w) = 1 + (w - v) * onsetCorrection v w`
     (one integration by parts); `onsetPulseTransform_zero`; `differentiable_onsetPulseTransform`
     (entire); `onsetPulseTransform_ray_eventually_ne_zero` (zeros isolated along every ray
     `L ↦ L z₀`); `exists_real_near_onsetPulseTransform_ne_zero`;
     `onsetPulseTransform_ofReal_re_pos` and `_ne_zero` (strictly positive at real exponents).
   - `GaloisForLFunctions/RHTower/ThetaCuspHawkingBMClearedOnsetPulseTransform.lean`
     (namespace `RHTower.D4BMJointSource`): `clearedOnset_eq_onsetPulseTransform :
     clearedOnset s w = onsetPulseTransform (2 s - w)`; `clearedOnset_source_rate`;
     `clearedOnset_ne_zero_of_im_eq_zero` (real exponent difference);
     `clearedOnsetDuration s w L := onsetPulseTransform (L (2 s - w))` with
     `clearedOnsetDuration_one`, `_zero`, `differentiable_clearedOnsetDuration`,
     `clearedOnsetDuration_eventually_ne_zero`, `exists_real_duration_clearedOnsetDuration_ne_zero`.
   - Scope: this isolates the onset factor of the fundamental Laurent coefficient and proves it is
     generically nonzero in the onset duration. Re-deriving the fixed-duration pipeline with a
     stretched transition `u ↦ χ(u/L)` is not done; the identification is
     `clearedOnsetDuration s w 1 = clearedOnset s w`.

2. **Affine collision control (two of three factors).**
   - `GaloisForLFunctions/RHTower/XiAffineCollisionControl.lean` (namespace `RHTower`):
     `xi_three_half_ne_zero_of_re` (`Re ρ ≥ 2/3`), `xi_five_half_sub_one_ne_zero_of_re`
     (`Re ρ ≥ 4/5`), `xi_three_half_collision_partner` (a `3ρ/2` collision forces `Re ρ < 2/3`
     and the partner is strict-right, below `Re = 1`, with zero-free `3/2`-partner);
     half-descent `xiHalfDescent ρ n = 2/3 + (-1/2)^n (ρ - 2/3)` with `_re`, `_im`, `_tendsto`;
     `exists_xiHalfDescent_half_ne_zero` (isolation of Xi zeros at the real point `2/3`);
     `exists_xi_zero_half_ne_zero` (from every strict-right nonreal zero, a strict-right nonreal
     zero `ρ'` with `xi (ρ'/2) ≠ 0`); `exists_strict_right_representative`.
   - `GaloisForLFunctions/RHTower/ThetaCuspHawkingBMAngularSourceCollisionControl.lean`
     (namespace `RHTower.D4BMJointSource`): `physicalSelfSourceCoefficient_zero_iff_of_two_thirds_le`,
     `physicalSelfSourceCoefficient_zero_iff_half_of_four_fifths_le`,
     `physicalSelfSourceCoefficient_ne_zero_of_four_fifths_le`,
     `exists_strict_right_zero_half_ne_zero_of_copy` (for copies with `Re ≠ 1/2`).
   - Not controlled: the `5ρ/2 - 1` factor for `1/2 < Re ρ < 4/5`. At `Re ρ = 3/5` the partner
     lies on the critical line, so no descent applies; the reflected map `σ ↦ 2 - 5σ/2` has a
     repelling 2-cycle at `σ = 4/7`, so chains need not terminate.

3. **Drop the +− correction from the cut.** Already in the corpus:
   `ThetaCuspHawkingHBPeierlsStationaryChannelElimination`
   (`d4GaugeFixedTeukolskyTotalPlusPlusMinusCokernelCausalCut_eq_radiative_of_Peierls` and the
   `_eq_zero_iff_radiative_of_Peierls` form): under a cyclic Peierls pairing with causal
   skewness, the stationary `+-` arm is a vanishing self-pairing and the full cut equals the
   radiative `++` projection. Nothing new was written for this item.

4. **Step 31 recipe.** The corpus already had `firstEndpointMellinRemainder_differentiableAt`
   (uniform horizon Lipschitz bound ⇒ frequency holomorphy of the remainder). Added
   `GaloisForLFunctions/HTGeometry/FirstEndpointMellinLaurentInterchange.lean`
   (namespace `GaloisForLFunctions.HTGeometry`): `firstEndpointMellin_differentiableAt` (full
   finite part with endpoint counterterm), `firstEndpointMellin_analyticAt`,
   `firstEndpointMellin_const_mul`, `firstEndpointMellin_div_sub`, and
   `laurentCoeff_firstEndpointMellin_div_sub`: the order `-1` Laurent coefficient of the finite
   part of `F u t / (u - w)` at `w` equals the finite part of `F w`. Applying this to the actual
   projected temporal current (supplying its uniform horizon Lipschitz constant from
   `ThetaCuspHawkingBMIncomingHorizonExpansion`) remains open.

5. **Reorder 33/34 after 39.** Recorded in the pipeline card; no Lean content.

### audit and bookkeeping (2026-09-11, later)

- **Axioms.** `#print axioms` (scratch file importing all five modules) on the sixteen main
  theorems: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `axiom`, `opaque`,
  `unsafe`, or added premise.
- **Umbrellas.** Imports inserted in place next to alphabetical neighbours:
  `RHTower.lean` — `XiAffineCollisionControl` (after `XiAdmissibleHeights`),
  `ThetaCuspHawkingBMAngularSourceCollisionControl` (after `…BMAngularScalarEquation`),
  `ThetaCuspHawkingBMClearedOnsetPulseTransform` (after `…BMCausalSchwarzSupport`),
  `ThetaCuspHawkingBMOnsetPulseTransform` (after `…BMOnsetGreenReconstruction`);
  `HTGeometry.lean` — `FirstEndpointMellinLaurentInterchange` (after `FirstEndpointMellin`).
  No umbrella build was run.
- **Static lint** (`scripts/formal_tools.py lint`): the only error is another agent's untracked
  module `ThetaCuspHawkingBMQuarticCutoffMellin` not yet wired into `RHTower`; none of the five new
  modules is flagged.
- **`lake build <module>` audit** (final gate, one process at a time, foreground):
  `XiAffineCollisionControl` green (8746 jobs replayed, 33 s);
  `ThetaCuspHawkingBMOnsetPulseTransform` green (87 s);
  `ThetaCuspHawkingBMClearedOnsetPulseTransform` green (62 s);
  `FirstEndpointMellinLaurentInterchange` green (11 s);
  `ThetaCuspHawkingBMAngularSourceCollisionControl`: lake is rebuilding ~110 stale dependency
  oleans in the `ThetaCuspHawkingBMPhysicalAngularSourceXi` cone (other agents' modules whose
  lake traces were out of date); the first bounded run stopped at job 12824/12907, the resumed
  run is at 12869/12977 with zero errors at the time of writing. `lake env lean` on the module
  itself was clean.
- **Process hygiene.** No lean/lake process of this session was left running after each step;
  the other lean processes on the machine belong to other agents (`/tmp/hb-quartic-green.lean`,
  `/tmp/sqb99_*`, `/tmp/hb-opposite-factor-0911m.lean`, a `lake build` of
  `DeningerL1CofinalPrimeTomography`) and were not touched.
- **Card.** `docs/drafts/pipeline/3-formalized/hb-onset-collision-laurent-toolkit.md`
  (ID `HB-ONSET-COLLISION-LAURENT-TOOLKIT`). It was first written under the decoy
  `formal/docs/…` tree and swept into another agent's auto-commit `0e5476c39` there; moved with
  `git mv` to the repo-root pipeline folder (staged rename, not committed). The five Lean modules,
  the earlier `docs/notes.md` record, and a cross-reference log entry on
  `docs/drafts/pipeline/1-in-progress/hb-fundamental-radial-source-moment.md` were also included
  in that auto-commit.
- **What the frontier gains, in step numbers of the first table.** Step 33a (`clearedOnset ≠ 0`):
  circumvented by onset-duration genericity, positive at real exponents; the fixed unit duration
  is still not proved nonzero at the physical point. Step 34 (affine collisions): `ρ/2` and
  `3ρ/2` factors controlled, `5ρ/2 − 1` open for `1/2 < Re ρ < 4/5` with an explicit obstruction
  at `Re ρ = 3/5`. Step 31 (Laurent/horizon interchange): abstract interchange theorem in place;
  the application to the projected temporal current is the remaining assembly. Step 35: the `+−`
  arm of the cut was already eliminated in the corpus. Steps 32, 33b, 36–40, 44: unchanged.
