HB full temporal/metric/QNM matching remains OPEN. RH and impossibility are not proved.
Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Immediate authorized scope is full matching or impossibility. Do not reread computations/results.md, edit frontier, run experiments, Git, launch.sh, #print axioms, heartbeat/transparency/instance hacks, or umbrella/full builds. One foreground Lean/Lake job at a time. No subagents authorized. Methods and AGENTS were read.

DE/DF completed and CLEAN:
10 new leaves installed, individually scratch-checked and isolated exact-leaf lake-audited, all umbrella imports wired. scripts/formal_tools.py lint passed (existing large-file warnings). All 94 owned /tmp/hb-de-* and /tmp/hb-df-* paths removed, including isolated audit tree; no owned Lean/Lake process remains. All 10 root oleans retained. Needed missing existing cache leaves were individually repaired without source edits (DE: BogoliubovBornEndpoint, XiReciprocalTranslationSeamNormLaw, ReflectedBiHeatMultiplicityLeadingJetBalance; DF: SelbergMaassTraceEnergy). Do not rebuild these unless a concrete missing-file error recurs.
Own facts now end F267 in docs/drafts/pipeline/1-in-progress/hb-own-research-facts.md.
Own contact card docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md has exact current state and remaining construction. Frontier and universal STATUS untouched.

New module paths all formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBM<suffix>.lean:
1 OriginalMetricSourceJets: actual source coordinate derivatives identified with base operators; physical U=R U0, partialY U=R exp(-k) U1, Delta U=R(exp(2k)U2+U3-U1).
2 OriginalMetricSourceTransfers: four unchanged transfer cuts = original normalized source/reader products (source factors R² exp(-wp), forcing R exp(-wp)).
3 OriginalCompleteTransfer: complete finite metric boundary minus original 3 cusp powers equals all 4 product moments and both endpoints. f=R²-1 cancels every radius denominator, including R² Z=f. radialTransfer_continuousAt derives actual joint (p,x) continuity at fixed positive L.
4 OriginalBoundaryCollarBounds: D_j-H_j bounded C exp(-L-Nk-p) for every j in a derived right half-plane. Full boundaryError bound C exp(-L-Nk), collar-integrated limit 0 uniformly for arbitrary positive temporal intervals and radial caps. Norm bounds alone do not establish radial admission.
5 OriginalBoundaryRestoration: actual leading transfers separately compact-integrable via uniform limits of actual smooth fields. physical_boundary_restoration attaches literal complete physical metric boundary, its 3 CTs and leading H functional to boundaryError. physical_boundary_collar_joint_limit retains Jacobian 1/2. Boundary radial admission and identifying H with prescribed full-action horizon/corner terms still open.
6 OriginalSourceTailCollar (audit 107s): namespace D4BMOriginalSourceTailCollar. tailSet k={z:UpperHalfPlane | exp k<z.im}, original modular measure finite. tailDensity = exp(-wp)*reader(q,w,L)*sourceJet0(p,L,z.re,log im)*angularJetfalse. horizonTailDensity uses actual horizon reader/source. originalPeriodError = exp(-wp)*reader*(originalFiniteHeightPeriod(p,p+L,exp k)-originalRadialPeriod(p,p+L)); horizonPeriodError = -integral tailSet horizonTailDensity. original_period_error_tail exact original tail identity; tail_density_integrable and horizon_tail_integrable separate angular admission; original_period_mixed_error gives C exp(-L-Nk-p) for p>0,k>=0,exp k>=4,eventually L,right half-plane.
7 OriginalSourceTailAdmission (audit 68s): namespace D4BMOriginalSourceTailAdmission. tail_density_joint_continuousAt uses literal physical potential/principal coefficients, no hypotheses. jointMeasure L0 k=(volume.restrict(Ioi L0 × Ioi 0)).prod(measure.restrict(tailSet k)), PUBLIC. horizon_joint_measurable derived via actual L=exp(r) approximants. joint_tail_error_integrable line156: on derived right half-plane, exists L0>0, all k>=0, actual tailDensity-horizonTailDensity absolutely integrable on full product. original_period_error_integrable line198: period error minus leading horizon period absolutely integrable on unbounded (L,p) product (exp k>=4). Source-tail Fubini is now actual admission, not default-zero integral.
8 OriginalCanonicalHorizon (audit 88s): generic helper namespace GaloisForLFunctions.HTGeometry:
 endpointJetValue F w = limUnder nhdsGT0 (F w);
 endpointJetSlope F w = limUnder nhdsGT0 ((F w z-endpointJetValue F w)/z).
 HasUniformJet2.canonical_coefficients hb hw fixes both coefficients; AnalyticJet2At.canonical proves actual limit coefficients analytic at center and gives uniform canonical jet on same closed ball; HasUniformJet2.coefficients_unique.
 Physical namespace RHTower.D4BMOriginalCanonicalHorizon:
 gauss_germ and negative_gauss_germ at EVERY nonreal w, derived from horizonGauss_uniform_second_bound.
 original_profiles_germ: actual incomingProfile/oppositeProfile of OriginalMetricHorizon have analytic quadratic jets at every nonreal w.
 incomingValue, incomingSlope, oppositeValue are those actual canonical limits.
 original_coefficients_analytic line151: all 3 analytic at EVERY nonreal frequency.
 original_incoming_coefficients_unique and original_opposite_coefficient_unique: any admitted actual local jet agrees with these coefficients on its full parameter set.
9 OriginalCanonicalRestoration (audit 153s): namespace D4BMOriginalCanonicalRestoration.
 canonical_horizon_restoration line73: for ANY nonreal w0 with Re w0>-2, exists R,B>0 B<=1/2, every 0<b<=B: horizonFinitePart with the SAME canonical coefficient family analytic at w0; for every w in ball(w0,R), actual pullback integral e..b minus 2 powers and log CT tends to that FP as e→0+.
 canonical_radial_restoration line169 is same theorem for literal original integral tortoiseOf(e)..tortoiseOf(b).
 canonical_regular_part_analytic line193 adds original regularOuterMoment to prove local analyticity of complete OriginalMetricRadial.regularFinitePart with canonical coefficients, any nonreal Re>-2.
 This closes regular coefficient/restoration domain gap but not full matching.
10 OriginalCanonicalMetricCutoff (audit 184s): namespace D4BMOriginalCanonicalMetricCutoff.
 original_green_endpoint_below: general s,chi,amp,J,K,w, w.im!=0, Re w>-2, w-2s!=0; exists R,B>0, B<=1/2, every positive b<=B, source primitive at b analytic at center and for u in ball off connection zeros, greenHorizonAmplitude(...,u)=incomingResponseEndpoint(...,u,b). Proof evaluates incomingSourcePrimitive_common_data split at any smaller interface and uses actual quotient horizon limit.
 gradient(q,br) PUBLIC = reducedGreenGradient(chi,s,1).
 canonicalGreenCounterterm: original Green CT using actual greenHorizonAmplitude instead of local E_b.
 canonicalMetricCutoff line59: literal integral of OriginalMetricOuter.outerDensity from tortoiseOf(e)..0 + greenCoefficient*canonicalGreenCT - forcingCoefficient*forcingCounterterm(canonical incomingValue,incomingSlope,oppositeValue), no b parameter.
 original_metric_cutoff_canonical line69: any actual q/br/amp, nonreal Re w>-2, derives R,B; all small b, u in ball off connection zeros and all e, canonicalMetricCutoff equals existing radialCutoff with canonical regular coefficients and local b. Source-pole exclusion derived from currentRate_re_lt, NOT assumed.

CURRENT NEXT HARD ATTACK:
Construct the global cutoff-limit of canonicalMetricCutoff, prove it meromorphic on D={w: Im w!=0, Re w>-2}, retain physicalCornerCandidate, and identify its canonical QNM analytic removal. Then attach to fully independent metric/time/cusp/horizon restoration. No code for global value exists yet.
Useful direct construction:
- Combine incomingPairingFinitePart_horizon_restoration_below, oppositePairingFinitePart_horizon_restoration_below, new canonical_radial_restoration and new original_green_endpoint_below at one common smaller b and intersect frequency balls.
- Incoming theorem gives analytic incomingNormFinitePart, incomingSourcePairingFinitePart, incomingSourcePrimitive at b and actual incoming cutoff convergence, valid any nonreal Re>-2 and w-2s!=0.
- Opposite theorem gives analogous analytic norm/source parts and cutoff convergence.
- incomingResponseEndpoint(...,b) = continuedResponse(b)/horizon(b) - incomingSourcePrimitive(b); meromorphic from continuedResponse_meromorphicAt and actual primitive/horizon analyticity. Use the small-b analytic primitive supplied by incoming theorem, not the existential fixed-b endpoint meromorphy theorem.
- OriginalMetricRadial.radialCutoff_decomposition line133 attaches sum of both Green cutoffs and full forcing intervals to literal original outerDensity cutoff.
- OriginalMetricRadial definitions CURRENT: regularFinitePart = horizonFinitePart(K=gradient) + regularOuterMoment(tortoiseOf b); radialFinitePart = greenCoefficient*normalizableOuterPairing + forcingCoefficient*regularFinitePart. Do NOT use old summary aliases nativeForcingHorizon/shiftedForcingOuterMoment; they are not actual names here.
- normalizableOuterPairing (JointSource namespace, PhysicalNormalizablePairing line103) = normalizableHorizonPairingFinitePart + continuedReducedOuterPairing.
- incomingPairingFinitePart=E_b*incomingNormFinitePart+incomingSourcePairingFinitePart.
- oppositePairingFinitePart=(connection/(2w))*(E_b*oppositeNormFinitePart+oppositeSourcePairingFinitePart).
- ReducedOuterPairing.clearedReducedOuterPairing_analyticAt line92 valid every nonreal Re>-2 and T<0. clearedReducedOuterPairing_eq line178 = reducedGreenClearingFactor*continuedReducedOuterPairing off connection/source zeros. This gives meromorphic actual outer integral by punctured-germ equality to numerator/denominator.
- Define canonical global value as limUnder nhdsGT0 of the SAME cutoff. Every local radial finite-part value agrees off connection zeros by Tendsto.limUnder_eq. MeromorphicAt.congr then glues, using connection_eventually_ne_zero. No need to force one interface across an entire path or choose unrelated local functions.
- Existing OriginalHorizonGreenMatch.greenHorizonAmplitude_local/meromorphic, continuedCornerAmplitude_meromorphic cover entire nonreal Re>-2. Actual physicalCornerCandidate (OriginalCornerForcing line368) retains continuedCornerAmplitude, its frequency derivative, and derivative of continuedForcingTransform. Verify latter's exact regularity API before use. Mathlib Analysis/Meromorphic/Basic.lean: MeromorphicAt.div line312, protected MeromorphicAt.deriv line374 are present.
- Existing OriginalMetricQNM.original_corrected_action_QNM line182 has LOCAL existential coefficients; cannot simply assume these coincide globally. Use canonical construction to obtain canonical QNM removal (or establish precise local coefficient/finite-part equality). It gives finite value, not value zero.

Remaining full metric limitations:
source-tail product admission closed, but boundary radial admission, full endpoint/bulk assembly, retained horizon/corner counterterm attachment, independent outer-region restoration and complete metric-to-QNM identification are not proved.
Do not label finite identity / norm estimates / regular-term restoration as full matching.
No new mathematical no-go or impossible-RH claim.

Searches used broad OR and deep mechanism/method requests; all candidate/source-argument/idea/ingredient metadata reviewed. Results partial, many compiler entries source-only/pending (latest inventory58034,compiler pending45179), no assertion corpus compiler freshness. Existing source/Lean applicability was checked. Broad primary arXiv items were read earlier in DF (2603.10804 polyhomogeneous Radon mapping) and DE (2601.03616 transmutation); no theorem depends on them.
No numerical work, no experiments reviewed, no #print axioms, no Git, no launch.sh, no heartbeat or instance hacks.