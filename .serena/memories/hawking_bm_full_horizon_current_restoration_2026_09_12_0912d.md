# HB full temporal horizon current: identification, regularity, restoration, residue — 0912d

Goal ACTIVE, UNBOUNDED, UNPROVED. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Prior state: `mem:hawking_bm_same_cutoff_both_horizon_branches_2026_09_12_0912c`.
Latest steering: optimize Lean, NO heartbeat/resource increases, NO axiom checks. Analytical only. Frontier READ ONLY. No Git/launch.sh, full/umbrella builds, numerical experiments or subagents. One owned foreground Lean/Lake at a time.

## Completed and installed; do not recheck unchanged
All files under formal/GaloisForLFunctions/RHTower, namespace RHTower.D4BMJointSource.
All checked with lake env lean /tmp/scratch and warning-free exact-module Lake audits in source-less cache-only package. Default limits. Source+five artifacts installed. Three RHTower umbrella imports wired.

1. ThetaCuspHawkingBMTemporalCurrentHorizonIdentification.lean,107lines; audit80s,2jobs,4421cached project dependencies.
- selfPart_eq_physicalResponse line10:
 z(t)^(w/2)*selfPart(q,branch,a,w,z(t)) = D(w)*continuedPhysicalSelfResponse(q,branch,w,a,t).
 t<0, w-2s≠0, connection(w,chi)≠0. Uses exact physicalSelfResponse_decomposition and clearedReducedGreen_eq, all3 principal channels.
- contactPart_eq_sourceProjection line26: analogous identity for full horizonRegularAngularSourceProjection; needs only t<0. Actual amplitude source and quotient retained.
- clearedDensityCore_eq_physicalCurrent line42: z(t)^w*clearedDensityCore = D*((radius²-1)*continuedPhysicalTimeAction outer=false).
- clearedDensityProfile_eq_physicalCurrent line71: restore z^(w-1), divide by 2*z*sqrt(1-z). Exact original radial Jacobian.
- clearedDensityProfile_eq_actualAction line92: on original physical band, equals actual physicalProjectedModeAction component0 (outer=false); uses existing continuedPhysicalTimeAction_eq_actual with positive angular height.
Proofs use small factored identities, field_simp, one linear_combination. Removed redundant ring and push_cast calls. No backward/resource options added.

2. ThetaCuspHawkingBMTemporalCurrentHorizonRegularity.lean,173lines; audit36s,2jobs,4421cached.
- clearedReducedGreen_continuousAt line10: nonreal Rew>-2,t<0; includes connection zeros! Direct moving-endpoint derivatives of undivided source moments plus explicit lift. Does NOT divide by connection.
- tortoiseOf_continuousAt line24 for z∈(0,1).
- selfClearedProfile_continuousAt30, principalProfile_continuousAt39, amplitudeProfile_continuousAt48, quotientProfile_continuousAt56, gaussProfile_continuousAt69.
- clearedDensityProfile_continuousAt75: whole profile for nonreal Rew>-2 and z∈(0,1), even self-connection zeros.
- clearedDensityProfile_analyticAt110: same strip, actual source pole excluded and all3 principal connections nonzero; self connection need NOT be nonzero. Actual numerator analytic through QNM.
Optimizations: replaced broad fun_prop on whole current/source polynomial with explicit add/mul/div composition and existing polynomial evaluation continuity. ContinuousAt.comp prematurely unifies composite evaluation point; use comp_of_eq hi rfl. For quotient continuity, use simpa only [horizonQuotientBase_eval,horizonQuotientSlopePoly_eval,Function.comp_def,Pi.add_apply,Pi.mul_apply,Pi.div_apply,quotientProfile,reducedHorizonQuotient] using! ... to resolve complex instance diamonds. Complex nonzero casts need exact_mod_cast positive real, not positivity alone. One slow owned scratch run interrupted then replaced with explicit composition; no live process remains.

3. ThetaCuspHawkingBMTemporalCurrentHorizonRestoration.lean,145lines; audit110s,2jobs,4425cached.
- continuedTemporalRadialDensity line14:
 j(q,branch,a,zang,w,z) =
 ((tortoiseRadius(tortoiseOf z)^2-1)*continuedPhysicalTimeAction(q,branch,w,a,false,tortoiseOf z,zang))
 /(2*z*sqrt(1-z)).
 This is actual temporal density in horizon coordinate with radial Jacobian. No independent full r-variable integral substitution theorem added here.
- clearedDensityProfile_eq_radialDensity21:
 z^(w-1)*F(w,z)=D(w)*j(w,z), z∈(0,1),source/selfconnection nonzero.
 F=clearedDensityProfile; D=-(w-2s)*connection(w,chi).
- physicalTemporalCurrent_horizon_restoration_and_residue35, fully instantiated actual q branch side amplitude angular point:
 ∃R B>0, B≤1/2, c0 c1 : ℂ→ℂ, ∀0<b≤B:
 (1) N_b(w):=QuadraticEndpointMellin.finitePart F c0 c1 b w analytic at physical w0;
 (2) lim_(w→w0 punctured)(w-w0)*(N_b(w)/D(w))
     = N_b(w0)/physicalFundamentalDenominatorSlope(q,branch,side);
 (3) ∀w∈ball(w0,R),connection(w,chi)≠0:
   lim_(e→0+) [∫e..b j(w,z)
       +(c0(w)*e^w/w+c1(w)*e^(w+1)/(w+1))/D(w)]
     = N_b(w)/D(w).
 Coefficients come from existing clearedDensityProfile_germ, not assigned. Uniform frequency ball derived from actual nonreal/strip facts, separated source/principal poles, and coefficient analyticity neighborhoods. QuadraticEndpointMellin proves integral regularity before slope/residue extraction. Physical slope actual and nonzero. Every smaller b is allowed with same c0,c1 and R, so later same-cutoff joining requires no recentering.
 This closes FULL horizon-mode temporal current including inner lift, all principal channels and source contact. It does not finish full normalizable left-mode current, outer interval, surviving residue, extinction or RH.
 Proof tactics: explicit typed eventual Iio statement before .filter_mono; after intervalIntegral.integral_congr, change to beta-reduced scalar equality before rw. Analytic finite-part and strengthened residue both passed; no placeholder/supplied residue hypothesis.

## New corpus ingredients reused and current NEW concurrent files
Initial four jet modules had cached oleans: HorizonCoordinateJets,SelfChannelHorizonJet,PrincipalChannelHorizonJet,TemporalCurrentHorizonJet.
Also HTGeometry.UniformSecondOrderJet,ElementaryHorizonJets,AnalyticJetGerm.
AnalyticJet2At alone contains ONLY uniform quadratic jet + analytic coefficient germs; no spatial continuity or frequency analyticity of F. New regularity module above discharges those.
TemporalCurrentHorizonJet's comment said actual current identification in companion, but no companion existed at opening. During turn concurrent sources appeared:
- RHTower.ThetaCuspHawkingBMTemporalCurrentClearedDensity (~230lines inventory only read): clearedTemporalDensity30, selfExpression35,contactExpression43,clearedTemporalExpression52; tortoiseMode_false_eq_gaussProfile60; clearedTemporalDensity_eq_expression67; clearedTemporalDensity_eq_current92; spatial continuity helpers109..157; frequency analyticity helpers168..220. Imports currentjet,HorizonModeOuterUniformBound,ReducedGreenUniformBound,ReducedOuterPairing,PhysicalSourceCoefficient,PhysicalPrincipalRegularity,PhysicalPrincipalNoncollision. No naming collisions with our public theorems observed. NOT edited/audited by us; read statements next time before using.
- RHTower.ThetaCuspHawkingBMHorizonModeOuterUniformBound (~100+): radialMode_false23,First_false26,Second_false29; tortoiseMode_hasDerivAt_continued34, equation50, horizon_growth_bound69, outer_uniform_bound96. Inventory only read.
- HTGeometry.JetCoefficientUniqueness: norm_eq_zero_of_le_mul_sq_add_mul17; eq_zero_of_norm_add_mul_le_mul_sq30. Inventory only read; USE this before rebuilding jet coefficient uniqueness.
All three remain outside this turn's edit/build scopes.

## Strongest next attacks
1. Full opposite-current profile: same self/contact combination, replace incoming Gauss(u,z) by Gauss(-u,z). Density has z^(-1). Actual normalizable coefficient connection/(2u), divided by D, equals -1/(2u*(u-2s)); removes connection zero. Derive uniform first/second jet for negative-frequency Gauss, exact actual full-current decomposition, then LogarithmicEndpointFinitePart. This should yield analytic opposite-current finite part and zero residue, at ANY common b chosen above. Do not omit explicit lift/contact.
2. Evaluate current numerator at w0: clearedReducedGreen_fundamental_factor (FundamentalGreenFactor, line51, whole proof read) gives sourceMoment*clearedOnset times actual fundamental mode. At D(w0)=0, principal terms in selfPart and all contactPart vanish. Thus F(w0,z) should equal
 K*incomingPairingFactor(w0,chi,z),
 K = modeAngularSquare * (-2*w0*(physicalAngularParameter²-1/4-2))
     *physicalSelfSourceCoefficient *fundamentalSourceMoment(w0,s,a)*clearedOnset(s,w0).
 At fundamental mode incomingPairingFactor=sqrt(1-z)/2.
 Use fresh JetCoefficientUniqueness to identify c0(w0),c1(w0), then N_b(w0)=K*incomingNormFinitePart(chi,b,w0). NOT yet proved. Avoid redoing uniqueness.
3. Join actual full-current outer interval, now aided by fresh HorizonModeOuterUniformBound/TemporalCurrentClearedDensity. Existing bare-response physicalNormalizableOuterPairing theorem still insufficient for full current. Prior source norm join/slope machinery is available and audited.
4. Source angular coefficient, source moment, fixed onset nonvanishing / full retained pairing survival remain open. Full angular reconstruction/all multiplicities/SS-VV/Peierls also not closed. No RH inference from a merely conditional/nonzero-assumed residue.

## Searches
5 cached searches completed: amplitude broad; full-current horizon finite-part mechanism deep; clearedDensityProfile broad; logarithmic broad; logarithmic endpoint mechanism deep.
First deep partial at reranking; others completed. Coverage~57027files but compiler metadata mostly pending, stale snapshot/semantic unavailable. Candidates/source arguments/ingredient sets inspected.
Applicable first deep candidate QuadraticEndpointMellin.finitePart_analyticAt, actually verified/used.
Broad logarithmic hits mostly irrelevant; rephrased deep search found source argument HTGeometry.LogarithmicEndpoint.remainder_analyticAt in LogarithmicEndpointFinitePart (signature read from result). Existing opposite finitepart imports that file.
Broad arxiv transmutation/polyhomogeneous; opened arxiv2601.03616, revision27June2026 Kannai transform diffusion as weighted wave propagators. No premise taken, no computation.

## Docs, wiring, lint, cleanup
Updated docs/drafts/pipeline/{1-in-progress,3-formalized}/hb-physical-mode-action-contact.md with precise full horizon-current result and remaining normalizable/outer/nonvanishing gap.
Frontier and universalSTATUS untouched.
RHTower umbrella appends all3new modules. Also appended used UniformSecondOrderJet,ElementaryHorizonJets,AnalyticJetGerm to HTGeometry umbrella (required theorem-area reachability; no umbrella builds).
Lint initially failed7unreachable; after wiring3usedHTGeometryhelpers, final lint exit1 with4 untouched concurrent modules:
RHTower.ThetaCuspHawkingBMHorizonModeOuterUniformBound
RHTower.ThetaCuspHawkingBMTemporalCurrentClearedDensity
HTGeometry.JetCoefficientUniqueness
HTGeometry.SecondEndpointMellinLaurentInterchange.
All new/currently-used modules reachable; global lint NOT passed.
All owned Lean/Lake/search/lint/helper handles terminal. Cleanup76781 finished: removed13explicit owned /tmp paths incl5searchjson,3scratchlean,analyticfragment,resultdoc,audithelper,auditpackage,lintlog. Final owned-process filter EMPTY (rg exit1). No remaining handle or tempfile to resume.

## CRITICAL cache-only audit recipe detail
Recreate helper; old helper/package removed. Root lean_lib name GaloisForLFunctions MUST have roots=[EXACT.TARGET.MODULE], not broad default GaloisForLFunctions. Otherwise Lake tries source-less project dependencies with missing traces and fails/rebuilds. This turn first attempt failed immediately (no rebuild) because root overly broad; fixed roots, all3audits exactly2jobs.
Read manifest; source-less path stubs each lean_lib per top-level cached namespace, symlink dependency .lake/build. Root recursively stage .olean/.hash/.ilean/.hash/.trace where available, via both source import headers and .ilean.directImports, hardlink only. No dependency sources. Some dependencies legitimately only have olean/ilean; exact target roots make them external cached imports, no invented traces.
Copy ONLY target source; unlink any target hardlinks before build. lake build EXACT.TARGET. Verify checked scratch==audit source, install source+five artifacts, remove audit source. Change roots for each target. No git/fetch/update, umbrella or dependency builds.