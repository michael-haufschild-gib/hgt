# HB both original horizon branches restored at same cutoff — 0912c

Goal ACTIVE, UNBOUNDED, UNPROVED. Previous turn classified PROGRESS: four affected modules now audited/installed, both original horizon branches joined before frequency residue. Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.
Continues mem:hawking_bm_common_cutoff_norm_and_regular_outer_residue_2026_09_12_0912b. Latest constraints persist: optimize Lean, NEVER raise heartbeat/resource limits, NO axiom checks, no computations, Git, launch.sh, full/umbrella builds. Frontier READ ONLY, universal STATUS untouched. No agents spawned.

## Installed and audited — do NOT recheck unchanged
1. MODIFIED formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMIncomingPairingFinitePart.lean,252lines.
   Namespace RHTower.D4BMLaplaceRadial.
   New incomingPairingFinitePart_horizon_restoration_below line105:
   s chi a J K w; w.im≠0,Rew>-2,w-2s≠0 → ∃R B,R>0,B>0,B≤1/2,
     ∀b>0,b≤B: analyticAt incomingNormFinitePart chi b, incomingSourcePairingFinitePart...b, incomingSourcePrimitive...u b at w,
     and for u in ballwR,C(u)≠0, actual incoming cutoff integral+two counterterms tends to incomingFP.
   Private pairing_common_data unchanged. New local hbds restricts continuous source primitive and quadratic bounds from B to b, and RE-CENTERS endpoint amplitude via Q(z)=Q(B endpoint)+P(z), Q(b)=Q(B endpoint)+P(b), hence Q(z)=Q(b)-P(b)+P(z). Simple mul/ring algebra; no change of source.
   Original incomingPairingFinitePart_horizon_restoration signature preserved as corollary at b=B.
   Scratch clean. Exact leaf audit 124sec,2jobs,4337 cached project imports. Source+5artifacts installed, umbrella already wired.

2. MODIFIED ThetaCuspHawkingBMOppositePairingFinitePart.lean,203lines.
   New oppositePairingFinitePart_horizon_restoration_below line77, same forall-small-cutoff form with analytic oppositeNorm,oppositeSourceFP,sourcePrimitive, original opposite integral+log counterterm.
   Restricts private opposite_common_data and re-centers endpoint by exact quotient identity at b.
   Original theorem preserved as corollary.
   Scratch clean; exact audit9.3sec,2jobs,4335cachedimports; source+5artifacts installed, existing umbrella import.

3. NEW ThetaCuspHawkingBMNormalizableHorizonPairing.lean,94lines.
   Namespace RHTower.D4BMLaplaceRadial.
   incomingPairingCutoff(s,chi,a,J,K,b,w,e): original integral response*horizon(w)/(2z sqrt(1-z)) + (A_b/2)e^w/w + ((GaussFirst+1/4)A_b+d/2)e^(w+1)/(w+1).
   oppositePairingCutoff: integral (C/(2w))*response*horizon(-w)/(2zsqrt) + (C/(2w))*(A_b/2)*log e.
   normalizableHorizonPairingFinitePart = Aplus(w)*incomingFP+oppositeFP.
   normalizableHorizonPairingCutoff = SINGLE integral response*normalizable/(2zsqrt) + Aplus(w)*(two power CTs) + opposite log CT.
   private horizonPairing_intervalIntegrable: actual continuedResponse_hasDerivAt (requires nonreal Re>-2) + actual horizon mode spatial derivative + nonzero real denominator derive finite positive-cutoff integrability; no assumed integration law.
   normalizableHorizonPairingCutoff_eq line59: exact equality to Aplus*incomingCutoff+oppositeCutoff, for0<e≤b<1,nonrealRe>-2. Uses actual original_homogeneous_horizon_representation, normalizable_opposite_coefficient=C/(2w), and proved integrability before integral_add.
   Scratch clean first attempt; exact audit100sec,2jobs,4341cachedimports. Source,5artifacts,new RHTower umbrella import installed.

4. NEW ThetaCuspHawkingBMPhysicalNormalizablePairing.lean,~215lines.
   Namespace RHTower.D4BMJointSource.
   private incoming_residue_at_cutoff: actual q branchsidea,interiorb and analyticN,J,P (discharged in main) → physical incoming residue Camp*N_b. Uses physicalIncomingQuotient_residue, no supplied pole amplitude. Source-endpoint scalar step normalized by explicit change then mul_sub, not expansion of source integral in ring.
   private opposite_residue_at_cutoff: analytic L,K,P at SAMEb → zero residue. Derives physical nonzero horizon, actual numerator analytic, oppositePairingExtension analytic, equality on connection/horizon-nonzero punctured germ, then (u-w)*analyticExtension→0. No artificial assigned pole value asserted analytic.
   normalizableOuterPairing line107 = normalizableHorizonFP(s,chi,a,1,reducedGreenGradient chi s1,z(T),w)+continuedReducedOuterPairing(chi,s,a,T,w).
   normalizableOuterPairingCutoff line112 = native normalizableHorizonCutoff at z(T) + original outer integral.
   physicalNormalizableOuterPairing_residue_and_restoration line117:
     actual q branchsidea → ∃T R,T<0,R>0,
       limit_(u→w0 punctured)(u-w0)*normalizableOuterPairing(...T,u)
       = physicalIncomingPoleAmplitude(q,branch,side,a)*D4BMFundamentalNorm.normFinitePart(w0),
       and ∀u∈ballw0R,C(u)≠0 → native cutoff expression tends to this pairing as e→0+.
   Constructs b=min BI BO using new forall-small restoration theorems, R=min RI(min RO Rvalid); Rvalid ensures u.im≠0,Reu>-2. T from exists_matching_horizon_cutoff.
   Residue combines Aplus analytic and Aplus(w0)=1, incoming Camp*N_b, SAME-b opposite0, existing outer residue, existing physicalFundamentalNorm_join.
   Scratch warning-free after fixing id eta and source integral alias elaboration. Typed identity Tendsto helper is preferable to simpa on bare tendsto_id.sub_const. Final exact audit10sec,2jobs,4425cachedimports. Installed source,5artifacts,newumbrellaimport.
   No resource options increased in any file.

## Exact next gap / strongest positive inner-lift plan
Current normalizableOuterPairing includes continuedResponse in horizon and FULL continuedReducedGreen in outer. It still omits the INNER explicit lift correction. continuedReducedGreen = continuedTortoiseGreen - radialLift(s,w,a,continuedOnset(s,w),t)*J. Sign MINUS.
After admitting/subtracting inner lift, self-channel complete radial pairing may retain same residue; all3principal source channels and BOTH Einstein contacts still need full-current assembly. No sourceMoment/onset/retained pairing nonvanishing or RH proved.

Do NOT assume the new final existential T can be shrunk. Raw incoming/opposite APIs are now forall-small, but physicalNormalizableOuterPairing_residue_and_restoration still constructs one T. To adjoin lift at its own small radius, strengthen physical theorem to all smaller cutoffs/a requested positive upper bound (reuse existing proof/local private helpers), OR prove lift admission up to arbitrary positive interior b by compact continuation. Do not take min of existential T radii without a proof.

Actual lift analytical derivation (not yet paired/restored in Lean):
sourceAmplitude(s,w,a,T,t)=exp(wt)*(1+r)^(2s)*a²T, r=radialUnit(t)=sqrt(1-z).
radialLift=(-s(s-1)/4)*z^(w/2)*(1+r)^(2s-w)*a²T*r³.
IMPORTANT: lift leading profile generally NONZERO; initial speculation of extra z gain was rejected by actual source definition.
Pairing with incoming horizon mode h_w gives z^(w-1) times
  (-s(s-1)/8)*amplitudeProfile(s,a,T,w,z)*(1-z)*H_w(z).
Pairing with opposite h_-w gives z^(-1) times same kernel with H_-w.
Thus retain two incoming power CTs and an opposite log CT; do NOT claim ordinary convergence/one-subtraction just from reduced forcing's z gain.
F0=λ*2^(2s-w)*a²*T(w), λ=-s(s-1)/8.
Incoming F1=F0*(horizonGaussFirstCoefficient(w,chi)-1-(2s-w)/4).
These coefficients analytic at physical w0 since fixed onset analytic away from separated source pole. Proposed resulting lift finite part analytic, residue0; NOT proved yet.

Useful existing source / actual next ingredients:
- ThetaCuspHawkingBMHorizonCoordinateJets.lean:
  liftProfile line70, sourceAmplitude_eq_profile73, radialLift_eq_profile82,
  amplitudeProfile_jet (around97), liftProfile_jet117.
  liftProfile_jet gives HasUniformJet2 on closed frequency ball, exact constant/linear coefficients, provided bound on T(u).
  amplitudeProfile_jet + EXACT factor1-z + Gauss jet is better paired-kernel proof than introducing inverse sqrt estimate.
  Source reads this turn covered liftProfile/radialLift_eq_profile and liftProfile_jet statement/initial proof, not whole file.
  This module had cached olean earlier but remains unwired in lint; DO NOT re-audit merely because memory names it. Inspect actual current state before reuse/wiring.
- Existing horizonGauss_uniform_second_bound, QuadraticEndpointProducts, quadratic/logarithmic finite-part analytic/cutoff tools available.
- Source formulas read at sourceAmplitude definition13, radialLift18, continuedReducedGreen12. continuedOnset=1/(w-2s)+onsetCorrection(2s,w).
- ThetaCuspHawkingBMSelfChannelHorizonJet and PrincipalChannelHorizonJet other-agent source uses liftProfile_jet; untouched. TemporalCurrentHorizonJet and HTGeometry.AnalyticJetGerm also now appear unwired. Investigate fresh completed source/cache next turn; names alone not proof.
- PhysicalLiftHorizonCurrent.physical_finite_horizon_limits line570 was read: time integral on finite0..V at partner -s-3, radius→1, returns clockEnergy/Mass/onsetSquare. Not the required independent-frequency radial lift pairing; do not misapply. File>500lines; only570-606read.

## Search / external
Broad restriction hybrid; natural-language small-endpoint method deep; continuedResponse hybrid per-module0; lift deep scoped to ThetaCuspHawkingBM. Candidate lemmas, source_arguments, proof_ideas, ingredient_sets inspected. Retrieved actual continuedResponse_hasDerivAt and liftProfile_jet. Generic transport/finite-product suggestions not applied. Requests completed; about57000files, compiler~44575pending, stale/snapshot warnings, semanticcoverage unavailable. All used names verified in Lean.
Broad arxiv sewing/localization searches; opened June2026 arxiv2606.27387 nonlocal localization/variance addition paper. Its detector-kernel hypotheses/variance law not used in bilinear current. No numerical computation.

## Docs / lint / cleanup
Updated docs/drafts/pipeline/{1-in-progress,3-formalized}/hb-physical-mode-action-contact.md: completed below-cutoff/raw+physical both-branch joining; exact audits; true inner lift/full-source gap; concrete next kernel. Frontier and universalSTATUS untouched.
Lint once,exit1. Exact8 outside-edit unreachable:
RHTower.ThetaCuspHawkingBMHorizonCoordinateJets
RHTower.ThetaCuspHawkingBMPrincipalChannelHorizonJet
RHTower.ThetaCuspHawkingBMSelfChannelHorizonJet
RHTower.ThetaCuspHawkingBMTemporalCurrentHorizonJet
HTGeometry.AnalyticJetGerm
HTGeometry.ElementaryHorizonJets
HTGeometry.SecondEndpointMellinLaurentInterchange
HTGeometry.UniformSecondOrderJet
145 largefilewarnings outside new work. All4affectedleavesdirectlyreachable. Global lint NOT passed; do not rerun unchanged or edit other-agent pending modules blindly.
All owned Lean/Lake processes finished; exact final ps filter empty. Every search/audit/lean/helper/lint handle terminal, including finalaudit33489,lint56412,cleanup46486. No handle to resume.
Removed14 explicit owned /tmpitems incl6 scratch/backups,4searchjson,2audithelpers,lintlog, /tmp/hb-audit-0912c. Source/artifacts retained. Do not access oldtemps.
Cache-only audit recipe in mem0912b; same used now. Source-less dependency stubs, cached project-import hardlinks, only exact target source, unlink target hardlinks before build, lake build exactmodule,2jobs, source==checkedscratch. Existing source replacements checked against saved-before snapshot to avoid concurrent clobber. Helpers removed; recreate if needed.