# HB DO: actual reader diagonal and direct source cancellation

Sole task: full temporal/metric/QNM matching or impossibility. RH remains unproved, goal active. Do not review experiments/results.md, edit frontier map, run computations, print axioms, use Git/launch.sh, raise heartbeats/instance hacks, or run umbrella/full builds. One owned foreground Lean/Lake process at a time. Relevant earlier memory: `mem:hb-dn-source-moment-matching-2026-09-15`.

## Verified this turn
All four leaves installed under formal/GaloisForLFunctions/RHTower/, exact isolated `lake build Exact.Module` audits passed and all four imports wired in RHTower.lean. No full or umbrella build. New code uses only autoImplicit false, no added axioms/hypothetical matching inputs.
1. ThetaCuspHawkingBMOriginalSourceResolventEndpoints: actual mixedBracket horizon limit 0 on Re(w±v)>0; outer limit 0 in independent source/reader chambers. Actual quotient/source transport and original Green moments discharge boundary hypotheses.
2. ThetaCuspHawkingBMOriginalWholeSourceResolvent.whole_source_resolvent (line 203): both absolute whole-domain integrals admitted and (v²−w²)*int_0^1 rho*y_w*n_v=int_0^1 n_v*S_w on original mixed convergence wedge. No integral/boundary premise.
3. ThetaCuspHawkingBMOriginalReaderRegularization: fixed source, independent reader core and uniform linear horizon remainder, subtracted Mellin differentiability for Re(a)>−2 including a=−1; readerHorizonRegularPart_continuousAt_below crosses v=w; readerOppositeRegularPart_original_below identifies exact original opposite finite part including log constant.
4. ThetaCuspHawkingBMOriginalReaderDiagonalMatch.readerHorizonRegularPart_original_below (line 102): in Re(w)>0, Im(w)≠0, connection≠0, w−2s≠0, exists one B>0 supporting all 0<b≤B, continuous readerHorizonRegularPart at w AND its diagonal equals original normalizableHorizonPairingFinitePart. Both power counterterms and log retained. Incoming proof uses firstEndpointMellin_eq_integral, genuine admitted integral cutoff limit, and original incoming restoration plus vanishing powers.

Namespaces new leaves: RHTower.D4BMOriginalSourceResolvent. Definitions in ReaderRegularization:
- mixedGaussPairingFactor w v chi z = G_w(z)G_v(z)/(2 sqrt(1−z)).
- readerResponseCore s chi amp J K w b v z = (E_b + P_w(z))*mixedGaussPairingFactor, where E_b=incomingResponseEndpoint and P_w=incomingSourcePrimitive.
- readerResponseCore_common_data gives one B for the source, then every smaller b and any nonreal reader center have a uniform neighborhood/bound, continuous core, exact density identity. This avoids separate cutoffs for opposite/incoming branches.
- readerMellinCore ... b a = Icc(0,b).indicator(core at reader 2(a+1)−w). Extension is auxiliary only; integral is on Ioc(0,b).
- readerMellinRemainder is firstEndpointMellinRemainder of this family.
- readerIncomingPart(v)=E_b/2*b^((w+v)/2)/((w+v)/2)+Rem((w+v)/2−1).
- readerOppositeRegularPart(v)=E_b/2*dslope (a↦b^a) 0 ((w−v)/2)+Rem((w−v)/2−1).
- readerHorizonRegularPart(v)=A(v)*Incoming(v)+[c(v)/(2v)]*OppositeRegular(v), using original A.
These prove the right-chamber seed match, not evaluation at physical QNM. Canonical existing continuation and source Mellin continuation must carry the eventual full equality to QNM.

## Decisive next attack — shorter than the old reader derivative route
Own fact log docs/drafts/pipeline/1-in-progress/hb-dn-source-resolvent-facts.md is DN1–DN9. Do not append to shared hb-own-research-facts.md (other stream through F302). Detailed paper docs/drafts/pipeline/1-in-progress/hb-dn-source-moment-reduction.md updated, including section Direct source difference before the diagonal limit. Frontier map unchanged.

Let Ireg(w,v)=reader horizon regularization + actual full outer density integral. J(w,v)=int n_v*S_w, beta(v)=c(v)/(2v), E(w)=greenHorizonAmplitude. Need global original pole-subtraction equality and continuity; horizon side now verified. In wedge:
(v²−w²)*Ireg=J(w,v)+(v+w)E(w)beta(v).
Use literal diagonal J(v,v)=−c(v)E(v) BEFORE taking the limit:
(v+w)*Ireg(w,v)+c(v)*[E(v)−(v+w)E(w)/(2v)]/(v−w)
 = −int n_v*(S_v−S_w)/(v−w).
Then v→w:
2w GreenFP+c(w)*(E'(w)+E(w)/(2w)) = −int n_w*partial_w S_w.
Added term is precisely actual Green temporal corner. This avoids separate proofs differentiating reader J or connection c. Keep chi,K,s,amp fixed. Need outer integral continuity, E_b=actual E on same small cuts, genuine J(v,v) integral identity, chamber E differentiability, and DCT domination of source divided difference (power×(1+|log z|)). Source formula is exp(w*x)A(z)T(w), so derivative exp(w*x)A(x*T+T'). Existing compact DN theorem remains verified but J_v proof is no longer a prerequisite.

Then retain original forcing contribution −mu*w*C*FP int n_w*S_w/z and forcing temporal corner mu*c*C*Fforcing'/2 until QNM. Paper exact three-period QNM target M,X,Z and their counterterms remains global Lean pending. Do NOT differentiate fundamentalSourceMoment along fundamental curve: K would vary. x=log(z)/2−log(1+sqrt(1−z)), so X needs −log(2) finite constant.

## Validation / cleanup
All owned Lean/Lake sessions ended. Private /tmp/hb-do-audit removed, completed scratch sources/helpers removed; final sources and installed objects retained. Audit logs /tmp/hb-do-endpoints-audit.log, hb-do-whole-audit.log, hb-do-reader-audit.log, hb-do-diagonal-audit.log retained. Whole repo lint ran once; exit 1 solely because unrelated RHTower.SuzukiEulerianSignedGammaCurrent is unreachable from umbrella. All four new imports verified present; no new leaf flagged. Do not claim global lint passed or repair unrelated ongoing module as busywork.

Build helper: isolated temporary Lake package with roots=[exact new module], ordinary copied source, dependency/root installed top-level Lean objects symlinked under private .lake/build/lib/lean (91 links). Exact target built 2 jobs each, no dependency/full rebuilds. Root formal cwd scratch uses LEAN_NUM_THREADS=1 lake env lean /tmp/file.lean. No need recheck completed leaves.

Proof pitfalls resolved: intervalIntegral.integral_symm a b states int_b^a=−int_a^b (arguments reversed from tempting recall). Use typed f/volume and correct order. Explicit ContinuousAt.comp (f:=reader map) (x:=w) prevents elaborator selecting partial division. Normalize integral_congr lambda applications with dsimp only before rw. For module diamonds use `using!`/explicit typed terms, no instance hacks. RegularOuterPairing import hit missing unrelated MixedRadialActionCurrent object; avoided via verified Endpoints import and direct local coefficient continuity from original jet formula.

## Searches
Deep independent-reader/regularized divided differences, Mellin Abelian, variational, horizon scaled derivatives and power integrability searches completed; JSONs /tmp/hb-do-*.json retained. Coverage ~58k files, ~752k declarations; compiler snapshot mostly source-only/pending, so search hits are not compile evidence. Broad Abelian/variational results mostly unrelated. FirstEndpointMellin, original source/Gauss uniform bounds and mathlib compact endpoint extension/FTC were the applicable corpus methods and were checked in actual proofs. Earlier broad arXiv evanescent/transversality searches read primary 2605.03051 and 2609.04084; conceptual only, no imported assumptions.