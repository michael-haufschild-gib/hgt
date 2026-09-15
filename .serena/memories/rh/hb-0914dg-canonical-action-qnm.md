# HB DG canonical radial/action continuation — 2026-09-14

Scope remains full temporal/metric/QNM matching or impossibility. Neither is proved; RH remains unproved. Active HB/RH goal stays active. Never reread experiments/results.md. Frontier map read-only. Analytical only; no Git, launch.sh, #print axioms, numerical experiments, heartbeat/transparency/instance overrides, umbrella/full builds. One owned foreground Lean/Lake process. Read mem:rh/hb-0914df-canonical-metric-matching for preceding work.

## Completed, kernel checked
New single 345-line leaf:
formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMOriginalCanonicalMetricAction.lean
Imports OriginalCanonicalMetricCutoff only; two namespaces.
Wired once in formal/GaloisForLFunctions/RHTower.lean directly after OriginalCanonicalMetricCutoff.
Final isolated exact command:
LEAN_NUM_THREADS=2 lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalCanonicalMetricAction
PASS (53s, only leaf built). Formal lint PASS (existing large-file warnings elsewhere). All source-specific proofs checked in combined scratch; final pure removability helper also checked separately under Mathlib.Analysis.Meromorphic.Order and Mathlib.Tactic before complete exact audit. No axioms printing; no computations.

D4BMOriginalCanonicalMetricGerm:
- original_outer_pairing_meromorphic line21: actual continuedReducedOuterPairing is meromorphic at nonreal Re(w)>-2 off source pole, using actual cleared integral / reducedGreenClearingFactor and punctured equality.
- original_normalizable_local_data line42: actual q/br/amp, every nonreal Re(w)>-2, common R,B>0, B<=1/2, every 0<b<=B: normalizableOuterPairing at tortoiseOf b meromorphic at center; original normalizableOuterPairingCutoff converges to it throughout ball off connection zeros. Both incoming/opposite branches included.
- original_canonical_metric_local_data line113: same common-interface construction including actual regular forcing term and original radialCutoff_decomposition. Literal canonicalMetricCutoff converges to radialFinitePart with canonical incomingValue/incomingSlope/oppositeValue.
- canonicalRadialValue line178 = limUnder (nhdsGT 0) (canonicalMetricCutoff q br amp w). No auxiliary interface parameter.
- canonical_radial_value_local line182: every sufficiently small local formula agrees with this value off connection zeros.
- canonical_metric_cutoff_tendsto line199: actual cutoff converges at all nonreal Re(w)>-2 nonconnection-zero frequencies; no admission premise.
- canonical_radial_value_meromorphic line208: same global function meromorphic throughout domain, including connection zeros, by local formula equality on punctured neighborhoods.

D4BMOriginalCanonicalAction:
- canonicalAction line233 = canonicalRadialValue + physicalCornerCandidate.
- canonical_action_meromorphic line237 on all nonreal Re(w)>-2. Uses actual continuedCornerAmplitude_meromorphic, derivative closure, continued_forcing_analyticAt. Source-pole exclusion derived from currentRate_re_lt.
- canonical_action_QNM_residue_zero line262: (w-w0)*canonicalAction ->0 for either fundamental QNM. Choose b below both canonical local cap and canonical regular analyticity cap via original_radial_restoration_and_corner_balance_below. Difference from that existing restored action is forcingCoefficient*(canonical regularFinitePart - old regularFinitePart), analytic at w0. Its scaled limit is zero; transfer old actual residue cancellation. Does NOT assume arbitrary old coefficients equal canonical ones.
- private removable_of_scaled_limit_zero line296: meromorphic f and (u-p)*f(u)->0 imply analytic punctured-germ representative. Mathlib tendsto_zero_iff_meromorphicOrderAt_pos and meromorphicOrderAt_mul show 0<1+order(f); integer order is >=0, then hf.meromorphicOrderAt_nonneg_iff. Spaces around comparisons are necessary: '0<meromorphic...'/'0≤meromorphic...' are lexed as Matroid notation in this corpus.
- canonicalQNMValue line314 = actual punctured-frequency limUnder canonicalAction.
- canonicalQNMAction line317 updates only QNM value.
- canonical_action_QNM line323: updated action analytic at QNM, actual canonicalAction converges to unique finite value, and whole canonicalMetricCutoff+physicalCornerCandidate converges to canonicalAction throughout frequency domain off connection zeros.
DO NOT assert this finite value is zero or that full physical matching/RH follows.

## Persisted facts/state
Own fact log docs/drafts/pipeline/1-in-progress/hb-own-research-facts.md now F268 (one canonical radial limit/meromorphy), F269 (canonical action QNM removal).
Own card docs/drafts/pipeline/1-in-progress/hb-physical-mode-action-contact.md replaces previous remaining canonical construction list with audited current state and precise remaining physical matching. Frontier and universal-law STATUS unchanged. No new route-independent law, no new no-go.

## Actual remaining full matching attack
Identify independent time/cusp/horizon removal of original metric pairing with canonicalAction. Existing angular-first continuation and local/QNM analytic proofs cannot replace this equality.
Source exact finite decomposition at:
OriginalMetricTimePeriod.lean private metric_time_cut_decomposition line467:
metricTimeCut =
 sourcePrefactor*(sourcePeriodCut b-sourcePeriodCut a+2*w*integral_a_b sourcePeriodCut)
 + forcingPrefactor*integral_a_b forcingPeriodCut
 + integral_a_b boundarySlice - sum3 compactBoundaryCoefficient*exp(fluxExponent*logY).
All terms actual original physical fields; original_metric_time_transfer public line425 is available if private decomposition needs export/derivation. Preserve old private names if adding public wrapper (do not rename/remove cached dependency declarations).
sourcePrefactor = mu*(mu-2)/(R^2*(R^2-1)); forcingPrefactor=mu*R*w/(R^2-1)^2.
original_source_period_cut line192 public: exact sourcePeriodCut = R*readerCoefficient(q,w,outer,R)*exp(-wp)*originalFiniteHeightPeriod(p,p-2*tortoiseR,Y).
readerCoefficient line168 = exp(w*tortoiseR)*radiusLift(modeProfile)R.
OriginalSourceTailCollar.originalPeriodError line218 already actual finite-height-minus-radial period with original exp(-wp)*reader(q,w,L), after radius cancellation. horizonPeriodError line222 its actual negative cusp-tail horizon integral. F263-F264 give mixed estimate and full product admission.
OriginalCompleteTransfer gives exact whole boundary functional after radius cancellations. F261-F262 give boundary error collar limit, but separate radial integral admission and leading trace identification with prescribed horizon/temporal contacts remain open.
Potential direct next step: assemble exact finite-height metric difference using scalar period error, forcing discrepancy and full boundaryError; identify their actual horizon traces, derive radial admission and independent joint limit. Do not define the desired equality into a new pairing or omit endpoint/forcing terms.

Useful inspected continuity route:
OriginalCompleteTransfer transfer_continuous private line27 uses sourceScalar_exterior_smooth on full P=Fin4->R, modeScalar_smooth, coordDeriv_contDiffAt; all source/mode derivatives smooth at exterior positive time/height. It only exports fixed-L time/horizontal continuity (radial_transfer_continuousAt line341). Generalize composition to varying positive L for genuine radial admission.
coefficient_continuous private line62 uses actual radialResponse_continuous, radialLift_hasDerivAt, timeOnset_hasDerivAt; varying L should use tortoiseRadius chart rather than global tortoise continuity.
OriginalBoundaryRestoration.horizon_transfer_continuous gives actual horizon transfer compact admission via uniform limit. horizonTransfer itself has no L argument.

Existing original temporal/corner equality:
OriginalMetricOuterTime.original_exterior_cutoff_difference line342 (Rew>3/2, Imw!=0) gives actual angular-restored static-minus-radial exterior difference -> physicalCornerCandidate. It retains outerStaticTimeIntegral and actual metricCutoffDifference.
OriginalMetricCorner.original_metric_current_finitePart line560 gives fixed L,a,b angular finite-part -> integral collarDensity. Only fixed cutoffs, not joint.
metricCutoffDifference line511 = (staticCut collarDensity - radialCut collarDensity)/2 - (T+log(horizonCoordinate(-T))/2)*integral leadingDensity. Both branches and first temporal moment retained.

## Searches this turn, already reviewed
1 deep120 no-refresh 'local meromorphic limit glue cutoff finite part': partial snapshot916918 pending, unfinished deep queries; candidate/source arguments inspected, proof_ideas/ingredient_sets empty. Useful actual meromorphic derivative and Green amplitude APIs.
2 deep120 no-refresh 'meromorphic pole order multiply linear factor limit zero removable singularity': partial snapshot916929/916930, source/compiler freshness mixed (many pending; do not infer absence). Inspected candidate_lemmas/source_arguments/proof_ideas/ingredient_sets. Useful Mathlib Order iff plus existing GammaSimpleZeroBellHorizonAnalytic.neg_nat_le_meromorphicOrderAt_of_tendsto_pow_mul method (zero limit needs stronger >=0, derived exactly). Suggested derivative-order ingredient not needed.
3 hybrid OR 'admission transgression finitePart' --any --no-refresh: partial snapshot916946 semantic_retrieval unfinished; methods/candidates included unrelated XiShifted/Sonin/Interfinity and original_leading_triangle_finitePart. No full matching theorem identified. Do not rerun same searches without purpose.
Broad primary arXiv searches conormal, holonomy, transgression; opened https://arxiv.org/abs/2608.08289 (conormal elliptic problems, trace estimates) and https://arxiv.org/abs/2606.15970 (conormal invariants/determinantal complexity). No HB applicability established; neither used as proof.

## Validation and cleanup
One missing existing cache SelbergModularArcIntegration.olean appeared after earlier scratch had loaded dependency graph. Regenerated ONLY that unchanged source with lake env lean -o .lake/build/lib/lean/.../SelbergModularArcIntegration.olean .../SelbergModularArcIntegration.lean. PASS. No need repeat.
Owned combined check2 was stopped promptly once two additional errors were noticed: exact child22480,parent22428 terminated, handle59018 exit143. Other owned Lean/search handles all terminal.
Isolated audit uses /tmp/hb-dg-audit with ONLY new source and namespace symlinks into root caches. Final root .olean preserved. Planned cleanup removes only /tmp/hb-dg-* after verification, never follows cache symlinks. No owned process should remain.
