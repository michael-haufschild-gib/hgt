# Active BSU contribution-7 checkpoint

Goal active: 100 significant native contributions; accepted count remains 6/100. User steering requires corpus research search, avoiding duplicate existing work. Attachment `/Users/michael/.codex/attachments/348d2c8d-c66f-465c-9a58-411a7c617aa4/pasted-text-1.txt` reread fully. No hgtl7, subagents, numerical experiments, heartbeat increases, full/umbrella builds, commits, README edits. One owned foreground Lean process at a time. No production writes for candidate 7 yet.

Card `docs/drafts/pipeline/1-in-progress/biscale-parity-neighborhood-phase-transitions-2026-10-19.md` remains uncounted. Programme count6. README SHA remains `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275`.

## Verified
- `/tmp/bsu-100-parity-sharp-r1.log`: exit0/no diagnostics; inverse, exact count obstructions, sharp raw arrays, physical Fourier phase separation, parity-ball coefficient bounds and all witness neighborhood bounds.
- `/tmp/bsu-100-parity-core-r1.log`: exit0/no diagnostics. All 13 prior drafts combined into `/tmp/bsu_parity/ParityCore.lean`; export `/tmp/bsu_parity/ParityCore.olean` exists. Compile with `lake --old env lean -R /tmp/bsu_parity ... -o ...`, cwdformal. Without -R export fails because /tmp is outside package root; terminal r0failed immediately, corrected r1passed.
- `/tmp/bsu-100-parity-bounds-r0.log`: exit0/no diagnostics. `/tmp/bsu_parity/ParityBounds.lean` exports `LocalPairwiseHolder`, root upper bounds3/5/6 and N2linear. Radius1, C12W+8 for roots, C5 N2, ALL epsilon>=0. Olean exists.
- `LocalPairwiseHolder N b alpha` explicitly quantifies positive physical radius, nonnegative C, arbitrary actual weight pairs in that ball, all raw5/6errors<=epsilon, exists naturalshift controlling every physical value by C epsilon^alpha.

## Current owned process
RUNNING session34394: `lake --old env /bin/zsh -c 'export LEAN_PATH="/tmp/bsu_parity:$LEAN_PATH"; exec lean -R /tmp/bsu_parity /tmp/bsu_parity/ParityScaling.lean -o /tmp/bsu_parity/ParityScaling.olean' > /tmp/bsu-100-parity-scaling-r0.log 2>&1`, cwdformal. Poll before any next Lean.

Terminal session60845 `/tmp/bsu-100-parity-holder-sharpness-r0.log` exit1: only N2 finite-filter equality failed because broad simp rewrote addOrder1 before using order equations. `/tmp/bsu_parity/ParitySharpness.lean` fixed to `simp only[mem_filter,mem_univ,true_and]`, then split support and `rw[h2/h1];norm_num`; NOT YET rerun. Other proof statements in that file had no errors. It contains private small-power and witness-to-no-holder helpers, and no-improved-exponent theorems3/5/6/N2. N2 now reuses generic sharpWeights with A=B=1 (constant perturbation), raw bound d1, Fourier phase1=1; no separate Lipschitz estimate needed.

`/tmp/bsu_parity/ParityScaling.lean` reuses actual existing THIM `sieveSeq_scale_weight`, proves moment homogeneity, LocalPairwiseHolder invariant under every nonzero scalar, defines actual paritySource N a=(a/2)*parityWeights N and proves its full coordinate profile. Under normalization s=lambda^-1, K=|s|^5+|s|^6, normalize raw epsilon to K epsilon and multiply physical error back. ALL epsilon property simplifies transfer; no exponent positivity assumption needed for equivalence. Yet unverified.

`/tmp/bsu_parity/ParityClassification.lean` unverified, imports Sharpness and Scaling. Defines parityRecoveryDegree:1 ifN2,3 ifN<12,5 ifN<20,6otherwise; exponent reciprocal. Main theorem `sharp_parity_neighborhood_exponent N hN a ha` gives attainment and failure for every larger exponent for allN>=2,a!=0. No extra analytic premise.

## Searches reviewed this window
- scaling and small-power hybrid JSONs `/tmp/bsu-100-parity-scaling-search.json`, `/tmp/bsu-100-parity-holder-obstruction-search.json`: all20candidate+20source statements and allprose/passages inventories reviewed. Both nonpartial,74340filecompleteinventory; semanticcoverage unmeasured,compilerrefresh incompletebackgroundindexer. No generated proposals. Existing PrimeReadoutSharpness private small_power_iff/scaled_power_iff and SieveHighestModeSharpness explicitexp proof pattern read and reused without novelty credit.
- Wholecorpus lexical `/tmp/bsu-100-parity-signal-scale-search.json` confirms THIM scalelemma in `RadicalCheckpointSignRigidityAndGaugeLaw.lean:94`. Source/header1-112read. Existingolean present. Its local import closure9401files does NOT contain BSU umbrella (metadata traversal), so newBSUleaf importing it has no umbrella cycle. RHTower unit-power bound also already reused. No wholecorpus absenceclaim.

## Next
1 PollScaling34394; fix if needed. RerunSharpnessfixed; thencompileClassification via same scratchLEAN_PATH command. Run one Lean at a time.
2 After allscratchclaimsverified, production extraction manifest `/tmp/bsu-parity-module-plan.json` proposes9 scopedmodules, no filescreatedyet. Groups: AnchorEstimate(scalar/readouts/rounding), CutoffRecovery(upper_products/phase_transfer/cutoff_phase/rounded_recovery), FourierBounds(inverse/physical_fourier), ResonanceCounts, SharpWitnesses(profiles/phase_sep), NeighborhoodStability(neighborhood/ParityBounds), NeighborhoodSharpness, AmplitudeScaling, NeighborhoodClassification.
3 Strip imports `ParityCore/ParityBounds/...` and API example probes from production; add manifestlocaldeps, preserve needed originalimports and namespaces. Avoid accidental scope leaks; verifyeach originalproduction source with `lake --old env lean GaloisForLFunctions/BiScaleUncertainty/<name>.lean -o .lake/build/lib/lean/...` foreground, sequential. No umbrella build.
4 Fullpublicstatement/definition/axiom audit, explicitmainclosure and actualraw/metric/source definitions, standardaxiomsonly. Umbrella exactonce, index/lint, preserveconcurrent BVI/THIM/APTchanges. READMEhash,cleanupverifiedscratchproofsources, significanceaudit, cardmove/countincrement ONLYwhenallrequiredworkcomplete. Goalremainsactive afterward.
