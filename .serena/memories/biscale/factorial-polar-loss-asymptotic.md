# Actual factorial polar-loss asymptotic and Gram-scale obstruction (2026-10-18)

Active goal remains unconditional RH in Lean. This turn made mathematical progress; RH and the coupled actual ramp diagonal margin remain unproved.

## Exact unconditional results
Namespace: GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar.
Set N=n+1, epsilon=sourceFactorialCollar N, H_N=harmonicCorrection N, C_N=chebyshevBiNullProducer N.
P_n is the actual half-line integral of polarDensity times autocorr(factorialRampSource n).
Prior exact identity: P_n=-(1+epsilon/2)*H_N*C_N/N.
New actual definition factorialPolarLoss n=|P_n|.

- b_N=centralBinom(2N)/centralBinom(N)^2.
  N+1 <= b_N^2 for all N; b_N^2 <= (9/4)*N for N>=1.
  Therefore log(N+1)/2 <= C_N <= log(N)/2+log(9/4)/2 for N>=1.
- N/(2N+1) <= H_N <= 1/2 for N>=1; H_N -> 1/2.
- factorialPolarLoss n >= log(N+1)/(8N)>0; P_n<0.
- N*factorialPolarLoss n/log(N+1) -> 1/4.
- The actual signed full-diagonal pole term obeys N*(2*P_n)/log(N+1) -> -1/2.
- For G_n=factorialWeilGramError n, N*G_n -> 0 and G_n/factorialPolarLoss n -> 0.
  Eventually G_n < factorialPolarLoss n; eventual reverse absorption is false.
These are actual source-family quantities. Scalar limits only; no limit passage through the full Weil form.

Paper mechanism: exact central-binomial doubling recurrence has squared multiplier bounded between (N+2)/(N+1) and (N+1)/N, using explicit positive polynomials. Harmonic pairs factor as (2j/(2j+1))*(1/(4j)-1/(4(j+1))); summing j=N,...,2N-1 telescopes. Collar budget epsilon*N<=1 gives epsilon->0. Multiply scalar limits in the exact pole identity. Gram error is E_n^2/(2N) with verified E_n->0, while N*polarLoss>=log(2)/8.

## Four verified modules
All under formal/GaloisForLFunctions/BiScaleUncertainty/:
1. CentralBinomialRatioGrowth.lean: centralBinomialDoublingRatio; seven theorems including add_one_le_centralBinomialDoublingRatio_sq, centralBinomialDoublingRatio_sq_upper, centralBinomialDoublingRatio_log_lower/upper.
2. FactorialPolarLossLowerBound.lean: factorialPolarLoss; nine theorems including harmonicCorrection_bounds_sharp, factorialPolarLoss_eq, factorialPolarLoss_log_lower, factorialPolarLoss_scaled_lower, integral_polar_autocorr_factorialRamp_neg.
3. FactorialPolarLossAsymptotic.lean: five theorems harmonicCorrection_tendsto_half, chebyshevBiNullProducer_normalized_tendsto_half, factorialPolarCollar_tendsto, factorialPolarLoss_normalized_tendsto_quarter, factorialRamp_polarContribution_normalized_tendsto.
4. FactorialPolarGramScaleSeparation.lean: factorialWeilGramError_scaled_tendsto, factorialWeilGramError_div_polarLoss_tendsto, factorialWeilGramError_eventually_lt_polarLoss, not_eventually_factorialPolarLoss_le_gramError.

All four final leaves verified sequentially with lake --old env lean -j 1 and empty logs. Core observed exit0; asymptotic and Gram observed success markers; audit exit0.
The final lower-bound tool result was truncated: its process terminated, empty log and fresh .olean were verified, then both dependent leaves and the full axiom audit imported that object. Its unavailable exit code is null in the record, not fabricated.
All 27 public declarations (25 theorems + 2 definitions) were individually audited; only propext, Classical.choice, Quot.sound.
Audit /tmp/biscale_polar_scale_axioms.lean; output /tmp/bsu-polar-scale-axioms.log.
Full source hashes, evidence, all 27 audit results, lint and cleanup: /tmp/bsu-polar-scale-verification.json.
Final own compiler processes are terminal. No unchanged passed leaf was rerun, no full/umbrella build, no heartbeat increase.

All four modules wired exactly once into formal/GaloisForLFunctions/BiScaleUncertainty.lean.
scripts/formal_tools.py index passed, updating formal/LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md.
Global lint --check-generated exited1 on three unrelated missing umbrella imports: MertensValuationBudget, RobinMovingValuationDefect, StationaryResolventMarkovPositivityAndNodalDefectProducer. No error names these four modules. Log /tmp/bsu-polar-scale-lint.log. No global lint pass.
A broad rm -rf cleanup was rejected. A safer script validated all 8737 copied .olean paths/types/count, individually removed them, then removed empty directories. /tmp/bsu-polar-scale-cache is gone; normal-cache own objects and logs remain. Old /tmp/bsu-polar-*.setup.json mappings reference the removed cache and must not be reused without regeneration.

## Pipeline and remaining target
Positive stage3 card: docs/drafts/pipeline/3-formalized/factorial-polar-loss-asymptotic-2026-10-18.md.
Failed shortcut and full dependency-closed paper proof: docs/drafts/pipeline/5-failed/factorial-polar-loss-gram-obstruction-2026-10-18.md.
Its old 1-in-progress path no longer exists. Seven relative card links and all four copied source hashes were checked.
Parent stays in progress: docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md.
Only the polar-loss-into-Gram-error absorption shortcut is retired, NOT WL/RW.
Write actual diagonal A_n=B_n-2*polarLoss_n, where B_n is archimedean minus resummed logarithmic/prime contribution. Remaining sufficient margin is B_n >= 2*polarLoss_n + factorialWeilGramError n. No such bound, no sign of A_n or the full span, and no unconditional RH theorem was proved. Even two-dimensional span positivity alone would not establish all-source RW.

## Verification hashes
CentralBinomialRatioGrowth: e29d0279f4dc4c4211478e2b661b2cb2770beb9c95c764ef1719de1c6aca1b9d
FactorialPolarLossLowerBound: 1007532adb368d5220e913461a8ea7c682f12c0457ee4891735da22678da725b
FactorialPolarLossAsymptotic: b743dd20150170569dbb11eb43652f88a5ab334c9f621cd6a2499d297519651b
FactorialPolarGramScaleSeparation: 3169c329a897c6b6b6946d77a2e7fe808df3f2fd446da985b7877543e5e802b5

## Continuation discipline
Goal attachment /Users/michael/.codex/attachments/9fe32bd2-890b-4755-bcdf-afc3e45f611a/pasted-text-1.txt was read at this actual goal turn's start. Reread on next actual automatic goal turn, not merely compaction.
User constraints: corpus/source only, no web/novelty audit/old-markdown research browsing; no numerical experiments; one own foreground Lean process; direct leaves -j1 only; README/frontier-map read-only; preserve concurrent work.
Corpus searches this turn were partial (/tmp/bsu-ramp-margin-current-search.json and /tmp/bsu-central-binomial-ratio-search.json): deadline/worker interruptions and unmeasured semantic coverage. Available hits were inspected; do not claim exhaustive search or external novelty.
Concurrent Muntz/cycle/other research files were not edited or verified by this task.
Practical proof lesson: field_simp already closes simple rational cancellation identities in this toolchain; a trailing ring can cause No goals to be solved. Actual failing cases were fixed and rechecked.
