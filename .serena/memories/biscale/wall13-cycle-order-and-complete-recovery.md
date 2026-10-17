# Wall 13: finite-order obstruction and complete closed-cycle recovery

2026-10-18. This advances the C3 conjecture left open in `mem:biscale/wall13-schur-square-orientation`. Current goal remains active: develop BiScaleUncertainty until walls 2–15 are demolished. Wall 13 is NOT closed. No hgtl7 skill, RH work, numerical experiments, added axioms, heartbeat increases, full/umbrella builds, or agent commits/pushes. Field README and walls ledger unchanged by SHA-256.

## Three verified leaves

All paths under `formal/GaloisForLFunctions/BiScaleUncertainty/`; all declarations in namespace `GaloisForLFunctions.BiScaleUncertainty.SeparatedCycle`.

1. `SeparatedCopyCycleCharge.lean`: for actual compact continuous seed f, D=SeparatedSquare.radius f, order m, choose gap T=(m+2)D+1. `source f m a` is actual subtractCopy f a T. `packetIndex` labels central/positive/negative correlation packets by 0/1/-1. `rawProduct_sign` proves P_(-a)(L)=(-1)^Q P_a(L), where Q=packetCharge=sum labels. `rawProduct_eq_iff` classifies equality exactly by P_a=0 or Even Q. `packetCharge_bound` gives P_a=0 or |sum L-QT|<=length(L)D. Thus `shortData_source_neg` proves equality of every closed product through order m, including empty lists and zero factors. This is the exact positive invariant, not just a negative claim.

2. `SeparatedCopyCyclePolarAmbiguity.lean`: defines actual Gram determinant and all-order<=m Gram data. `gramData_source_neg` follows term by term from the permutation expansion, since lags t_(sigma i)-t_i sum to zero. `exists_smooth_same_finite_data_distinct_polar m` constructs smooth compact f,g with equal positive mass, equal complete closed-product and Gram-determinant data through order m, but zero versus positive normalized polar moment. Amplitude is exp(-T/2). `polarMoment_not_factor_through_finite_data m` excludes every functional recovering the moment from these JOINT data, for each m.

3. `ClosedCorrelationCycleRecovery.lean`: `closedProduct_eq_iff_autocorr_eq` proves equality of ALL finite closed products iff equality of entire signed autocorrelation, for arbitrary actual compact continuous f,g. No additional hypotheses. One-edge cycle identifies mass, two-edge cycle identifies squares. Zero mass handled by |h(x)|<=h(0). Positive mass plus continuity fixes a common positive sign near 0. Long list [-x,x/n,...,x/n] recovers h(x) by cancelling proven nonzero small-lag factors. `all_shortData_eq_iff_autocorr_eq` restates completeness across all finite orders. Concrete noncomputable `polarRecovery` chooses any source realizing the supplied full data (zero for unrealizable data); `polarRecovery_closedProduct` proves correctness and well-definedness via signed-correlation recovery. This is exact-data recovery, no stability or algorithm claim. Does NOT prove source uniqueness or recovery from Gram determinants alone.

## Verified evidence

27 public declarations: 17 theorems, 10 defs. Every signature and definition body inspected. Every axiom list printed: only propext, Classical.choice, Quot.sound. Logs `/tmp/bsu-wall13-cycle-axioms-r2.log`; retained scratch `/tmp/bsu_wall13_cycle_axioms.lean`. All 3 serial direct leaf checks passed with empty logs; final direct `lake --old env lean -j 1 GaloisForLFunctions/BiScaleUncertainty/ClosedCorrelationCycleRecovery.lean` also exit 0, empty output. Manifest of source/olean hashes, output freshness, unique umbrella imports: `/tmp/bsu-wall13-cycle-manifest.json`. Installed API probes passed; obsolete API scratch files removed. No own Lean process remains.

Umbrella wiring and `scripts/formal_tools.py index` complete. Exact lexical searches find both finite-data no-go and full closed-data recovery; `/tmp/bsu-wall13-cycle-{counterexample,recovery}-discovery.json`.
Global lint at audit time FAILS, exit 1, exactly two unrelated concurrent errors: `BiScaleUncertainty.CoshDecayGroundPotentialAndThetaVolumeCollarProducer` unreachable from umbrella; `BezoutValuationIncidence.lean` research leaf at package root. 381 large-file warnings. Do not claim global lint passed or modify another task's unfinished files. External git activity committed snapshots during this task; this agent did not commit.

Research evidence: `/tmp/bsu-wall13-cycles-frontier.json`, `/tmp/bsu-wall13-cycles-copy-search.json`, `/tmp/bsu-wall13-full-cycle-search.json`, `/tmp/bsu-wall13-cycle-threshold-search.json`. All 20 candidate and 20 source statements per query inspected. Searches completed, but semantic coverage unmeasured; background refresh incomplete/source-only compiler evidence. No exhaustive absence or external novelty claim. Initial broad cycle search returned unrelated orientation results; narrower searches supplied real subtraction, continuity and mass parents.

## Persistent state and next conjecture

Formalized package: `docs/drafts/pipeline/3-formalized/wall13-closed-cycle-order-obstruction.md`.
Failed route with strongest positive survivor: `docs/drafts/pipeline/5-failed/wall13-fixed-order-polar-recovery.md`.
Prior square-transfer card updated to mark C3 proved and point to this successor.

Next CONJECTURE, not proved: `docs/drafts/pipeline/0-backlog/wall13-minimal-cycle-order.md`. Construct an explicit smooth compact seed with autocorrelation positive exactly on (-1,1). For T>2 and nonzero a, least closed-product order distinguishing opposite copies should be floor(T)+1. Lower bound: odd nonzero charge Q and strict interior packet errors force |Q|T<n. Candidate upper witness at n>T: one lag T-T/n, then n-1 copies -T/n; charge 1, all factors nonzero. Concrete seed positivity/support proof and endpoint audit outstanding. Same threshold for Gram determinants requires separate cancellation proof. Do not count it as done.

Big-picture boundary: fixed order fails uniformly over sources, the full hierarchy is complete for each source pair. Missing Wall-13 step remains a quantitative, blind-compatible positivity transfer/coercive bound; exact reconstruction alone does not provide it.