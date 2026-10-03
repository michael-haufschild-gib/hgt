# Verified proof optimization; main goal still open

Latest explicit user request: optimize Lean; no raised heartbeats hacks. Four proof bodies changed, statements/definitions/imports/umbrella wiring unchanged:

- HTGeometry/QuenchedReplicaIncidenceCovarianceLaw.lean:144, re_replicaTargetIncidenceCovariance_diag: shared typed coordinate. Matched proof-body counters 1,189,605 -> 770,094 (35.26%).
- RHTower/StaticChoiKurtosisNearActionLaw.lean:114, normalizedSpectralQuarticActivation_le_centralizerDeficit: direct power/order bound and mul_comm instead of nlinarith/ring. 4,772,180 -> 2,796,405 (41.40%).
- RHTower/StaticChoiObserverTransferKurtosisLaw.lean:114, normalizedSpectralTransferFourthMoment_le_centeredFourthMoment: narrow simp only on column norm, one finite-sum algebra normalization. 6,188,302 -> 2,671,269 (56.83%).
- Same observer leaf:30, normalizedSpectralTransferFourthMoment_nonneg: explicit even-power/finite-sum positivity. Passed; no paired performance percentage claimed.

Paired native synchronous scratch profiles, no proof resource limits changed. Whole-project wall-clock speedup NOT established. Actual source bodies match measured scratch. All three actual repository leaf/cache checks with lake --old env lean exit 0 without warnings. Axiom audit of exactly four changed actual declarations exits 0: only propext, Classical.choice, Quot.sound. No full/umbrella/dependency builds, git, subagents or added hypotheses/axioms. Existing umbrella imports verified by rg. Global lint currently has 11 unrelated unwired RHTower errors, none in these leaves. All owned tool processes exited. /tmp/hgt-proof-opt-aYxE6c source files and empty directory removed.

This is maintenance, NOT scientific frontier progress. Quenched ordinary-ensemble complete-circuit incidence-action producer remains open. Receiver, rank control, deterministic observer transfer and full-purity crowding do not close it. Retain budget-dependent initial cutoff, occupied image, fibre sheets, both return-excised time variables. Do not mark goal complete. Working log: docs/reports/quantum-recurrence-working-log.md.

Current broad/deep search also found existing HTGeometry/StaticGaussianCrossingMemoryLaw.lean; fourth-order crossing correction is already in corpus, not a new result. Future research must not conflate classical static Gaussian source with free/Brownian refreshed disorder or infer quenched circuit suppression from annealed moments.