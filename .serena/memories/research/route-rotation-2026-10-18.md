# Route rotation

User instruction (2026-10-18): “we have 27 live routes and 18 route candidates. dont just work on one all the time”.

All 45 open obligations in docs/reports/rh-current-frontier-map.md were reviewed. The ledger and two framework READMEs remain read-only for this task. After each bounded proof or failed-conjecture cycle, reassess the portfolio and prefer another mechanism/family or candidate; do not keep extending one route by default. This is a working policy responding to the user's instruction, not a claim that every route has been proved.

RW factorial Müntz completion is now audit-only. Seed and Completion direct audits passed. Tail and Readout remain unverified because an external worker's shared dependency rebuild repeatedly removed required .olean files. All four imports are wired, which is not a proof claim. No owned Lean process remains active. Preserve drafts and finish these checks when shared dependencies return; do not duplicate live external builds. Checkpoint: docs/drafts/pipeline/1-in-progress/factorial-ramp-muntz-completion-2026-10-18.md.

Work actually rotated to TH. ThetaInnerLargeActionCurrent.lean proves the complete actual enriched clock current positive for 0<t≤2, t≤u, and curvatureShapeAction u t≥4050 exp(4). Canonical leaf and all three axiom audits passed with only propext, Classical.choice, Quot.sound. Source and umbrella imports indexed. Card: docs/drafts/pipeline/3-formalized/theta-inner-large-action-current-2026-10-18.md. See `mem:biscale/theta-inner-large-action-current-2026-10-18`.

Remaining TH sign region: 0<t<2 and action below that threshold; all-degree Hankel landing is separate. Next research cycle should change mechanism again, not tune 4050 or add another adjacent theta/ramp lemma by habit. BVI has concurrent external workers; preserve their files. Final lint still reported five unrelated concurrent umbrella-coverage errors. No global lint pass or RH proof is claimed.