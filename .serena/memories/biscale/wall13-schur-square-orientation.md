# Wall 13: square transfer, signed reconstruction, polar ambiguity

2026-10-18. Current user goal remains active: develop BiScaleUncertainty until walls 2–15 are demolished. This package does NOT close Wall 13 or the goal. No hgtl7 skill, no RH work, no numerical experiments, no full or umbrella builds, no commits/pushes by this agent. README and walls ledger stayed byte-identical. Do not revive older paused contribution-count goals or count familiar modulus/Schur facts as new.

## Completed exact package

Three leaves in `formal/GaloisForLFunctions/BiScaleUncertainty/`, uniquely imported by its umbrella:

- `SchurSquareCorrelation.lean`, namespace `SchurSquare`: literal tensor wave on R² under diagonal translation realizes h(x)^2; finite Gram quadratic form equals an integral of an actual square; all zeros preserved. Exact nonnegative extended-energy identity `levyEnergy_add_quarticDefect` integrates `(R²-h²)+(R-h)²=2R(R-h)`. No integrability premise or infinity subtraction. Classical Schur product mechanism itself is not a novelty claim. No scalar one-dimensional factorization or individually blind fibre decomposition follows.
- `SeparatedCopySquareClassification.lean`, namespace `SeparatedSquare`: for an actual compact continuous seed choose positive autocorrelation support radius D and gap T=2D+1, source g_a(u)=f(u)-a f(u-T). With k(a)=a/(1+a²), normalized profile is H_a(x)=H(x)-k(a)[H(x-T)+H(x+T)]. Disjoint packets give squared profile formula. `square_profiles_eq_iff` classifies equality by R=0 or k(a)²=k(b)²; `profiles_eq_iff` by R=0 or k(a)=k(b). `correlation_reconstruction` recovers full signed profile from one anchor H_a(T). Zero-mass case covered.
- `SchurSquarePolarAmbiguity.lean`: `exists_smooth_same_square_distinct_polar` supplies actual smooth compact sources of equal positive mass, equal squared correlations for every real lag, with one normalized polar moment zero and the other positive. Uses a=exp(-T/2) and sign reversal of copy. `polarMoment_not_factor_through_square` excludes ANY real-valued functional recovering polar moment from squared profile. `exists_smooth_same_zeros_distinct_polar` gives identical complete zero sets.

## Evidence

All 3 serial direct leaf checks passed with empty logs; final direct `lake --old env lean -j 1 GaloisForLFunctions/BiScaleUncertainty/SchurSquarePolarAmbiguity.lean` passed. 37 public declarations (29 theorems, 8 defs), every signature/body inspected and every axiom list checked: only propext, Classical.choice, Quot.sound. Axiom scratch retained `/tmp/bsu_wall13_axioms.lean`, log `/tmp/bsu-wall13-axioms-r2.log`, source/olean hashes and freshness `/tmp/bsu-wall13-verified-manifest.json`. Installed API probes passed; obsolete API and smoothness scratch removed. No own running Lean process remains. No heartbeat changes, sorry/admit/axiom/opaque/unsafe declarations.

`formal_tools.py index` passed. Documented lexical corpus search discovers exact capstone, `/tmp/bsu-wall13-discoverability.json`. Global lint at audit time FAILED with exactly one error: concurrent `GaloisForLFunctions.BiScaleUncertainty.FactorialWeilGram` unreachable from theorem-area umbrella; 381 large-file warnings. Do not claim global lint passed; do not add imports for another unfinished task. No lint errors named these three leaves. Concurrent external git activity committed snapshots while work proceeded; agent did not commit. Preserve others' changes.

Corpus searches: `/tmp/bsu-wall13-{corpus,modulus-search,square-search,sign-search,cycle-search}.json`. All returned candidate/source statements inspected. Modulus deep search partial on reranking deadline; other searches completed but semantic coverage unmeasured/source-only compiler status, no exhaustive novelty claim. Cycle search included then-uncompiled drafts, not independent validation.

## Persistent cards and next conjecture

Main: `docs/drafts/pipeline/3-formalized/wall13-schur-square-orientation.md`.
Failed route with exact positive survivor: `docs/drafts/pipeline/5-failed/wall13-square-only-polar-recovery.md`.

C3 remains UNPROVED/UNFORMALIZED: for finite m take T>mD and T>2D; plus/minus copies may share every closed lag-cycle product of length <=m, hence all Gram determinants of size <=m, despite polar difference. Candidate mechanism: nonzero lags x_i=c_i T+e_i, c_i in {-1,0,1}, |e_i|<=D; closure forces sum c_i=0, hence even outer-factor count. Need rigorous permutation-cycle proof, boundary/converse/threshold audit, and exact Lean construction. Do not count this as proved. Strong prospective survivor is exact separation/order detection law, while signed anchor already avoids cycle-order cost.

Lean API gotchas: explicitly pass `(f := (f : ℝ → ℝ))` to subtractCopy autocorrelation APIs to avoid coercion rewrite mismatch. Smoothness downgrade from ↑(⊤:ℕ∞) to 2 uses `WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)`; exact_mod_cast alone did not solve this two-infinity coercion.