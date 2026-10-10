# Finite Weil cost/leakage tradeoff — formalized

Card: docs/drafts/pipeline/3-formalized/finite-weil-cost-leakage-tradeoff.md.

Only local Lean corpus and installed mathlib were used. User explicitly forbids web searches and external-paper rereading; see `mem:research/local-lean-corpus-only-2026-10-10`.

## Exact unconditional results
`WeilLogShiftGramCostLeakage.lean:12`, `exists_finiteWeilGram_exponential_cost_leakage`: exists B>0,K>=2, forall N>=2K, exists i:rangeN,d:rangeN->Real with normd=1, |di|=1, off-weight sum <= q-1 (q=N/K), forall actual tests w, y=VrangeNw,C=cost1w,E=2^q:
E|yi| <= BC+E sum_{j!=i}|dj||yj| <= BC+E(q-1)||y-single_i(yi)||.
All witnesses precede test w.

Same file line48 `exists_finiteWeilGram_exponential_cost_leakage_threshold`: for unit response at selected i, C<=E/(2B) forces leakage>=1/(2(q-1)); leakage<=that threshold forces C>=E/(2B).

## Implementation and verification
New `WeilLogShiftGramLeakageAlgebra.lean`: five helpers, only narrow mathlib imports. Generic erased-finset helpers require explicit [DecidableEq iota] to avoid classical-vs-concrete equality-instance mismatch. Explicit function type on residual norm terms avoids elaboration mismatch.
Refactored `WeilLogShiftGramCoordinateObstruction.lean`: new cluster_dual_witness line47 and exponential_dual_witness line125 preserve dual norm, coordinate unit magnitude, off-weight, and universal sensitivity. Both existing coordinate-obstruction APIs unchanged as corollaries.
Native Algebra -> CoordinateObstruction -> CostLeakage -> existing IsolationSeparation all pass. Final logs `/tmp/hgt-leakage-WeilLogShiftGram{LeakageAlgebra,CoordinateObstruction,CostLeakage,IsolationSeparation}.log`.
13 public declarations + 21 mathlib API terms pass `/tmp/hgt-cost-leakage-audit.lean`, output .log: only propext, Classical.choice, Quot.sound. No owned Lean process remains.
Sources and direct dependencies fresh; exactly-once umbrella imports. Index refreshed, both roots found by local lexical research. LEAN_API has all nine new declarations.
Lint log `/tmp/hgt-cost-leakage-lint.log` exit1: five unrelated missing umbrella imports RHTower.XiReciprocalSliceNearestZero; HTGeometry.PaperMoebiusPrimePrefixEscape, PaperPrimeEscapeAnalyticCost, QKrawtchoukCompanionTriangular, ReciprocalPositivityMinimumModulus. Leave unrelated work untouched.

## Next question
Current q-1 off-weight bound uses only dimension and sup norm, not actual cluster coefficient structure. Inspect actual existing envelope construction in Lean before conjecturing a sharper weight bound. No sharpness or external novelty claim. Whole indefinite research goal remains active.
