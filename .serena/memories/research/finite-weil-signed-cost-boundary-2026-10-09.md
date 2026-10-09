# Exact signed-cost boundary for minimal Gram dictionaries
Local Lean + installed Lean/mathlib ONLY. No web, papers, numerics. Overall indefinite corpus goal remains ACTIVE. This turn is verified progress. No subagents; no owned process remains running.

Completed card: docs/drafts/pipeline/3-formalized/finite-weil-signed-cost-boundary.md.
NEW sole Lean leaf: formal/GaloisForLFunctions/RHTower/WeilLogShiftGramSignedCostBoundary.lean, importing GramCanonicalDictionary. One public theorem at line41: exists_finiteWeilGram_signed_cost_dictionary. Dictionary/positive relation a chosen before L and signed price vector kappa; canonical q chosen before kappa. Let S=sum a_w*kappa_w, C=sum q_w*kappa_w. Proves exactly:
- Attainable costs R iff (S>0 and C<=R) OR (S=0 and R=C) OR (S<0 and R<=C).
- A nonnegative representation of cost<=R exists iff S<0 OR C<=R.
- Costs are bounded below iff S>=0.
- At S!=0, any feasible b has costC iff b=q. Hence unique minimum when S>0 and unique maximum when S<0.
Empty support included without a premise. No coordinatewise sign assumption on kappa. Negative-slope obstruction has full positive survivor (exact range + unique max + budget classification).

Proof uses corpus feasible-ray theorem b=q+t*a, t>=0, finite-sum distributivity, and private gram_nonnegative_affine_range. Half-lines filled exactly via t=(R-C)/S; budget under negative slope uses min C R; necessity of nonnegative slope for a lower bound uses bound-1. No numerics.

Native compile first attempt exit0, empty log. /tmp/hgt-weil-gram-signed-cost-final-audit.lean exit0; eight new API terms and #print axioms for sole new public theorem + source ray theorem. Only propext, Classical.choice, Quot.sound. Freshness/direct imports pass; umbrella import exactly once. Index exit0 and exact local query verifies source line41. Global lint exit1:6 unrelated HTGeometry unreachable modules: PaperPrimePolynomialActions, PaperPrimePolynomialAlgebra, PaperPrimePolynomialClocks, PaperPrimePolynomialDenominators, PaperPrimePolynomialExtensionBoundary, QKrawtchoukCompanionTriangular. No branch/placeholder errors. Do not claim global lint clean.

Logs /tmp/hgt-weil-gram-signed-cost-{api,build,final-audit,index,lint}.log; /tmp/hgt-weil-gram-signed-cost-index-verification.json. All builds were sequential; short API probe imported Mathlib.Data.Real.Basic instead of the large corpus module, final audit repeated terms under actual new import.

This completes the signed-cost candidate left in mem:research/finite-weil-canonical-positive-weights-2026-10-09. Does NOT optimize dictionary choices or yield total-cutoff-cost upper bounds. Single-test image surjectivity and native <=d scaled-test sum interface remain unformalized/open as previously noted. Possible next conjectures: canonical weight map is positively homogeneous/subadditive; addition defect is a nonnegative multiple of the positive relation; exact additivity/triangle equality occurs precisely when the two canonical supports share an omitted test. These could produce native cost gauges. Not proved yet; search local corpus before pursuing. Overall goal not complete.