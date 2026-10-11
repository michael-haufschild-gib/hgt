# Degree-independent mass limit for polynomial cluster starts

Status: formalized, including arbitrary degree functions; native builds and complete axiom/API audit passed.
Date: 2026-10-10. Only local Lean corpus and installed dependencies.

The exact cubic mass limit and its finite relative-error proof reveal that the limit uses only a lower bound on cluster start, not the cubic formula itself.

Paper argument:
1. Write n=r+1 and G_r for arithmetic reference mass. The proved general relative error gives abs(S_(r,k)/G_r-1)<=2n²/(k+2) whenever k+2>=2n².
2. For every k>=2n³, n>=1 implies the width condition, and clearing positive denominators gives 2n²/(k+2)<=1/n. Thus the same reciprocal-order error holds uniformly for every start above the cubic sequence.
3. Define k_(d,r)=2n^(d+3), d:Nat. Since n>=1 and d+3>=3, monotonicity of natural powers gives k_(d,r)>=2n³. Hence abs(S_(r,k_(d,r))/G_r-1)<=1/n for every d,r.
4. For each d, squeeze against 1/(r+1)->0 to get S_(r,k_(d,r))/G_r->1. The standard arithmetic mass limit G_r/sqrt(r+1)->sqrt(pi/2), formalized in the predecessor, then gives S_(r,k_(d,r))/sqrt(r+1)->sqrt(pi/2).

Stronger completed root exposed by the uniform finite estimate: for every degree function d:Nat->Nat, use k_r=2(r+1)^(d(r)+3). Step3 holds pointwise with d(r), so the same squeeze argument and normalized-mass limit hold without any regularity or growth assumption on d. Fixed degrees are corollaries. This has no analytic premise. The common limit is inherited from the already-proved exact binomial mass identity and local Wallis limit.

Predecessors: `finite-weil-standard-mass-normalization.md`, plus the formalized relative error and cubic limit. No external asymptotic result or numerical fit.

Prior focused local search `polynomial mass limit`, module WeilLogShift, had no hits. The normalization search found only the predecessor's arithmetic half-order mass limit. Broader mass-limit search found the existing cubic results and this increment's newly indexed drafts; no separate producer was found. All returned declarations belonged to already-read sources.

Completed leaves: `WeilLogShiftPolynomialMassLimit.lean` has six declarations: explicit start, cubic lower bound, the general error estimate for any start above cubic (line18), uniform polynomial error (line40), ratio limit (line46), and fixed-degree normalized limit (line57). `WeilLogShiftVariableDegreeMassLimit.lean` proves the arbitrary-degree-function ratio limit (line9) and root `tendsto_finiteWeilCanonicalCluster_variable_degree_mass_div_sqrt_order` (line20).

All 13 declarations across this pair and the standard-normalization predecessor passed the complete native axiom audit with 7 explicitly checked API terms. Final leaf logs are empty, axioms standard only, freshness/import/coverage checks clean. Global lint has only the five unrelated missing imports recorded in the predecessor card. No analytic premise, numerical experiment, external paper/web lookup, heartbeat change, or full build.

Follow-up completed: `finite-weil-logarithmic-mean-distortion.md` formalizes a local ratio comparison for nodal distortion, including monotonicity and exact cancellation of the shared factor. All 15 declarations passed native builds and axiom audit. The broader quadratic-start mass-limit conjecture remains unproved in `../0-backlog/finite-weil-local-nodal-distortion.md`; it does not follow from this polynomial family alone.

Local index refresh exited0. Exact post-index lookup found `tendsto_finiteWeilCanonicalCluster_variable_degree_mass_div_sqrt_order` at source line20. All owned build, audit, lint, index, and search sessions are terminal.
