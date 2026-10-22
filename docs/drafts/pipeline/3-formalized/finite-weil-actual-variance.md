# Actual-mean variance of canonical logarithmic transport

Status: paper route closed; formalization in progress.
Sources: local Lean corpus only. No external novelty claim.

## Target

Upgrade fixed-center fluctuation laws to actual-mean variance laws at
k=2(r+1)^2+t(r), for every natural-valued offset. Prove edge-index variance
divided by n=r+1 tends to 1/4, and n times local-correction variance tends
to 1/4. Transfer the latter to actual optimal mixture plans, centered at
their moving-part mean, uniformly over arbitrary endpoint sequences.

## Paper proof

Let q,G,f,F,x,d be the arithmetic/canonical profile notation from the
completed fluctuation-scale proof. The arithmetic centered first moment
sum q*x is zero. Since 2|d||x|<=d^2+x^2, existing second moments give
sum q|d||x| <= (3n+2)G/8 <= nG. The local profile modulus therefore gives
sum |f-q||x|<=G. Normalize with F>=G/2: midpoint mean differs from n/2
by at most 2. The exact midpoint-edge mean identity yields |E-r/2|<=2.
Consequently |E/n-1/2|<=3/n. Existing |Q-E/n|<=1/n gives |Q-1/2|<=4/n.

Finite probability centering identities give
V_E=H-(E-r/2)^2 and V_T=R-(Q-1/2)^2. Thus normalized centering errors
are at most 4/n and 16/n. Existing H/n->1/4 and nR->1/4 prove both
actual-mean variance limits. Quantitative bounds may use S=sqrt((n+1)/2),
1/n<=S/n: edge variance error <=10S/n, correction variance error <=38S/n.

For node pairs, use squared correction deviation from Q off the diagonal
and zero on the diagonal. Its canonical expectation is V_T; its mixture
expectation is delta V_T, delta=|a-b|<=1. Therefore n*plan_variance-delta/4
tends to zero uniformly over arbitrary varying endpoints.

Formalize the stronger exact observable identity: for every real test
function phi, the mixture plan's off-diagonal correction expectation equals
delta times sum m_i phi(T_i). Tests phi=1 and phi(x)=x identify moving mass
delta and first moment delta Q, making Q the moving-part mean whenever
moving mass is nonzero. The identities themselves hold also when delta=0.

## Plan and audit

- Prior fluctuation closure metadata revalidated, no issues.
- Audit existing finite weighted-centering identities for reuse.
- Formalize arithmetic mixed second moment and uniform mean-bias bounds.
- Formalize actual variances, centering identities, quantitative limits.
- Formalize centered moving-plan cost and full-mixture limit.
- Native leaf/API/axiom checks, imports/freshness, unique names, local root
  search, and formal lint. No full or umbrella builds.

## Verification log

- Existing unnormalized Fin-index centering identity in SoninPrimeGramCompression
  inspected. The new probability identity allows any finite index type and
  arbitrary comparison center, without importing the unrelated Sonin analysis.
- Arithmetic centered first moment and mixed second-moment bound passed
  native Lean without diagnostics.
- Mean bounds, actual variances, rate/limit and observable-transfer leaves
  drafted; native checks in progress.


## Formalization completion — 2026-10-11

Current status: FORMALIZED. This completion record supersedes the initial in-progress status.
Research evidence was restricted to the local Lean corpus. No web, external papers, or numerics.

Write n=r+1, k=2n²+t, e=sqrt((n+1)/2)/n. For the canonical probability edge law,
let E be its edge-index mean and Q its local logarithmic-correction mean. Lean proves
|E-r/2|≤2 and |Q-1/2|≤4/n. The actual-mean variances satisfy the exact identities
VE=H-(E-r/2)² and VT=R-(Q-1/2)², where H and R are the previously formalized
fixed-center second moments. Consequently

- |VE/n-1/4|≤10e;
- |n VT-1/4|≤38e.

Both limits equal 1/4 for arbitrary natural-valued offsets t(r). All analytic
premises are discharged. The centering identity is proved for any finite family
whose weights sum to one; it does not require analytic machinery.

The mean bounds follow from the arithmetic centered first moment vanishing, the
mixed second-moment bound sum(q |i-floor(n/2)| |i-n/2|)≤nG, the profile distortion
bound, and F≥G/2. Thus the midpoint mean differs from n/2 by at most 2. The exact
midpoint/edge mean identity gives the edge bound; the existing correction/index
comparison gives the Q bound. Squaring these controls the two centering losses
by 4/n and 16/n, respectively. The existing fixed-center limits then close the proof.

A stronger finite observable identity also holds: every zero-diagonal log-correction
test cost phi has canonical expectation sum(m_i phi(T_i)) and mixture expectation
|a-b| times that quantity. Taking phi=1 identifies moving mass; phi=id identifies
its mean Q; phi=(x-Q)² identifies actual variance cost C=|a-b| VT. Hence
|n C-|a-b|/4|≤38e and n C-|a-b|/4 tends to zero for arbitrary varying mixture
endpoints. No convergence of the endpoints is assumed, and coincident endpoints
are included.

Exact roots:

- `WeilLogShiftActualVarianceLimit.lean:101`: `tendsto_finiteWeilCanonicalEdgeIndexVariance_quarter`.
- `WeilLogShiftActualVarianceLimit.lean:110`: `tendsto_finiteWeilCanonicalEdgeLogCorrectionVariance_quarter`.
- `WeilLogShiftActualVariancePlanLimit.lean:41`: `tendsto_finiteWeilMixtureCoupling_log_correction_variance_error_zero`.

Seven leaves, 34 public declarations (4 definitions, 30 theorems), all checked by
native Lean individually. Final leaf logs are empty. The final imported-root audit
checked all 34 declarations: exactly [propext, Classical.choice, Quot.sound]. Own
and direct dependency freshness, global declaration uniqueness, all 17 direct
imports, all 13 incoming imports, whitespace, and seven umbrella imports passed.
The local search index returns all three roots as eligible, with no markers.

Global formal lint exited 1: 10 unrelated errors and 367 size warnings. None concern
these leaves. This is not a claim that the repository-wide gate passes. Exact errors:
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMPolarOddPrimeJumps`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MontgomeryPairCorrelationShortLength`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperEGCCompactifiedCopy`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperEGCCompactifiedCorrection`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperEGCCompleteCorrection`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperEGCSourceLanding`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.PaperEGCVerticalMajorant`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalLogLog`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular`
- `error: proof debt: formal/GaloisForLFunctions/RHTower/CCM/CCMPolarOddPrimeJumps.lean:104: sorry (theorem ccmPolarOddSource_eq_core_add_atoms)`

Validation artifacts: `/tmp/hgt-actual-variance-metadata.py`,
`/tmp/hgt-actual-variance-metadata.json`, `/tmp/hgt-actual-variance-declarations.json`,
`/tmp/hgt-actual-variance-incoming-imports.txt`, `/tmp/hgt-actual-variance-final-audit.lean`,
`/tmp/hgt-actual-variance-final-audit.log`, `/tmp/hgt-actual-variance-root-search.json`,
`/tmp/hgt-actual-variance-lint.log`, and the seven `/tmp/hgt-WeilLogShift*.log` leaf logs.

This completes the actual-mean variance increment; the broader research goal remains active.
