# Finite Weil fluctuations share one leading mode

Status: in progress. Research sources: local Lean corpus only.

Prior corpus audit: lexical covariance search scoped to WeilLogShift returned no
declarations. Exhaustive family text search found the fixed-center comparison and
actual-variance limits, but no covariance or correlation theorem. The preceding
seven-leaf actual-variance increment was revalidated: metadata issues empty.

Let n=r+1, m the canonical probability edge law, X_i=i, E=sum m X,
T_i the local log correction, and Q=sum m T. Existing Lean proves
|n T_i-X_i|≤1 whenever n²≤k+2. Existing actual variances satisfy
VE/n→1/4 and n VT→1/4 at k=2n²+t(r), for arbitrary natural t.

Conjecture and paper closure:

1. Define W=sum m [n(T-Q)-(X-E)]². Apply the existing finite centering identity
   to Z=nT-X. Its mean is nQ-E. Thus W=sum m Z²-(nQ-E)², so 0≤W≤1.
2. Define C=sum m (X-E)(T-Q). Expanding squares gives
   W/n=n VT+VE/n-2C. Since W/n→0, C→1/4.
3. VE VT=(VE/n)(n VT)→1/16. Therefore C/sqrt(VE VT)→1.
   This is positive perfect asymptotic correlation, not merely equal variances.
4. For arbitrary real a,b, J=sum m [a(X-E)+bn(T-Q)]²/n equals
   a²VE/n+2abC+b²nVT and tends to (a+b)²/4. The covariance matrix of the
   normalized fluctuations tends to the rank-one matrix with every entry 1/4.
   The antisymmetric direction a=-b has vanishing leading variance.

These conclusions follow entirely from corpus theorems and finite algebra.
Final roots will quantify structural parameters only, with no analytic premises.
No distributional limit, external novelty claim, or RH consequence is asserted.

Plan: residual identity and bound; covariance identities; residual/covariance
limits; correlation limit; joint quadratic-form limit. Build one leaf at a time,
audit every public declaration in a final native Lean scratch import, wire each
leaf exactly once, inspect direct freshness and exhaustive incoming imports,
check local root indexing and formal lint. Keep unrelated work untouched.


## Formalization completion — 2026-10-11

Current status: FORMALIZED, superseding the initial in-progress status.
All four conjectured conclusions were proved. No external papers, web searches,
numerics, new axioms, heartbeat increases, or full builds were used.

New finite insight: W is exactly the variance of nT-X, not a sum of separately
estimated centering errors. Therefore the existing pointwise bound immediately
gives W≤1 under n²≤k+2. The exact identity W/n=nVT+VE/n-2C transfers both
known marginal fluctuation limits into their joint covariance. A finite weighted
Cauchy-Schwarz theorem also proves C²≤VE VT for every r,k.

The resulting six roots prove W/n→0, C→1/4, VE VT→1/16, VE VT-C²→0,
correlation C/sqrt(VE VT)→1, and the full quadratic-form limit
J(a,b)→(a+b)²/4. All hold at k=2(r+1)²+t(r), for arbitrary t:Nat→Nat;
the last root quantifies arbitrary real a,b. No analytic premises remain.
The normalized covariance matrix thus tends to [[1,1],[1,1]]/4: one common
leading fluctuation direction, with a vanishing antisymmetric direction.
This proves fluctuation equivalence in mean square; it does not assert a Gaussian
distributional limit or an RH conclusion.

Root declarations:
- `GaloisForLFunctions/RHTower/WeilLogShiftFluctuationRankOneLimit.lean:10`: `tendsto_finiteWeilCanonicalFluctuationResidual_normalized_zero`.
- `GaloisForLFunctions/RHTower/WeilLogShiftFluctuationRankOneLimit.lean:24`: `tendsto_finiteWeilCanonicalIndexCorrectionCovariance_quarter`.
- `GaloisForLFunctions/RHTower/WeilLogShiftFluctuationRankOneLimit.lean:36`: `tendsto_finiteWeilCanonicalEdgeVariances_product`.
- `GaloisForLFunctions/RHTower/WeilLogShiftFluctuationRankOneLimit.lean:48`: `tendsto_finiteWeilCanonicalFluctuationDeterminant_zero`.
- `GaloisForLFunctions/RHTower/WeilLogShiftFluctuationCorrelation.lean:14`: `tendsto_finiteWeilCanonicalIndexCorrectionCorrelation_one`.
- `GaloisForLFunctions/RHTower/WeilLogShiftJointFluctuation.lean:45`: `tendsto_finiteWeilCanonicalJointFluctuation_rank_one`.

Validation: five leaves, 20 public declarations (4 definitions, 16 theorems).
Every leaf passed native Lean with an empty final log. The final imported-root
audit checked all 20 declarations, each using exactly
[propext, Classical.choice, Quot.sound], plus 12 local API `have := @Name` checks.
Own/direct object freshness, all 6 direct imports, all 9 incoming imports,
global declaration uniqueness, whitespace, and five single umbrella imports
passed. Local lexical searches return all six roots as eligible without markers.

Global lint snapshot: 8 unrelated errors and 367 warnings.
This does not claim a passing repository-wide lint gate. Errors:
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.CCM.CCMPolarOddPrimeJumps`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.MontgomeryPairCorrelationShortLength`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.WeilMarginTwistLockRigidity`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiCriticalityLogLogDepth`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.XiGaussianHeatHankelInertia`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.ZetaZeroAntiCrystalLogLog`
- `error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.QKrawtchoukCompanionTriangular`
- `error: proof debt: formal/GaloisForLFunctions/RHTower/CCM/CCMPolarOddPrimeJumps.lean:104: sorry (theorem ccmPolarOddSource_eq_core_add_atoms)`

Audit artifacts: `/tmp/hgt-rank-one-metadata.py`, `-metadata.json`,
`-declarations.json`, `-incoming-imports.txt`, `-final-audit.lean`,
`-final-audit.log`, `-api.lean`, `-api.log`, `-covariance-search.json`,
`-joint-search.json`, `-lint.log`, and the five per-leaf native logs.
The rank-one increment is complete; the broader research goal remains active.
