# Finite Weil joint quantiles: compact probability convergence

Status: dependency-closed paper proof and exact Lean formalisation complete.

## Claim

For every offset family `t : ℕ → ℕ` and compact `K ⊆ (0,1)`, the actual joint quantile at `k = 2(r+1)^2 + t(r)` converges uniformly on `K` to the diagonal Gaussian quantile. Consequently arbitrary rank-dependent levels in `K`, and arbitrary tests with a common Lipschitz constant, have vanishing quantile gaps.

## Local corpus dependencies

- `HTGeometry.QuantileCoupling`: inverse-CDF Galois connection and pointwise convergence mechanism.
- `RHTower.WeilLogShiftGaussianQuantile`: strict Gaussian CDF and CDF convergence from the actual weak limit.
- `RHTower.WeilLogShiftJointQuantileLimit`: actual joint quantile, Gaussian quantile and uniform transverse bound `2 / sqrt(r+1)`.
- Existing corpus finite-subcover proofs supply the compactness mechanism.

No external mathematical sources or numerical evidence used.

## Dependency-closed proof

Fix an interior probability `p` and `ε > 0`. Put `δ = ε/4`, `q = Qν(p)`, `L = q-δ`, `R = q+δ`. The inverse-CDF Galois connection gives `Fν(L) < p`; strict increase of `Fν` and `p ≤ Fν(q)` give `p < Fν(R)`. Put `A = (Fν(L)+p)/2` and `B = (p+Fν(R))/2`. Then `Fν(L) < A < p < B < Fν(R)`.

Pointwise CDF convergence makes `Fμr(L) < A` and `B < Fμr(R)` hold eventually. For every interior level `u ∈ (A,B)`, the same Galois connection places both `Qμr(u)` and `Qν(u)` between `L` and `R`. Their distance is less than `2δ < ε`. The open intervals `(A,B)`, indexed by `p ∈ K`, cover `K`; compactness selects finitely many. The finite intersection of their eventual conditions proves uniform convergence. This argument requires no monotonicity in rank and no continuity of the finite atomic quantiles.

Instantiate with the actual projected index law and its nondegenerate Gaussian limit; all CDF and strictness hypotheses are already proved locally. The actual joint quantile lies within `2/sqrt(r+1)` of the diagonal scalar quantile, uniformly in the level. The diagonal map is 2-Lipschitz. The triangle inequality therefore transfers compact uniform convergence to the joint realization. Evaluation at any rank-dependent level in `K` preserves the limit; multiplication by a common Lipschitz constant transfers it to rank-dependent tests.

## Boundary

Only compact subsets of `(0,1)` are claimed. The finite atomic laws and unbounded Gaussian tails prevent uniform convergence over the entire open interval.

## Verification

- Three new leaves compiled natively with terminal exit 0 and empty logs: `HTGeometry.QuantileCompactConvergence`, `RHTower.WeilLogShiftProjectedQuantileUniform`, `RHTower.WeilLogShiftJointQuantileUniform`.
- Seven public theorems; all seven `#print axioms` audits contain only `propext`, `Classical.choice`, `Quot.sound`. Fourteen supporting API names checked in a scratch file. No proof placeholders or extra axioms.
- Six direct imports, five incoming imports, each new module reachable from its theorem-area umbrella exactly once. Source/object and direct dependency freshness checks passed. Declaration uniqueness and scoped `git diff --check` passed.
- Local research index returns all four joint convergence roots, with no markers. Supporting generic and scalar declarations are exported through their respective modules.
- Global `scripts/formal_tools.py lint`: nine unrelated errors, 367 warnings; no finding in the three new leaves. Unreachable modules: `CCMPolarOddPrimeJumps`, `PaperThetaSchurCompactGap`, `PaperThetaSchurFiniteStageLimit`, `PaperThetaSchurIdealClassification`, `PaperThetaSchurModeCharge`, `PaperThetaSchurModeOperator`, `WeilRationalCuspLockSpectrum`, `HTGeometry.QKrawtchoukCompanionTriangular`. Existing proof debt: `CCMPolarOddPrimeJumps.lean:104`, `ccmPolarOddSource_eq_core_add_atoms`.

## Exact formal result

The generic finite-bracket theorem uses the corpus's normalized CDF and its Galois connection, so no probability-measure instance is needed for that helper. The paper argument above remains unchanged: it uses only the two bracket implications and strict increase of the limiting CDF. The actual finite Weil roots instantiate genuine probability laws and discharge all distributional hypotheses. Their only parameters are the offset family, a compact interior probability set, levels in that set and tests with a common Lipschitz constant.

The pointwise realization from `finite-weil-joint-quantile-realization` is thus upgraded to compact uniform convergence. No full-open-interval uniform limit or quantitative scalar convergence rate is claimed.

Audit artifacts: `/tmp/hgt-compact-quantile-{metadata.json,declarations.json,final-audit.lean,final-audit.log,roots-search.json,lint.log}`.

## Next conjecture

Audit whether existing higher-moment limits upgrade this same common-uniform realization from quadratic mean convergence to every finite moment. This requires tail control derived from the actual finite Weil laws; compact quantile convergence alone does not supply it.
