# All-order logarithmic cluster cancellation

Status: dependency-closed paper argument and Lean proofs verified. Global lint exits 1 on 14 unrelated unreachable modules; no errors reference these five leaves.
Evidence: local Lean corpus and installed Lean dependencies only. No external sources or numerics.

## Claim

For each fixed r >= 0, r+2 nearby logarithmic translates admit a unit coefficient vector whose actual paired-kernel potential is O(n^(-r-3) exp(2|y|)). Consequently every normalized finite Gram certificate containing that cluster has cost bounded below by a positive multiple of n^(r+3). Constants may depend on r. At full cutoffs this forces growth beyond every fixed polynomial under any fixed positive cost normalization.

## Paper proof

1. Existing `hasDerivAt_riemannKernelDeriv` and `contDiff_riemannKernelDeriv` identify every iterated derivative of the actual Riemann kernel. Existing cubic exponential envelopes bound each derivative by C_r exp(-3|x|).
2. Taylor's theorem on [x,x+1] gives a degree-r polynomial with remainder at nonnegative shift h <= 1 bounded by D_r exp(-3|x|) h^(r+1). Its coefficients are the actual derivatives. Take real parts. Autocorrelation reflection handles the other sign without differentiating an improper integral.
3. Any finite signed coefficients annihilating h^p for p<=r cancel the polynomial exactly. The remaining bound is D_r exp(-3|x|) H^(r+1) times their l1 norm when all shifts lie in [0,H].
4. Multiply by the original kernel and integrate. The inequality 3|t|+3|t-y| >= |t|+2|y| gives an integrable dominating function. Finite sums commute with the already integrable translates. Hence the actual autocorrelation has the same cancellation bound with exp(-2|y|).
5. The first r+1 logarithmic moments define a real linear map from r+2 coordinates to r+1 coordinates. Rank-nullity gives a nonzero kernel vector. Normalize its sup norm to one, giving l1 norm <= r+2.
6. At arithmetic nodes n,...,n+r+1, set h_j=log(n+j)-log n. For n>=r+1, 0<=h_j<=(r+1)/n<=1. The two paired translates and log-center decay supply n^-2; cancellation supplies n^(-r-1).
7. Zero extension preserves sup norm one on every containing finite support. Existing normalized Gram certificates give distinct negative witnesses for c and -c. Each costs more than the reciprocal sensitivity bound, so their combined cost exceeds twice that bound. Cost is linear in its positive normalization parameter.
8. Put the cluster near the upper cutoff. For a target degree p, use r=p, start at k=N-(p+2), and take N>=2(p+2). Then k+2>=N/2, while the cost bound has degree p+3. Exact linear scaling reconciles the order-dependent constant with any positive normalization fixed in advance. This proves eventual domination of every fixed multiple of N^p.

No new analytic premise, RH assumption, differentiation-under-integral premise, or axiom. This does not claim an exponential lower bound or a matching upper bound.

## Checkpoint

- Local novelty search found existing all-order smoothness in `WeilNearRadicalDimension`; reuse it.
- Existing quartic result is verified and retained.
- All five leaves compile with exit 0 and empty native logs: `RiemannKernelMomentCancellation`, `RiemannAutocorrMomentCancellation`, `WeilLogShiftAllOrderCancellation`, `WeilLogShiftAllOrderClusterCost`, and `WeilLogShiftSuperpolynomialGramCost`.
- All ten public declarations have exactly `[propext, Classical.choice, Quot.sound]` as their axiom closure. The final scratch audit additionally checks 49 installed APIs as explicit `have := @Name` terms, without warnings.
- Umbrella imports are wired; `scripts/formal_tools.py index` exited 0. Source artifacts and direct imported project artifacts are current.
- A local Lean elaboration issue in the scalar cost bound exposed two definitionally equal real order instances. The diagnostic identified the exact three conversion goals; discharge the instance and reflexive goals by `rfl`, then prove the scalar reassociation by `ring`.
- No global proof-route retirement: the obstruction concerns polynomial certificate budgets. Positive survivors are the unconditional normalized cancellation directions and actual all-order kernel/autocorrelation envelopes.

## Exact receiver and remaining frontier

`finiteWeilGram_cutoff_cost_superpolynomial B hB p A` states: for every fixed B>0, degree p, and real A, some N exists such that for every n>=N and every normalized certificate on `Finset.range n`, total cost exceeds A*n^p. The existing unconditional finite-certificate theorem confirms non-vacuity for every finite cutoff.

This increment did not prove a rate uniform in the cancellation order. The subsequent [exponential cluster-cost result](finite-weil-exponential-cluster-cost.md) closes that question using the corpus's actual factorial derivative envelope. It preserves and re-audits the ten public declarations from this increment.

Audit logs: `/tmp/hgt-weil-all-order-final-audit.log`, `/tmp/hgt-weil-all-order-index.log`, and `/tmp/hgt-weil-all-order-lint.log`.

Global lint snapshot: unreachable `RHTower.Sieve` modules `UnitBlockFrequencyBounds`, `UnitBlockFrequencyComparison`, `UnitBlockFrequencyDecay`, `UnitBlockPoissonKernel`, `UnitBlockPoissonSummation`, `UnitBlockReflection`, and `UnitBlockReflectionMoment`; unreachable `HTGeometry` modules `IntervalIntegralHolderSwap`, `MonotonePhaseFirstDerivativeTest`, `PaperDiscriminantAllDerivations`, `PaperDiscriminantRootUnits`, `PaperLocallyNilpotentMultipliers`, `QKrawtchoukCompanionTriangular`, and `SmoothPlateau`. No active-placeholder error was reported in this run. These concurrent unrelated files were left unchanged.
