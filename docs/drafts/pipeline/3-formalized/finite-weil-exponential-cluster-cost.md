# Exponential finite Gram certificate cost

Status: dependency-closed paper argument and Lean proof verified. Global lint exits 1 on 14 unrelated unreachable modules; no errors reference this branch.
Sources: local Lean corpus and installed Lean dependencies only. No web, external papers, or numerics.

## Exact target

There exist B>0 and an integer K>=2 such that, for every cutoff N>=2K, every normalized finite Gram certificate on `Finset.range N` has total cost greater than 2^(N/K), where division in the exponent is natural-number division. Under any fixed positive cost normalization B0, the same bound holds with a positive prefactor depending only on B0. This is an exponential lower bound; no matching upper bound is claimed.

## Paper closure

1. `WeilWorkDeficitDerivativeBudget.kernel_derivative_factorial_envelope` supplies common B,C>0 for all actual kernel derivatives: norm of derivative k is bounded by B*C^k*(k+2)!*exp(-exp(2|x|))*exp(-|x|), choosing its allowed parameter a=1. Since exp(2|x|)>=2|x|, this is bounded by B*C^k*(k+2)!*exp(-3|x|). Increase C to max(1,C).
2. Expose the already proved Taylor estimate's constant: degree-r remainder is bounded by exp(3)*B*C^(r+1)*(r+3)!/r! times exp(-3|x|)*h^(r+1), for 0<=h<=1. The factorial ratio is (r+1)(r+2)(r+3)<=6*8^r. Thus one D>0 and L>=1 bound every real-kernel remainder by D*L^r*exp(-3|x|)*h^(r+1).
3. Expose constant-preserving forms of the existing moment-cancellation and autocorrelation-transfer proofs. They give one E>0, independent of r, with autocorrelation cancellation bounded by E*L^r*exp(-2|y|)*l1(c)*H^(r+1).
4. The normalized rank-nullity vector on r+2 labels has l1 norm <=r+2<=2^(r+1). In a cluster starting at arithmetic n, offsets have width H=(r+1)/n. If 4L(r+1)<=n, then L*H<=1/4 and H<=1. The actual paired potential is therefore bounded by 4E*exp(2|y|)/(n^2*2^r), with the same constant for every order.
5. Expose the existing unit-cluster-to-certificate transfer. It supplies cost >2*n^2*2^r for any containing finite support, using the two distinct signed witnesses.
6. Choose integer K>=4L+1 and K>=2. For cutoff N>=2K, put q=N/K, r=q-2, and k=N-q. Then q>=2, k+q=N, and Kq<=N. The r+2=q cluster coordinates are k,...,N-1, with arithmetic start n=k+2. The inequality 4L(r+1)<=n follows from K>=4L+1 and Kq<=N. Since n>=2 and q=r+2, 2^q<=2*n^2*2^r. This proves the exact target.
7. Exact homogeneity of finite Gram tail cost transfers the bound to every fixed B0>0, with prefactor B0/B. Existing unconditional finite certificate existence proves non-vacuity.

## Scope and verification plan

Expose quantitative helpers in the five leaves from the previous increment, preserving their public theorems. Add uniform moment and exponential cost leaves. Recompile every changed leaf and every dependent leaf in this branch; audit every new public declaration and the preserved ten declarations with `#print axioms` in a scratch file. Wire imports, refresh index, and run authoritative lint. Leave concurrent unrelated files unchanged.

Positive survivor: uniform actual kernel/autocorrelation cancellation estimates with controlled order dependence, together with normalized finite coefficient directions. The obstruction concerns polynomial or subexponential certificate budgets, not existence of finite certificates or RH itself.

## Checkpoint

- The five earlier leaves now expose quantitative Taylor, moment, paired-kernel, certificate-cost, and scaling helpers. Their native rebuilds all exited 0 with empty logs.
- The actual uniform factorial-envelope source passed an axiom audit with exactly `[propext, Classical.choice, Quot.sound]`.
- `RiemannUniformMomentCancellation.lean` and `WeilLogShiftExponentialClusterCost.lean` compile with exit 0 and empty logs. All seven branch artifacts and their direct project dependencies are current.
- `/tmp/hgt-weil-exponential-final-audit.lean` passed without warnings: all 24 public declarations across the seven leaves and the actual factorial-envelope source have exactly `[propext, Classical.choice, Quot.sound]` as their axiom closure. Twenty-two explicit installed-API term checks also pass.
- Umbrella imports are wired; `scripts/formal_tools.py index` exited 0. No heartbeats or recursion limits were raised; no axioms or analytic premises were introduced.

## Formal receiver

`finiteWeilGram_cutoff_cost_exponential B0 hB0` gives c>0 and integer K>=2 such that for every N>=2K and every normalized certificate on `Finset.range N`, total cost under B0 is strictly greater than c*2^(N/K). The constants are chosen before the cutoff and before its certificate. Division in the exponent is natural-number division.

`exists_finiteWeilGram_geometric_cluster_cost_bound` is the containing-support form: one B>0 and L>=1 work for every order r and every finite support containing k,...,k+r+1, whenever 4L(r+1)<=k+2. Its cost bound is 2*(k+2)^2*2^r. The proof also retains normalized coefficient directions with sensitivity at most B*exp(2|y|)/((k+2)^2*2^r).

The earlier ten public declarations remain present and audited. New quantitative helpers expose the constants previously hidden behind separate existential bounds. The local prior-search hits in `OffLineDensityWeilLowerBound` are plateau/depth-exponential Gram upper bounds, not normalized-certificate cost lower bounds.

## Remaining frontier

No matching exponential upper bound or optimal exponential rate was proved. The precise surviving question is the growth rate of the least normalized certificate cost, now known to have an exponential lower bound. Any next result must continue from the actual corpus and preserve non-vacuity through the existing unconditional finite-certificate theorem.

Logs: `/tmp/hgt-weil-exponential-final-audit.log`, `/tmp/hgt-weil-exponential-index.log`, and `/tmp/hgt-weil-exponential-lint.log`.

Global lint snapshot: unreachable `RHTower.Sieve` modules `UnitBlockFrequencyBounds`, `UnitBlockFrequencyComparison`, `UnitBlockFrequencyDecay`, `UnitBlockPoissonKernel`, `UnitBlockPoissonSummation`, `UnitBlockReflection`, `UnitBlockReflectionDualBlocks`, `UnitBlockReflectionFourthMoment`, and `UnitBlockReflectionMoment`; unreachable `HTGeometry` modules `IntervalIntegralHolderSwap`, `MonotonePhaseFirstDerivativeTest`, `PaperDiscriminantAdditiveActions`, `QKrawtchoukCompanionTriangular`, and `SmoothPlateau`. No active-placeholder error was reported. These concurrent unrelated files were left unchanged.
