# Exact doubling incidence is discontinuous; weighted incidence is stable

- **ID:** biscale-perturbed-incidence-1810
- **Stage:** 2-fully-proven; node and weighted-incidence Lean coverage, common-model gates pending
- **Type:** BRIDGE; incidence obstruction and quantitative survivor
- **Parent:** [field programme](../../1-in-progress/rh/bi-scale-uncertainty/biscale-field-development-1810.md), items 7 and 12

## Explicit comparable-spacing counterexample

On `1,…,N`, with `N=2^(h+4)−1`, choose `0<δ<1/4` and set

`x_n=n+δn²/N²`, `ell_n=log x_n`.

Then `0<x_n−n≤δ`, and the nodes remain strictly increasing. Consecutive physical gaps are `1+δ(2n+1)/N²`. Logarithmic gaps satisfy

`log((n+1)/n) ≤ ell_(n+1)−ell_n ≤ (1+δ/N)log((n+1)/n)`.

For the last inequality, write `ell_n=log n+log(1+δn/N²)`. The extra gap is at most `δ/N²`, while `log((n+1)/n)≥1/(n+1)≥1/N`. Node displacements in logarithmic coordinates are at most `δ/N`.

Nevertheless **no pair of perturbed nodes satisfies `x_j=2x_i`**. If `j≠2i`, the nonzero integer `j−2i` has absolute value at least one, while the perturbation `δ(j²−2i²)/N²` has absolute value at most `2δ<1/2`. If `j=2i`, the difference is `2δi²/N²>0`. Equivalently, no logarithmic node pair has difference exactly `log 2`.

Keep the adjacent-node energy `A(f)=Σ(f_(n+1)−f_n)²` and define exact doubling energy by the actual incidences `x_j=2x_i`. On the perturbed grid the latter vanishes for every signal. The additive-only test `f_n=n` then requires a coercivity constant at least `N(N+1)/12`. On the unperturbed grid, the [joint-coercivity proof](biscale-dyadic-joint-coercivity-1810.md) bounds it by `24N`. Thus arbitrarily small perturbations with comparable spacing destroy the linear-order gain of the exact-incidence model.

This comparison uses adjacent-node energy; it does not assert that literal translation by one preserves the perturbed nodes. It also does not identify graph incidence with autocorrelation-zero constraints on a continuum source.

## Quantitative positive survivor

For arbitrary perturbations `x_n=n+epsilon_n` with `|epsilon_n|≤δ<1/6`, use all node pairs and the explicit weight

`w_(i,j)=max(0,1−2|x_j−2x_i|)`.

For `j≠2i`, `|x_j−2x_i|≥1−3δ>1/2`, so the weight is zero. For `j=2i`, the mismatch is at most `3δ`, giving `1−6δ≤w_(i,2i)≤1`. Therefore the weighted incidence energy `D_w=Σ_(i,j) w_(i,j)(f_j−f_i)²` satisfies

`(1−6δ)D≤D_w≤D`,

where `D` is the original integer doubling energy. Combining with the joint bound gives

`V(f)≤24N/(1−6δ) · (A(f)+D_w(f))`.

The original dyadic tent still has `D_w=0`, bounded `A`, and variance proportional to `N`, so linear deterioration remains sharp in order. The weights recover the same incidence from the perturbed locations; the construction does not assume an externally supplied matching. In logarithmic coordinates the mismatch is `|exp(ell_j)−2exp(ell_i)|`; it is not an unspecified fixed tolerance in log distance.

## Audit and gates

- Corpus query `perturbed integer logarithmic grid doubling exact incidence approximate energy` returned grid-trace and multiplier-collision identities, without this finite graph perturbation law among returned statements. Coverage was a source snapshot with unmeasured semantic completeness.
- The survivor uses elementary energy comparison and a classical graph mechanism. No external originality claim is made.
- [x] Exact perturbed grids, complete incidence exclusion, gap bounds and weighted survivor proved symbolically.
- [x] Lean arithmetic/gap/weight proofs and transfer of the joint-coercivity constants.
- [ ] Instantiate the common finite arithmetic model and its divisor-sieve realization.
- [ ] Determine the corresponding statement for actual continuum correlation constraints; do not substitute the graph example for that question.
- [x] Named-source/axiom audits, wiring, index and scoped lint. Global unrelated failures are recorded below.

This component alone does not close item 12.

## Frozen Lean completion

The two started leaves passed the combined source and transitive axiom audit:
24 public declarations, using only `propext`, `Classical.choice`, `Quot.sound`.
Both final direct checks passed without diagnostics. Neither leaf needs an
olean for another started module. Unique umbrella imports and indexed names
are verified; global lint has no diagnostic for these leaves (20 unrelated
errors and 417 size warnings).

| Exact claim | Canonical leaf and declaration |
|---|---|
| Actual all-pairs triangular weights, exclusion of off-doubling pairs, exact weighted sum and `(1−6δ)D≤D_w≤D` | `WeightedDoublingIncidence.lean`: `softDoublingWeight_eq_zero_of_ne`, `softDoublingEnergy_eq_doubling_sum`, `softDoublingEnergy_comparison` |
| Original tent remains null; exact `24N/(1−6δ)` window bound | `WeightedDoublingIncidence.lean`: `softDoublingEnergy_dyadicMantissaTent`, `softDoubling_window_coercivity` |
| Actual quadratic nodes, displacement, strict order, exact physical gaps and doubling exclusion | `QuadraticPerturbedNodes.lean`: `strictMono_quadraticPerturbedNode`, `quadraticPerturbedNode_succ_sub`, `quadraticPerturbedNode_ne_double` |
| Log displacement, exact two-sided relative gap bounds and exclusion of a `log 2` difference | `QuadraticPerturbedNodes.lean`: `quadraticPerturbedLogNode_displacement`, `quadraticPerturbedLogNode_gap_bounds`, `quadraticPerturbedLogNode_sub_ne_log_two` |

All names use `GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon`.
The positive survivor uses actual node locations and all ordered pairs;
matching is proved from the weights, not assumed. The companion dyadic leaves
prove the original tent's variance and its finite divisor-sieve realization.

This remains a partial card. A dedicated exact-incidence energy and its
vanishing/coercivity consequence, transport of energies into the common
arithmetic model, and a statement for actual continuum correlation constraints
remain under active formalization in the resumed programme. Drafts include
exact graph-energy identities, all-energy sieve transport, weighted sharpness,
quantitative correlation-sample stability, and actual smooth integer-grid-blind
sources with half-sized perturbed-node violations. No draft is counted as
certified before its direct source and transitive axiom checks pass. Current
evidence is recorded in [the full programme](../../1-in-progress/leftovers-unconditional-formalization.md).

Evidence: `/tmp/leftovers-dyadic-perturbed-public-names.json` and
`/tmp/leftovers-dyadic-perturbed-audit-r2.log` (62 declarations across both cards).

## Final source checks for the started scope

Both leaves passed direct `lake --old env lean -j 1` checks from `formal/`,
without writing oleans. Their 24 public declarations have standard-axiom
certificates in the shared 62-name audit. No umbrella was compiled.

| Leaf | SHA-256 | Final direct-check log |
|---|---|---|
| `WeightedDoublingIncidence` | `f5431b77daf6edf45efeba4a681be25bc9874910f71d16413a97a586915cee03` | `/tmp/leftovers-weighted-incidence-final.log` |
| `QuadraticPerturbedNodes` | `ace2e3553f44f6af64eae9d1bc136f7c203009a0952389138fe8682cd0125a49` | `/tmp/leftovers-quadratic-nodes-final.log` |
