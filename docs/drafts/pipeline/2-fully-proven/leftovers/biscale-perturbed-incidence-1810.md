# Exact doubling incidence is discontinuous; weighted incidence is stable

- **ID:** biscale-perturbed-incidence-1810
- **Stage:** 2-fully-proven for the finite graph comparison; Lean and common-model realization pending
- **Type:** BRIDGE; incidence obstruction and quantitative survivor
- **Parent:** [field programme](../1-in-progress/biscale-field-development-1810.md), items 7 and 12

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
- [ ] Lean arithmetic/gap/weight proofs and transfer of the joint-coercivity constants.
- [ ] Instantiate the common finite arithmetic model and its divisor-sieve realization.
- [ ] Determine the corresponding statement for actual continuum correlation constraints; do not substitute the graph example for that question.
- [ ] Named-source/axiom audits, wiring, index and lint.

This component alone does not close item 12.
