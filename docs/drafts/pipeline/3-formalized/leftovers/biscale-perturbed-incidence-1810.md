# Exact doubling incidence is discontinuous; weighted incidence is stable

- **ID:** biscale-perturbed-incidence-1810
- **Stage:** 3-formalized
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

## Exact-incidence energy and the arithmetic model

Define the physical exact energy as the sum over ordered window pairs of `(f_j−f_i)²` over
pairs with `x_j=2x_i`. At integer positions it equals the doubling energy `D`; on the
quadratic grid every term vanishes, so `f_n=n` forces the constant `N(N+1)/12`, while the
integer grid keeps `24N`. Taking `δ=min(ε/2,1/8)` gives an incidence-free strictly ordered
grid within any displacement `ε>0`.

Finite Möbius inversion realizes every window signal as an actual divisor sieve. All the
energies above, and the centered variance, only read values on `1,…,N`, so the set of valid
constants is the same for arbitrary signals and for divisor sieves. In particular the weighted
constant obeys `N/4096 ≤ C` for every allowed perturbation, by the dyadic tent.

## Continuum correlation constraints

For a source of normalized singular energy at most `E`, the quadratic grid displaces every
logarithmic sample by at most `δ/N`. The singular-energy modulus gives

`|c(ell_n) − c(log n)| ≤ sqrt(8E/(e^{−1/2}·(−log(δ/N))))`,

so exact zeros on either grid are approximate zeros on the other. A jump of the normalized
correlation from `0` to `1/2` across a displacement `d ≤ 1` forces
`E ≥ e^{−1/2}(−log d)/32`.

Conversely, for `log 2 < T < log 3` two narrow smooth copies separated by `T` have correlation
`1/2` at `T` and `0` at every `log n`, `n≥2`, with energy at most `C − log ρ(T)`, where
`ρ(T)=min(1, log2/2, (T−log2)/2, (log3−T)/2)`. With `T=ell_2` this is an integer-blind source
with a half-sized violation on the quadratic grid; its energy necessarily grows like
`−log(δ/N)`. Exact incidence constraints and exact correlation constraints are therefore
different questions: correlation samples move continuously with bounded energy.

## Lean formalization

Declarations in `GaloisForLFunctions.BiScaleUncertainty` (sub-namespace `FiniteHorizon` for
the graph leaves), folder `formal/GaloisForLFunctions/BiScaleUncertainty/`, wired into
`BiScaleUncertainty.lean`. Standard axioms only.

| Claim | Leaf: declarations |
|---|---|
| Quadratic nodes, displacement, strict order, gaps, no `x_j=2x_i` | `QuadraticPerturbedNodes`: `strictMono_quadraticPerturbedNode`, `quadraticPerturbedNode_succ_sub`, `quadraticPerturbedNode_ne_double` |
| Log displacement `≤ δ/N`, relative gap bounds, no `log 2` difference | `QuadraticPerturbedNodes`: `quadraticPerturbedLogNode_displacement`, `quadraticPerturbedLogNode_gap_bounds`, `quadraticPerturbedLogNode_sub_ne_log_two` |
| Exact-incidence energy; integer case; vanishing on the quadratic grid; `N(N+1)/12` and `24N`; small incidence-free grids | `ExactDoublingEnergy`: `exactDoublingEnergy_integer`, `exactDoubling_integer_coercivity`, `exactDoublingEnergy_quadraticPerturbedNode`, `exactDoubling_quadratic_coercivity_lower`, `exists_small_incidence_free_grid` |
| All-pairs weights, off-doubling exclusion, `(1−6δ)D ≤ D_w ≤ D`, tent null, `24N/(1−6δ)` | `WeightedDoublingIncidence`: `softDoublingWeight_eq_zero_of_ne`, `softDoublingEnergy_comparison`, `softDoublingEnergy_dyadicMantissaTent`, `softDoubling_window_coercivity` |
| Divisor-sieve transport of all energies; equal constant sets; weighted `N/4096` sharpness; log-coordinate weights | `FiniteSieveGraphEnergyTransport`: `exists_sieveSeq_graph_realization`, `sieveSeq_exact_quadratic_coercivity_lower`, `sieveSeq_soft_coercivity_iff`, `softDoubling_dyadic_coercivity_lower`, `sieveSeq_soft_dyadic_coercivity_lower`, `softDoublingEnergy_exp_log` |
| Sample stability and the half-jump energy barrier | `PerturbedCorrelationSamples`: `quadratic_correlation_samples_close`, `quadratic_correlation_of_integer_zero`, `integer_correlation_of_quadratic_zero`, `correlation_zero_half_energy_barrier`, `quadratic_correlation_half_energy_barrier` |
| Integer-blind smooth peak in the first log gap; quadratic-grid violation | `IntegerGapCorrelationPeak`: `integerLogGapRadius_pos`, `exists_smooth_integer_gap_peak`, `exists_quadratic_integer_grid_blind_violation` |
