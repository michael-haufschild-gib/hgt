# Adjacent and doubling differences: sharp linear deterioration

- **ID:** biscale-dyadic-joint-coercivity-1810
- **Stage:** 3-formalized
- **Type:** BRIDGE; elementary graph-energy comparison
- **Parent:** [field programme](../../1-in-progress/rh/bi-scale-uncertainty/biscale-field-development-1810.md), items 7 and 12

## Exact family and conclusion

For `h≥0`, put `N=2^(h+4)−1`. On the actual integer window `1,…,N`, define

`A(f)=Σ_(n=1)^(N−1) (f(n+1)−f(n))²`,

`D(f)=Σ_(n=1)^floor(N/2) (f(2n)−f(n))²`,

`V(f)=min_c Σ_(n=1)^N (f(n)−c)²`.

These are the existing additive energy and the multiplicative energy with cutoff `K=2`. The joint kernel is the constants. The best constant in `V≤C_N(A+D)` satisfies

`N/4096 ≤ C_N ≤ 24N`.

The lower constant is deliberately conservative; the sharp assertion is linear dependence on `N`. Additive energy alone requires a constant at least `N(N+1)/12`; doubling energy alone has a nonconstant null vector. Thus neither scale alone gives the same conclusion and parameter dependence.

## Upper bound by actual incidence

Use the complete binary tree on the same labels, with children `2n` and `2n+1`. Its energy `T` obeys

`T ≤ 3D+2A`.

Indeed, the even-child edges contribute exactly `D`. Each odd-child difference is the sum of its adjacent difference `f(2n+1)−f(2n)` and the doubling difference `f(2n)−f(n)`; squaring costs at most twice each square. Every used adjacent edge belongs to `A`.

For a root-to-vertex path, let `Δ_k` denote its edge difference at child depth `k≥1`. Weighted Cauchy–Schwarz gives

`(Σ_k Δ_k)² ≤ (Σ_k (3/4)^k)(Σ_k (4/3)^k Δ_k²) ≤ 4 Σ_k (4/3)^k Δ_k²`.

An edge at depth `k` has at most `2N/2^k` descendants. Summing the path bound over all vertices therefore charges that edge at most

`8N(2/3)^k ≤ 8N`.

Consequently `V(f)≤Σ_n(f(n)−f(1))²≤8NT≤24N(A+D)`. Descendant counts follow directly by summing the complete levels below the edge; no spectral computation is used.

## Matching family and single-scale failures

Write each positive integer uniquely as `n=2^k+j`, `0≤j<2^k`, and set

`f(n)=min(j,2^k−j)/2^k`.

Doubling sends `(k,j)` to `(k+1,2j)`, so `f(2n)=f(n)` and `D(f)=0`. Across a full level with `k≥1`, all consecutive differences, including the transition to the next level, have absolute value `2^(−k)`. Its additive energy is `2^(−k)`; the root level contributes zero. Omitting the final transition only decreases energy, hence `A(f)<2`.

In the last level, set `q=2^(h+3)`, so `N=2q−1` and `8∣q`. At least `q/2` entries have `f≥1/4`, using `q/4≤j≤3q/4`. At least `q/4` entries have `f≤1/8`, using `0≤j≤q/8` and `7q/8≤j<q`. For any real `c`, either `c≤3/16` and the first group lies at distance at least `1/16`, or `c≥3/16` and the second group does. Thus

`Σ_n(f(n)−c)² ≥ q/1024 ≥ N/2048`.

Together with `A+D≤2`, this gives `C_N≥N/4096`. The same nonconstant tent defeats coercivity to constants from `D` alone.

For the additive-only test `g(n)=n`, the exact variance is `N(N²−1)/12` and `A(g)=N−1`; their ratio is `N(N+1)/12`. The formulas follow from finite sums of first and second powers, without numerical evaluation.

## Lean formalization

All declarations live in `GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon`, folder
`formal/GaloisForLFunctions/BiScaleUncertainty/`, wired into `BiScaleUncertainty.lean`.
Standard axioms only.

| Claim | Leaf: declarations |
|---|---|
| Tree comparison `T ≤ 3D+2A` | `FiniteHorizonPositiveCoercivity`: `binary_energy_le_doubling_additive` |
| Weighted Cauchy–Schwarz along a path, `Σ(3/4)^k ≤ 4`, descendants `≤ 2N/2^k`, edge charge `8N(2/3)^k ≤ 8N`, `V ≤ 8NT` | `BinaryDepthCoercivity`: `binary_path_geometric_sum`, `binary_path_geometric_cauchy`, `binary_descendant_depth_bound`, `binary_descendant_depth_charge`, `binary_descendant_depth_charge_le`, `binary_parent_window_bound_eight` |
| Actual root-to-vertex paths: depth `log₂ n`, weighted path bound | `BinaryPathWeights`: `sum_binaryAncestors_by_depth`, `card_binaryAncestors_eq_log`, `binary_ancestor_geometric_sum`, `binary_parent_geometric_point_bound` |
| Mantissa tent, `f(2n)=f(n)`, level increments and energy, `A < 2` | `DyadicMantissaTent`: `dyadicMantissaTent_two_mul`, `dyadicMantissaTent_full_level_energy`, `additiveStepEnergy_dyadicMantissaTent_lt_two` |
| High/low counts `q/2`, `q/4` on the last level; doubling energy alone is not coercive | `DyadicTentLevelCounts`: `dyadicMantissaTent_high_count`, `dyadicMantissaTent_low_count`, `dyadicMantissaTent_last_level_counts`, `not_doubling_only_window_coercivity` |
| Linear signal: variance `N(N²−1)/12`, `A = N−1`, additive-only constant `≥ N(N+1)/12` | `IntegerLinearVariance`: `sum_Icc_linear_centered_sq`, `additive_coercivity_constant_linear_lower_bound` |
| Mean minimizes the centered sum; the best constant is attained | `FiniteWindowVariance`: `integerWindowVariance_le_centered`, `windowCoercivityBound_sInf` |
| Tent variance `≥ N/2048`; `N/4096 ≤ C_N ≤ 24N` | `DyadicMantissaVariance`: `dyadicMantissaTent_variance_lower`, `dyadicWindowBestConstant_bounds`, `dyadicWindowBestConstant_valid` |
| Finite Möbius coefficients realize every window signal | `FiniteSieveRealization`: `exists_finite_sieveSeq_realization` |
| Variance, adjacent, doubling and physical energies are preserved by the sieve realization; same valid constants | `FiniteSieveGraphEnergyTransport`: `exists_sieveSeq_graph_realization`, `sieveSeq_joint_coercivity_iff` |

The perturbed-incidence statements are on the
[companion card](biscale-perturbed-incidence-1810.md).
