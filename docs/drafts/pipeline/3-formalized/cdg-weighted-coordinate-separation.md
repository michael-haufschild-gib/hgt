# Weighted coordinate separation from collective small forms

- **ID:** CDG-WEIGHT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Retain at least half of any nonnegative prime weight in a
  coordinate subfamily with a scalar separation floor of linear dimension degree.

## Theorem

For `k≥1` distinct primes and coefficient height `H≥1`, put
`W=ceil(Σ log p_j)+1`, `U=10⁴(W+1)(k+1)²`, `C=U^(100(k+1))`,
`H′=k!H^k`, and

`β=exp(−C(log(k!H′^k)+2))/(k·k!H′^(k−1))`,
`ε=β/(k!H^(k−1))`.

For every family of nonnegative coordinate weights, there is a subset carrying
at least half the total weight on which every nonzero integer form of
height at most `H` has absolute value at least `ε`.

## Proof [PROVED HERE]

Let `V` be the rational span of all height-`H` integer forms of size below
`ε`. The set is finite, also for real `H`, by containment in the integer box
of height `ceil(H)`.

[Bounded elimination](cdg-bounded-coordinate-elimination.md)
and the strict-majority collective floor give

`2 dim(V ∩ ℚ^J) ≤ |J|` for every coordinate set `J`.

The uniform arithmetic comparison is proved in
[CDG-HERED](cdg-hereditary-rank-bounds.md). Its threshold is exactly the
one displayed above.

Choose an injective coordinate projection `φ` of `V`, with `dim V` chosen
coordinates, minimizing their total weight. The projection is a linear
isomorphism onto its coordinate space. Pulling back the standard basis
therefore gives a basis `b_i` of `V` with `b_i(φ(j))=δ_ij`.

If `b_i(j)≠0`, exchanging `φ(i)` for `j` preserves injectivity: a vector
killed by the exchanged projection has all old basis coefficients except
possibly the `i`th equal to zero, and its `j`th coordinate kills that last
coefficient. Minimality consequently gives `w(φ(i))≤w(j)`.

Let `N(i)` be the unchosen coordinates where `b_i` is nonzero. For any
basis-index set `A`, its independent rows span a space of dimension `|A|`
supported on `φ(A)∪N(A)`. These coordinate sets are disjoint, so hereditary
sparsity gives `2|A|≤|A|+|N(A)|`. Hall's theorem supplies an injection
`μ(i)∈N(i)`. Every matched weight is at least `w(φ(i))`. Nonnegativity of
all remaining weights gives

`weight(chosen projection) ≤ weight(unchosen coordinates)`.

Thus the complement carries at least half the total weight. A vector of
`V` supported on that complement has zero projection and hence is zero.
Every nonzero height-`H` integer form supported there therefore has value
at least `ε` in absolute value.

## Contribution and boundary

A mere bound on the total rank can concentrate every exceptional coordinate
on the largest weights. The hereditary bound prevents that obstruction
and retains a fixed mass fraction for logarithmic or critical-column weights.
The bound retains the collective linear degree through height-controlled
elimination. The comparison with quadratic scalar degree concerns the
Fel'dman estimate formalized in this corpus only.

[Matveev, Corollary 2.3](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=314&what=fullteng)
already supplies linear dimension degree for every nonzero scalar form,
retaining all coordinates and a stronger floor. Consequently this is a
formal coefficient-body mechanism, not an improvement on published scalar
separation or a new breadth estimate.

This is a coefficient-body separation theorem. Constant-precision first-return
exclusion and the prime-degree trace producer remain separate open inputs.

## Formalization

`CollectiveDiophantineGeometry/WeightedCoordinateSeparation.lean`:

- `exists_half_weight_avoiding_subspace`: weighted selection from hereditary rank.
- `exists_weighted_prime_coordinate_separation`: the actual prime-logarithm
  theorem, with the hereditary premise discharged and arbitrary real `H≥1`.

The direct `lake --old env lean` source check passed. Both transitive axiom
audits contain only `propext`, `Classical.choice` and `Quot.sound`.
The programme umbrella imports the module.
