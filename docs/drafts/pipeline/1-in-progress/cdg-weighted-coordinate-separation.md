# Weighted coordinate separation from collective small forms

- **ID:** CDG-WEIGHT
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Retain at least half of any nonnegative prime weight in a
  coordinate subfamily with a scalar separation floor of linear dimension degree.

## Target

For `k≥1` distinct primes and coefficient height `H≥1`, put
`W=ceil(Σ log p_j)+1`, `U=10⁴(W+1)(k+1)²`, `C=U^(100(k+1))`,
`H′=k!H^k`, and

`β=exp(−C(log(k!H′^k)+2))/(k·k!H′^(k−1))`,
`ε=β/(k!H^(k−1))`.

For every family of nonnegative coordinate weights, seek a subset carrying
at least half the total weight on which every nonzero integer form of
height at most `H` has absolute value at least `ε`.

## Arithmetic mechanism

Let `V` be the rational span of the height-`H` forms of size below `ε`.
The stronger intermediate target is hereditary coordinate sparsity:

`2 dim(V ∩ ℚ^J) ≤ |J|` for every coordinate set `J`.

If a coordinate intersection has dimension exceeding half its support,
eliminate the other coordinates from a basis selected among the original
small forms. Maximal-minor elimination produces independent forms
supported on `J`, with coefficient height at most `k!H^k` and values below
`k!H^(k−1)ε`. At strict majority rank the collective root degree is
one, so the common exponent `C` is sufficient for every restriction.
The elimination theorem is formalized as `exists_bounded_coordinate_basis`:
[CDG-ELIM](../3-formalized/cdg-bounded-coordinate-elimination.md).

## Weighted selection mechanism

Choose an injective coordinate projection of `V` of minimum weight.
Normalize its row basis to the identity on the chosen coordinates.
A nonzero entry in an unchosen column permits basis exchange, so minimum
weight forces the unchosen weight to be at least the exchanged weight.
Hereditary sparsity gives Hall's condition for the support graph of any
row subset. A matching injects chosen coordinates into unchosen ones
with no loss of weight. Hence the chosen projection costs at most half
the total weight. Its complement contains no nonzero small relation.

## Contribution and boundary

A mere bound on the total rank can concentrate every exceptional coordinate
on the largest weights. The hereditary bound would prevent that obstruction
and retain a fixed mass fraction for logarithmic or critical-column weights.
Scalar selection of the heaviest half retains mass but keeps the existing
quadratic dimension degree. The proposed bound retains the collective
linear degree through height-controlled elimination.

This is a coefficient-body separation theorem. Constant-precision first-return
exclusion and the prime-degree trace producer remain separate open inputs.

## Dependencies to close

1. Uniform comparison with every strict-majority collective floor.
2. Weighted projection selection from hereditary sparsity, with no matroid
   packing or matching premise left unproved.
3. Exact arithmetic capstone and transitive Lean axiom audit.
