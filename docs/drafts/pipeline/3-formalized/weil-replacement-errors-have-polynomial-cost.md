# Weil replacement errors have polynomial cost

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

On each fixed positive Ramanujan conductor, the literal two-pole and
separated-cross replacement residuals have normalized squared norms
`O(c⁴/log N)`. Existing kernel bounds give raw squared mass `O(c⁴)`;
normalization divides by `log N`. The pole estimate needs `c≤N`.

The full center residual scales exactly by `c`; its unit-charge raw
squared norm is bounded, giving `O(c²/log N)` uniformly in overlap.
The self error is `O(c/N)` when `c≤N`, and normalized conductor norm
is eventually at most `√2`, giving squared norm `O(c²/N²)`.
Every source is the actual complete Weil replacement term.

## Lean status

`WeilReplacementErrorsHavePolynomialCost` proves all four literal
normalized bounds. Final direct Lean check passed without warnings;
all four transitive axiom audits contain only standard logical axioms.
CACT umbrella wired. Supporting explicit source estimates; no separate
contribution count.
