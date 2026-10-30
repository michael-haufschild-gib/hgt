# Affine prime shells have polynomial growth

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement

For a smooth unit-supported profile of positive squared mass, every
positive modulus `q`, every `c≥1`, `X≥1`, affine multiplier and shell-shift
family, the complete affine shell source has absolute value at most
`4(log 4+4)ϕ(q)c²`. Its signed unit mean has the same bound; their
error is at most `8(log 4+4)ϕ(q)c²`.

## Proof

Write `M=∫φ²` and `G=φ⋆φ`. The bounds `|G|≤M` and `G(s)=0`
for `|s|≥1` imply that every active term in shell `h≥1` has
`k≥hX/c≥X/c`. Thus its reciprocal prime weight is at most
`cΛ(k)/X`. The Ramanujan coefficient has absolute value at most
`ϕ(q)`, and the full cumulative source satisfies
`ψ(X)≤(log 4+4)X`. Each shell is therefore bounded by
`(log 4+4)ϕ(q)Mc`.

There are at most `2c` shells. Multiplication by `2/M` gives the
stated full-source bound, uniformly in both affine parameters and all
shifts. Pass to the existing signed-mean limit at fixed `c` to obtain
the same mean bound. The triangle inequality gives the error bound.
No prime power or endpoint contribution is omitted.

## Lean status

`AffinePrimeShellsHavePolynomialGrowth` proves the polynomial bounds
for the actual correction, its signed mean and their difference. Final
direct Lean check passed without warnings; both dependency audits contain
only standard logical axioms. CACT umbrella wired. Supporting source
estimate; no separate contribution count.
