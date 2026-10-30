# Upward kernel linearization has polynomial cost

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement and proof

Assume `c≥1`, `c/N≤1`, and `2(e+3)cB≤N`. For integer gap at most
`B`, the logarithmic autocorrelation kernel with square-root Jacobian
differs from its reciprocal-offset kernel by at most
`C c²(B+1)²/N`. An active logarithmic kernel forces both indices above
`N/(ec)`; an active reciprocal kernel gives `N≤cT`, and the gap bound
then gives `N≤2cj`. Thus both use `A=(e+3)c` in the existing Taylor
bound `[4LA²B²/c+ABM]/N`. Bounding `1/c≤1` gives the claimed polynomial.

Summing both signs and all actual prime powers yields
`D c²(B+1)³ mertensSum(N+B)/N` for the coefficient error. Each
Ramanujan coefficient has size at most `ϕ(m)`, and no cutoff changes.

When `B≤N` and `log N≥1`, bounded Mertens finite part gives
`mertensSum(N+B)≤C log N`. Harmonic summation and
`(log N/N)²≤4/√(log N)` therefore give normalized squared error
`K c⁴(B+1)⁶/√(log N)`.

## Lean status

`UpwardKernelLinearizationHasPolynomialCost.lean` proves the kernel,
coefficient and harmonic-norm estimates. Final direct Lean audit passed
without warnings; all three axiom audits contain only `propext`,
`Classical.choice`, `Quot.sound`. No separate contribution count.
