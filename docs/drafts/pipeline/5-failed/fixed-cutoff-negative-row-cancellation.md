# Fixed-cutoff negative-row cancellation fails

- **Stage:** 5-failed
- **Type:** FALSIFIED SHORTCUT
- **Route:** Argon §4.1.

## Failed claim

A row-dependent Poisson-horizon theorem cannot justify negative cancellation
for every row of a model with one fixed conductor cutoff Q.

## Killing theorem

`exists_positive_stabilizerLinearRow` constructs a smooth nonnegative window
supported in `[31/32,33/32]` whose complete Q=7 row at m=7/π is at least
43/576. The construction works at every radius `0<δ≤1/32` about 1,
so the support can approach the horizon arbitrarily closely. `exists_eventually_positive_finite_stabilizerRow` gives positive
finite linear truncations. Thus universal negative-row cancellation is false.
This does not refute a global model asymptotic or the actual prime-pair bound.

## Positive survivor

The exact Poisson decomposition identifies the correction as a sum of
nonnegative primitive spatial samples. Negative cancellation holds precisely
when all samples at active squarefree odd conductors vanish. In particular,
`Qb≤πm` gives exact cancellation, including equality. Along `m=bQ/π`, the
row divided by log Q tends to `−Ωhat(0)/2`.

This supplies an exact criterion and a sharp support boundary. Beyond that
boundary, the negative diagonal is a lower bound; an upper bound must pay
the surviving samples. The proof and Lean declarations are recorded in
[Exact Poisson rows](../3-formalized/exact-poisson-row-for-the-odd-stabilizer.md).
