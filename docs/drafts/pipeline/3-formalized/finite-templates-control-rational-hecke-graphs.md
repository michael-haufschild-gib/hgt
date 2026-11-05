# Finite templates control rational Hecke graphs

- **ID:** finite-templates-control-rational-hecke-graphs
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-0411 §2.1, A6.

## Statement

Let a finite rational template `T` contain `1` and every ratio-`n` neighbour
of its vertices in `[1,R)`, for `2≤n≤N`. If its Hecke form is nonnegative,
the same holds on every finite positive rational set whose pairwise ratios
are less than `R`, with the same coefficients.

## Proof

In a nonempty vertex set `S`, choose its least element `r` and remove
`B=S∩rT`. It contains `r`. If `u∈B` and an active edge joins `u` to `v∈S`,
then `1≤v/r<R`; template closure puts `v/r` in `T`, hence `v∈B`.
Thus there are no cross terms between `B` and `S∖B`.

Scaling by `r` identifies the first block with a subgraph of `T`; extending
its amplitudes by zero proves its positivity. Strong induction on the
remaining finite set proves positivity of the second block. Their sum is
the original quadratic form. Coefficients may have either sign.

## Lean status

`WindowTowerOfSpecZ.rationalHeckeForm_nonneg_of_closed_template` in
`FiniteTemplatesControlRationalHeckeGraphs.lean` passed its direct source check
and transitive axiom audit (`propext`, `Classical.choice`, `Quot.sound`).
The owning umbrella imports the module.
