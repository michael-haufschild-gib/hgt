# Route-T terminal-first lateral landing

- **ID:** `route-t-terminal-first-lateral-landing`
- **Stage:** 5-failed
- **Route:** T / C5b
- **Disposition:** retired as a noncircular preliminary strategy

## Proposed strategy

First prove, throughout `0 < y < 1/2`, that finite positive-ray Abel-renormalized cutoffs differ
from raw edge integrals by a term tending to zero. Then construct or identify their common lateral
limit and use it to prove regularity of the forced residual continuation.

## Exact obstruction

Finite Abel transport proves the difference is exactly

```text
R_N exp(-i h_N (x+i y)),
```

with norm `|R_N| exp(y h_N)`. Ordered-to-natural Wold interpolation now proves unconditionally,

```text
RH iff this difference tends to zero for every x and every 0 < y < 1/2.
```

Therefore the proposed first step is not an easier route to RH. It already contains the full RH
burden.

## Positive survivor

The obstruction exposes an exact architecture constraint: terminal and edge current must remain
coupled during lateral regularization. A viable construction may prove convergence or regularity
of their joint finite current, but cannot independently erase terminal flux throughout the strict
sector before that landing.

Paper proof and Lean formalization are dependency-closed in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldResidualBorelTerminalUnconditionalClassification.lean`.
