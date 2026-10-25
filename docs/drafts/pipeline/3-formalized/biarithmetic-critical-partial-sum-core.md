# Exact finite core of the critical partial-sum domain

- **ID:** biarithmetic-critical-partial-sum-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Payment graph norm](../1-in-progress/biarithmetic-payment-graph-norm.md)
- **Statement:** Corrected finite complex sequences have exact coefficient and partial-sum errors. They converge in both components of the critical graph norm, and their coefficient distance for an arbitrary absolutely summable sequence tends to the norm of its total evaluation.

For `S_M=sum_(r<=M)g_r`, set
`g^[N]_r=1_(r<=N)g_r-1_(r=N)S_N`.
Its partial sums equal `S_M` below `N` and vanish from `N` onward.
Consequently every correction has square-summable partial sums, and

`sum_r |g^[N]_r-g_r|=|S_N|+sum_(r>N)|g_r|`.

For `g` in `ell1`, this tends to `|sum_r g_r|`. If the original partial
sums also belong to `ell2`, their limit is zero, forcing `sum_r g_r=0`.
The squared partial-sum error is exactly `sum_(M>=N)|S_M|^2`, which tends
to zero. Both graph errors therefore tend to zero for every member of
the critical partial-sum domain.

Lean: `BiarithmeticGeometry/CriticalPartialSumCore.lean`.
Seven main declarations were audited: the partial-sum identity, corrected
square summability, zero total evaluation, exact coefficient error, its
limit, exact square error, and convergence of both graph errors.

- [x] Direct repository check with `lake --old env lean`.
- [x] Umbrella import wired; umbrella not compiled.
- [x] All seven transitive audits contain only `propext`, `Classical.choice`, `Quot.sound`.

Actual Wiener closure transfer and the continuum quotient theorem remain
separate obligations on the parent cards.
