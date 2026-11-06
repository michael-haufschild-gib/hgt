# Convex cancellation of multiplicative-chain phases

- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper; Lean formalization in progress)
- **Wall:** Σ6

For `|z|=1`, set `U_n=Σ_(j=0)^n z^j conjugate(z)^(n−j)` and
`C_n=Σ_(k=0)^n Σ_(j=0)^k Re U_j`. Then `C_n≥0` for every `n`.
For a real sequence `f` with `f_N=f_(N+1)=0`,

`Σ_(k=0)^N f_k Re U_k = Σ_(k=0)^(N−1) C_k(f_k−2f_(k+1)+f_(k+2))`.

Consequently every nonnegative second difference gives a nonnegative
weighted phase sum. If `N>0` and the initial second difference is strictly
positive, the sum is strictly positive at every phase.

## Proof

Write `c=Re z`. The geometric sums satisfy
`U_0=1`, `U_1=2c`, and `U_(n+2)=2c U_(n+1)−U_n`.
Each summand has modulus one, so `Re U_n≤n+1`.
Twice summing the recurrence gives the exact identity

`2(1−c) C_n = n+2−Re U_(n+1)`.

If `c<1`, both the right-hand side and the divisor are nonnegative,
with positive divisor. If `c=1`, the recurrence gives `U_n=n+1`,
so all summands defining `C_n` are positive. These exhaust `|z|=1`.

Two finite summations by parts give the displayed weighted identity;
the endpoint terms vanish by `f_N=f_(N+1)=0`.
Every summand is then nonnegative. Strictness follows from `C_0=1`
and the strictly positive initial second difference. [PROVED HERE]

The corpus anchors are `HTGeometry.fejerKernel_eq_double_sum` and
`thetaPairApertureSpectrum_eq_shifted`. This theorem controls a complete
geometric phase chain. Distinct-prime interaction and the full-source
signed inequality are not conclusions of this theorem.
