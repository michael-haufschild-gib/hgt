# Critical clock primitive cancellation [BRIDGE]

Owner: critical-clock product task. Status: paper argument; Lean checking pending.
Frozen primary target: paid exhaustive continuation, then bounded critical action, then RH.

## Source fact and conjecture

The literal prime insertion identity is
`H_(P+p)(x) = H_P(x) - sqrt(p) H_P(x/p)`.
The corpus proves `H_P(n)/sqrt(n) -> 0` for every fixed nonempty prime core.
Square-root interpolation should extend this to the real ray. In logarithmic
clock time, set `f_P(t) = H_P(exp t)/sqrt(exp t)`. Then insertion is exactly
`f_(P+p)(t) = f_P(t) - f_P(t-log p)`, and the source vanishes for `t <= 0`.
Consequently, for `T >= log p`,

`integral_0^T f_(P+p) = integral_(T-log p)^T f_P`.

The last integral tends to zero when P is nonempty. This proves physical
critical signed primitive cancellation after two distinct primes without
assuming absolute integrability on the critical Mellin line. Its finite
boundary is part of the statement, rather than being discarded.

## Whole-route meaning and failure test

This addresses the proposed logarithmically weighted helper mean. It does
not yet bound its whole-child norm, its prime discretization, the copied
squares, or cutoff growth. A zero scalar primitive alone is not payment.
The candidate fails if real interpolation does not preserve the normalized
limit, or if the time shift has an unaccounted boundary term. Both are
checked against the literal source. No critical absolute convergence or
uniformity in the growing core is assumed.

## Dependency-closed paper argument

On each unit interval, `U(x)-c sqrt(x)` is affine in `sqrt(x)`. Its two
endpoint bounds therefore give the same normalized error bound throughout
the interval. The proved integer limit of the unit source extends to real
x. Finite Moebius dilation then gives a real normalized limit for every
fixed core. Restriction to integer x and uniqueness of the limit identify
that limit as zero for every nonempty prime core.

Divide the literal insertion identity by `sqrt(exp(t))`. Since
`exp(t-log(p)) = exp(t)/p`, the copied square-root coefficient cancels
exactly. Integrating the resulting finite difference leaves a terminal
strip and an initial strip. The latter vanishes because the actual source
is zero at nonpositive times. The terminal strip has fixed length `log(p)`;
its supremum tends to zero by the normalized real-ray limit. Substitution
`x=exp(t)` identifies the clock integral with
`integral_1^(exp T) H_P(x)/(x sqrt(x)) dx`.

All cores and inserted primes in this argument are fixed before the limit.
No estimate uniform in core size, inserted prime, or child depth is claimed.
