# CCM-FU: signed ceiling for complete smooth square blocks

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], source inequality under formalization
- **Parent:** [bounded quotient profiles](ccm-fu-bounded-quotient-profiles.md).
- **Goal:** Complete signed Abel bound and RH remain open.

## Arithmetic target

Write R(n) for the exact smooth divisor-hyperbola remainder and
`a=log(2*pi)/2-gamma-1/6`. Prove, for every s>=1,

`sum_(n=s^2..(s+1)^2-1) R(n) <= (2s+1)*a`.

The existing theorem gives only an absolute error of15 per complete
block. The proposed signed comparison would remove that positive loss.
It is a derived source theorem, not a replacement RH conjecture.

## Dependency-closed paper mechanism

Put c=s(s+1). Strengthen geometric harmonic centering to
`H_s-gamma-log(c)/2 >= 1/(6c)-1/(30c^2)`.
The difference of the correction between successive integers is compared
with `atanh(t)-t`, for t=1/(s+1). The derivative of
`atanh(t)-t-t^3/(3(1-t^2))+2t^5/(15(1-t^2)^2)` is
`8t^6/(15(1-t^2)^3)>=0`. The correction tends to zero, so telescoping
gives the stated harmonic inequality.

Pair terms at c-j and c+j. Exact Stirling upper bounds and

`(1+t)log(1+t)+(1-t)log(1-t) <= t^2+t^4/(6(1-t^2))`,
`log(1-t^2)<=-t^2`

give the paired quadratic term plus an explicit quartic remainder.
Use `j^4<=s^2*j^2`, `j<=s`, and the exact sum of j^2. Summing the
pairs and central term bounds the block excess above `(2s+1)*a` by

`(2s+1)*[-1/(4c)+(2c+1)/(30c^2)+1/(12s^2)+1/(36s(s+2))]`.

The bracket is nonpositive for s>=2 by a rational polynomial inequality.
The first block reduces exactly to `log(12)-9+12*gamma`; existing
analytic logarithm, pi and Euler-constant bounds give its ceiling.
No numerical experiment or computed source value is needed.

## Remaining obligations

The complete-block sign alone does not bound a terminal partial block
or its varying square-root weights. Those must be retained in any
global unit-channel comparison. The target `K_p(N)<=2K_1(N)`, arbitrary
mixed-state successor selection, complete extension and RH remain open.
Do not promote an unweighted block sign into an Abel or RH bound.
