# CCM-FU: weighted smooth block ceiling

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], actual source comparison
- **Parent:** [signed smooth blocks](../3-formalized/ccm-fu-signed-smooth-block-ceiling.md).
- **Goal:** Uniform signed Abel bound and RH remain open.

## Target and role

Let `R(n)` be the literal smooth divisor-hyperbola remainder,
`a=log(2*pi)/2-gamma-1/6`, and `w(n)=sqrt(n+1)-sqrt(n)`.
The target is `sum_(n=s^2..(s+1)^2-1) R(n)w(n)<=a` for every s>=1.
Its unweighted counterpart is already closed. The weighted statement is
not assumed and is not a conjectural premise for a receiver.

Together with nonnegativity of R and control of the initial blocks, this
would imply `SmoothAbel(M)<=a*sqrt(M)` at every cutoff: bound a partial
last block by its full block, retain the initial missing square-root unit,
and use `s<=sqrt(M)`. Any initial nonnegativity exceptions must be handled
explicitly. A smooth ceiling alone still does not prove the uniform signed
Möbius bound, the all-state successor comparison, or RH.

## Paper mechanism under audit

Write c=s(s+1). First prove the source orientation
`R(c-j)<=R(c+j)` for `0<=j<=s`. Its exact difference is the logarithm of
the product of `(c-i+1)(c+i)=c^2+c-i(i-1)`, minus `4j(H_s-gamma)`.
Use the existing upper geometric harmonic correction and the analytic
bound `log(1+x)>=x-x^2/2`. This keeps the paired source direction.

The orientation lets each source pair be replaced by its average before
multiplying the symmetric average of the two Abel weights. The remaining
source majorant is the explicit quadratic from the signed block proof.
The unresolved clock estimate is

`sum_(n=s^2..(s+1)^2-1) (n-c)^2*w(n) <= c/3+1/18` for s>=2.

A possible proof bounds the derivative of the even clock as a function
of j^2 by `1/(4*c^(5/2))`, then applies the exact finite covariance
identity and the uniform second/fourth moments. The continuous reciprocal
root comparison needed for that derivative must itself be proved.

The old rational block correction plus one thirty-sixth of its quadratic
coefficient is negative for s>=2; check the exact factorization in Lean.
The first weighted block needs its own analytic logarithm and root bounds.
No numerical experiment is planned: the proposed estimates have analytic
mechanisms whose inequalities must be settled directly.

## Current boundary

Orientation, clock covariance bound, complete weighted ceiling, and the
terminal-block transfer are under proof development. No new weighted or
global unit-channel theorem is currently claimed.
