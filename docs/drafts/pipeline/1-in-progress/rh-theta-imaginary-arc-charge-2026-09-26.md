# Exact imaginary-axis charge of the theta source — root research

- **Stage:** 1-in-progress
- **Type:** [BRIDGE], new analytic derivation; Lean transfer pending
- **Owner:** root
- **Goal:** settle the concrete source-zero stop test in the boundary renewal proposal without numerical premises, and retain the exact signed law it exposes.
- **Prior evidence:** `docs/reports/xi.md` §2.25 lists an interior imaginary source zero only as a computation. `ThetaCuspComplexStrip` proves strip holomorphy and reflection. `ThetaCuspReflection` proves the real Ward equation. `JacobiThetaBoundaryLimits` proves the odd-cusp exponential bound. None of these alone states the arc charge below.

## Frozen attack

For the literal completed theta source `k`, set `L=pi/4`. Test the exact identities

`integral_0^L cos(t/2) k(i*t) dt = 0`,

`integral_0^L sin(t/2) k(i*t) dt = -theta(1)/4`.

These are derived candidates, not the primary RH conjecture. They predict a negative source value and hence a zero strictly inside the strip. They do not predict a zero of Xi.

## Dependency-closed paper derivation

Write `theta(y)=sum_{n in Z} exp(-pi*n^2*y)` for `Re y>0`, and

`P(z)=exp(z/2) theta(exp(2z))`.

The theta transformation gives `P(-z)=P(z)` on `|Im z|<L`; real coefficients give `P(conj z)=conj P(z)`. Consequently `p(t)=P(i*t)` is real for real `|t|<L`, `p(0)=theta(1)>0`, and `p'(0)=0`.

Termwise differentiation of the locally normally convergent theta series, or analytic continuation of the existing real Ward identity, gives

`k(z)=(P''(z)-P(z)/4)/2`, hence `k(i*t)=-(p''(t)+p(t)/4)/2`.

### Flat endpoint with derivative control

Put `delta=L-t`, `a=pi/8`, and `q=exp(-pi*cot(delta))`. The shifted Gaussian Poisson identity at the odd cusp gives the exact formula, for sufficiently small positive `delta`,

`p(L-delta)=sqrt(2) (sin delta)^(-1/2) exp(-a*cot delta) R(q)`,

`R(q)=sum_{m>=0} (-1)^(m*(m+1)/2) q^(m*(m+1)/2)`.

Indeed `w=exp(2i*t)-i=2 sin(delta) exp(-i*delta)` and `1/w=(cot(delta)+i)/2`. In the shifted Poisson series `sum_{m in Z} exp(-pi*(m+1/2)^2/w)`, the phase of the square-root prefactor cancels the common `exp(-i*pi/8)` phase. Pairing `m` with `-m-1` gives the formula. This uses the same shifted Poisson transformation as the already paper-proved theta rational-cusp boundary law.

For `|q|<1`, `R` is an absolutely convergent power series, with `R(0)=1`. Its first two derivatives are bounded on any disk of radius less than 1: after differentiation, the terms are bounded by a polynomial in `m` times `r^(m*(m+1)/2-2)`, a summable sequence. Thus `R(q)=1+O(q)` with the corresponding differentiated bounds.

Let `f(delta)=(sin delta)^(-1/2) exp(-a*cot delta)`. Then

`(log f)'=-cot(delta)/2+a*csc(delta)^2`,

`(log f)''=csc(delta)^2/2-2a*csc(delta)^2*cot(delta)`.

Also `q'=pi*csc(delta)^2*q` and `q''=pi*q*(pi*csc(delta)^4-2*csc(delta)^2*cot(delta))`. Since `delta*cot(delta)->1` and `sin(delta)/delta->1`, all derivatives through order two of `p(L-delta)` tend to zero faster than any fixed power of `delta`. This proves endpoint flatness and integrability of `k(i*t)` up to `L` without differentiating an unproved asymptotic.

More precisely,

`delta^4 p''(L-delta)/p(L-delta) -> a^2`,

so `k(i*(L-delta))<0` for every sufficiently small positive `delta`.

### Exact charges

Integration by parts twice is now justified on `[0,L]`, with `p(L)=p'(L)=0`. For `v(t)=cos(t/2)` or `sin(t/2)`, `v''=-v/4`, so

`integral_0^L v(t) k(i*t) dt = -[v(t)p'(t)-v'(t)p(t)]_0^L/2`.

The cosine charge is zero. The sine charge is `-theta(1)/4`. Positivity `k(0)>0` follows directly from its theta series: every summand has factor `2*pi*n^2-3>0`. Continuity and eventual strict negativity therefore force some `t in (0,L)` with `k(i*t)=0`.

## Whole-route consequence

The literal source admits no holomorphic logarithm on its whole strip. A continuation proof using the linear source remains viable. Its imaginary-axis source is signed, with a zero cosine charge and a strictly negative sine charge; positivity cannot be transported from the real source axis. This does not establish any off-axis Xi zero, determine the renewal winding, or prove RH.

## Formal obligations

1. Complex Ward identity for the literal `thetaCuspStripSource`, not a newly defined substitute.
2. Differentiated odd-cusp flatness, including integrability at the endpoint.
3. Both exact arc charges and the unconditional interior source-zero theorem.

All three remain Lean-open. The no-log obstruction is not marked formally closed until these exact positive survivors are checked. No numerical experiment; no global novelty claim.
