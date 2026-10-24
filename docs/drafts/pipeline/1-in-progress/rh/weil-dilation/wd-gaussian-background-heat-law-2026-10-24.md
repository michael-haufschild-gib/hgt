# Gaussian-background heat law

- **Stage:** 1-in-progress; complete paper proof below, Lean pending.
- **Source:** WD goal loop, row 377; user request to formalize noteworthy paper proofs.
- **Scope:** exact Gaussian-background model. No transfer to the actual Xi source or RH claim.
- **Leaf planned:** `RHTower/XiSliceHeatGaussianSharpThreshold.lean`.

## Scope and connection task

The user explicitly requested completing this model formalization, then searching
the broader Lean corpus for a connection giving more significant route progress.
Formalization is active again. The model alone does not discharge the global
signed source inequality, a source-to-WD signed trace comparison, or a uniform
zero-block absorption premise. Any connection to a general Xi background must
be proved separately and its missing inputs stated explicitly.

## Exact theorem and paper proof

Let `a>0`, `lambda>0`, and `2*a*lambda<1`. Put
`mu=1-2*a*lambda`, `v=lambda/mu`, `t=a*lambda`, and `X=a*mu*delta^2`.
For the literal variance-`lambda` Gaussian heat average of
`exp(a*x^2)*(delta^2-x^2)^2`, completing the square gives

```
H(x) = mu^(-1/2) exp(a*x^2/mu)
       * [(x/mu)^4 + (6*v-2*delta^2)*(x/mu)^2
          + delta^4-2*delta^2*v+3*v^2].
```

Indeed its integrand has Gaussian center `2*a*lambda*x/mu` and variance
`v`. After translating that center, the polynomial argument is `x/mu+u`.
The already formalized Gaussian quartic moment gives the displayed formula.
It also proves integrability; no formal interchange of a divergent heat series
is used. Expanding the exponential and multiplying by the quadratic in `x^2`
gives an everywhere convergent even power series. Its coefficient `c_k` of
`x^(2*k)` satisfies

```
c_k = mu^(-1/2) * (a/mu)^k / (k! * (a*mu)^2) * Q(t,X,k),
Q(t,X,k) = (X-k-t)^2 + (4*t-1)*k + 2*t^2.
```

The positive prefactor is retained. The identity also holds at `k=0,1`;
it follows by expanding the three convolution terms with falling factorials.

1. If `t>=1/4`, then `Q>=2*t^2>0` for every `delta` and every `k`.
   Thus every even coefficient is strictly positive throughout the convergent
   heat chamber above and at this threshold; odd coefficients vanish.
2. If `0<t<1/4`, choose a natural `k` with
   `(1-4*t)*k>2*t^2` and set `delta=sqrt((k+t)/(a*mu))>0`.
   Then `X=k+t` and `Q=-(1-4*t)*k+2*t^2<0`. Consequently
   all offsets have nonnegative coefficients iff `a*lambda>=1/4`.
3. For any fixed offset with large `X`, let `k=floor(X-t)` (natural floor,
   with `X>=t`). Then `0<=X-t-k<1`, whence
   `Q<1-(1-4*t)*k+2*t^2`. If
   `X-t>1+(1+2*t^2)/(1-4*t)`, this is negative. Hence below threshold
   sufficiently large offsets have a negative coefficient, without the
   paper row's unresolved integer-rounding qualification.

This is stronger and more precise than the heuristic discriminant sentence
in row 377. The Mehler normalization `mu^(-1/2)` was omitted from that row's
displayed coefficient; it does not affect signs but belongs in the exact identity.
The row's transfer from a Gaussian model to a general counting-controlled
background remains unproved and is excluded from this formalization.

### Fixed-offset dense-background consequence

Fix `delta>0` and `0<kappa<1/4`, and set `lambda=kappa/a`.
Write `m=1-2*kappa`, `d=1-4*kappa`, and
`C=kappa+1+(1+2*kappa^2)/d`. Both `m` and `d` are positive.
For `a >= A=(C+1)/(m*delta^2)>0`, the normalized offset is
`X=a*m*delta^2 >= C+1`, so the fixed-offset floor bound applies.
Consequently every sufficiently dense Gaussian background has a negative
coefficient at heat `kappa/a` whenever `kappa<1/4`. Conversely, if
`1/4<=kappa<1/2`, all coefficients are nonnegative for every `a>0`.
This proves the sharp limiting heat constant for each fixed positive offset,
as well as the universal-offset statement.

## Implementation obligations

- Reuse `integrable_and_integral_gaussDensity_quartic` and the existing Gaussian density.
- Prove the completed-square kernel identity, integral, and actual convergent series.
- Prove the coefficient square decomposition and exact universal threshold.
- Prove the fixed-offset integer-rounding bound if its stated strict inequalities survive Lean.
- Direct named-module check, transitive axiom audit, umbrella import, scratch cleanup.
- No numerical experiments, web search, novelty claims, placeholders, or limit increases.
