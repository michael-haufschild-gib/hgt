# Gamma damping crosses the prime-log half-weight only through nonadditive covariance

- **ID:** `gamma-damped-stationary-prime-log-covariance-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the archimedean Gamma characteristic, the Euler-log prime-power Herglotz carrier,
  and positive-definite kernel theory
- **Statement:** A canonical diagonally damped Gamma covariance is positive and has exactly enough
  exponential diagonal decay to cross the prime-log half-weight.  Its distinct prime-power
  channels have strictly positive cross terms, however, so its Gram energy cannot equal the
  additive Euler logarithmic derivative.  A successful construction must retain and renormalize
  this covariance rather than identify it with the source trace directly.

## Setup

Let

```text
phi(t)=(cosh t)^(-1/2)
```

be the characteristic function of the normalized archimedean cyclic Gamma measure `mu_infinity`.
For `t>=0`, put

```text
d(t)=sqrt(phi(2t)),
K_Gamma(t,u)=d(t)d(u)phi(t-u).                            (1)
```

## Positive Gamma-sewn covariance

For every finite family `t_1,...,t_n` and complex coefficients `c_1,...,c_n`,

```text
sum_(i,j) conjugate(c_i)c_j K_Gamma(t_i,t_j)
 =int |sum_i c_i d(t_i) exp(i t_i s)|^2 dmu_infinity(s)
 >=0.                                                     (2)
```

Thus `K_Gamma` is positive semidefinite.  This is diagonal congruence of the stationary positive
kernel `phi(t-u)`; it is not the indefinite sum-frequency kernel `phi(t+u)`.

Its diagonal is

```text
K_Gamma(t,t)=phi(2t).                                     (3)
```

For `t>=0`,

```text
exp(-t)<=phi(2t)<=sqrt(2)exp(-t),                         (4)
```

because

```text
exp(2t)/2<=cosh(2t)<=exp(2t).
```

Hence the diagonal supplies exactly one full exponential power.

## Crossing the Cauchy-feature half-weight

At an exponent-one prime-log atom `t=log p`, the Cauchy-feature energy after transport by the
critical half-weight `b=1/2` is proportional to

```text
1/(1+(log p)^2).
```

The prime carrier alone therefore diverges.  Multiplication by the Gamma diagonal gives

```text
phi(2 log p)/(1+(log p)^2)
 <=sqrt(2)/(p(1+(log p)^2)).                              (5)
```

The series on the right converges.  Grouping primes with `exp(m)<=p<exp(m+1)` bounds the `m`-th
block by a constant times `1/m^2`.  Higher prime powers are even smaller.  Therefore the sewn
positive covariance has a well-defined critical-half-weight Cauchy feature even though the prime
facet alone does not.

This proves that the half-weight wall is not an impossibility theorem for every positive sewing;
it is specifically a wall for uncoupled positive prime transport.

## Exact additivity obstruction

For all real `t,u`, every factor in `(1)` is strictly positive.  In particular,

```text
K_Gamma(t,u)>0.                                           (6)
```

For two distinct prime-power atoms with positive amplitudes `a,b`,

```text
||a g_t+b g_u||^2
 =a^2 K_Gamma(t,t)+b^2 K_Gamma(u,u)
   +2ab K_Gamma(t,u),                                    (7)
```

and the last term is strictly positive.

The Euler logarithm and its log-position derivative are additive over prime powers:

```text
log zeta(1+s)=sum_(p,k) exp(-s k log p)/(k p^k),
-zeta'(1+s)/zeta(1+s)=sum_(p,k) log p exp(-s k log p)/p^k. (8)
```

There are no pairwise prime-power terms in `(8)`.  Consequently the coherent Gram energy `(7)`
cannot be identified with the additive source trace.  Orthogonal direct-sum channels restore
additivity but discard the Gamma covariance; the existing point-source Hankel no-go results then
apply.  The only surviving architecture keeps the cross covariance and supplies an exact
relative-trace/covariance subtraction before the final positive square.

## Consequence for the countable Gram route

The canonical kernel `(1)` is the first positive source object found in this route that genuinely
crosses the prime-log half-weight.  It does not prove the finite-degree Xi Gram identity.  Instead
it fixes the shape of the missing operation:

```text
Gamma-damped stationary prime covariance
  + source-defined cancellation of its off-diagonal prime-power energy
  + log-position derivative
  -> completed principal-relative Gram.                  (9)
```

The cancellation cannot be a scalar normalization, because every cross entry in `(6)` is nonzero.
It must be operator-valued or relative, matching the principal-shell/Sonin and Gauss-paired
quantized-differential carriers already present in the pipeline.

## Scientific classification

Characteristic-function positivity, diagonal kernel congruence, and the elementary exponential
bounds are standard.  The result is a route bridge, not new scientific knowledge.

## Gates

- [x] canonical positive Gamma-sewn covariance constructed
- [x] exact exponential diagonal decay proved
- [x] critical half-weight Cauchy summability proved
- [x] strict nonadditive cross terms isolated
- [ ] construct the source-defined operator covariance subtraction
- [ ] identify the completed finite-degree Gram with the Xi Hankel block
- [ ] RH

## Source-selection caveat

The formula `d(t)=sqrt(phi(2t))` is canonical once one asks to use the diagonal of the Gamma
sum-frequency kernel, but the current Hardy--Titchmarsh square does not select this diagonal
congruence.  It selects multiplication by the exact local symbol and its Euler Gram.  Therefore
`K_Gamma` is a legitimate source-built candidate kernel, not yet the proved compression of the
semilocal trace operator.  A promotion theorem must derive `(1)` from the Gauss-paired local ratios,
Sonin projection, or conductor graph; merely observing that `(1)` uses only `phi` and prime-log
coordinates would not satisfy the source-selection gate.
