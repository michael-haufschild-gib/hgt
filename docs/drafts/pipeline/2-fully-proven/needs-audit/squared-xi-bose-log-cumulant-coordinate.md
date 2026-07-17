# Squared-Xi completion is a Bose-log cumulant difference

- **ID:** squared-xi-bose-log-cumulant-coordinate
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / cancellation-preserving source coordinate
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [NOT FORMALIZED]`
- **Parents:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`; the classical Mellin integral for `Gamma(s) zeta(s)`
- **Statement:** On the live absolute-Euler ray, every completed Xi jet is an exact difference between cumulants of a strictly log-concave Bose-log distribution and half-Gamma polygamma cumulants, with the polar term already absorbed.

## Mellin probability coordinate

Let `a>0`, `s=1+a`, and define

```text
M(a) = integral_0^infinity t^a/(exp(t)-1) dt
     = Gamma(a+1) zeta(a+1).                             (1)
```

The probability measure

```text
d mu_a(t) = [t^a/((exp(t)-1) M(a))] dt                  (2)
```

has all logarithmic moments.  Write `kappa_r(a)` for the order-`r`
cumulant of `log t` under `mu_a`.  Exponential-family differentiation gives

```text
kappa_r(a) = d^r/da^r log M(a),    r>=1.                (3)
```

## Exact completed-Xi theorem `[PROVED HERE]`

The duplication formula for Gamma and `(1)` give

```text
xi(1+a)
  = (1+a) 2^(-a) pi^(-a/2) M(a)/Gamma(a/2).             (4)
```

Therefore, with `L=xi'/xi`,

```text
L(1+a)
  = 1/(1+a) - log(2 sqrt(pi))
    - (1/2) digamma(a/2) + kappa_1(a),                  (5)
```

and, for every `j>=1`,

```text
L^(j)(1+a)
  = (-1)^j j!/(1+a)^(j+1)
    - 2^(-(j+1)) polygamma_j(a/2)
    + kappa_(j+1)(a).                                   (6)
```

Equations `(5)`--`(6)` retain the zeta pole inside the Mellin normalization.
Indeed,

```text
(s-1) zeta(s) = M(a)/Gamma(a),                          (7)
```

so this is the probability form of the already formalized pole-filled zeta
coordinate, not a termwise separation of `1/(s-1)` from `zeta'/zeta`.

## Strict log-concavity `[PROVED HERE]`

For `X=log t`, the density induced by `(2)` is proportional to

```text
exp((a+1)X)/(exp(exp X)-1).                              (8)
```

Its log-density has second derivative

```text
-t * d/dt [t/(1-exp(-t))],    t=exp X.                  (9)
```

The derivative in `(9)` is positive because

```text
1-(1+t)exp(-t) > 0
```

for `t>0`, equivalently `exp(t)>1+t`.  Thus the Bose-log law is strictly
log-concave for every `a>0`.

## Independent-factor interpretation `[PROVED HERE]`

Let `G` have the Gamma distribution of shape `a+1`, and independently let

```text
P(N=m) = m^(-(a+1))/zeta(a+1),    m>=1.                 (10)
```

Then `T=G/N` has law `(2)`.  Hence

```text
kappa_r(log T)
  = polygamma_(r-1)(a+1) + (-1)^r kappa_r(log N),       (11)
```

where the Euler product gives the positive compound-Poisson cumulants

```text
kappa_r(log N)
  = sum_(m>=2) Lambda(m) (log m)^(r-1) m^(-(a+1)) > 0.  (12)
```

Thus the all-order prime sign alignment is also a probability law: it is the
positive cumulant sequence of the zeta-distributed integer.

## Order-fourteen source target

Put `w=a+1/2` and substitute `(5)`--`(6)` into

```text
Q_14(w)=sum_(j=0)^14 (-1)^j b_(14,j) w^j L^(j)(1+a).
```

The live RH-disproof certificate is still `Q_14(w)<0` for some
`0<a<sqrt(8)-1/2`, but it is now a finite inequality between explicit
half-Gamma polygamma terms and cumulants of one strictly log-concave
one-dimensional probability law.  No pole subtraction, zero location, or
numerical evaluation is present.

`[CONJECTURE]` A sharp one-dimensional transport or dispersive-order bound
between the Bose-log law `(8)` and the half-Gamma log law controls this
reverse-Bessel cumulant functional strictly.  The sign must be established,
not inferred from log-concavity alone; ordinary log-concavity has no fixed
sign for cumulants of order three and above.

## Gates

- [x] exact Mellin probability representation
- [x] pole-filled Xi factorization
- [x] all completed jets expressed as cumulant differences
- [x] strict log-concavity and independent Gamma/Zipf factorization
- [ ] find a transport order strong enough for the order-fourteen functional
- [ ] prove the resulting strict sign, whichever direction it has
- [ ] formalize only the source-bearing inequality and its Xi endpoint

