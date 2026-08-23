# The Euler logarithm has a canonical prime-power Herglotz carrier with a sharp half-weight wall

- **ID:** `euler-log-prime-power-herglotz-half-weight-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Source:** `PrimeLogHerglotz.lean`, `critical-euler-position-commutator-carrier-law.md`,
  and the Euler product for zeta
- **Statement:** The exact Euler-logarithm coefficients define a canonically renormalized positive
  Herglotz measure on the locally finite prime-power log support. Multiplication by log position
  recovers the von Mangoldt logarithmic derivative. Every positive exponential transport of its
  canonical Cauchy features diverges, so the critical half-weight cannot be crossed by the prime
  carrier alone.

## The carrier

Index the positive prime powers by

```text
I={(p,k):p prime, k>=1}
```

and put

```text
t_(p,k)=k log p,
a_(p,k)=1/(k p^k).
```

The support is positive, locally finite, and injective. Positivity is immediate. If
`t_(p,k)<=R`, then `p^k<=exp R`, so only finitely many pairs occur. If
`p^k=q^l`, unique factorization gives `p=q` and `k=l`.

Define the Herglotz-normalized Cauchy kernel

```text
kappa(t,z)=1/(t-z)-t/(1+t^2)
```

and the Euler-log carrier

```text
H_E(z)=sum_((p,k) in I) a_(p,k) kappa(t_(p,k),z).          (1)
```

The subtraction is real. It changes convergence but not the imaginary part.

## Integrability of the positive measure

The Herglotz measure is

```text
mu_E=sum_((p,k) in I) a_(p,k) delta_(t_(p,k)).             (2)
```

It satisfies

```text
sum_(p,k) a_(p,k)/(1+t_(p,k)^2)<infinity.                  (3)
```

### Exponent one

For `k=1`, group primes by the intervals

```text
exp(m)<=p<exp(m+1),   m>=1.
```

Every summand is at most `exp(-m)/m^2`, while the interval contains fewer than
`exp(m+1)` integers. Its total is therefore at most `e/m^2`. Summing over `m` proves

```text
sum_p 1/(p(1+(log p)^2))<infinity.                         (4)
```

No prime number theorem is used.

### Higher powers

For `k>=2`, discard the Herglotz denominator and use

```text
sum_(k>=2) 1/(k p^k)
 <=sum_(k>=2) p^(-k)
 =1/(p(p-1))
 <=2/p^2.
```

The sum over primes is dominated by the ordinary convergent square series. This proves `(3)`.

## Herglotz theorem

Let `K` be compact and `R=max_(z in K)|z|`. For `t>=2R+1`,

```text
|kappa(t,z)|
 =|1+tz|/(|t-z|(1+t^2))
 <=2(R+1)/(1+t^2).                                        (5)
```

Local finiteness handles the remaining support points. Equations `(3)`--`(5)` give locally
uniform convergence off the pole set and hence holomorphy there.

If `Im z>0`, then

```text
Im kappa(t,z)=Im z/|t-z|^2>0.                              (6)
```

Therefore

```text
Im H_E(z)>0,   Im z>0.                                    (7)
```

Each support point `t_(p,k)` is a simple pole with residue `-a_(p,k)`.

## Exact Euler transform

For `Re s>0`, the Laplace transform of `(2)` is absolutely convergent and equals

```text
L_mu(s)
 =sum_(p,k) a_(p,k) exp(-s t_(p,k))
 =sum_(p,k) 1/(k p^(k(1+s)))
 =log zeta(1+s).                                           (8)
```

Multiplication by log position gives

```text
t_(p,k) a_(p,k)=log p/p^k.                                (9)
```

Consequently

```text
-d/ds L_mu(s)
 =sum_(p,k) log p/p^(k(1+s))
 =-zeta'(1+s)/zeta(1+s).                                  (10)
```

Thus the `X_A,Z_A` position-commutator law is the finite-aperture compression of one canonical
positive prime-power measure. The orbital length is intrinsic; it is not an imposed normalization.

## Sharp positive-weight obstruction

Fix a nonreal Cauchy node `z` and its feature

```text
v_z(t)=1/(t-z).
```

For every `b>0`, positive exponential transport has squared prime contribution

```text
sum_p a_(p,1) exp(2b t_(p,1)) |v_z(t_(p,1))|^2
 =sum_p p^(2b-1)/|log p-z|^2.                              (11)
```

This series diverges. For large primes, `|log p-z|^2<=C_b p^b` by the elementary bound
`log x<=x^(b/2)/(b/2)`. Hence the summand in `(11)` is bounded below by a positive constant times

```text
p^(b-1)=p^(-(1-b)).                                       (12)
```

The prime power series `sum_p p^(-r)` converges exactly for `r>1`; here `r=1-b<1`. Therefore
`(11)` diverges.

In particular, the half-weight `b=1/2` required to move the Euler line `Re(s)>1` to the critical
center is outside the Cauchy-feature domain. No fixed number of extra prime-log powers repairs the
failure: exponential transport dominates every polynomial decay in `log p`.

## Consequence for the countable Gram route

The carrier `(1)` supplies three pieces that the earlier residual Sonin Gram lacked:

1. exact channel resolution at every prime power;
2. positive Herglotz geometry before analytic continuation;
3. intrinsic orbital length through the log-position multiplier.

It does not identify its positive Gram moments with the Xi reciprocal-zero moments. The transform
from `(8)` to the critical completed trace crosses the divergent half-weight wall `(11)`. The
archimedean/Gamma channel and a source-defined covariance or relative trace must perform a genuine
sewing; analytic continuation or source uniqueness alone does not preserve Herglotz positivity.

`facet-sewn-herglotz-stanley-reisner-differential-matroid.md` strengthens this warning. Unpointed
Herglotz/HT relation geometry is universal. The exact residues `(9)`, the functional-equation
polarization, and the Gamma seam must remain marked data; an arbitrary facet sewing has no RH
selection content.

## Scientific classification

The normalized Herglotz representation, Euler logarithm, and prime-series threshold are standard
parent theory. Their assembly gives a useful source normal form but is not new scientific
knowledge. The result is a `[BRIDGE]` that identifies the first canonical positive carrier and its
exact failure boundary.

## Gates

- [x] locally finite injective prime-power log support
- [x] Herglotz integrability of the exact Euler-log weights
- [x] locally uniform normalized Cauchy convergence
- [x] positive imaginary part and exact residues
- [x] Laplace transform identified with `log zeta(1+s)`
- [x] log-position derivative identified with `-zeta'/zeta(1+s)`
- [x] every positive exponential transport of Cauchy features proved divergent, uniformly after
  every finite prime-log cancellation order
- [x] exact positive prime-power atom/time/residue algebra formalized in
      `formal/GaloisForLFunctions/RHTower/EulerLogPrimePowerHerglotz.lean`
- [ ] formalize the full normalized prime-power carrier in Lean; the positive-transport wall is
  formalized at all finite orders as
  `not_summable_primeLogHerglotzTransportMassOrder_of_pos`
- [ ] construct the marked Gamma-sewn covariance/relative trace across the half-weight wall
- [ ] identify the resulting finite-degree Gram blocks with the Xi reciprocal moments
- [ ] RH

## Log

- 2026-07-11 -- extracted from `PrimeLogHerglotz.lean:211` and the existing position-commutator
  pipeline; paper proof completed and the half-weight obstruction isolated.
- 2026-08-23 (Codex) — `EulerLogPrimePowerHerglotz.lean` now proves the exact normalized
  prime-power support time, positive weight, and `t_(p,k)a_(p,k)=log(p)/p^(k+1)` residue
  identity. Targeted source check, module build, and axiom audit pass with only `propext`,
  `Classical.choice`, and `Quot.sound`. The full Herglotz sum and its Laplace transform remain
  unformalized; this card stays at stage 2.
