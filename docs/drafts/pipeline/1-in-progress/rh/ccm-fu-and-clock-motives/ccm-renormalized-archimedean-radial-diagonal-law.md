# The scalar-renormalized CCM archimedean radial diagonal has an explicit limit

- **ID:** `ccm-renormalized-archimedean-radial-diagonal-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, `[OPEN SECOND-ORDER ASYMPTOTIC]`
- **Scientific status:** `[CONJECTURE] [NOT AN RH PROOF]`
- **Parent theories:** Suzuki's archimedean Fourier multiplier, Dunster's radial phase, and the
  constrained-prolate radial leakage measure
- **Statement:** `[CONJECTURE]` After subtracting the universal scalar term
  `log(c)*||H_(lambda,k)||^2`, the sum
  of the diagonal archimedean radial energies has an explicit finite `d_1(lambda)`-scale limit.

## Setup

Let

```text
H_(lambda,k)(s)
 =sqrt(lambda*e^s)q_lambda(k*lambda*e^s),
c=2*pi*lambda^2,
d_1(lambda)=1-chi_4(lambda)^2.                                  (1)
```

Write Suzuki's archimedean form as the Fourier multiplier

```text
A_arch(u)
 =1/(2*pi) integral_R m(xi)|hat u(xi)|^2dxi,
m(xi)=Re psi(1/4+i*xi/2)-log pi.                                (2)
```

Define its scalar-renormalized diagonal value

```text
B_(lambda,k)
 =A_arch(H_(lambda,k))-log(c)*||H_(lambda,k)||_2^2.              (3)
```

## Local Mellin symbol

For `y=k*e^s`, Dunster's degree-four phase is `c*xi_s(y)`, where

```text
xi_s'(y)=sqrt((y^2-sigma_4(c)^2)/(y^2-1)).                      (4)
```

Its local Mellin frequency is therefore

```text
omega_c(y)
 =c*y*xi_s'(y)
 =c*y*sqrt((y^2-sigma_4(c)^2)/(y^2-1)).                         (5)
```

Since `sigma_4(c)^2=9/c+O(c^(-2))` and

```text
m(xi)=log|xi|-log(2*pi)+O(|xi|^(-2)),                            (6)
```

the renormalized symbol converges locally uniformly on `1<y<infinity` to

```text
L(y)=log(y^2/(2*pi*sqrt(y^2-1))).                               (7)
```

The two oscillatory Bessel branches have opposite frequencies and the same even multiplier
value. The already proved logarithmic-chirp lemma certifies the leading `log(c)` term, but not the
order-one symbol `(7)`. Promoting the next formulas requires a second-order localization theorem
uniform at the Bessel endpoint.

## Fixed diagonal limit

The proved constrained radial leakage law is

```text
lambda*|q_lambda(lambda*y)|^2/d_1(lambda)dy
 =>8/(11*pi)*dy/[y*sqrt(y^2-1)].                                (8)
```

`[CONJECTURE]` After `y=k*x`, equations `(5)`--`(8)` should give, for every fixed `k>=1`,

```text
B_(lambda,k)/d_1(lambda)
 ->8/(11*pi*k) integral_k^infinity
     log(y^2/(2*pi*sqrt(y^2-1)))
       dy/[y*sqrt(y^2-1)].                                     (9)
```

The proposed limiting density passes the first integrability checks: the logarithmic singularity
at `y=1` is integrable. At infinity the integrand in `(9)` is
`O(log(y)/y^2)`. Dunster's uniform radial envelope supplies the corresponding uniform-integrability
majorant, including the Bessel endpoint.

## Summed diagonal law

The required uniform second-order envelope is

```text
|B_(lambda,k)|/d_1(lambda)<=C*(1+log k)/k^2.                    (10)
```

Once `(10)` is proved, dominated convergence yields

```text
sum_(k>=1) B_(lambda,k)/d_1(lambda) ->D_arch^ren,                (11)

D_arch^ren
 =8/(11*pi) sum_(k>=1)1/k integral_k^infinity
    log(y^2/(2*pi*sqrt(y^2-1)))
      dy/[y*sqrt(y^2-1)].                                      (12)
```

Set `y=sec(theta)` and then `u=pi/2-theta`. Since

```text
dy/[y*sqrt(y^2-1)]=dtheta,
y^2/(2*pi*sqrt(y^2-1))=1/(pi*sin(2*u)),                         (13)
```

the constant has the explicit arcsine-log form

```text
D_arch^ren
 =8/(11*pi) sum_(k>=1)1/k integral_0^arcsin(1/k)
    log(1/(pi*sin(2*u)))du.                                    (14)
```

The series is absolutely convergent: its `k`-th term is
`O((1+log k)/k^2)`.

## Route consequence

The previously found positive `d_1*log(c)` exterior energy is exactly

```text
log(c)*sum_(k>=1)||H_(lambda,k)||^2
```

on the diagonal. It is a universal scalar identity contribution and disappears from the
Rayleigh-excess-to-gap ratio. Equation `(14)` is the first order-`d_1` archimedean datum relevant
to ground-vector selection.

This theorem does not yet identify the renormalized energy of the full radial sum: one must prove
that the scalar-renormalized archimedean off-diagonal terms are summable at the `d_1` scale.

## References

- M. Suzuki, *Weil's quadratic form via the screw function*, archimedean multiplier formula.
- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*.

## Gates

- [x] universal scalar `log(c)` term removed
- [x] local Mellin-frequency symbol derived
- [ ] prove second-order logarithmic-chirp localization at the Bessel endpoint
- [ ] prove the fixed radial diagonal limit
- [ ] prove the uniform diagonal majorant
- [ ] sum the full diagonal constant
- [ ] scalar-renormalized off-diagonal archimedean bound
- [ ] combine with the prime incidence constant and true even gap
