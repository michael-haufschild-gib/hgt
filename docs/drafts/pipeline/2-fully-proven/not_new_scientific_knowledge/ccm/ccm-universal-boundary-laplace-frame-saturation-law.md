# Every fixed boundary profile asymptotically saturates the CCM polar--Euler frame level

- **ID:** `ccm-universal-boundary-laplace-frame-saturation-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / COFINAL BOUNDARY-CARRIER LAW / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the prime number theorem, translation autocorrelations, and
  `ccm-polar-euler-frame-minus-level-law.md`
- **Statement:** Every fixed smooth boundary profile produces an even two-edge aperture family for
  which the positive frame energy is asymptotic to the exact scalar level. The leading prime
  cross-boundary term and the positive polar moment cancel identically in the limit. Therefore a
  CCM lower-frame proof must control the subleading critical Mellin defect on an infinite-dimensional
  boundary-profile space; leading prime mass, the polar channel, or finitely many prolate vectors
  cannot supply the sign.

## 1. Two-edge boundary family

Fix `L>0` and a nonzero function

```text
f in C_c^infinity(0,L).                                      (1)
```

For `a>L`, define the even aperture vector

```text
v_a(x)=f(a-|x|),       |x|<a,                                (2)
```

and extend it by zero. Then `v_a in C_c^infinity(-a,a)` and

```text
||v_a||_2^2=2||f||_2^2.                                      (3)
```

Put

```text
F_-=integral_0^L exp(-s/2)f(s)ds,
F_+=integral_0^L exp(s/2)f(s)ds.                              (4)
```

## 2. Exact polar asymptotic

The even polar feature is

```text
sqrt(2)inner(cosh(. /2),v_a).
```

Directly changing variables from `x` to `s=a-x` on the positive half interval gives

```text
2|inner(cosh(. /2),v_a)|^2
 =2|exp(a/2)F_-+exp(-a/2)F_+|^2
 =2exp(a)|F_-|^2+O_f(1).                                     (5)
```

## 3. Prime cross-boundary asymptotic

For `h>=0`, let

```text
C_a(h)=integral_R v_a(x+h)conjugate(v_a(x))dx.                 (6)
```

The two boundary layers are separated by a gap. Apart from the fixed same-edge range `0<=h<=L`,
the only nonzero correlations occur for `h=2a-r` with `0<=r<=2L`, where

```text
C_a(2a-r)
 =c_f(r):=integral_R f(r-s)conjugate(f(s))ds.                  (7)
```

The prime number theorem implies weak convergence on every fixed compact `r`-interval:

```text
exp(-a) sum_(n<=exp(2a))Lambda(n)n^(-1/2)
  delta_(2a-log n)(dr)
 ->exp(-r/2)dr.                                                (8)
```

To prove `(8)`, write the sum as a Stieltjes integral against
`Psi(x)=sum_(n<=x)Lambda(n)`, use `Psi(x)=x+o(x)`, and integrate by parts after the change
`x=exp(2a-r)`. The error is uniform against every fixed compactly supported `C^1` test function.

Applying `(8)` to `c_f` and using `(7)` yields

```text
sum_(n<=exp(2a))Lambda(n)n^(-1/2)C_a(log n)
 =exp(a)integral_0^(2L)exp(-r/2)c_f(r)dr+o_f(exp(a))
 =exp(a)|F_-|^2+o_f(exp(a)).                                  (9)
```

The last equality is Fubini applied to the convolution `(7)`. The fixed same-edge prime range
contributes only `O_f(1)` and is absorbed by the error.

The prime term in the restricted Weil form is minus twice the real part of `(9)`. Therefore

```text
Q_(prime,a)(v_a,v_a)=-2exp(a)|F_-|^2+o_f(exp(a)).             (10)
```

Equations `(5)` and `(10)` prove the universal leading cancellation

```text
Q_(polar-prime,a)(v_a,v_a)=o_f(exp(a)).                       (11)
```

## 4. Gamma term and frame saturation

The two translates in `(2)` have a fixed smooth profile. The digamma multiplier has logarithmic
growth, so each diagonal Gamma energy is independent of `a`, while the cross term tends to zero by
the Riemann--Lebesgue lemma with its integrable smooth Fourier weight. Hence

```text
Q_(Gamma,a)(v_a,v_a)=O_f(1).                                 (12)
```

Combining `(11)`--`(12)` gives

```text
QW_a(v_a,v_a)=o_f(exp(a)).                                   (13)
```

For the exact even analysis map `B_a` and scalar level `mu_a` of
`ccm-polar-euler-frame-minus-level-law.md`, the prime number theorem also gives

```text
mu_a=4exp(a)+o(exp(a)).                                       (14)
```

Since

```text
QW_a(v_a,v_a)=||B_a v_a||^2-mu_a||v_a||_2^2,                 (15)
```

equations `(3)`, `(13)`, and `(14)` prove

```text
||B_a v_a||^2/[mu_a||v_a||_2^2] ->1.                         (16)
```

Thus every nonzero profile `f in C_c^infinity(0,L)` is an asymptotic level-saturating direction.

## 5. Positive CCM obligation

The family of profiles in `(1)` is infinite-dimensional. Consequently every proof of the exact
lower-frame inequality

```text
||B_a v||^2>=mu_a||v||_2^2                                  (17)
```

must establish the sign of the subleading remainder uniformly on a cofinal boundary-profile
space. The surviving carrier is

```text
critical Mellin error measure dR
  + Gamma logarithmic form
  + full boundary autocorrelation C_v
  + exact even polar pointing.                               (18)
```

This is stronger than requiring one prolate seed to have small Rayleigh value: every fixed smooth
boundary profile already has relative Rayleigh error `o(1)` at the exponential frame scale. The
RH-bearing statement is the one-sided sign of that remainder, not its leading magnitude.

## Classification

The proof is a direct boundary-layer use of the prime number theorem and standard Fourier
translation calculus. It is a route-useful bridge, not new scientific knowledge.

## Gates

- [x] exact two-edge boundary family constructed
- [x] polar rank-one leading term computed
- [x] rescaled prime boundary measure converged by PNT
- [x] universal polar--prime cancellation proved
- [x] Gamma contribution proved lower order
- [x] infinite-dimensional frame-level saturation proved
- [ ] prove the one-sided subleading lower-frame remainder
- [ ] RH
