# The exact CCM low radial first row vanishes at the leakage scale

- **ID:** `ccm-exact-finite-aperture-first-row-vanishing`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's pole-uniform radial PSWF expansion, Bessel symbol asymptotics,
  one-dimensional stationary phase, and the exact logarithmic-aperture cutoff
- **Statement:** For the actual constrained degree-four radial mode, uniformly in the low radial
  range `2<=k<=lambda^2`,

  ```text
  |G_lambda(1,k)|/d_1(lambda)
    <= C*c^(-1/2)*k^(-2)+C*c^(-1)*k^(-1),
  c=2*pi*lambda^2.
  ```

  Consequently its logarithmically weighted first row is `o(d_1(lambda))`.

## Low radial range before asymptotics

The Lean theorem `logApertureDilationCorrelation_eq_zero` proves that a vector supported in
`[-log lambda,log lambda]` has zero correlation with the **prime shift** `log q` whenever
`q>lambda^2`. In the radial decomposition `k=q*n`, the multiplier `n` remains unbounded. The
present theorem controls the useful low radial subrange

```text
2<=k<=lambda^2=c/(2*pi).                                        (1)
```

This subrange is separated by a fixed factor from the endpoint-coalescing scale `k` of order `c`.
In particular, at the unique stationary point the first Bessel argument is at least a fixed
positive multiple of `c/k>=2*pi`; no uniform passage through `k/c=1` is required by the finite
operator.

## Actual fixed-degree Bessel phase

Put `s=sigma_4(c)^2`. Dunster's fixed-degree separation law gives

```text
s=9/c+O(c^(-2)).                                                 (2)
```

Thus `s->0`, but `c*s->9`: replacing the actual phase by the literal `s=0` phase loses a bounded
degree-four phase marking. Retain instead

```text
xi_s(x)=integral_1^x sqrt((t^2-s)/(t^2-1))dt,
A_s(x)=xi_s(x)^(1/2)/[(x^2-1)(x^2-s)]^(1/4).                    (3)
```

For `0<=s<=1/2` and `x>=1`, direct comparison of the integrands gives

```text
sqrt(1-s)*sqrt(x^2-1)<=xi_s(x)<=sqrt(x^2-1),
|A_s(x)|<=C*x^(-1/2).                                           (4)
```

After endpoint normalization, the leading part of the exact first-row Gram entry is a fixed
constant times

```text
L_(c,s)(k)=c*integral_1^infinity A_s(x)A_s(k*x)
  J_0(c*xi_s(x))J_0(c*xi_s(k*x))dx.                              (5)
```

## Exact stationary point

For the difference phase `phi_(s,k)(x)=xi_s(x)-xi_s(k*x)`, the stationary equation is

```text
sqrt((x^2-s)/(x^2-1))
 =k*sqrt((k^2*x^2-s)/(k^2*x^2-1)).                              (6)
```

Writing `y=x^2`, equation `(6)` reduces exactly to

```text
k^2*y^2-(k^2+1)*y+s=0.                                         (7)
```

The unique root with `y>1` is

```text
y_(s,k)=((k^2+1)+sqrt((k^2+1)^2-4*k^2*s))/(2*k^2),              (8)

y_(s,k)-1
 =2*(1-s)/(sqrt((k^2+1)^2-4*k^2*s)+k^2-1)
 asymptotic to k^(-2),                                         (9)
```

uniformly for `k>=2` and `0<=s<=1/2`. Differentiating `(3)` gives

```text
d/dx xi_s(r*x)
 =r*sqrt((r^2*x^2-s)/(r^2*x^2-1)),                              (10)
```

and a second differentiation at `(8)` yields

```text
|phi_(s,k)''(sqrt(y_(s,k)))| asymptotic to k^3.                 (11)
```

The implicit constants in `(9)` and `(11)` are absolute in the stated range.

## Uniform leading bound in the finite range

Split off the Bessel endpoint layer `x-1<=C*c^(-2)`. Its absolute contribution to `(5)` is

```text
O(c^(-3/2)*k^(-1))=O(c^(-1/2)*k^(-2)),                          (12)
```

because `k<=c/(2*pi)<c`.

On the complement, use the two Bessel symbol branches. At `(8)` their arguments have sizes
comparable to `c/k` and `c*k`. The product of the two Bessel symbols is `O(c^(-1))`,
`A_s(k*x)=O(k^(-1/2))`, and stationary phase with `(11)` supplies
`(c*k^3)^(-1/2)`. Including the prefactor `c` in `(5)` gives

```text
|L_(c,s)(k)|<=C*c^(-1/2)*k^(-2),
2<=k<=c/(2*pi).                                                  (13)
```

Outside a fixed relative neighbourhood of `(8)`, the difference-phase derivative is monotone
and bounded below by its distance from the critical point times a constant comparable to `k^3`.
One integration by parts on dyadic pieces gives `(13)`. The sum phase has no stationary point and
is smaller. The estimates in `(4)` and `s=O(c^(-1))` make all amplitude seminorms uniform.

## Dunster remainder is summable on the exact aperture

Dunster's pole-uniform formula is

```text
A_s(x)[J_0(c*xi_s(x))+O(c^(-1))*env J_0(c*xi_s(x))],             (14)
```

uniformly for `1<x<infinity`. The endpoint normalization changes `(14)` only by another uniform
factor `1+O(c^(-1))`.

Use `env J_0(u)<=C*(1+u)^(-1/2)`, `(4)`, and
`xi_s(k*x)>=sqrt(1-s)*sqrt(k^2*x^2-1)`. Then

```text
integral_1^infinity A_s(x)A_s(k*x)
  env J_0(c*xi_s(x))*env J_0(c*xi_s(k*x))dx
 <=C/(c*k).                                                      (15)
```

Indeed the second envelope and the two amplitudes contribute
`C*c^(-1/2)*k^(-1)*x^(-3/2)`, while splitting at `x=2` and using
`r=sqrt(x^2-1)` near the endpoint gives

```text
integral_1^infinity x^(-3/2)*(1+c*sqrt(x^2-1))^(-1/2)dx
 <=C*c^(-1/2).                                                   (16)
```

In the Gram product the prefactor `c` cancels the single `c^(-1)` from a cross remainder.
Equations `(15)`--`(16)` therefore give the exact-solution error

```text
|G_lambda(1,k)/d_1(lambda)-L_(c,s)(k)|<=C/(c*k).                 (17)
```

The product of two remainders is smaller. Combining `(13)` and `(17)` proves the stated bound.

## Arithmetic conclusion

The exact aperture and the elementary harmonic estimate give

```text
sum_(2<=k<=lambda^2) log(k)*|G_lambda(1,k)|/d_1(lambda)
 <=C*c^(-1/2)*sum_(k>=2)log(k)/k^2
   +C*c^(-1)*sum_(k<=lambda^2)log(k)/k
 =O(c^(-1/2))+O(log(c)^2/c)
 =o(1).                                                         (18)
```

Hence the complete exceptional first row vanishes cofinally at the leakage scale.

## Consequence and remaining gates

Together with the already proved exact nonstationary `j,k>=2` sector and the diagonal radial
leakage spectrum, `(18)` closes the low radial part of the exceptional first row. It does not close
the truncated-divisor weighted tail `k>lambda^2`; see
`ccm-prime-shift-radial-index-separation-law.md`. The Poisson center, archimedean form, and true
Weil even-gap lower bound remain later gates.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, especially the radial
  approximation `(3.6)` / summary formula `(6.5)` in the published numbering.
- NIST Digital Library of Mathematical Functions, Bessel envelopes and large-argument symbols.

## Gates

- [x] exact low radial index range established before asymptotics
- [x] nonzero fixed-degree phase retained
- [x] unique stationary point solved exactly
- [x] leading Bessel first row bounded uniformly on the finite aperture
- [x] Dunster envelope remainder summed on that aperture
- [x] logarithmically weighted exact first row proved `o(d_1)`
- [ ] prove the high truncated-divisor weighted radial tail
- [ ] combine with the intact Poisson central correction
- [ ] prove the archimedean and true-Weil gap comparison
