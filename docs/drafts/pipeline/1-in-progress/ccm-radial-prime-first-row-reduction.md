# The CCM radial prime charge reduces to one coalescing first-row series

- **ID:** `ccm-radial-prime-first-row-reduction`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE, `[OPEN ANALYTIC SUBCLAIM]`
- **Scientific status:** `[CONJECTURE] [NOT AN RH PROOF]`
- **Parent theories:** Dunster's uniform radial Bessel expansion, one-dimensional nonstationary
  phase, and the von Mangoldt divisor identity
- **Statement:** After removing the solved diagonal divisibility spectrum, every weighted radial
  Gram entry with both indices at least two contributes only `O(d_1/lambda^2)`. The sole possible
  gap-scale off-diagonal prime contribution is
  `-2 sum_(k>=2)log(k)G_lambda(1,k)`, whose stationary point coalesces with the radial endpoint at
  `k` of order `2*pi*lambda^2`.

## Setup

Use the constrained source and radial Gram matrix

```text
G_lambda(j,k)
 =inner(H_(lambda,j),H_(lambda,k))_(L2(ds)),

H_(lambda,k)(s)
 =sqrt(lambda*e^s) q_lambda(k*lambda*e^s),

c=2*pi*lambda^2.                                                (1)
```

For a radial cutoff `K`, define the raw prime Gram charge

```text
P_(lambda,K)
 =-2 sum_(k=2)^K log(k) sum_(j=1)^K G_lambda(j,k).                (2)
```

Equation `(2)` is the finite divisibility expansion of the prime pairing: writing `k=mn` and
summing `Lambda(m)` over divisors gives

```text
sum_(m|k;m>=2)Lambda(m)=log k.                                   (3)
```

It deliberately excludes the Poisson central correction, which is kept intact later in the exact
closed-form tail.

## Uniform nonstationary Gram bound

`[CONJECTURE; PROVED FOR THE LEADING DUNSTER BESSEL MODEL]` There is a constant `C` such that, for
all sufficiently large `lambda` and all
distinct integers `j,k>=2`,

```text
|G_lambda(j,k)|
 <=C*d_1(lambda)/(c*j*k*|j-k|).                                  (4)
```

### Leading-model proof and exact missing estimate

Dunster's radial expansion and the constrained `m=4` dominance give, uniformly for `x>=1` and
`r>=2`,

```text
sqrt(lambda*x) q_lambda(lambda*r*x)
 =sqrt(d_1(lambda))/r
   *a_(r,c)(x)
   *[cos(c*xi_c(r*x)-pi/4)+O(c^(-1))],                            (5)
```

where `a_(r,c)` and its first derivative are bounded by an integrable envelope independent of
`r,c`. More precisely, after the `ds=dx/x` measure is included, the product envelope in the
`(j,k)` entry is bounded by `C/(j*k*x^2)` together with its first derivative.

For the limiting phase `xi_infinity(t)=sqrt(t^2-1)`,

```text
d/dx xi_infinity(r*x)=r^2*x/sqrt(r^2*x^2-1).                      (6)
```

As a function of the integer parameter `r>=2`, the right side of `(6)` has derivative bounded
above and below by positive absolute constants, uniformly for `x>=1`. The small
`sigma_4(c)^2=O(c^(-1))` perturbation in Dunster's exact phase preserves this property. Hence

```text
|d/dx[xi_c(j*x)-xi_c(k*x)]|>=c_0|j-k|,   j,k>=2.                  (7)
```

The sum phase has an even larger derivative. One integration by parts in each **leading Bessel
product** from `(5)`, using `(7)` and the integrable amplitude derivative, gives `(4)` for that
model.

The exact missing estimate is error stability through the infinite index sum. Dunster's published
envelope bound is pointwise uniform and is sufficient for every fixed pair, but it does not by
itself attach the extra factor `|j-k|^(-1)` to the product of two remainder terms. One must either
derive an oscillatory representation of the error, prove a two-parameter differentiated remainder
bound, or sum the error sector by a separate Hilbert-space almost-orthogonality theorem. Until then,
`(4)` for the exact radial PSWF remains conjectural.

## Summed nonstationary sector

Conditionally on `(4)`, the elementary Hilbert-kernel estimate

```text
sum_(j>=2;j!=k) 1/(j*k*|j-k|)
 <=C*(1+log k)/k^2                                              (8)
```

and `(4)` imply

```text
sum_(k>=2) log(k)
  sum_(j>=2;j!=k)|G_lambda(j,k)|

 <=C*d_1(lambda)/c
   *sum_(k>=2)log(k)(1+log k)/k^2
 =O(d_1(lambda)/c).                                              (9)
```

Therefore this entire sector would be `o(d_1)`.

## Exact first-row reduction

Split `(2)` into diagonal, first-row, and the sector in `(9)`:

```text
P_(lambda,K)
 =D_(lambda,K)+E_(lambda,K)+N_(lambda,K),                         (10)

D_(lambda,K)=-2 sum_(k=2)^K log(k)G_lambda(k,k),
E_(lambda,K)=-2 sum_(k=2)^K log(k)G_lambda(1,k).                  (11)
```

The radial leakage theorem proves

```text
D_(lambda,infinity)/d_1(lambda)
 ->-16/(11*pi)sum_(k>=2)log(k)/k*arcsin(1/k),                     (12)
```

and conjectural estimate `(9)` would prove

```text
N_(lambda,infinity)=O(d_1(lambda)/c)=o(d_1(lambda)).              (13)
```

Thus, once exact error stability is proved, the only unresolved raw radial prime contribution is
the first-row series

```text
E_lambda=-2 sum_(k>=2)log(k)G_lambda(1,k).                        (14)
```

## Coalescing stationary scale

For the limiting radial phase, a stationary point of

```text
xi_infinity(x)-xi_infinity(k*x)
```

must satisfy

```text
x/sqrt(x^2-1)=k^2*x/sqrt(k^2*x^2-1).
```

Its unique solution is

```text
x_k^2=1+1/k^2.                                                    (15)
```

Hence

```text
x_k-1~1/(2k^2).                                                   (16)
```

Dunster's radial Bessel endpoint coordinate has width `x-1` of order `c^(-2)`. Equations
`(15)`--`(16)` show that the stationary point coalesces with the endpoint precisely at

```text
k asymptotic to c=2*pi*lambda^2.                                  (17)
```

This is the same scale as the finite-prime cutoff in the CCM parity carrier.

## Positive open theorem

The intended full radial prime reduction is one-dimensional in the arithmetic index:

```text
determine the cofinal limit of
  d_1(lambda)^(-1) sum_(k>=2)log(k)G_lambda(1,k)
through the transition k/c,
then combine it with the exact Poisson central correction.        (18)
```

The relevant analytic object is a Bessel stationary point coalescing with a regular singular
endpoint. Dunster supplies the uniform radial Bessel model; the missing theorem is its weighted
arithmetic summation through `k/c`, not a general two-index Gram estimate.

## Novelty and significance verdict

The phase geometry and leading-model reduction use standard nonstationary phase and the classical
divisor identity. The exact all-index error-stability theorem may be nontrivial and remains under
the main route's novelty gate. No novelty claim is made before it is proved.

## References

- T. M. Dunster, *Asymptotics of Prolate Spheroidal Wave Functions*, arXiv:1601.00699.
- A. Connes, C. Consani, H. Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

## Lean decision

The formal tree has no radial PSWF or stationary-phase infrastructure. No Lean file is added.

## Gates

- [x] uniform nonstationary estimate proved for the leading Bessel model
- [ ] transfer the estimate to Dunster's exact uniform remainder
- [ ] sum the exact `j,k>=2` weighted sector
- [x] diagonal charge imported and separated
- [ ] isolate the exceptional first-row series for the exact radial charge
- [x] coalescing scale `k/c` identified
- [ ] evaluate the first-row coalescing series
- [ ] combine with exact Poisson central correction
- [ ] true Weil Rayleigh-excess and parity transfer
