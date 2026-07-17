# Theta-cusp Gaussian damping activates the reflected tail budget

- **ID:** `theta-cusp-half-density-damped-tail-domination`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (Lean 4) / `[VALUE RELATION] [TOP-DOWN HYPOTHESIS DISCHARGE]`
- **Scientific status:** `[LEAN-VERIFIED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `theta-cusp-half-density-ward-laplace-budget-transfer.md`;
  `../../1-in-progress/theta-cusp-dominant-first-atom-ratio-certificate.md`
- **Lean inputs:** `PrimeArchThetaSourceAtomDomination.lean`;
  `PrimeArchThetaFirstMoment.lean`; `ThetaCuspReflection.lean`
- **Lean output:** `PrimeArchThetaHalfDensityDampedTail.lean`
- **Statement:** Retaining the Gaussian factor discarded by the formal uniform atom domination
  produces an exponential decay in the logarithmic coordinate.  At the reflected half-density
  weight this decay absorbs `cosh(x/2)`.  Consequently the exact higher-atom half-density budget is
  at most `(8/2997)` times the first atom's zeroth moment, so the budget branch of both
  low-degree minimum coefficients is unconditionally active.

## 1. Refined pointwise atom domination

For `n>=2` and `x>=0`, write

```text
f_n(x)=thetaCuspSourceTerm x n,
C_n=2*n^4*exp(-pi*(n^2-1)),
lambda_n=2*pi*(n^2-1).
```

The source formula used by `thetaCuspSourceTerm_le_first` gives, with `u=exp(x)`,

```text
f_n(x)/f_1(x)
 =n^2*(2*pi*n^2*u^2-3)/(2*pi*u^2-3)
    *exp(-pi*(n^2-1)*u^2).                              (1)
```

The existing polynomial comparison is

```text
n^2*(2*pi*n^2*u^2-3)/(2*pi*u^2-3)<=2*n^4.             (2)
```

Instead of replacing the complete Gaussian by its endpoint value, split it as

```text
exp(-pi*(n^2-1)*u^2)
 =exp(-pi*(n^2-1))
  *exp(-pi*(n^2-1)*(u^2-1)).                            (3)
```

Since `exp(2*x)-1>=2*x`, equations `(1)`--`(3)` give the refined domination

```text
f_n(x)<=C_n*exp(-lambda_n*x)*f_1(x).                   (4)
```

This is the formal atom bound with its unused cusp damping restored.

## 2. Half-density absorption

For `n>=2`, `lambda_n>1/2`.  Hence, for every `x>=0`,

```text
cosh(x/2)*exp(-lambda_n*x)
 =(exp(-(lambda_n-1/2)*x)+exp(-(lambda_n+1/2)*x))/2
 <=1.                                                   (5)
```

Let

```text
a_0=2*integral_(0,infinity) f_1(x) dx,
K_n=2*integral_(0,infinity) cosh(x/2)*f_n(x) dx.
```

Multiplying `(4)` by the half-density weight and using `(5)` yields

```text
K_n<=C_n*a_0.                                           (6)
```

The paper argument also gives strictness because the first source is positive on `(0,infinity)`
and the right side of `(5)` is strictly below `1` for positive `x`.  The Lean theorem records the
non-strict form, which is exactly what the branch activation and RH reduction require.

## 3. The exact higher budget lies below the uniform zeroth-moment loss

The reflected Ward--Laplace card proves

```text
K_n=(4*pi*n^2-1)*exp(-pi*n^2),
H=sum_(n>=2) K_n
 =1/2-(4*pi-1)*exp(-pi).                                (7)
```

The formal domination weight is

```text
Q=sum_(n>=2) C_n<=8/2997=:q.                            (8)
```

Summing `(6)` gives the Lean-verified comparison

```text
H<=Q*a_0<=q*a_0.                                        (9)
```

Thus the comparison between the reflected constant and the first-atom mass is structural; it
does not require a decimal approximation, quadrature, or a special-function enclosure.

## 4. Activated low-degree transfer

Put

```text
W=a_0+a_1/8.
```

Since `a_1>=0`, equation `(9)` implies

```text
H/W<=q,
H<=q*a_0.                                               (10)
```

Therefore the two minimum coefficients in the parent card satisfy exactly

```text
min(q,H/W)=H/W,
min(q*a_0,H)=H.                                         (11)
```

The completed theta low block follows from

```text
14*(W+H)*a_2^2<=9*W*a_1*a_3,                           (12)
16*(a_0+H)*a_2<=45*a_1^2.                              (13)
```

Both are no stronger than the former single-loss conditions

```text
14*(1+q)*a_2^2<=9*a_1*a_3,
16*(1+q)*a_0*a_2<=45*a_1^2.                            (14)
```

Indeed `(10)` makes the new multiplier in each left side no larger.  This is a genuine
top-down hypothesis discharge; it still does not prove `(12)` or `(13)`.

## Consequence for the RH chain

```text
(12) and (13)
 -> completed theta constant/linear Hankel block
 -> [degree-at-least-two cone, or leading determinants from size three]
 -> RH.                                                  (15)
```

The remaining finite value problem is now exactly `(12)`--`(13)`.  The higher theta atoms no
longer contribute an unknown or a worst-case enclosure to that interface.

## Gates

- [x] refined exponentially damped atom domination proved on paper
- [x] half-density absorption proved on paper
- [x] exact reflected-budget branch activation proved on paper
- [x] both reflected-budget first-atom conditions proved no stronger than the single-loss forms
- [x] formalize the damped domination and budget comparison in Lean
  (`PrimeArchThetaHalfDensityDampedTail.lean`)
- [ ] prove first-atom inequalities `(12)` and `(13)`
- [ ] prove the independent higher-degree or leading-determinant tail
