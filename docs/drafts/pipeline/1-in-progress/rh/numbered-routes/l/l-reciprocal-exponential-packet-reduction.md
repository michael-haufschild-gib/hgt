# Route L: reciprocal-exponential reduction of the packet wall

- **Status:** dependency-closed paper proof; Lean formalization open.
- **Purpose:** replace the geometric packet by a continuous-time arithmetic profile with an error already below the required RH-scale block bound. This does not bound the remaining signed correlation.

For `r>1`, `k>=1`, put

```
q_n = (n-1)/(n+1),
S_r(k) = sum_(n>=1) mu(n) (n+1)^(-r) q_n^k,
T_r(t) = sum_(n>=1) mu(n) n^(-r) exp(-2t/n)  (t>0).
```

Both series converge absolutely. The following estimates hold for `k,t>=1`, with constants depending only on `r`:

```
|S_r(k)| + |T_r(k)| <= C_r k^(1-r),
|S_r(k)-T_r(k)| <= C_r k^(-r),
|T_r'(t)| <= C_r t^(-r).
```

The arithmetic coefficients are the literal Möbius coefficients; no estimate for their cancellation is used here. To prove the bounds, first note that for every `a>1`, `c>0`, `t>=1`,

```
sum_(n>=1) n^(-a) exp(-ct/n) <= C_(a,c) t^(1-a).       (1)
```

For `n>t`, compare with the integral of `x^(-a)`. For `n<=t`, split into `t/2^(j+1)<n<=t/2^j`; each block has at most `2t/2^j` integers and contributes at most
`2^(a+1)t^(1-a) 2^(j(a-1)) exp(-c2^j)`. Sum this convergent series.

For `n>=2`, set `x=1/n<=1/2`. Direct integration gives

```
0 <= log((1+x)/(1-x))-2x
   = 2 integral_0^x u^2/(1-u^2) du <= 8x^3/9.
```

Consequently `0<=q_n^k<=exp(-2k/n)` and

```
0 <= exp(-2k/n)-q_n^k
   <= (8k/(9n^3)) exp(-2k/n).                         (2)
```

Also `0<=n^(-r)-(n+1)^(-r)<=r n^(-r-1)` by the mean-value theorem. Equations (1)--(2) bound the sum of absolute atom errors by

```
exp(-2k) + r C_(r+1,2) k^(-r)
          + (8/9) C_(r+3,2) k^(-r-1) <= C_r k^(-r).
```

The first term handles `n=1`, where `q_1=0`. Equation (1) also bounds `S_r` and `T_r` by `C_r k^(1-r)`. Termwise differentiation of the locally uniformly convergent series gives `T_r'(t)=-2 sum mu(n)n^(-r-1)exp(-2t/n)`, hence the derivative estimate from (1).

**RH-scale energy equivalence.** For every integer `K>=1`,

```
| sum_(K<=k<2K) S_r(k)^2
    - integral_K^(2K) T_r(t)^2 dt | <= C_r K^(2-2r).    (3)
```

Indeed `|S_r(k)^2-T_r(k)^2|<=C_r k^(1-2r)`. The derivative bound gives `|(T_r(t)^2)'|<=C_r t^(1-2r)`, so replacing the sum of `T_r(k)^2` by its integral over unit cells has the same error. Sum at most `K` errors of size `C_r K^(1-2r)`.

The continuous kernel is explicit:

```
H^c_(r,K)(m,n)
  = (mn)^(-r) integral_K^(2K) exp(-2t(1/m+1/n)) dt
  = (mn)^(1-r) / (2(m+n))
      * [exp(-2K(m+n)/(mn))-exp(-4K(m+n)/(mn))].
```

Absolute convergence permits expansion of the integral into its signed pair sum. Its diagonal is `O_r(K^(2-2r))` by (1) with `a=2r,c=4`. The geometric diagonal has the same bound. Thus (3) also shows that the *signed strict off-diagonals* of the geometric and continuous kernels differ by `O_r(K^(2-2r))` (with the factor `2` from their diagonal/off-diagonal decompositions).

For the Route L producer, the unsolved theorem can therefore be stated equivalently with the continuous profile: for exponents `r` cofinal to `1`, find `0<eta<r-1` such that

```
integral_K^(2K) T_r(t)^2 dt <<_(r,eta) K^(2-2r+eta).
```

The replacement error in (3) is below this allowance. This isolates the one-power arithmetic saving in a smooth reciprocal-Laplace profile; it does not obtain that saving. The corpus search found the finite geometric packet identity and generic dyadic bounds, but no prior bound or reciprocal-exponential comparison for these literal Möbius packets. Deep search had partial source coverage, so corpus absence is not asserted globally.

**Exact critical renewal equation.** Möbius inversion gives an additional source law,

```
sum_(d>=1) d^(-r) T_r(t/d) = exp(-2t)  (t>0).          (4)
```

The double series is absolutely convergent for `r>1`; after grouping by `m=dn`, its coefficient is `m^(-r) sum_(n|m)mu(n)`, which vanishes except at `m=1`. Define the RH-normalized log-time profile

```
F_r(y) = exp((r-1/2)y) T_r(exp(y)).
```

Then (4) becomes the **same critical positive-integer renewal operator** already present in `MobiusLaplaceCriterionFrontier.tsum_mobiusLaplaceCriticalRenewal`:

```
sum_(d>=1) d^(-1/2) F_r(y-log d)
  = exp((r-1/2)y-2exp(y)).                            (5)
```

Its forcing is different from the corpus's direct Möbius--Laplace forcing. Precisely,

```
integral_K^(2K) T_r(t)^2 dt
  = integral_(log K)^(log(2K)) exp((2-2r)y) F_r(y)^2 dy.
```

On this fixed-width log interval the weight is comparable to `K^(2-2r)`. Thus the desired block estimate is equivalent, via (3), to `integral_(log K)^(log(2K)) F_r(y)^2 dy <<_(r,eta) K^eta`. The shared renewal *operator* supplies no such bound for this source by itself; (5) identifies the precise source-specific critical renewal estimate to attack.
