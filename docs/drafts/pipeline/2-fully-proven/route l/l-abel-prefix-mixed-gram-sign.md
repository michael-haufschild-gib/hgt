# Route L: Abel-prefix mixed Gamma--Hankel sign atlas

- **ID:** L-ABEL-PREFIX-MIXED-GRAM-SIGN
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM
- **Lean status:** Finite Abel identity, algebraic mixed-kernel formula, and quantitative pointwise sign bounds are closed in [MobiusAbelPrefixGramSign.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusAbelPrefixGramSign.lean). The Gamma integral identification, integrated unit-interval Gram signs, and frozen-prefix Fourier representation below remain paper-level.

## Exact prefix-energy representation

For `0 <= delta <= 1`, put `p=5+delta`, `f_x(t)=x² exp(-xt)` for `x,t>0`, and

```text
<u,v>_delta = Gamma(p)^(-1) integral_0^infinity t^(p-1) u(t)v(t) dt.
```

Let `a_n=mu(n)` and `M(n)=sum_(k<=n) a_k`. At every finite cutoff `N>=1`, summation by parts gives the *literal* source identity

```text
S_N(t) := sum_(n=1)^N a_n f_n(t)
        = M(N) f_N(t) + sum_(n=1)^(N-1) M(n) g_n(t),
g_n(t) := f_n(t)-f_(n+1)(t) = -integral_n^(n+1) partial_x f_x(t) dx.   (1)
```

The original atom Gram is `K_delta(x,y)=x²y²/(x+y)^p`. Differentiation under the finite Gamma integral gives

```text
G_delta(x,y) := <partial_x f_x,partial_y f_y>_delta
 = xy/(x+y)^(p+2) * B_delta(x,y),
B_delta(x,y) = (4-2p)(x+y)²+p(p+1)xy
             = (6+2delta)(3xy-x²-y²)+delta(1+delta)xy.            (2)
```

Indeed `partial_x f_x=(2x-x²t)exp(-xt)`. Multiplying the two derivatives yields `xy[4-2(x+y)t+xy t²]exp(-(x+y)t)`. The three Gamma moments are `1/(x+y)^p`, `p/(x+y)^(p+1)`, and `p(p+1)/(x+y)^(p+2)`, respectively. This proves (2) without a limit in `N`.

Define `D_delta(m,n)=<g_m,g_n>_delta`. By (1), Fubini on compact frequency intervals, and (2),

```text
D_delta(m,n) = integral_m^(m+1) integral_n^(n+1) G_delta(x,y) dy dx
 = K_delta(m,n)-K_delta(m+1,n)-K_delta(m,n+1)+K_delta(m+1,n+1).       (3)
```

Consequently the full finite energy has the exact arithmetic prefix form

```text
||S_N||_delta²
 = M(N)² K_delta(N,N)
   + 2 M(N) sum_(n<N) M(n)[K_delta(n,N)-K_delta(n+1,N)]
   + sum_(m,n<N) M(m)M(n)D_delta(m,n).                              (4)
```

## Quantitative sign atlas

For positive `x,y` and `0<=delta<=1`,

```text
x<=2y and y<=2x       imply B_delta(x,y) >= 3xy > 0;
x>=3y or y>=3x        imply 3 B_delta(x,y) <= -2xy < 0.          (5)
```

Both constants are sharp uniformly over this parameter range: the first has equality at `delta=0, x=2y`; the second at `delta=1, x=3y`.

The exact transition is also explicit. For `r=x/y>0`, (2) gives

```text
sign G_delta(x,y) = sign(c_delta-r-1/r),
c_delta = 3 + delta(1+delta)/(6+2delta).
```

The function `c_delta` increases on `[0,1]`: its derivative is `(6+12delta+2delta²)/(6+2delta)²>0`. Thus the positive ratio interval has upper endpoint `(3+sqrt(5))/2` at `delta=0` and `(13+sqrt(105))/8` at `delta=1`; the lower endpoint is its reciprocal. The factor-two and factor-three claims in (5) are uniform quantitative subregions of this sharp transition.

For the first bound, `2(3xy-x²-y²)-xy=-(x-2y)(2x-y)>=0`. Multiply by `6+2delta` and add the nonnegative `delta(1+delta)xy` to obtain the stronger lower bound `(3+2delta+delta²)xy`. For the second, assume `x>=3y` and use `3(3xy-x²-y²)+xy=-(x-3y)(3x-y)<=0`. Since `3delta(1+delta)-(6+2delta)<=-2` on `[0,1]`, multiplication gives `3B_delta<=-2xy`. Symmetry handles `y>=3x`.

The denominator in (2) is positive. Hence `G_delta` is strictly positive for comparable scales and strictly negative for scales separated by at least a factor of three. In particular, the *discrete* Gram in (3) is strictly positive whenever `m+1<=2n` and `n+1<=2m`, and strictly negative whenever `m>=3(n+1)` or `n>=3(m+1)`. For a unit rectangle that crosses the sharp transition, its integrated sign requires the full integral in (3).

## Exact logarithmic Fourier multiplier of the full source

The sign-changing kernel has a strictly positive spectral symbol. Set `a=(1+delta)/2=(p-4)/2`. For `x>=1`, let `P_N(x)=M(min(floor x,N))`; it equals `M(n)` on `[n,n+1)` for `n<N` and is frozen at `M(N)` for `x>=N`. Since `f_x(t)` tends to zero as `x` tends to infinity for every `t>0`, the terminal term in (1) joins the Abel integral exactly:

```text
S_N(t) = -integral_1^infinity P_N(x) partial_x f_x(t) dx.         (6)
```

Define `b_N(u)=exp(-a*u)*P_N(exp u)` on `u>=0`, and zero for `u<0`. Its frozen tail decays exponentially, so `b_N` is integrable and square-integrable. The *full* finite source energy is exactly

```text
||S_N||_delta²
 = integral_R integral_R b_N(u)b_N(v) H_delta(u-v) du dv,         (7)
H_delta(r) = exp((a+1)r) G_delta(exp r,1)
 = exp((a+2)r) B_delta(exp r,1)/(1+exp r)^(p+2).
```

This uses (6), `x=exp u`, `y=exp v`, and homogeneity `G_delta(lambda*x,lambda*y)=lambda^(-3-delta)G_delta(x,y)`. Fubini is justified first on finite `x,y` rectangles, then by exponential decay of `f'_x(t)` for each positive `t` and the Gamma norm bound `||f'_x||_delta=O_delta(x^(-3/2-delta/2))`; the frozen tail is integrable in that norm. With Fourier convention `hat h(tau)=integral_R h(r)exp(-i*tau*r) dr`, the beta integral gives

```text
hat H_delta(tau)
 = [a²+tau²] * |Gamma(p/2+i*tau)|²/Gamma(p) > 0.               (8)
```

To verify (8), substitute `x=exp r`. The `(4-2p)(1+x)²` part of `B_delta(x,1)` contributes `(4-2p) Gamma(p/2-i*tau)Gamma(p/2+i*tau)/Gamma(p)`. The `p(p+1)x` part contributes `(p²/4+tau²)` times the same factor. Their sum is `(a²+tau²)` times that factor. All beta parameters have positive real part because `p>=5`.

The frozen-prefix transform itself has a simple exact form. Since `P_N(exp u)=sum_(n<=N) mu(n) 1_(u>=log n)`, Tonelli for this finite sum gives

```text
hat b_N(tau)
 = (a+i*tau)^(-1) sum_(n<=N) mu(n)n^(-a-i*tau).             (9)
```

Plancherel and cancellation of `a²+tau²` between (8) and (9) make (7) the full Mellin--Plancherel identity

```text
||S_N||_delta² = 1/(2*pi*Gamma(p)) integral_R
  |Gamma(p/2+i*tau)|²
  * |sum_(n<=N) mu(n)n^(-a-i*tau)|² d tau.                 (10)
```

This agrees with the corpus's finite Möbius Laplace/Mellin receiver, now derived through the exact Mertens-prefix Gram. The sign change in (5) is not a negative spectral direction: every log-frequency is retained, and the multiplier in (8) is strictly positive. The remaining arithmetic input is a cutoff-uniform bound on the weighted logarithmic Fourier mass of the *literal* frozen prefixes, equivalently the weighted critical Dirichlet polynomial in (10).

## Consequence for the hard source bound

Equation (4) replaces the original Möbius pair coefficients by correlations of the *actual Mertens prefixes* against an explicitly signed mixed Gram. The archimedean part now has a proved local-positive/far-negative structure and quantitative margins. The remaining obstruction is arithmetic: for abscissas `a=(1+delta)/2` cofinal from the right at `1/2`, upper-bound the full signed sum `sum M(m)M(n)D_delta(m,n)` together with its terminal cross term, uniformly in `N` **for each chosen `delta>0`**. The [formal cofinal cubic criterion](../3-formalized/l-cofinal-cubic-source-criterion.md) shows that constants may depend on `delta`; no bound at `delta=0` is part of the RH receiver. In particular, pointwise signs of `D_delta` alone do not control products `M(m)M(n)`. A productive next conjecture must quantify how Mertens-prefix signs and magnitudes interact across the comparable and separated scale regions of (5); it cannot replace those prefixes by absolute values.
