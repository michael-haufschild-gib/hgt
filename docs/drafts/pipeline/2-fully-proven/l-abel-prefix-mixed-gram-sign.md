# Route L: Abel-prefix mixed Gamma--Hankel sign atlas

- **ID:** L-ABEL-PREFIX-MIXED-GRAM-SIGN
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM
- **Lean status:** Finite Abel identity, algebraic mixed-kernel formula, and quantitative pointwise sign bounds are closed in [MobiusAbelPrefixGramSign.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusAbelPrefixGramSign.lean). The Gamma integral identification and integrated unit-interval Gram sign statements below remain paper-level.

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

For the first bound, `2(3xy-x²-y²)-xy=-(x-2y)(2x-y)>=0`. Multiply by `6+2delta` and add the nonnegative `delta(1+delta)xy` to obtain the stronger lower bound `(3+2delta+delta²)xy`. For the second, assume `x>=3y` and use `3(3xy-x²-y²)+xy=-(x-3y)(3x-y)<=0`. Since `3delta(1+delta)-(6+2delta)<=-2` on `[0,1]`, multiplication gives `3B_delta<=-2xy`. Symmetry handles `y>=3x`.

The denominator in (2) is positive. Hence `G_delta` is strictly positive for comparable scales and strictly negative for scales separated by at least a factor of three. In particular, the *discrete* Gram in (3) is strictly positive whenever `m+1<=2n` and `n+1<=2m`, and strictly negative whenever `m>=3(n+1)` or `n>=3(m+1)`. The strip between these two ratio regimes is determined exactly by `B_delta`; it has not been assigned a sign here.

## Consequence for the hard source bound

Equation (4) replaces the original Möbius pair coefficients by correlations of the *actual Mertens prefixes* against an explicitly signed mixed Gram. The archimedean part now has a proved local-positive/far-negative structure and quantitative margins. The remaining obstruction is arithmetic: upper-bound the full signed sum `sum M(m)M(n)D_delta(m,n)` together with its terminal cross term, uniformly in `N` and `delta`. In particular, pointwise signs of `D_delta` alone do not control products `M(m)M(n)`. A productive next conjecture must quantify how Mertens-prefix signs and magnitudes interact across the comparable and separated scale regions of (5); it cannot replace those prefixes by absolute values.
