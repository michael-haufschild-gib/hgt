# Hedenmalm center-mixed cofinal three-point closure

- **ID:** `hedenmalm-center-mixed-cofinal-three-point-closure`
- **Stage:** 2-fully-proven
- **Type:** SOURCE THEOREM / COFINAL ORDER-THREE POSITIVITY
- **Date:** 2026-07-20
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NO COMPUTATION] [NOT RH]`
- **Parent:** `../3-formalized/needs-audit/hedenmalm-center-mixed-asymmetric-near-three-point-chamber.md`

## Exact conjecture

For `0 < a < 1/2`, let `M_a` be the actual center-mixed theta density.  There is `Y` such that
for every `y >= Y` and every `x > 0`, the ordered correlation matrix at `0,x,x+y` is positive
semidefinite.  Equivalently, the full order-three wall is closed whenever either adjacent gap is
sufficiently large.

This is strictly stronger than the compiled theorem
`eventually_exists_thetaCuspCenterMixed_nearCenter_posDef`, which supplies only a nonempty
`y`-dependent interval of admissible small `x`.

## Internal frontier

`[CORPUS]` The project proves strict positivity, evenness, radial antitonicity, strict center drop,
`C^2` source differentiation, `M_a''(0)<0`, and `M_a,M_a' -> 0`.  The derivative-product tail
theorem also immediately supplies `M_a'' -> 0`.  The far chamber

`M_a(x)^2 + M_a(y)^2 <= M_a(0)^2`

is already positive semidefinite.  The complementary near-center determinant is the exact
remaining order-three wall.

## External parent boundary

Castano--Paksoy--Zhang, *Angles, triangle inequalities, correlation matrices and
metric-preserving and subadditive functions*, Linear Algebra Appl. 2014,
arXiv:1407.2800, proves the classical equivalence between positivity of a nonnegative `3 x 3`
correlation matrix and the triangle inequalities for the three `arccos` angles.  Schoenberg and
Bochner provide the all-packet positive-definite parent theory.  Targeted searches found no theorem
specializing center curvature plus two-jet decay to a cofinal order-three closure for this theta
source.  Priority remains `[NOVELTY UNVERIFIED]`.

## Proposed mechanism

For a `C^2` profile `f`, write `d=f(0)` and

`D_y(x)=d^3+2f(x)f(y)f(x+y)-d(f(x)^2+f(y)^2+f(x+y)^2)`.

The exact second derivative is already formalized.  As `(y,x) -> (+infinity,0)`, the source tail
limits and `f'(0)=0` give

`D_y''(x) -> -2 d^2 f''(0) > 0`.

Hence there are uniform `Y_0,delta>0` such that `D_y` is strictly convex on `[0,delta]` for every
`y>=Y_0`.  Since `D_y(0)=D_y'(0)=0`, this gives `D_y(x)>0` for every `0<x<=delta`.

Strict center drop gives `f(delta)<d`.  Since `f(y)->0`, after increasing `Y_0` one has

`f(delta)^2+f(y)^2<d^2`.

Radial antitonicity then forces every near-center packet
`d^2 < f(x)^2+f(y)^2` to satisfy `x<delta`; it is therefore in the uniform convexity chamber.
Every other `x` is in the already proved far chamber.

## Hostile audit

- The statement does not assume a determinant sign or positive definiteness.
- It does not extrapolate from order three to all finite orders.
- Generic log-concavity is not the mechanism; the decisive extra input is strict negative center
  curvature together with decay of the profile and its first two derivatives.
- The result cannot imply RH: it leaves the compact two-gap core and every higher matrix order open.
- The main possible failure is lack of a uniform product-neighborhood passage for `D_y''`; the
  two-parameter limit above is the exact proof obligation.

**Current verdict:** `SURVIVES PRELIMINARY ATTACK`.

## Dependency-complete paper proof

Let `d=f(0)`, `h=f''(0)`, and `c=-2*d^2*h>0`.  Split the exact second derivative as

```text
D_y''(x)=L(x)+R_y(x),
L(x)=-2*d*(f'(x)^2+f(x)f''(x)).
```

Continuity and `f'(0)=0` give `L(0)=c`.  Choose `delta>0` such that
`L(x)>3c/4` on `[0,delta]`, and choose `A>=1` bounding `|f|,|f'|,|f''|` there.
The exact remainder is

```text
R_y(x)=2[f''(x)f(y)f(x+y)+2f'(x)f(y)f'(x+y)+f(x)f(y)f''(x+y)]
       -2d[f'(x+y)^2+f(x+y)f''(x+y)].
```

Choose `epsilon>0` with `(8A+4d)epsilon^2<c/4`.  Since `f,f',f'' -> 0`, there is
`Y_0` such that all three absolute values are below `epsilon` on `[Y_0,infinity)`.  If
`y>=Y_0` and `0<=x<=delta`, then both `y` and `x+y` lie in that tail, so termwise estimation gives

`|R_y(x)| <= (8A+4d)epsilon^2 < c/4`.

Thus `D_y''(x)>c/2` throughout `[0,delta]`, uniformly in `y>=Y_0`.  The algebraic identities
`D_y(0)=D_y'(0)=0` and two applications of the positive-derivative monotonicity theorem imply

`D_y(x)>0` for every `y>=Y_0` and `0<x<=delta`.                         (1)

Now use the source order.  Strict center drop gives `0<=f(delta)<d`; hence
`eta=d^2-f(delta)^2>0`.  Increase the threshold to `Y>=Y_0` so that `f(y)^2<eta` for `y>=Y`.
If `x>=delta`, antitonicity and nonnegativity give `f(x)^2<=f(delta)^2`, whence

`f(x)^2+f(y)^2 < f(delta)^2+eta=d^2`.                                  (2)

Therefore every near-center packet with `y>=Y` must have `0<x<delta`, and its determinant is
strictly positive by `(1)`.  Every complementary packet satisfies the existing far-chamber
hypothesis and is positive semidefinite.  This proves the exact conjecture.

For the actual theta source, the compiled derivative-product integral identities give `C^2`,
`f'(0)=0`, and `f''(0)<0`.  The existing product-integral tail theorem applied at `(m,n)=(0,0)`,
`(1,0),(0,1)`, and `(2,0),(1,1),(0,2)` gives respectively `f,f',f'' -> 0`.  Strict positivity,
radial antitonicity, and strict center drop are already source theorems.  Hence every hypothesis
used above is unconditional and source-resolved.

## Gates

- [x] exact internal frontier established
- [x] exact correlation-matrix parent identified
- [x] conjecture is stronger than the previous asymmetric chamber
- [x] dependency-complete proof of the two-parameter uniform convexity limit
- [x] dependency-complete proof that the near-center condition is trapped in that neighborhood
- [x] formalize the generic analytic theorem
- [x] discharge every source hypothesis and connect to the named wall
- [ ] axiom, lint, and final module-build audit
