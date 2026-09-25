# Continuum tangent space of the critical Euler prime source

- **ID:** `stc-euler-prime-boundary-tangent-space`
- **Stage:** 2-fully-proven (paper)
- **Type:** exact source-boundary scaling theorem
- **Routes:** STC, RHist
- **Status:** `[PROVED ON PAPER] [CENTRAL GRAM LIMIT LEAN-CHECKED] [FULL LEAN FORMALIZATION PENDING] [NOT AN RH PROOF]`
- **Lean core:** `STCEulerPrimeBoundaryTangentGram.lean` proves (1)'s two-parameter Gram limit from `tendsto_gradedPrimeLogZeta 1`; direct `lake env lean` passed. Targeted Lake audit remains pending because Lake launched parallel transitive dependency rebuilds, which were stopped to honor the one-process rule.
- **Novelty:** the prime-pole asymptotic is classical; its tangent-Hilbert and double-scaled STC operator interpretation is a corpus-level source identification, with external novelty unverified.

## Source and statement

On the depth-zero face of the literal Gamma--Euler source, write

```text
b_u(p) = (log p) p^(-(1+u)/2),       u>0,
S(u)   = sum_p b_u(p)^2.
```

The exact amplitude identity is in
`CCMFirstClockPrimitivePromotedExteriorSource.lean`; the sharp square-summability
threshold is already proved there. The following theorem identifies what is lost
when the source approaches that threshold.

**Prime-pole tangent theorem.** As `v -> 0+`,

```text
S(v) = v^(-2) + O(1),
v^2 <b_(a v),b_(b v)> -> K(a,b) = 4/(a+b)^2       (a,b>0).     (1)
```

For finitely many distinct positive `a_j` and complex `c_j`,

```text
lim_(v->0+) ||sum_j c_j v b_(a_j v)||^2
  = integral_(0,infinity) t |sum_j c_j exp(-a_j t/2)|^2 dt.  (2)
```

The right side is strictly positive unless every `c_j=0`. Thus the
critical source has a canonical nonzero continuum tangent Hilbert space:
`L^2((0,infinity),t dt)`, generated densely by the exponential features
`f_a(t)=exp(-a t/2)`, `a>0`. Every `v b_(a v)` nevertheless converges
weakly to zero in the fixed prime `ell^2` space.

Equivalently, the probability measures

```text
mu_(a,v) = S(a v)^(-1) sum_p b_(a v)(p)^2 delta_(v log p)
```

converge weakly to the Gamma law with density `a^2 t exp(-a t) dt`.
The natural boundary coordinate is therefore `v log p`, rather than a
fixed prime index.

## Paper proof

For real `s>1`, termwise differentiation of the absolutely convergent
Euler product gives

```text
(log zeta(s))''
  = sum_p (log p)^2 p^(-s)
    + sum_p sum_(m>=2) m (log p)^2 p^(-m s).                (3)
```

The second sum and its needed local derivatives are uniformly bounded
for `s>=1`: its terms are dominated by a constant multiple of
`(log p)^2 p^(-2)`, which is summable. Since
`h(s)=(s-1)zeta(s)` is analytic and nonzero near `s=1`, with `h(1)=1`,

```text
(log zeta(s))'' = (s-1)^(-2) + (log h(s))''
                  = (s-1)^(-2) + O(1).                    (4)
```

Equations (3)--(4) give the first claim in (1). The exact source
amplitude gives
`<b_(a v),b_(b v)> = S((a+b)v/2)`, proving the second.
Expanding the finite square and using
`integral_0^infinity t exp(-c t) dt = c^(-2)` proves (2).
Distinct positive exponentials are linearly independent, so the
integral is strictly positive for a nonzero coefficient vector.
For density, suppose `h` is orthogonal to every `f_a`. For any
`c>0`, Cauchy--Schwarz puts `t h(t) exp(-c t/2)` in `L^1(dt)`.
Its Laplace transform vanishes at every positive argument by the
orthogonality assumption. Uniqueness of the Laplace transform gives
`t h(t)=0` almost everywhere, hence `h=0` in the weighted Hilbert
space. The exponential span is therefore dense.
Each fixed prime coordinate of `v b_(a v)` tends to zero, while its
norm stays bounded by (1); density of finite-support vectors proves
weak convergence to zero.

For `lambda>=0`, the Laplace transform of `mu_(a,v)` is

```text
S((a+lambda)v)/S(a v) -> (a/(a+lambda))^2.
```

This is the Laplace transform of `a^2 t exp(-a t) dt`.
The continuity theorem for Laplace transforms of probability measures
proves the asserted weak convergence.

## Double-scaled STC source

The literal two-channel source kernel from
`stc-gamma-prime-hilbert-chamber.md` satisfies

```text
Q_(u,g) = (P_(b_(u-g)) - P_(b_(u+g)))/2,
P_x(y) = <x,y>x.
```

Fix `kappa>|lambda|` and set `u=kappa v`, `g=lambda v`.
The rescaled operator

```text
v^2 Q_(kappa v,lambda v)
  = (P_(v b_((kappa-lambda)v))
     - P_(v b_((kappa+lambda)v)))/2                    (5)
```

is uniformly bounded and tends strongly to zero on the fixed prime
Hilbert space. Its moving-source matrix elements instead converge to
those of the nonzero continuum operator

```text
Q^tan_(kappa,lambda)
  = (P_(f_(kappa-lambda)) - P_(f_(kappa+lambda)))/2
      on L^2((0,infinity),t dt).                         (6)
```

For `lambda != 0`, the two exponential features are linearly
independent, so (6) has rank two. This is an exact boundary object
retaining a grade that fixed-Hilbert strong convergence erases.
Its integral kernel relative to measure `s ds` is exactly

```text
exp(-kappa*(t+s)/2) sinh(lambda*(t+s)/2),              (7)
```

a Hankel kernel in the *sum* of the continuum boundary coordinates.
It remains compact on the tangent Hilbert space, so it does not by
itself produce the nonzero Sonin Calkin seam or prove RH.

There is a sharp distinction for a **fixed** grade `g != 0`. Put
`u=|g|+v` and keep `g` fixed as `v -> 0+`. Then

```text
v^2 Q_(|g|+v,g)
  = sign(g) (P_(v b_v)-P_(v b_(v+2|g|)))/2.
```

The second vector tends to zero in norm, since `S(v+2|g|)` stays
bounded. The first has tangent feature `f_1`. Consequently the
moving-source matrix elements converge to those of
`sign(g) P_(f_1)/2`, independent of `|g|`. The fixed-grade boundary
blowup retains only the sign of the grade; its magnitude is lost.
The grade-dependent rank-two tangent geometry in (6) exists only
when grade and regulator approach zero together.

Subtracting the universal leading term does retain fixed-grade data:

```text
Q_(|g|+v,g) - sign(g) P_(b_v)/2
  -> -sign(g) P_(b_(2|g|))/2
```

in operator norm. This finite part is rank one and compact. Thus the
fixed-grade data occupy a compact correction after the escaping bulk
is removed. The norm limit follows from coordinatewise convergence
`b_(v+2|g|) -> b_(2|g|)` and domination by the square-summable
`b_(2|g|)`, followed by continuity of `x -> P_x` in operator norm.
A bounded transport preserving compactness cannot turn
this correction into the nonzero Sonin Calkin class; any such passage
must use additional source structure or a controlled singular map.

## Interpretation and open gate

The source's failure to lie in prime `ell^2` at the critical boundary
is mass escape to primes of logarithmic size `1/v`, not disappearance
of the source. The tangent representation retains that mass. It
retains a nontrivial grade magnitude only under simultaneous grade
scaling; at a fixed off-line grade its limit is universal. The Xi-seam
endpoint concerns a *fixed* off-line spectral grade as the prime
cutoff grows. A route must derive a source-faithful transport
from fixed grade into this moving tangent regime, preserve a
zero-specific observable, and obtain the required cofinal bound.
Neither (1)--(6) nor the change of carrier provides that transport.
