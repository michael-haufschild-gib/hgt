# Infinitesimal Hardy leakage resolves a static horizontal layer

- **ID:** `infinitesimal-hardy-leakage-horizontal-layer-resolvent`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper), `[PROVED HERE; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `euler-hardy-leakage-offline-zero-rank.md`;
  `shifted-hardy-leakage-static-continuity-no-go.md`
- **Statement:** The unnormalized shifted Hardy leakage of a fixed off-line layer vanishes linearly,
  not invisibly.  After division by the transverse shift it converges in operator norm to a
  positive finite-rank Laplace--Hankel operator.  Its trace is the inverse-displacement sum
  `sum_j m_j/a_j`, and first-order normalization is the unique power normalization with a finite
  nonzero static limit.

## Setup

For `a>0`, put

```text
b_a(z)=(z-i a)/(z+i a).
```

Fix distinct displacements `a_1,...,a_r>0` and multiplicities `m_1,...,m_r>=1`.  For

```text
0<omega<min_j a_j
```

define the finite Blaschke products

```text
A_omega=product_j b_(a_j+omega)^(m_j),
B_omega=product_j b_(a_j-omega)^(m_j),
phi_omega=A_omega conjugate(B_omega)
```

on the real boundary of the upper half-plane.  Let

```text
L_omega=P_- M_(phi_omega)|H^2_+.
```

This is the local shifted-quotient model of all right-hand zero layers at one fixed ordinate, after
translating that ordinate to the origin.  The factors at `a_j-omega` are the denominator poles and
the factors at `a_j+omega` are their matched numerator zeros.

## Theorem A: the first-order leakage limit

There is operator-norm convergence

```text
omega^(-1) L_omega -> T_A,                               (1)
```

where, after the Paley--Wiener identification of `H^2_+` and the reflected `H^2_-` with
`L^2(0,infinity)`, `T_A` is the positive finite-rank integral operator

```text
(T_A f)(x)
 = integral_0^infinity
     2 sum_j m_j exp(-a_j(x+y)) f(y) dy.                 (2)
```

Consequently

```text
rank(T_A)=r,
trace(T_A)=sum_j m_j/a_j,                                (3)
||T_A||>=max_j m_j/a_j.                                  (4)
```

Repeated copies at the same displacement increase the positive coefficient and trace but not the
rank; distinct displacements give linearly independent exponential modes.

### Proof

The map `a |-> b_a` is differentiable in the boundary `L^infinity` norm on every compact subinterval
of `(0,infinity)`.  Since `phi_0=1`, finite product differentiation gives

```text
d/domega phi_omega(x)|_(omega=0)
 = sum_j m_j 2 partial_(a_j) log b_(a_j)(x)
 = sum_j m_j
     (-2i/(x-i a_j)-2i/(x+i a_j)).                      (5)
```

The second rational summand in each parenthesis is the boundary value of a function analytic in the
upper half-plane, so its Hankel compression is zero.  Therefore differentiation commutes with the
bounded multiplication and Hardy-projection maps and yields

```text
T_A=H_psi,
psi(x)=sum_j -2i m_j/(x-i a_j).                          (6)
```

Use the unitary Fourier transform

```text
F(f)(t)=(2pi)^(-1/2) integral_R exp(-ixt)f(x)dx.
```

The transform of the `j`th summand in `(6)` is

```text
2 sqrt(2pi) m_j exp(a_j t) 1_(t<0).
```

If the input Fourier variable is `y>0` and the reflected output variable is `x>0`, the convolution
formula for multiplication therefore gives the kernel

```text
2 m_j exp(-a_j(x+y)).                                    (7)
```

Summing `(7)` proves `(2)`.  It is a sum of positive rank-one operators

```text
2m_j |exp(-a_j dot)><exp(-a_j dot)|.
```

The exponentials at distinct positive rates are linearly independent, so the rank is `r`.  The
trace is

```text
sum_j 2m_j integral_0^infinity exp(-2a_j x)dx
 = sum_j m_j/a_j,
```

and positivity gives `(4)` by retaining any one rank-one summand.  This proves `(1)`--`(4)`.

## Theorem B: unique static power normalization

For real `alpha`, suppose at least one layer is present.  Then

```text
alpha<1  ->  omega^(-alpha)L_omega -> 0,
alpha=1  ->  omega^(-alpha)L_omega -> T_A,
alpha>1  ->  ||omega^(-alpha)L_omega|| -> infinity.       (8)
```

### Proof

Equation `(1)` says

```text
L_omega=omega T_A+o(omega)
```

in operator norm, with `T_A!=0`.  Multiplication by `omega^(-alpha)` proves all three cases.

## Corollary: the critical-strip threshold

For a nontrivial zeta zero at horizontal displacement

```text
a=Re rho-1/2>0,
```

one has `0<a<1/2`.  Hence one uncancelled layer of multiplicity `m` forces

```text
||T_A||>=m/a>2m>=2.                                      (9)
```

Thus, for an ordinate-localized infinitesimal leakage operator, the source-side estimate

```text
||T_A||<=2                                                (10)
```

would exclude every off-line zero at that ordinate.  The strict inequality in `(9)` uses the
classical zero-free line `Re s=1`.

## What this changes in Route C

The static-continuity no-go remains correct for `L_omega` itself, but it does not close the leakage
mechanism.  The vanishing law

```text
||L_omega||=O(omega)
```

contains a nonzero first-order coefficient.  The normalized coefficient is positive at a fixed
ordinate, amplifies a layer as it approaches the critical line, and has an absolute threshold fixed
by the width of the critical strip.  It therefore survives the rank-one falsifier that killed bare
continuity.

The theorem does not yet prove RH.  Constructing the fixed-ordinate block from the global Euler
source without first selecting a zero ordinate, and proving `(10)` directly from that source, are
both open.  A global one-dimensional Hankel sum also mixes different ordinates by oscillatory
exponentials, so positivity of `(2)` cannot simply be asserted before an ordinate-diagonal
projection is constructed.

## Scientific-novelty verdict

`[NOT NEW SCIENTIFIC KNOWLEDGE]` The calculation is a finite Blaschke-product derivative followed by
the classical Paley--Wiener realization of a rational finite-rank Hankel operator.  Positivity and
the trace formula are standard Laplace Gram calculus.  The theorem is decisive route control, but
it fails the parent-theory and anti-theatre gates.

Scientific novelty would begin with a source-defined, ordinate-diagonal first-order leakage object
whose norm or trace obeys an unconditional absolute bound not obtained by reading the Xi divisor.

## Gates

- [x] 0 -> 1: the first-order normalization and its falsifier isolated.
- [x] 1 -> 2: operator-norm limit, positive kernel, rank, trace, unique scaling, and strip threshold
  proved on paper.
- [ ] 2 -> 3: no Lean formalization selected; the existing formal tree lacks Hardy projections and
  Paley--Wiener Hankel operators, and a scalar wrapper would not formalize the theorem.
- [ ] 3 -> 4: the theorem is standard parent theory and is not a publication target by itself.
