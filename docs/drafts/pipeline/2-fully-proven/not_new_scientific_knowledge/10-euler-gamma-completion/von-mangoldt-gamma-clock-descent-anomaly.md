# The full von Mangoldt source has the exact Gamma clock descent anomaly

- **ID:** `von-mangoldt-gamma-clock-descent-anomaly`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper) / FULL PRIME-POWER AFFINE HT COLLIGATION
- **Scientific status:** `[PROVED HERE] [BRIDGE] [FINITE ALGEBRAIC CORE FORMALIZED] [NOT AN RH PROOF]`
- **Parents:**
  `prime-laplace-gamma-clock-descent-anomaly.md`,
  `../../1-in-progress/source-anomaly-boundary-colligation-field.md`,
  `../../3-formalized/not_new_scientific_knowledge/ccm-complex-polar-prime-mellin-colligation.md`
- **Statement:** The resolved von Mangoldt prime-power channel carries a canonical Hilbert scale on
  which coefficient translation is a contraction, every finite Gamma-jet observation is
  Hilbert--Schmidt, and the observations are jointly faithful.  The finite Gamma Taylor shadow
  fails to intertwine source translation by exactly the omitted Taylor tail; its adjacent-depth
  Bianchi defect is the rank-one factorial Gamma boundary current.  The Euler unit field is the
  nonnormal boundary of this source scale, not a vector in its interior.

## The prime-power source Hilbert space

Index prime powers by

```text
P={(p,k): p prime, k>=1},
q_(p,k)=(log p)/p^k.                                      (1)
```

Let

```text
H_VM={a:P->C: sum_(p,k)q_(p,k)|a_(p,k)|^2<infinity}.      (2)
```

For `a in H_VM` and `Re z>0`, define

```text
F_a(z)=sum_(p,k)q_(p,k)a_(p,k)p^(-kz).                   (3)
```

For every `x>0` and `j>=0`,

```text
sum_(p,k)q_(p,k)(k log p)^(2j)p^(-2kx)<infinity.         (4)
```

Indeed `(4)` is the absolutely convergent von Mangoldt derivative series at `1+2x`; any
logarithmic power is absorbed by a smaller positive abscissa margin.  Cauchy--Schwarz therefore
gives local uniform convergence of `(3)` and all its derivatives:

```text
F_a^(j)(z)
 =sum_(p,k)q_(p,k)a_(p,k)(-k log p)^j p^(-kz).           (5)
```

Thus `(3)` is holomorphic on the whole right half-plane.

## Source translation and finite Gamma observation

Define the bounded source operation

```text
(S a)_(p,k)=p^(-k)a_(p,k).                               (6)
```

It is a strict coordinatewise contraction and satisfies the exact source law

```text
F_(S a)(z)=F_a(z+1).                                    (7)
```

Fix `x_0>1`.  At depth `N>=1`, let

```text
(J_N a)_i=F_a^(i)(x_0),             0<=i<N.              (8)
```

Equation `(4)` makes every row of `J_N` a vector in `H_VM`; since there are finitely many rows,
`J_N` is Hilbert--Schmidt.

The complete observation tower is faithful.  If `J_N a=0` for every `N`, all derivatives of
`F_a` vanish at `x_0`, so the identity theorem gives `F_a=0` on `Re z>0`.  Uniqueness of ordinary
Dirichlet series then gives

```text
q_(p,k)a_(p,k)=0
```

at every prime power, and positivity of `q_(p,k)` gives `a=0`.

Let the finite Gamma shadow be unit Taylor translation

```text
(E_N y)_i=sum_(h=0)^(N-1-i)y_(i+h)/h!.                  (9)
```

## Exact descent anomaly

The disk of radius greater than one around `x_0` lies in the right half-plane.  Taylor's theorem,
`(5)`, and `(7)` give

```text
F_(S a)^(i)(x_0)
 =F_a^(i)(x_0+1)
 =sum_(h>=0)F_a^(i+h)(x_0)/h!.                          (10)
```

Define

```text
alpha_N=E_N J_N-J_N S.                                  (11)
```

Then the complete coordinate formula is

```text
(alpha_N a)_i
 =-sum_(h>=N-i)F_a^(i+h)(x_0)/h!.                       (12)
```

All sums converge absolutely.  Hence the finite Gamma clock is not an exact descent of the
prime-power source operation, but its failure is a canonical analytic tail rather than an
unspecified comparison defect.

## Adjacent-depth Bianchi current

Let `pi_N:C^(N+1)->C^N` forget the highest derivative.  Subtracting the tails in `(12)` yields

```text
pi_N alpha_(N+1)-alpha_N
 =kappa_N J_(N+1),                                      (13)
```

where

```text
(kappa_N y)_i=y_N/(N-i)!.                               (14)
```

Every term cancels except the derivative newly exposed at depth `N`.  Equation `(14)` is exactly
the already-formalized rank-one factorial Gamma boundary transfer.  Thus

```text
(S,J_N,E_N,alpha_N,kappa_N)                              (15)
```

is the full prime-power affine anomaly-colligation skeleton required by the general HT boundary
theory.

## Coherent cone orientation of the anomaly

The anomaly has more structure than rank-one Bianchi coherence.  Put

```text
lambda_(p,k)=k log p,
R_m(lambda)=1/(m-1)! integral_0^lambda
  exp(-t)(lambda-t)^(m-1)dt,                m>=1.        (15a)
```

For the coordinate vector `e_(p,k)` and `0<=i<N`, the finite anomaly is

```text
(alpha_N e_(p,k))_i
 =q_(p,k) exp(-x_0 lambda) (-lambda)^i
   [sum_(h=0)^(N-1-i)(-lambda)^h/h!-exp(-lambda)].      (15b)
```

Taylor's integral remainder gives

```text
(-1)^(N+1)(alpha_N e_(p,k))_i
 =q_(p,k) exp(-x_0 lambda) lambda^i R_(N-i)(lambda)>0.  (15c)
```

The sign is independent of both `i` and `(p,k)`.  The derivative parity `(-1)^i` and the omitted
Taylor-tail parity `(-1)^(N-i+1)` cancel to the single depth orientation `(-1)^(N+1)`.
Consequently the oriented anomaly maps the positive prime-power cone into the positive jet cone at
every depth.  This is a source-specific positivity statement; it is not true for an arbitrary
analytic jet packet with signed spectral weights.

Laplace transformation in the positive base-point variable gives explicit right-half-plane
Cauchy features:

```text
A_(N,i)(w;p,k)
 =sqrt(q_(p,k)) lambda_(p,k)^i R_(N-i)(lambda_(p,k))
   /(w+lambda_(p,k)),                         Re w>0.    (15d)
```

At every positive radial damping, the matrices

```text
sum_(i<N) sum_(p,k)
  A_(N,i)(w_j;p,k) conjugate(A_(N,i)(w_l;p,k))           (15e)
```

are positive semidefinite.  Thus the full prime-power/Gamma anomaly supplies an explicit positive
finite square root in Cauchy coordinates.  The undamped Euler-boundary limit of `(15e)` is not
asserted to exist: the unit coefficient field is outside `H_VM`.  The correct limit must first
cancel the causal and shifted-polar channels in a reduced anomaly complex and only then pass to
the nonnormal boundary.

## Euler unit field and the thin boundary

The constant coefficient field `one_(p,k)=1` is not a vector of `H_VM`, because

```text
sum_(p,k)q_(p,k)=sum_(n>=2)Lambda(n)/n=infinity.         (16)
```

For every `theta>0`, however,

```text
a^theta_(p,k)=p^(-k theta)                               (17)
```

belongs to `H_VM`, and

```text
F_(a^theta)(z)
 =sum_(n>=2)Lambda(n)n^(-(1+theta+z))
 =-zeta'(1+theta+z)/zeta(1+theta+z).                    (18)
```

The limit `theta down to 0` is therefore the actual Euler unit current, but it lies on the
nonnormal boundary of the Hilbert scale.  Each finite observation and anomaly has a radial
interior representative, while no bounded single-carrier limit contains the unit field.

This is a literal zeta realization of the general HT geometry:

```text
every finite clock comparison is Hilbert--Schmidt and faithful;
the complete source section escapes the Hilbert carrier;
the escape is retained by a rank-one boundary current at every depth. (19)
```

## Squarefree completed current

The same construction applies linearly to

```text
J_sq(s)=A(s)-2A(2s).                                    (20)
```

The first summand uses `(18)`.  The second is its frequency-doubled pullback and is holomorphic
throughout the strict right half-plane relevant to the Ward localization.  Consequently `(15)`
is the affine prime-power clock skeleton for the completed squarefree current whose anti-causal
normal is `ell_E`; it does not yet prove that the radial anomaly tower has a conservative Hardy
limit.

## No-go and positive successor

The theorem kills two shortcuts.

1. **No exact finite descent:** `alpha_N` is generally nonzero at every depth.
2. **No fixed factorial-Fock colimit:** the actual unit Euler field is outside `H_VM`.

The positive successor is stronger than either negative statement.  The source operation,
Hilbert scale, faithful observations, finite Gamma shadow, complete analytic anomaly, and
rank-one Bianchi current are all canonical and explicit.  The remaining Ward theorem is exactly
to construct their source-rigged affine characteristic transform and prove the Gauss--Ward Gram
factorization before taking `theta down to 0`.

If that transform fails, the failure is a coherent affine Ward-defect field on the nonnormal
Euler boundary.  This is additional general HT structure not recorded by the metric capacity
path alone.

## Gates

- [x] canonical full prime-power Hilbert scale constructed
- [x] holomorphic source transform and all derivatives justified
- [x] source translation proved contractive and identified with unit argument translation
- [x] finite Gamma observations proved Hilbert--Schmidt
- [x] complete observation tower proved faithful
- [x] omitted-tail descent anomaly computed exactly
- [x] adjacent-depth factorial Bianchi current computed exactly
- [x] Euler unit field identified as the nonnormal radial boundary
- [x] squarefree-current specialization stated
- [x] formalize the finite observation/anomaly/Bianchi package in Lean
- [x] finite coherent-cone orientation formalized in
      `RHTower/VonMangoldtGammaFiniteApertureOrientation.lean` and
      `RHTower/VonMangoldtGammaPointedWardReconstruction.lean`
- [x] finite Beta-integral remainder identity formalized in
      `RHTower/VonMangoldtGammaFactorialBetaReflection.lean`
- [ ] construct the source-rigged affine characteristic transform
- [ ] prove its Gauss--Ward factorization and pass to the Euler boundary
