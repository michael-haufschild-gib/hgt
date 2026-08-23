# Li remote-quartet transverse visibility law

- **ID:** `li-remote-quartet-transverse-visibility-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; Li/Keiper; remote-divisor detection
- **Statement:** An off-critical quartet at height `T` and displacement `a` has exact Li profile
  `4(1-cosh(n ell) cos(n theta))`, where `ell ~ a/T^2` and `theta ~ 1/T`.  Hence every prefix
  `n=o(T^2/a)` remains positive on an explicit same-HT-field carrier, while a negative coefficient
  occurs by order `O((T^2/a) log(T^2/a))`.

## Goal

Replace the qualitative statement “every fixed finite Li prefix misses a remote quartet” by its
sharp transverse scale.  The Li map mixes two distinct effects:

1. an angular clock with scale `n asymp T`; and
2. a radial off-line defect with scale `n asymp T^2/a`.

Only the second sees horizontal displacement.  The theorem identifies its exact finite-size
profile inside one order-one HT differential-translation field.

## The quartet coordinate

Let

```text
rho = 1/2-a+iT,       0<a<1/2,  T>1/2,
q   = 1-1/rho = (rho-1)/rho.
```

Write

```text
q = exp(ell+i theta),       ell>0,  0<theta<pi/2.             (1)
```

Put `beta=1/2-a`.  Direct multiplication by `conj(rho)` gives

```text
q = [T^2-beta(1-beta)+iT]/[T^2+beta^2].                       (2)
```

Consequently

```text
ell
  = (1/2) log(1 + 2a/(T^2+(1/2-a)^2)),                       (3)

tan(theta)
  = T/(T^2-1/4+a^2).                                         (4)
```

For arbitrary sequences `T->infinity` and `0<a=a_T<1/2`, equations (3)--(4) imply uniformly

```text
ell T^2/a -> 1,
theta T   -> 1,
ell/theta -> 0.                                               (5)
```

Thus the transverse visibility parameter is

```text
H_(a,T) := 1/ell ~ T^2/a.                                    (6)
```

## Exact quartet Li profile `[PROVED HERE]`

For a symmetry-complete divisor, define the divisor-normalized Li sums by symmetric pairing,

```text
lambda_n(F) = sum_rho [1-(1-1/rho)^n].                        (7)
```

The functional-equation partner of `rho` has Mobius coordinate `q^(-1)`, while conjugation gives
`conj(q)` and `conj(q)^(-1)`.  Therefore the full quartet contribution is

```text
L_n(a,T)
  = 4-[q^n+q^(-n)+conj(q)^n+conj(q)^(-n)]
  = 4[1-cosh(n ell) cos(n theta)].                            (8)
```

Define its unitarized shadow by deleting only the radial defect,

```text
U_n(a,T) = 4[1-cos(n theta)] >= 0.                            (9)
```

Then the exact transverse difference is

```text
L_n-U_n = -4 cos(n theta)[cosh(n ell)-1].                     (10)
```

In particular, for every integer `N>=1`,

```text
sup_(1<=n<=N) |L_n-U_n|
  <= 4[cosh(N ell)-1],                                       (11)

L_n >= -4[cosh(N ell)-1],       1<=n<=N.                     (12)
```

Equations (8)--(12) isolate the transverse information exactly.  Angular oscillation may already
occur at degree `T`, but the difference between an off-line quartet and its unit-circle shadow is
small until degree `T^2/a`.

## Same-field HT realization

Fix `alpha>0` with `2 alpha-1 notin Z`, and let

```text
C_alpha(s)
  = 1/(Gamma(alpha+i(s-1/2)) Gamma(alpha-i(s-1/2))).          (13)
```

The reflected-gamma carrier theorem proves that `C_alpha` is entire of exact order one,
FE/Schwarz-symmetric, hypertranscendental over `C(s)`, and has precisely the simple critical-line
zeros

```text
1/2 +/- i(alpha+k),       k=0,1,2,... .                       (14)
```

With `w=s-1/2`, define the normalized rational gauge

```text
R_(a,T)(s)
  = ((w^2-(a+iT)^2)(w^2-(a-iT)^2))/(a^2+T^2)^2,

F_(a,T) = R_(a,T) C_alpha.                                   (15)
```

The gauge inserts exactly the quartet containing `rho`, preserves both scalar symmetries, and
tends to `1` with every derivative on compact sets.  Every `F_(a,T)` is entire of exact order one
and HT.  Since every translate of `R_(a,T)` is an invertible rational function,

```text
C(s)(D^m T_h F_(a,T) : h in C, m>=0)
  = C(s)(D^m T_h C_alpha : h in C, m>=0).                    (16)
```

The complete differential-translation field is therefore literally unchanged.  The Li sums obey

```text
lambda_n(F_(a,T)) = lambda_n(C_alpha) + L_n(a,T).             (17)
```

## Linear Li margin of the all-line carrier `[PROVED HERE]`

For a critical-line pair `1/2 +/- i gamma`, put

```text
z_gamma = 1-1/(1/2+i gamma),       |z_gamma|=1.
```

Its paired Li contribution is

```text
B_n(gamma) = 2-2 Re(z_gamma^n) = |1-z_gamma^n|^2.             (18)
```

Since `|1-z^n|<=n|1-z|` on the unit circle and

```text
|1-z_gamma|^2 = 1/(gamma^2+1/4),
```

one has

```text
0<=B_n(gamma)<=min(4,n^2/(gamma^2+1/4)).                      (19)
```

Summing (19) over `gamma=alpha+k`, split at `gamma=n`.  There are `O_alpha(n)` terms below the
split, and the tail is bounded by

```text
n^2 sum_(alpha+k>n) (alpha+k)^(-2) = O_alpha(n).
```

Hence

```text
lambda_n(C_alpha) <= C_alpha^+ n.                             (20)
```

For the matching lower bound, the phase of `z_gamma` is

```text
vartheta_gamma = 2 arctan(1/(2 gamma)).                       (21)
```

For all sufficiently large `n` and every `gamma in [n,2n]`, elementary bounds for `arctan` give

```text
1/4 <= n vartheta_gamma <= 1.                                 (22)
```

There are `n+O_alpha(1)` carrier ordinates in this interval, and each contributes at least
`2-2 cos(1/4)>0`.  Therefore

```text
C_alpha^- n <= lambda_n(C_alpha) <= C_alpha^+ n               (23)
```

for all sufficiently large `n`, with `C_alpha^->0`.  Every individual coefficient is strictly
positive: for fixed `n`, the phases in (21) tend to zero but are nonzero, so infinitely many terms
in (18) are positive.  Combining this with (23),

```text
m_alpha := inf_(n>=1) lambda_n(C_alpha) > 0.                  (24)
```

## Subcritical prefix-blindness theorem `[PROVED HERE]`

Let `a_T in (0,1/2)`, `T->infinity`, and let `N_T` be positive integers satisfying

```text
N_T a_T/T^2 -> 0.                                            (25)
```

By (5), this is equivalent to `N_T ell_T->0`.  Equations (12), (17), and (24) give uniformly for
`1<=n<=N_T`,

```text
lambda_n(F_(a_T,T))
  >= m_alpha-4[cosh(N_T ell_T)-1] > 0                         (26)
```

for all sufficiently large `T`.

Thus a Li prefix growing at any rate `o(T^2/a_T)` remains wholly positive although the carrier has
an off-critical quartet, and although order, scalar symmetries, HT, and the complete
differential-translation field are all fixed.

## Universal critical profile `[PROVED HERE]`

Let integers `n_T` satisfy

```text
n_T a_T/T^2 -> c in [0,infinity),
n_T theta_T -> phi modulo 2 pi.                              (27)
```

Then (5) gives `n_T ell_T->c`, and (8) yields the universal two-scale limit

```text
L_(n_T)(a_T,T) -> 4[1-cosh(c) cos(phi)].                      (28)
```

The radial coordinate `c` is the off-line signal; `phi` is the independent Li clock phase.

The scale is sharp.  Fix `c>0`.  Let `x_T=c/ell_T`.  Choose a multiple `2 pi m_T/theta_T` nearest
to `x_T`, and then choose an integer `n_T` nearest to that multiple.  Then

```text
|n_T-x_T| <= pi/theta_T+1/2,
dist(n_T theta_T,2 pi Z) <= theta_T/2.                        (29)
```

Because `ell_T/theta_T->0`, equations (29) imply

```text
n_T ell_T->c,
n_T theta_T->0 modulo 2 pi,
n_T ~ c T^2/a_T.                                             (30)
```

Along this phase-aligned sequence,

```text
L_(n_T)(a_T,T) -> 4[1-cosh(c)] < 0.                           (31)
```

Thus order `T^2/a_T` is exactly where an order-one transverse negative signal becomes available;
it is not merely an upper estimate.

## A negative total Li coefficient by the logarithmic overhead `[PROVED HERE]`

Let `H_T=1/ell_T`, and repeat the alignment construction with

```text
c_T=4 log H_T.                                                (32)
```

Then there are integers `n_T` such that

```text
n_T=(4+o(1)) H_T log H_T,
dist(n_T theta_T,2 pi Z)<=theta_T/2.                          (33)
```

Equations (8), (32), and (33) give

```text
L_(n_T)(a_T,T) = -2 H_T^4(1+o(1)).                           (34)
```

On the other hand, (20) gives

```text
lambda_(n_T)(C_alpha)=O_alpha(H_T log H_T).                   (35)
```

Therefore, by (17),

```text
lambda_(n_T)(F_(a_T,T))<0                                    (36)
```

for all sufficiently large `T`.  Since `H_T~T^2/a_T`, one may take

```text
n_T = O((T^2/a_T) log(T^2/a_T)).                              (37)
```

The extra logarithm is not the transverse crossover.  It is a sufficient overhead for the remote
quartet's exponential radial term to dominate the carrier's linear positive Li background.

## Exact route consequence

The theorem excludes any implementation that tries to replace the all-order Li criterion by a
prefix of degree `o(T^2/a)` while retaining only DA-gauge-invariant HT information.  Such a prefix
can remain completely positive on a same-field, order-one, symmetry-complete HT carrier with an
off-line quartet at height `T` and displacement `a`.

The full Li criterion is not excluded.  It escapes by using coefficients at the transverse scale
and beyond.  The theorem instead identifies the exact complexity bill:

```text
phase resolution:          n asymp T,
horizontal resolution:     n asymp T^2/a,
guaranteed total sign flip: n=O((T^2/a) log(T^2/a)).
```

Hence accurate positivity of a very long but subcritical prefix is not evidence that the HT
carrier's divisor is on the line.  A successful Li proof must control every coefficient, or supply
a separate source theorem that uniformly rules out remote defects before this scale.

## Parent-theory and novelty audit

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

Bombieri--Lagarias already prove the Li multiset criterion and its relation to Weil positivity.
Voros' exponential-asymptotic analysis explicitly identifies the off-line saddle as becoming
relevant when the coefficient order is the inverse imaginary part of the reciprocal centered zero;
for `rho=1/2-a+iT`, this is asymptotic to `T^2/a`.  The exact cosh--cos profile, uniform subcritical
prefix theorem, and same-HT-field realization are useful quantitative packaging, but follow by
elementary polar decomposition, rational gauge invariance, and an arithmetic-progression carrier.
They fail the parent-theory and anti-theatre novelty gates.

Primary comparisons:

- E. Bombieri and J. C. Lagarias, *Complements to Li's Criterion for the Riemann Hypothesis*, J.
  Number Theory 77 (1999), 274--287, DOI `10.1006/jnth.1999.2392`.
- A. Voros, *Sharpenings of Li's criterion for the Riemann Hypothesis*, Math. Phys. Anal. Geom. 9
  (2006), 53--63, arXiv:math/0506326.
- A. Voros, *Zeta functions over zeros of Zeta functions and an exponential-asymptotic view of the
  Riemann Hypothesis*, arXiv:1403.4558, especially Section 3.2.

## Lean status

The formal tree contains the finite Li/secular change of basis, polynomial quartet gauges, real
hyperbolic identities, and asymptotic infrastructure.  It does not contain the reflected-gamma HT
carrier, its divisor-summed Li series with two-sided linear bounds, or the phase-alignment selection
as one unconditional theorem.  Formalizing only (8) would be a partial algebraic anchor and would
not justify stage 3.

## Gates

- [x] 0 -> 1: exact visibility parameter and candidate profile isolated
- [x] 1 -> 2: exact quartet law, uniform prefix theorem, critical profile, and sign-flip upper scale
  proved unconditionally
- [x] primary Li/Voros literature audit; classified as a bridge
- [ ] 2 -> 3: complete unconditional claim formalized in Lean
- [ ] 3 -> 4: closed by failed novelty gate

## Log

- 2026-07-09 -- Backlog conjecture isolated the candidate scale `T^2/a`.
- 2026-07-11 -- Proved the exact cosh--cos quartet profile and separated angular from transverse
  visibility.
- 2026-07-11 -- Proved positive survival for every `o(T^2/a)` prefix inside one exact HT field and
  a negative total coefficient by order `O((T^2/a) log(T^2/a))`.
- 2026-07-11 -- Voros comparison source-killed scientific novelty; retained as a precise Li-route
  bridge.

## Lean status update (2026-08-23)

`formal/GaloisForLFunctions/RHTower/LiRemoteQuartetProfile.lean` now formalizes the complete exact
finite-profile layer.  It proves the Cartesian Möbius-coordinate identity `(2)`, the squared radial
identity underlying `(3)`, positivity of the logarithmic radial coordinate, and
`exp(2 ell)=|q|²`.  For every polar coordinate `q=exp(ell+i theta)` it then proves the literal
symmetry-complete Li identity `(8)`, the nonnegative unitarized shadow `(9)`, exact transverse
difference `(10)`, uniform prefix estimate `(11)`, lower bound `(12)`, and strict negativity under
exact phase alignment.

`formal/GaloisForLFunctions/RHTower/LiRemoteQuartetAsymptotics.lean` now closes the full coordinate
asymptotics `(5)` for arbitrary filters, cofinal height families, and varying displacements in
`(0,1/2)`: `ell*T²/a -> 1`, `theta*T -> 1`, and `ell/theta -> 0`.  It also formalizes convergence
modulo `2*pi` and proves the universal two-scale limit `(27)`--`(28)`.

Both exact leaf targets build successfully and every new theorem audits to only `propext`,
`Classical.choice`, and `Quot.sound`.  Remaining stage-3 gates are the reflected-Gamma carrier's
divisor-summed two-sided linear Li bounds `(20)`--`(24)`, the same-differential-translation-field
assembly `(16)`--`(17)`, the constructive phase-alignment selection `(29)`--`(33)`, and final
total-coefficient domination `(34)`--`(37)`.  No hypothesis wrapper has been introduced; card
remains at stage 2.
