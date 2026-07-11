# Prime-shift unique continuation for the CCM screw null equation

- **ID:** `ccm-prime-shift-screw-null-unique-continuation`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / DIRECT CCM RH CORE
- **Scientific status:** `[CONJECTURE] [OPEN CORE] [NOT AN RH PROOF]`
- **Source:** Suzuki's compact screw operator, the exact prime-power atomic kernel, and the CCM
  aperture Morse-index conservation law
- **Statement:** Every compactly supported mean-zero solution of the anchored
  archimedean-plus-prime shift null system is zero. Equivalently, the compact CCM screw operator is
  injective at every aperture, which proves RH.

## 1. Exact null equation

Fix `a>0`. Let `u in L2_0(-a,a)` and extend it by zero to the real line. Suzuki's compact operator
has the truncated-convolution form

```text
(G_a u)(x)=integral_(-a)^a g(x-y)u(y)dy,       |x|<a.    (1)
```

The screw kernel is even. Distributionally,

```text
K=-g''
 =K_infinity
  -sum_(n>=2) Lambda(n)n^(-1/2)
     (delta_(log n)+delta_(-log n)),                     (2)
```

where `K_infinity` is the completed pole--Gamma distribution. Away from the origin its regular
part is

```text
K_infinity(t)
 =exp(|t|/2)-exp(-5|t|/2)/(1-exp(-2|t|)),       t!=0.    (3)
```

If `G_au=0`, differentiating `(1)` twice on the open aperture gives the exact distributional
constraint

```text
(K_infinity*u)(x)
 =sum_(2<=n<exp(2a)) Lambda(n)n^(-1/2)
    (u(x-log n)+u(x+log n)),       |x|<a.                (4)
```

Terms with `log n>=2a` vanish because the zero-extended supports do not overlap. No prime cutoff is
chosen: `(4)` contains precisely every prime power visible to the aperture.

Differentiation loses the affine kernel of the second derivative. Therefore the exact null system
also retains two anchors, for example

```text
(G_a u)(0)=0,
(G_a u)(a/2)=0.                                        (4a)
```

Conversely, `(4)` says that `G_au` has zero second distributional derivative on `(-a,a)`, hence is
affine there. Since the screw kernel is continuous, these point values are defined. The two
conditions `(4a)` kill that affine function. Thus `(4)` plus `(4a)` is
equivalent to `G_au=0`; `(4)` alone is only necessary.

Suzuki--Yoshida and `ccm-aperture-morse-index-conservation-law.md` give

```text
RH
 iff ker G_a={0} for every a>0
 iff the anchored system (4)--(4a) has no nonzero mean-zero
     compactly supported solution.                              (5)
```

Thus `(4)` is the direct CCM core, not an auxiliary sufficient condition.

## 2. Why the equation is structurally different from a flow

The anchored system `(4)`--`(4a)` is one static compatibility constraint among three carriers:

```text
archimedean logarithmic pseudodifferential channel
  + finite faithful prime-shift module
  + hard aperture support boundary.                       (6)
```

The translations commute in the ambient line. Their nontrivial geometry enters only because the
zero extension and the aperture restriction do not commute with them. This is the same boundary
noncommutation forced by the pole-to-divisor capacity theorem.

At aperture `a`, the distinct prime rays have rational rank `pi(exp(2a))`. Prime powers on one ray
are dependent, but two different rays have disjoint shift labels by unique factorization.

## 3. Candidate mechanisms

### A. Log-elliptic support rigidity `[CONJECTURE]`

The Fourier symbol of `K_infinity` grows like `log|xi|`, whereas the right side of `(4)` is a finite
sum of unitary translations. Localize inside `(-a,a)` and seek an iterated logarithmic-elliptic
estimate strong enough to place `u` in a quasi-analytic class. The zero extension would then be
flat across an exterior interval and force `u=0`.

The required estimate must be genuinely quasi-analytic. Membership in every logarithmic Sobolev
space is not enough.

`[PROVED ATTACK]` Pure logarithmic elliptic bootstrapping cannot supply that conclusion. For every
nonzero `v in C_c^infinity(-a,a)` and every integer `k>=0`,

```text
(log(2+|D|))^k v in L2(R).                               (7)
```

Thus

```text
intersection_(k>=0)D((log(2+|D|))^k)                    (8)
```

already contains nonzero compactly supported functions and is not quasi-analytic. Any successful
version of mechanism A must extract super-logarithmic derivative bounds from the coupled prime and
boundary relations, not merely iterate the archimedean symbol.

### B. Boundary-shell prime peeling `[CONJECTURE]`

Order the finitely many visible shift lengths. On a thin interval adjacent to `a`, half of each
translation pair vanishes by support. Compare the equations after translating by two
rationally-independent prime logs. The goal is to peel the outer support shell and iterate inward.

The archimedean term is nonlocal, so the peeling must use a simultaneous cancellation identity or
a boundary value of its Wiener--Hopf factorization; treating it as a local remainder is invalid.

### C. Two-direction periodic-pencil weld `[CONJECTURE]`

If the boundary-shell relations generate an exact nonpure Stanley--Reisner annihilator, the
periodic-pencil theorem forces at least two genuine analytic directions and constructs the optimal
dimension-two HT realization. One direction would carry the Euler shift module and the other the
reflected boundary relation.

This mechanism is conditional on first proving the exact relation complex. Two Hardy
polarizations of one variable do not satisfy that hypothesis by themselves.

### D. Singular finite-interval Wiener--Hopf factorization `[OPEN CORE]`

Let `m_infinity` be the real even Fourier symbol of `K_infinity`. The full-line symbol associated
with the interior equation is

```text
M_a(xi)
 =m_infinity(xi)
  -2 sum_(2<=n<exp(2a)) Lambda(n)n^(-1/2)cos(xi log n).  (9)
```

Equation `(4)` is equivalent to a support-separated relation

```text
M_a(D)u=r,
supp u subset [-a,a],
supp r subset (-infinity,-a] union [a,infinity).        (10)
```

This is a finite-interval Wiener--Hopf problem, not a global multiplier equation. The two anchors
`(4a)` remain part of the boundary data and cannot be recovered from `(10)` alone.

`[PROVED ATTACK]` For every sufficiently large `a`, `M_a` has real characteristic zeros. Indeed,

```text
M_a(0)
 =m_infinity(0)
  -2 sum_(n<exp(2a))Lambda(n)n^(-1/2) ->-infinity,       (11)
```

since partial summation with the prime number theorem gives

```text
sum_(n<X)Lambda(n)n^(-1/2)~2sqrt(X).                    (12)
```

For fixed `a`, the prime cosine polynomial in `(9)` is bounded, while the Gamma symbol satisfies

```text
m_infinity(xi)=log|xi|+O(1) ->+infinity.                (13)
```

Continuity and evenness therefore give at least one pair of real zeros. The scalar symbol is not
bounded away from zero, so a canonical zero-free scalar Wiener--Hopf factorization cannot prove
injectivity. A surviving factorization must retain the real characteristic crossings and prove
that their finite-interval boundary Evans determinant never vanishes, or replace the scalar symbol
by a source-selected matrix relation.

## 4. Attacks

1. **Global Fourier division is unavailable.** Equation `(4)` holds only on `(-a,a)`, not on the
   whole line. Dividing by the archimedean symbol would silently discard the aperture seam.
2. **Ambient shift independence is insufficient.** Finite sums of rationally independent
   translations can have compactly supported solutions to inhomogeneous equations. The proof must
   use the support boundary and the exact Gamma channel.
3. **Analytic-kernel rhetoric is insufficient.** An analytic convolution kernel can have finite
   Fourier support and a large truncated nullspace. One needs a verified quasi-analytic or
   Wiener--Hopf condition for the actual `K_infinity`.
4. **Positivity is circular here.** Showing the Fourier symbol of the full left-minus-right side is
   nonnegative is the Weil criterion. The target is injectivity/unique continuation, which is
   weaker at each fixed aperture but cofinally equivalent to RH.
5. **Fixed-prime induction is insufficient.** The visible number of prime rays grows with `a`; any
   estimate whose constants deteriorate without a controlled cofinal law cannot prove `(5)`.
6. **Zero-free scalar factorization is false.** Equations `(11)`--`(13)` force real characteristic
   crossings at large aperture. They must be carried, not divided away.

## 5. Promotion and kill conditions

Promote the route only after proving one of:

- a Denjoy--Carleman estimate for every solution of `(4)` whose class is quasi-analytic uniformly
  on compact subapertures;
- a boundary-shell theorem that strictly shrinks the essential support of every nonzero solution;
- a Wiener--Hopf factorization whose partial indices vanish from the exact Euler--Gamma source;
- an exact nonpure relation complex plus a two-direction source-selected positivity theorem.

Kill the unique-continuation mechanism if an explicit nonzero compactly supported solution exists
for the actual coefficients at one aperture, or if the strongest regularity consequence of `(4)`
is proved non-quasi-analytic and the boundary-shell equations admit a free datum.

## Gates

- [x] exact compact screw null equation isolated
- [x] two lost affine modes restored by exact source anchors
- [x] finite visible prime-power cutoff derived from support
- [x] direct equivalence to the CCM aperture injectivity core recorded
- [x] three distinct mechanisms generated
- [x] invalid Fourier, analyticity, and fixed-prime shortcuts excluded
- [x] pure logarithmic ellipticity proved non-quasi-analytic
- [x] scalar truncated symbol proved to have real characteristic crossings cofinally
- [x] zero-free scalar Wiener--Hopf factorization excluded
- [ ] prove a local logarithmic-elliptic regularity theorem
- [ ] prove or refute quasi-analyticity
- [ ] prove or refute boundary-shell support peeling
- [ ] construct the singular finite-interval Evans determinant or a matrix factorization
- [ ] prove `ker G_a=0` for every aperture
- [ ] RH
