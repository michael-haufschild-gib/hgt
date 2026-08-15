# Euler-region Gamma framing forces critical Radon--Nikodym recession

- **ID:** `ccm-euler-gamma-radon-nikodym-frame-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the Euler-log prime-power Herglotz measure, the archimedean Gamma cyclic
  characteristic, and Hilbert--Schmidt frame theory

## 1. The two canonical measures

For a prime power coordinate `alpha=(p,k)`, `k>=1`, put

```text
t_alpha=k log p,
w_alpha=1/(k p^k),
phi(t)=(cosh t)^(-1/2),
d_alpha^2=phi(2t_alpha).                                  (1)
```

The weights `w_alpha` are exactly the atoms of the Euler-log measure

```text
mu_E=sum_(p,k>=1) 1/(k p^k) delta_(k log p).              (2)
```

The values `d_alpha^2` are exactly the diagonal norms of the Gamma-damped cyclic modes from
`ccm-gamma-damped-cauchy-frame-trace-law.md`.

## 2. Exact Radon--Nikodym correction

Define

```text
r_alpha=w_alpha/d_alpha^2.                                (3)
```

Since

```text
phi(2k log p)
 =sqrt(2)p^k/sqrt(p^(4k)+1),                              (4)
```

one has the exact formula

```text
r_(p,k)
 =sqrt(p^(4k)+1)/(sqrt(2)k p^(2k))
 =sqrt(1+p^(-4k))/(sqrt(2)k).                             (5)
```

Consequently

```text
1/(sqrt(2)k)<=r_(p,k)<=1/k<=1.                            (6)
```

Thus the correction is a positive diagonal contraction. It is uniquely determined by the demand
that the Gamma diagonal equal the exact Euler atom:

```text
r_alpha d_alpha^2=w_alpha.                               (7)
```

No cutoff-dependent normalization or asymptotic replacement is involved.

## 3. Euler-weighted Gamma frame

Let `(H_infinity,U,xi)` be the pointed Gamma cyclic representation. For a Cauchy test `a` on the
prime-power log support, define the channel-resolved synthesis columns

```text
T_a e_alpha
 =a(t_alpha)sqrt(r_alpha)d_alpha U_(t_alpha)xi
 =a(t_alpha)sqrt(w_alpha)U_(t_alpha)xi.                   (8)
```

For every finite upper-half-plane Cauchy packet,

```text
sum_alpha ||T_a e_alpha||^2
 =sum_(p,k>=1) w_(p,k)|a(k log p)|^2<infinity.            (9)
```

Indeed the `k=1` layer is bounded by a constant multiple of

```text
sum_p 1/(p(log p)^2)<infinity,
```

while the `k>=2` tail is absolutely summable even before Cauchy decay:

```text
sum_p sum_(k>=2)1/(k p^k)
 <=sum_p 1/(p(p-1))<infinity.                             (10)
```

Hence `T_a` is Hilbert--Schmidt.

## 4. Exact Euler-region trace identity

For two such tests `a,b`, the Gram operator `T_b^*T_a` is trace class and

```text
Tr(T_b^*T_a)
 =sum_(p,k>=1)w_(p,k) conj(b(t_(p,k)))a(t_(p,k)).         (11)
```

This is exactly the polarized Cauchy Gram of the Euler-log measure `(2)`. At the same time the full
operator retains Gamma covariance:

```text
<e_alpha,T_b^*T_a e_beta>
 =sqrt(w_alpha w_beta)
  conj(b(t_alpha))a(t_beta)phi(t_beta-t_alpha).           (12)
```

Thus the exact Euler diagonal and non-diagonal Gamma covariance coexist in one positive
channel-resolved carrier.

For centered Cauchy tests `C_z(t)=(t-z)^(-1)`, partial fractions give

```text
Tr(T_w^*T_z)
 =sum_(p,k) w_(p,k)/((t_(p,k)-z)(t_(p,k)-conj(w)))
```

This is an Euler-region Herglotz Gram. It is **not** the centered von-Mangoldt source in
`XiWeilResolventSource.lean`. The latter has, on the critical boundary, prime-power magnitude

```text
ell_(p,k)=(log p)p^(-k/2),                               (13)
```

not `1/(k p^k)`.

## 5. Exact critical recession law

The positive diagonal factor that would force the Gamma norm to equal the critical von-Mangoldt
magnitude `(13)` is uniquely

```text
q_(p,k)=ell_(p,k)/phi(2klog p)
 =((log p)/sqrt(2))p^(k/2)sqrt(1+p^(-4k)).                (14)
```

In particular,

```text
q_(p,k)>=(log p)p^(k/2)/sqrt(2),                          (15)
```

so the required critical correction is unbounded in both the prime and prime-power directions.
The bounded Euler-region contraction `(5)` therefore does not extend to the centered source. The
exact transition is positive:

```text
Euler-log Herglotz diagonal -> bounded Gamma contraction,
critical von-Mangoldt diagonal -> cofinally recessing Gamma correction. (16)
```

A viable CCM construction must carry the recession `(14)` through an unbounded but closable
relative operator, a non-diagonal Sonin/Hardy carrier, or an equivalent infinite-dimensional
source constraint. It cannot obtain the critical source by bounded diagonal renormalization of the
Gamma frame.

There is a second exact obligation. The centered prime flux depends on the test parameter through
`exp(-i z t_alpha)`, so its polarized divided-difference atom is proportional to

```text
(exp(-i conjugate(w)t_alpha)-exp(-i z t_alpha))
  /(z-conjugate(w)).                                      (17)
```

This is an exponential Loewner/relative kernel, not the Cauchy product in `(11)`. Therefore even
the unbounded weight `(14)` is only a necessary diagonal comparison. The successful carrier must
also implement the Laplace-to-relative-resolvent transform `(17)` inside its Hardy/Sonin
polarization.

That generic carrier already exists: `ccm-logderivative-closed-two-channel-graph-law.md` constructs
the canonical closed causal/anti-causal graph of the complete logarithmic source, and `(17)` has
the exact bilateral factorization

```text
i t integral_0^1
  exp(-i t(1-u)z)exp(-i t u conjugate(w))du.
```

The remaining theorem is quantitative and source-specific: identify the distinguished Sonin
compression of this closed graph and prove its relative trace-slope/Loewner domination bound. That
bound is the RH-bearing step.

## 6. Scope and classification

Equations `(4)`--`(7)` are elementary. Equations `(8)`--`(12)` are standard Hilbert--Schmidt and
trace identities. The connection is a useful CCM bridge but is not new scientific knowledge.
Equations `(14)`--`(16)` are the exact weight comparison behind the already formalized positive
transport wall. The result does not prove positivity of the full Weil form: it shows that the
bounded Euler-region frame cannot be substituted for the critical prime--archimedean source.

## Gates

- [x] exact Euler/Gamma Radon--Nikodym correction computed
- [x] correction proved to be a positive contraction
- [x] finite-Cauchy Hilbert--Schmidt domain proved
- [x] exact Euler-log trace and Gamma covariance combined
- [x] exact critical von-Mangoldt correction computed and proved cofinally unbounded
- [x] exponential Loewner kernel separated from the Euler Cauchy Gram
- [x] realize the unbounded source and exponential kernel in the canonical closed two-channel graph
- [ ] identify its distinguished Sonin compression and relative trace-slope bound
- [ ] add the exact archimedean/boundary relative channel on the same domain
- [ ] transport Pick inertia cofinally
- [ ] RH

## Lean status

`[FORMALIZED]` — module `formal/GaloisForLFunctions/RHTower/CCMEulerGammaRadonNikodym.lean`
(9 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `gammaDampingProfile`, `eulerAtom`, `gammaDiagSq`, `gammaDampingProfile_eq_inv_sqrt` — the two
  canonical weights of `(1)`–`(2)`.
- `gammaDiagSq_eq` — **equation (4)**: the exact Gamma diagonal
  `φ(2 k log p) = √2 · p^k / √(p^{4k}+1)`, proved from `cosh(2k log p) = (p^{4k}+1)/(2p^{2k})`.
- `radonNikodym`, `radonNikodym_eq` — **equations (3), (5)**: the exact correction
  `r_{p,k} = √(p^{4k}+1)/(√2 k p^{2k})`.
- `radonNikodym_lower`, `radonNikodym_upper` — **equation (6)**:
  `1/(√2 k) ≤ r_{p,k} ≤ 1/k`, so the correction is a positive diagonal contraction.
- `radonNikodym_mul_gammaDiagSq` — **equation (7)**: the correction is exactly the factor making the
  Gamma diagonal equal the Euler atom, with no cutoff-dependent normalization.
- `tsum_eulerAtom_tail_le` — **equation (10)**: for each prime the deep prime-power tail satisfies
  `∑_{k≥2} 1/(k p^k) ≤ 1/(p(p-1))`, which is the absolute summability behind the Hilbert–Schmidt
  bound `(9)`.
- `vonMangoldtMagnitude`, `criticalCorrection`, `criticalCorrection_lower` — **equations (13)–(15)**:
  the diagonal factor matching the critical von Mangoldt magnitude is at least
  `(log p) p^{k/2}/√2`.
- `criticalCorrection_unbounded` — **equation (16)**: that factor is cofinally unbounded, so the
  bounded Euler-region contraction does **not** extend to the centered source; no bounded diagonal
  renormalization of the Gamma frame produces the critical source.

Reused, not rebuilt: `CCMTwoChannelGraph.bilateral_atom_factorization` already carries the exact
bilateral factorization of the exponential divided-difference kernel `(17)`.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the pointed Gamma cyclic representation `(H_∞, U, ξ)` and the synthesis columns `(8)`;
- the Hilbert–Schmidt/trace-class operator statements `(9)`, `(11)`, `(12)`;
- the prime sum `∑_p 1/(p (log p)²) < ∞` used for the `k = 1` layer.
