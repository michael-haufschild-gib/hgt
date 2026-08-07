# Suzuki high-clock prime-tangent tomography

- **ID:** `suzuki-high-clock-prime-tangent-tomography`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / SUZUKI SOURCE OPERATOR / PRIME-POWER TOMOGRAPHY
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL]`
  `[NOVELTY UNVERIFIED AFTER TARGETED SEARCH] [NOT AN RH PROOF]`
- **Primary source input:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), equations (2.2), (2.9)--(2.11), and Theorem 1.1.
- **Parent:** `suzuki-boundary-log-nonclock-nonflat-tangent.md`.
- **New conclusion:** the complete finite von-Mangoldt packet inside Suzuki's first projective
  tangent is recoverable from its high free-clock samples at every nonresonant aperture; such
  apertures form a cofinal dense set. The source paper does not state this sampling law.

## 1. Setup

Fix `a>0`. Let `A_a` be Suzuki's Friedrichs realization on `L^2(-a,a)`, let

```text
e_a(x)=e^x,
w_a(x)=e^(-x)(A_a e_a)(x),
H_a(z)=integral_(-a)^a (A_a e_a)(x)e^(izx) dx.
```

The parent theorem proves `e_a in Dom(A_a)`, so all three objects are defined unconditionally.
For `n>=1`, put

```text
k_(a,n)=pi n/a,
z_(a,n)=k_(a,n)+i,
theta_m(a)=pi log(m)/a,
c_m=Lambda(m)(sqrt(m)+m^(-3/2)).                         (1)
```

Because `e^(iz_(a,n)x)=e^(-x)e^(ik_(a,n)x)`, one has

```text
H_a(z_(a,n))=integral_(-a)^a w_a(x)e^(ik_(a,n)x) dx.     (2)
```

Write `Si(t)=integral_0^t sin(u)/u du`.

## 2. Main theorem: exact high-clock phase law

As `n -> infinity` through positive integers,

```text
(-1)^n k_(a,n) Re H_a(z_(a,n))
  = Si(2 pi n)
    + sum_(2<=m<=e^(2a)) c_m sin(n theta_m(a))
    + epsilon_(a,n),                                     (3)

epsilon_(a,n) -> 0.                                      (4)
```

Thus the scaled first tangent is not merely nonzero. It is an exact finite almost-periodic
von-Mangoldt packet plus one universal archimedean term and a vanishing error.

### Proof

Suzuki's distribution formula (2.11), applied to the zero extension of `e_a`, gives

```text
w_a(x)=-(1/2)log(a^2-x^2)+S_a(x)+q_a(x),                 (5)

S_a(x)=-sum_(2<=m<=e^(2a)) Lambda(m)/sqrt(m)
  [m^(-1) 1_(-a+log(m),a)(x)+m 1_(-a,a-log(m))(x)].      (6)
```

Here `q_a` is real and `C^1` on the closed interval. This regularity deserves an explicit check.
For the finite-part term, after removing its endpoint logarithm, the weighted divided difference
is

```text
j_a(x)=integral_0^(x+a) (e^(-t)-1)/t dt
      +integral_0^(a-x) (e^t-1)/t dt.                    (7)
```

Both quotients have removable singularities at zero, so `j_a` extends `C^1` to `[-a,a]`.
The scalar delta term is constant after multiplication by `e^(-x)`. For Suzuki's `C^2`
archimedean remainder `r`, substitution `t=x-y` gives

```text
e^(-x) integral_(-a)^a r''(x-y)e^y dy
  = integral_(x-a)^(x+a) e^(-t)r''(t) dt,                (8)
```

which is `C^1` by the fundamental theorem of calculus. This proves the assertion about `q_a`.

For the logarithmic term, split
`log(a^2-x^2)=log(a-x)+log(a+x)` and substitute into the two pieces. Since
`k_(a,n)a=pi n`, cutoff integration by parts at zero gives

```text
integral_(-a)^a log(a^2-x^2)e^(ik_(a,n)x) dx
  = -2(-1)^n Si(2 pi n)/k_(a,n).                         (9)
```

The boundary term `log(t)sin(k_(a,n)t)` vanishes at zero, so (9) is an ordinary improper-integral
identity, not a formal endpoint manipulation. Multiplication by `-1/2` yields the first term in
(3).

For one prime-power displacement `L=log m`, direct integration of (6) gives

```text
k_(a,n) Re integral_(-a)^a S_(a,m)(x)e^(ik_(a,n)x) dx
  =(-1)^n Lambda(m)(sqrt(m)+m^(-3/2))
     sin(pi n log(m)/a).                                 (10)
```

Indeed, the two interval integrals have numerators

```text
(-1)^n(1-e^(ik_(a,n)L)),
(-1)^n(e^(-ik_(a,n)L)-1),                                (11)
```

and the real part after division by `i k_(a,n)` is exactly (10). Only finitely many `m` occur.

Finally, integration by parts for the `C^1` residual gives

```text
k_(a,n) integral_(-a)^a q_a(x)e^(ik_(a,n)x) dx
 = [q_a(x)e^(ik_(a,n)x)/i]_(-a)^a
   + i integral_(-a)^a q_a'(x)e^(ik_(a,n)x) dx.          (12)
```

The endpoint exponentials are both `(-1)^n`; because `q_a` is real, the boundary term in (12) is
purely imaginary. The real part of the remaining integral tends to zero by the
Riemann--Lebesgue lemma. Equations (9), (10), and (12) prove (3)--(4).

## 3. Aperture-independent Cesaro trace

For every fixed `a>0`,

```text
lim_(N->infinity) (1/N) sum_(n=1)^N
  (-1)^n k_(a,n) Re H_a(z_(a,n)) = pi/2.                 (13)
```

This follows from (3): `Si(2 pi n)->pi/2`; every finite sine phase has Cesaro mean zero
(including the identically zero resonant phases); and a null sequence has null Cesaro mean.
The trace is universal but nonzero at every aperture. It gives a normalization check for any
future construction of the concrete tangent from Suzuki's resolvent.

## 4. Bohr reconstruction of every prime-power coefficient

Set

```text
T_(a,n)=(-1)^n k_(a,n) Re H_a(z_(a,n)),
P_(a,n)=T_(a,n)-Si(2 pi n),
q_m(a)=exp(i theta_m(a)).                                (14)
```

Fix `m` with `2<=m<=e^(2a)`. Suppose that among the finite aperture packet

```text
q_j(a) != q_m(a)              for j!=m,
q_j(a)^(-1) != q_m(a)         for every j.               (15)
```

Then

```text
lim_(N->infinity) (1/N) sum_(n=1)^N P_(a,n)q_m(a)^(-n)
  = c_m/(2i),                                             (16)

Lambda(m)= [2i/(sqrt(m)+m^(-3/2))] times the limit in (16).  (17)
```

### Proof

Use

```text
sin(n theta_j)=(q_j^n-q_j^(-n))/(2i).                    (18)
```

After multiplication by `q_m^(-n)`, the Cesaro mean of a unit phase is zero unless that phase is
one. Conditions (15) leave exactly the positive `j=m` term, proving (16). The error in (3) remains
Cesaro-null after multiplication by a unit phase. Since the scale in (17) is strictly positive,
(17) follows. In particular, the reconstructed coefficient is nonzero exactly when `m` is a
prime power.

## 5. Cofinal nonresonant apertures

There is one countable exceptional set `B subset (0,infinity)` outside which (15) holds
simultaneously for every pair of positive integers. Indeed, positive-positive collisions require

```text
a=(log j-log m)/(2 ell),     j!=m, ell in Z\{0},          (19)
```

and reflected collisions require

```text
a=log(jm)/(2 ell),           ell in Z_(>0).               (20)
```

Conversely, equality of the corresponding unit phases gives (19) or (20). Hence `B` is a
countable union of countable sets. Every open interval contains a point outside `B`; choosing
`a_r in (r,r+1)\B` produces a cofinal nonresonant schedule.

For such a schedule, once `a_r >= log(m)/2`, formula (17) recovers `Lambda(m)`. Consequently:

> The complete von-Mangoldt function is an unconditional cofinal invariant of the high-clock
> samples of Suzuki's first projective source tangent.

This is an informational completeness theorem, stronger than fixed-aperture tangent
nonvanishing. It shows that the far-negative tangent has not lost the arithmetic source before
the projective limit is taken.

## 6. Relation to the RH frontier

The theorem closes the prior handover's request for a persistent arithmetic statistic that sees
infinitely many source atoms: along one cofinal nonresonant schedule, the family of Bohr
coefficients sees every prime power and its exact von-Mangoldt weight.

It does **not** yet solve Suzuki's cofinal carrier problem. As `a->infinity`, each fixed phase
`theta_m(a)->0`; recovery uses longer and longer clock-mode averages and is not uniform on compact
spectral sets. Therefore (17) alone does not imply tightness of the actual Clark measure, a
non-free locally uniform carrier limit, or identification of its zero divisor with Xi.

The new sharp open core is:

```text
transfer the cofinally complete tangent Bohr data through a source-selected finite shift
into a tight infinite atomic Nevanlinna measure, without phase information escaping to
unbounded clock modes, then identify that measure's divisor with the Xi/de Branges divisor.
```

This is narrower than asking whether arithmetic survives at all: it survives completely at first
order, but presently only in a nonuniform high-mode topology.

## 7. Formalization map

Lean module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiPrimeTangentTomography.lean
```

Formalized unconditionally:

1. Cesaro means of every nontrivial unit geometric phase vanish;
2. finite complex exponential packets are exactly recovered by Bohr demodulation;
3. finite sine packets are recovered under positive/reflected phase noncollision;
4. Suzuki's exact phase `exp(i pi log(m)/a)` has unit norm;
5. the source coefficient is exactly
   `Lambda(m)(sqrt(m)+1/(m sqrt(m)))`;
6. that scale is exactly the sum of Suzuki's reflected `m` and `m^(-1)` step multipliers after
   extraction of `1/sqrt(m)`;
7. this coefficient is nonzero exactly on prime powers;
8. normalized nonresonant Bohr recovery converges to `Lambda(m)` itself;
9. one nonresonance certificate reconstructs every coefficient in a finite aperture packet.

The analytic passage from Suzuki's distributional operator to (3) is paper-proved above. The Lean
module formalizes the exact finite harmonic-analysis and arithmetic recovery core without axioms.

## 8. Hostile audit

1. **No hidden RH.** Only Suzuki's unconditional operator formula and elementary Fourier analysis
   are used.
2. **No numerical evidence.** Every coefficient and limit is symbolic.
3. **Endpoint term retained.** The logarithmic singularity gives the exact `Si(2 pi n)` term; it is
   not discarded as an error.
4. **Residual scaling justified.** `q_a in C^1`, the clock endpoint term is purely imaginary, and
   Riemann--Lebesgue is applied only to `q_a' in L^1`.
5. **Both reflected shifts retained.** Their unequal factors `m` and `m^(-1)` produce the exact
   positive scale `sqrt(m)+m^(-3/2)`.
6. **Resonances not ignored.** Recovery is stated for an explicit countable-complement cofinal set
   of apertures.
7. **No cofinal compactness overclaim.** Bohr reconstruction is not uniform in `a`, so no Xi
   divisor limit is claimed.

## 9. Gates

- [x] 0 -> 1: exact source identity and non-circular attack isolated
- [x] 1 -> 2: dependency-closed paper proof and hostile audit complete
- [x] 2 -> 3: Lean module, exact build, and axiom audit complete
- [ ] 3 -> 4: external mathematical novelty review and publication treatment pending
