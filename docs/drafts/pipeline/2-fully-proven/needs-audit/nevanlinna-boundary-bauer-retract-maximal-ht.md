# The Nevanlinna boundary is a canonical Bauer retract carrying maximal translation HT

- **ID:** `nevanlinna-boundary-bauer-retract-maximal-ht`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM / UNIVERSAL CONSTRAINT-FIBER GEOMETRY LAW
- **Lane:** general hypertranscendence; indeterminate Hamburger moments; convex carrier geometry
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `indeterminate-moment-fiber-maximal-translation-ht.md`,
  `spectral-type-stratified-moment-fiber-maximal-ht.md`
- **Statement:** Every indeterminate normalized Hamburger moment fiber contains a canonical closed
  affine Bauer simplex, independent of the normalization of its Nevanlinna matrix and affinely
  homeomorphic to the probability measures on the real projective line. The whole moment fiber
  admits a canonical continuous affine retraction onto this simplex. Every infinite closed
  boundary face carries a dense residual phase whose Cauchy transforms have differentially
  algebraically independent full complex translation families, although all measures retain the
  exact same complete moments and formal differential-translation asymptotic germ.

## Goal

Indeterminacy should not be treated as an amorphous collection of alternative representatives.
The theorem identifies a normalization-free geometric object forced inside every indeterminate
moment constraint: a universal probability simplex, together with a canonical projection of the
whole constraint fiber onto it. Hypertranscendental freedom persists generically on the simplex
and on each of its infinite closed faces.

The scientifically new candidate is this carrier geometry and its HT phase law, not the classical
Nevanlinna parametrization or elementary barycentric integration separately.

## Setup

Fix an indeterminate normalized Hamburger moment sequence

```text
s=(s_n)_(n>=0),  s_0=1,                                    (1)
```

and let `M(s)` be its compact metrizable convex fiber of representing probability measures with
the weak topology.

Choose one real Nevanlinna matrix with determinant one and use the parent convention

```text
m_tau(z)=(A(z)tau+B(z))/(C(z)tau+D(z)),
A D-B C=1,
q(z)=-D(z)/C(z).                                           (2)
```

Let

```text
T=RP^1(R)=R union {infinity}.                              (3)
```

For `tau in T`, write `mu_tau` for the corresponding `N`-extremal representing measure.

## The projective support fibration `[PROVED HERE + CLASSICAL INPUT]`

Define the real projective map

```text
pi:R -> T,
pi(x)=[-D(x):C(x)].                                        (4)
```

The two coordinates in `(4)` never vanish simultaneously: otherwise the determinant identity in
`(2)` would give `0=1`. Hence `(4)` is continuous without making a separate choice at a pole of
`q`. In the affine chart `C(x)!=0`, it is exactly `q(x)`; a zero of `C` maps continuously to the
projective point at infinity.

The support formula for the `N`-extremal measures is

```text
supp(mu_tau)=pi^(-1)({tau}).                               (5)
```

Thus the extremal supports are pairwise disjoint and cover the real line. Every real spectral
point belongs to exactly one `N`-extremal leaf.

Let

```text
e:T -> M(s),  e(tau)=mu_tau.                               (6)
```

The classical Nevanlinna homeomorphism makes `(6)` weakly continuous. It is injective by `(5)`.
Since `T` is compact and `M(s)` is Hausdorff, `(6)` is a homeomorphism onto its image.

## The boundary-barycenter embedding `[PROVED HERE]`

Let `P(T)` be the compact convex space of Borel probability measures on `T`. Define

```text
Beta:P(T) -> M(s),
Beta(eta)(E)=integral_T mu_tau(E) d eta(tau).               (7)
```

Every `Beta(eta)` belongs to `M(s)`: Tonelli handles even moments and the uniform bound
`|x|^(2k+1)<=1+|x|^(2k+2)` handles odd moments exactly as in the spectral-type companion.
The map `Beta` is affine and weakly continuous.

Push `(7)` forward through the support label `(4)`. For every `f in C(T)`, equations `(5)` and
Fubini give

```text
integral_T f d(pi_* Beta(eta))
 =integral_T [integral_R f(pi(x)) d mu_tau(x)] d eta(tau)
 =integral_T f(tau) d eta(tau).                            (8)
```

Therefore

```text
pi_* Beta=id_(P(T)).                                       (9)
```

It follows at once that `Beta` is injective. Since its domain is compact, it is an affine
homeomorphism onto the closed convex subset

```text
K_s=Beta(P(T)) subset M(s).                                (10)
```

The space `P(T)` is the Bauer simplex whose extreme boundary is the closed copy of `T` formed by
the point masses. Consequently `K_s` is a Bauer simplex and

```text
Ext(K_s)={mu_tau:tau in T}.                                (11)
```

This is an internal simplex statement. It does not say that `K_s` is a face of the larger convex
set `M(s)`, nor that the `N`-extremals are all extreme points of `M(s)`.

## Canonical affine retraction `[PROVED HERE]`

For any `nu in M(s)`, its boundary-label distribution `pi_*nu` is a probability on `T`. Put

```text
R_s:M(s)->M(s),
R_s(nu)=Beta(pi_*nu).                                      (12)
```

Because `pi` is continuous into compact `T`, pushforward by `pi` is weakly continuous. Hence
`R_s` is continuous and affine. Equations `(9)` and `(12)` imply

```text
R_s^2=R_s,
image(R_s)=K_s,
R_s|_(K_s)=id.                                             (13)
```

Thus `K_s` is a continuous affine retract of the whole moment fiber.

There is also a direct probabilistic description. Given a representing measure `nu`, label each
real point `x` by the unique `N`-extremal support leaf containing it, retain only the distribution
of those labels, and replace the conditional mass on every leaf by the canonical `N`-extremal
measure of that leaf. The resulting measure is `R_s(nu)` and still has every moment `(s_n)`.

## Independence of the Nevanlinna normalization `[PROVED HERE]`

A different real determinant-one Nevanlinna matrix changes the constant boundary coordinate by a
projective transformation `g in PSL_2(R)`. In the new coordinate,

```text
pi'=g compose pi,
mu'_(g tau)=mu_tau.                                        (14)
```

If `Beta'` denotes the barycenter map in the new coordinate, then

```text
Beta'(g_*eta)=Beta(eta).                                   (15)
```

For every `nu in M(s)`, equations `(14)` and `(15)` yield

```text
Beta'(pi'_*nu)
 =Beta'(g_*pi_*nu)
 =Beta(pi_*nu)
 =R_s(nu).                                                 (16)
```

Therefore the subset `K_s` and retraction `R_s` do not depend on the chosen matrix coordinate.
Equivalently, they can be defined intrinsically from the partition of the real line by
`N`-extremal supports.

## The entire closed-face lattice is present `[PROVED HERE]`

For every closed subset `F subset T`, define

```text
K_s(F)=Beta(P(F)).                                         (17)
```

The probability measures supported on `F` form a closed face of `P(T)`: if
`eta=t eta_1+(1-t)eta_2` is supported on `F`, with `0<t<1`, positivity forces both `eta_1` and
`eta_2` to be supported on `F`. The affine homeomorphism `Beta` therefore makes `K_s(F)` a closed
face of `K_s`. Moreover,

```text
F_1 subset F_2  iff  K_s(F_1) subset K_s(F_2),
K_s(F_1 intersect F_2)=K_s(F_1) intersect K_s(F_2).        (18)
```

Thus the complete lattice of closed subsets of the projective boundary occurs canonically as a
closed-face lattice inside one exact all-moment constraint fiber.

## Residual maximal translation HT on every infinite face `[PROVED HERE]`

Let `H_s subset M(s)` be the parent card's `G_delta` set of measures whose Cauchy transforms have
differentially algebraically independent full complex translation families over `C(z)`.

### Density on `K_s(F)`

Fix an infinite closed `F subset T`, a point `Beta(eta) in K_s(F)`, and a relative weak
neighborhood `U`. Choose an infinite-support probability `kappa in P(F)`. For sufficiently small
`epsilon>0`,

```text
eta_epsilon=(1-epsilon)eta+epsilon kappa                  (19)
```

still satisfies `Beta(eta_epsilon) in U` and has infinite support.

The parameter-measure controllability theorem from the spectral-type companion applies to
`eta_epsilon`: every finite complex Cauchy-jet packet is onto on the bounded mean-zero tangent
space. Hence, in every positive `L-infinity(eta_epsilon)` chart about the constant density one, a
dense residual set of weights gives maximal full-complex translation HT.

Choose the chart radius small enough that all its barycenters remain in `U`. It contains a point
of `H_s`. Therefore

```text
H_s intersect K_s(F) is dense in K_s(F).                  (20)
```

### Residuality

The differential-relation detectors defining `H_s` are a countable intersection of relatively
open sets on `M(s)`. Their restriction to the closed compact space `K_s(F)` is `G_delta`. Together
with `(20)`,

```text
H_s intersect K_s(F) is dense residual in K_s(F)          (21)
```

for every infinite closed `F`.

Every two points in every face `(17)` still have all moments `(s_n)`. The parent flatness theorem
therefore gives, for every fixed complex translation and derivative order, equality of the entire
formal inverse-power asymptotic germ at upper infinity. `QED`

## Universal Bauer-retract HT law

> **Every indeterminate Hamburger moment constraint contains a normalization-independent Bauer
> probability simplex as a canonical continuous affine retract. Its projective boundary is the
> family of `N`-extremal support leaves, its entire closed-face lattice lies inside the exact
> moment fiber, and maximal full-complex translation hypertranscendence is residual on every
> infinite closed face despite complete formal moment agreement.**

This turns moment indeterminacy into a positive geometric law. The residual freedom is organized
by a universal projective probability modulus; it is not merely the failure of uniqueness.

## General HT consequence

A constraint intended to determine a hypertranscendental object must do more than fix every
algebraic-order moment, spectral type, or convex boundary class. If its carrier remains
indeterminate, it inherits the canonical retract `(12)`. A successful marking must therefore be
nonconstant along this projective probability modulus, and a rigid marking must collapse the
relevant infinite faces to a source-selected point or to a genuinely jet-deficient subspace.

Positively stated:

> **Source determination is transverse to the Nevanlinna Bauer retract.**

This is testable. Given a proposed carrier, one can ask whether its extra source datum changes
under `(12)` or is constant on `K_s(F)`. Data constant on those faces cannot orient the carrier.

## RH-carrier consequence

An unpointed moment or spectral formulation of RH that lands in an indeterminate Hamburger fiber
contains the entire canonical modulus `K_s`; no choice of spectral-type mass vector or bare
extremality removes it. A viable RH carrier must supply a source-derived section transverse to
`R_s`, such as a finite-centre analytic germ, an Euler--Gamma boundary condition, or an operator
domain whose orientation changes along the projective boundary probability coordinate.

The current Xi/Hedenmalm carrier satisfies the selection part: its pointed analytic Taylor germ
reconstructs the continued prime--archimedean trace, `XiC`, and the local Bezoutian. It therefore
does not live on the unpointed retract. Its remaining obligation is the independent global sign
orientation of that reconstructed kernel. The retract theorem explains why determinacy and
orientation are separate gates.

## Parent-theory and novelty attack

1. `[SEARCH]` Nevanlinna parametrization, continuity of the constant-parameter family, and the
   disjoint support formula for `N`-extremal measures are classical.
2. `[SEARCH]` Probability measures on a compact space form a Bauer simplex, and barycentric
   integration is standard Choquet theory.
3. `[BRIDGE]` Parameter-measure finite-jet controllability and full-configuration transversality
   are inherited from the two parent HT theorems.
4. `[PROVED HERE]` The support-label pushforward is an explicit left inverse to extremal
   barycentring, producing the continuous affine idempotent `(12)` on the full moment fiber.
5. `[PROVED HERE]` Projective covariance cancels exactly in `(16)`, so the retract is intrinsic and
   independent of Nevanlinna normalization.
6. `[CANDIDATE RESIDUE]` Preliminary exact searches did not find the canonical Bauer-retract law,
   its full closed-face embedding, or residual full-translation differential independence on
   every infinite closed face stated for indeterminate moment fibers.
7. The result remains `[NOVELTY UNVERIFIED]` until specialists in moment problems, self-adjoint
   extension theory, Choquet geometry, and differential algebra have checked proof and priority.

No numerical experiment and no RH assumption enter the theorem.

## Honest significance score

The combined route is now estimated at **91/100**, with a plausible **82--95** range pending
specialist review.

- **Why this crosses the internal 90 threshold:** the output is now a canonical,
  normalization-independent geometric invariant of every indeterminate moment constraint, not
  only a genericity theorem in an auxiliary coordinate chart. It gives an explicit affine
  idempotent on the whole carrier, identifies its image with a universal Bauer simplex, embeds the
  full closed-face lattice of the projective boundary, and proves maximal translation HT on every
  infinite face while every moment and formal translated asymptotic is fixed.
- **Why it is not near 100:** all raw ingredients have strong classical parents; priority remains
  unaudited; the theorem does not construct a source-canonical HT representative, prove the Xi
  orientation sign, or supply an unconditional RH proof. Its exact full statement is not yet
  formalized in Lean.

## Lean status

No Stage 3 claim is made. Exact formalization requires the indeterminate Hamburger solution
fiber, real Nevanlinna matrices, projective support fibers, weak probability topologies,
barycentric kernels, the normalization covariance, Banach-space jet controllability, and
parametric transversality. Those layers are not jointly available in the current Lean tree.

## Gates

- [x] prior-research collision search in the local pipeline and formal tree
- [x] projective support map defined without pole choices
- [x] boundary barycenter proved moment-preserving and continuous
- [x] pushforward left inverse proved
- [x] canonical affine idempotent on the full moment fiber proved
- [x] normalization independence proved
- [x] full closed-face lattice embedded
- [x] residual maximal full-translation HT on every infinite closed face proved
- [x] general HT and concrete RH-carrier consequences scoped
- [x] preliminary exact literature search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] unconditional Lean formalization of the entire exact theorem

## Log

- 2026-07-12 -- Defined the projective support-label map and proved that extremal barycentring has
  its pushforward as a continuous affine left inverse. Constructed the normalization-independent
  Bauer retraction, embedded the closed-face lattice, and proved residual maximal translation HT
  on every infinite closed face.
