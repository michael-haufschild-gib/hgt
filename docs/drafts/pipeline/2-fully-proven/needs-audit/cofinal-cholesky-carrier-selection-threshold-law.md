# Finite Cholesky frames retain maximal HT; the complete divergent tower selects the carrier

- **ID:** `cofinal-cholesky-carrier-selection-threshold-law`
- **Stage:** 2-fully-proven on paper / needs audit
- **Type:** THEOREM / COFINAL FRAME-SELECTION GEOMETRY
- **Lane:** general hypertranscendence; indeterminate moment carriers; OPUC frame geometry
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Parents:** `finite-jet-aperture-complete-germ-closure-law.md`,
  `singular-maximal-ht-toeplitz-weld-graph-saturation.md`,
  `nevanlinna-boundary-bauer-retract-maximal-ht.md`
- **Statement:** On the canonical Bauer simplex of every indeterminate Hamburger moment problem,
  the complete compatible inverse-Cholesky tower is a faithful topological coordinate for the
  carrier. Every finite prefix of that tower leaves a positive Hilbert cube and an
  infinite-dimensional chart with
  residual maximal full-translation hypertranscendence at fixed spectral type. On the residual
  singular-continuous maximal-HT phase, the raw polynomial graph saturates the full
  source--carrier product, whereas the uniquely selecting Cholesky tower diverges and yields the
  unitary orthogonal-polynomial carrier only before closure.

## Purpose

The graph-saturation theorem proves that an unweighted cofinal Toeplitz weld forgets all
source--carrier incidence. The finite-jet theorem proves that no finite analytic packet selects a
boundary law. The present theorem identifies the exact canonical datum joining those facts.

> **The carrier is selected by the coherent inverse-Cholesky tower, not by any finite Toeplitz
> section. Every finite frame prefix retains a positive maximal-HT modulus; the full tower closes
> that modulus to one point. In the singular phase the selecting tower necessarily escapes every
> uniformly bounded frame geometry.**

This is a theorem about constrained HT carriers in general. The Riemann-hypothesis consequence is
only a later route constraint.

## Setup

Fix an indeterminate normalized Hamburger moment sequence and its canonical Nevanlinna Bauer
simplex

```text
Beta:P(T)->K_s subset M(s),
T=RP^1(R).                                                  (1)
```

Every `nu in K_s` has infinite support. Use the Cayley map

```text
kappa(x)=(x-i)/(x+i) in unit circle                         (2)
```

and write

```text
mu_nu=kappa_*nu,
c_k(nu)=integral zeta^k d mu_nu(zeta),
G_N(nu)=(c_(j-k)(nu))_(0<=j,k<=N).                         (3)
```

Every `G_N(nu)` is positive definite. Let `C_N(nu)` be the unique lower-triangular matrix with
positive diagonal satisfying

```text
C_N(nu) G_N(nu) C_N(nu)^*=I.                              (4)
```

The matrices are compatible under leading-block restriction. They are the coefficient matrices
of the first `N+1` orthonormal polynomials of `mu_nu` in the monomial frame.

Define the complete frame coordinate

```text
Theta(nu)=(C_0(nu),C_1(nu),...)                            (5)
```

and the exact level-`N` frame fiber through `nu_0` by

```text
F_N(nu_0)={nu in K_s:C_N(nu)=C_N(nu_0)}.                  (6)
```

## Cholesky prefixes are exactly finite Cauchy jets `[PROVED HERE]`

Let

```text
m_nu(z)=integral_R 1/(x-z)d nu(x).                         (7)
```

The binomial identity

```text
kappa(x)^k=(1-2i/(x+i))^k
 =sum_(r=0)^k binom(k,r)(-2i)^r (x+i)^(-r)                (8)
```

and the derivative formula

```text
m_nu^(r-1)(-i)=(r-1)! integral_R (x+i)^(-r)d nu(x)        (9)
```

show that

```text
(c_1(nu),...,c_N(nu))
  <-> (m_nu(-i),m_nu'(-i),...,m_nu^(N-1)(-i))             (10)
```

is an invertible complex-triangular change of coordinates. Negative circle moments are the
conjugates of the positive ones.

Equation `(4)` also gives

```text
G_N(nu)^(-1)=C_N(nu)^*C_N(nu).                            (11)
```

Consequently, for `nu_1,nu_2 in K_s`, the following are equivalent:

```text
C_N(nu_1)=C_N(nu_2),
G_N(nu_1)=G_N(nu_2),
c_k(nu_1)=c_k(nu_2) for 1<=k<=N,
m_nu1^(r)(-i)=m_nu2^(r)(-i) for 0<=r<N.                   (12)
```

The first equivalence uses positive-diagonal Cholesky uniqueness; the second reads the Toeplitz
diagonals; the third is `(10)`. Thus a finite canonical carrier frame is neither weaker nor
stronger than a finite regular Cauchy jet: it is that jet in intrinsic Hilbert coordinates.

## Every finite frame fiber retains a maximal-HT aperture `[PROVED VIA PARENT]`

Fix `nu_0=Beta(eta_0)` with `eta_0` of infinite support. For `0<delta<1`, vary `eta_0` through
strictly positive bounded densities

```text
eta_w=w eta_0,
||w-1||_infinity<delta,
integral w d eta_0=1,                                     (13)
```

subject to the `N` complex linear equations in `(10)`. The tangent is the kernel of finitely many
real continuous functionals on `L^infinity(eta_0;R)`. It is therefore infinite-dimensional and
contains positive balls of every prescribed finite dimension after scaling.

If `eta_0` is atomless, the same exact frame fiber contains a topologically embedded Hilbert cube.
Write the real normalization and frozen-jet equations as `K` bounded integration constraints.
Choose disjoint measurable blocks `B_j`, each split into `K+1` positive-measure pieces. On every
block, a nonzero linear combination `v_j` of the piece indicators annihilates all `K` constraints;
normalize `||v_j||_infinity=1`. Then

```text
w_t=1+(delta/2) sum_(j>=1) 2^(-j)t_j v_j,
t=(t_j) in [-1,1]^(mathbb N),                             (13a)
```

is strictly positive and satisfies the exact prefix equations. Disjoint supports make the map
injective; the weights `2^(-j)` make it continuous from the product topology to `L^infinity`.
Compactness of the Hilbert cube and injectivity of `Beta` make `(13a)` a topological embedding in
`F_N(nu_0)`. All its carriers have the same spectral type by positive bounded equivalence.

By `(12)`, every carrier in this chart belongs to `F_N(nu_0)`. Because `w` is bounded above and
below by positive constants, `eta_w` is equivalent to `eta_0`; exact spectral-type transport in
the Bauer parent theorem therefore keeps the pure-point / singular-continuous /
absolutely-continuous type of `nu_0` fixed.

The constrained principal-part theorem from the finite-jet parent applies at the frozen node
`-i`. On the tangent of `(13)`, every finite Cauchy-jet packet whose Nevanlinna parameter poles are
disjoint from the frozen finite pole set remains onto. Coefficient-uniform transversality and Baire
intersection then give a dense residual subset of this exact frame-prefix chart for which every
finite family of distinct complex translates of `m_nu` is differentially algebraically
independent over `C(z)`.

Therefore, for every finite `N`, `F_N(nu_0)` contains an infinite-dimensional positive chart with

```text
exact Hamburger moments,
exact spectral type,
exact inverse-Cholesky frame through level N,
residual maximal full-translation HT.                     (14)
```

For an atomless base law it additionally contains the positive Hilbert cube `(13a)`.

This conclusion is local to the positive chart and makes no claim that the residual subset is
residual in every component of the whole fiber `(6)`.

## The complete tower selects exactly one carrier `[PROVED HERE + CLASSICAL OPUC]`

If `Theta(nu_1)=Theta(nu_2)`, equation `(12)` gives

```text
c_k(nu_1)=c_k(nu_2) for every k in Z.                     (15)
```

Trigonometric polynomials are uniformly dense in the continuous functions on the circle, so the
circle measures agree. Cayley inversion gives

```text
mu_nu1=mu_nu2,
nu_1=nu_2.                                                 (16)
```

Equivalently,

```text
intersection_(N>=0) F_N(nu_0)={nu_0}.                     (17)
```

The map `Theta` is continuous for the product topology: each `C_N` is a continuous function of
finitely many circle moments on the open cone of positive-definite Toeplitz matrices. Since `K_s`
is compact and the target product is Hausdorff, `(5)` is a homeomorphism of `K_s` onto its image.

Thus the complete compatible Cholesky tower is not merely a convenient normalization. It is a
faithful topological coordinate on the entire canonical carrier simplex, while every finite
projection has the positive HT aperture `(14)`.

## Singular carriers force escape of the selecting coordinate `[PROVED VIA COMPANION]`

Assume now that `mu_nu` is purely singular. The Toeplitz graph companion proves that the raw
polynomial map

```text
A_mu:c_00 subset ell^2(Z_+)->L^2(mu),
A_mu(a)=sum_n a_n zeta^n                                  (18)
```

has

```text
closure(Graph(A_mu))=ell^2(Z_+) times L^2(mu).             (19)
```

Thus ordinary graph closure forgets the carrier incidence completely.

The same companion shows that `(4)` is the unique compatible lower-triangular positive-diagonal
repair. It obeys

```text
||C_N(nu)||=lambda_min(G_N(nu))^(-1/2)->infinity,          (20)

det C_N(nu)=det G_N(nu)^(-1/2),
(det C_N(nu))^(1/(N+1))->infinity.                         (21)
```

The repaired nested maps

```text
U_nu e_n=phi_n                                             (22)
```

extend to a unitary `U_nu:ell^2(Z_+)->L^2(mu)`. Surjectivity follows from the F. and M. Riesz
theorem: for a purely singular measure, a vector orthogonal to all analytic monomials would define
a finite measure that is both absolutely continuous and singular.

The carrier geometry is therefore an exact trichotomy:

```text
every finite raw section:      positive and invertible;
unweighted cofinal graph:      maximally multivalued;
coherently repaired limit:     unitary, with ||C_N||->infinity.       (23)
```

## Residual cofinal frame-selection phase `[PROVED VIA PARENTS]`

On `K_s`, singular-continuous carriers are residual and maximal full-translation HT carriers are
residual. Their intersection `R_s` is residual. Every `nu in R_s` simultaneously satisfies:

1. all complete Hamburger moments are the prescribed moments `s`;
2. `m_nu` has differentially algebraically independent finite translate families;
3. every finite frame prefix lies in the positive-definite Toeplitz interior;
4. the full raw graph saturates as in `(19)`;
5. the complete frame coordinate selects `nu` but escapes by `(20)--(21)`;
6. every finite prefix fiber contains the positive Hilbert cube `(13a)` and maximal-HT aperture
   `(14)`.

Hence the selection threshold is generic inside one exact complete-moment constraint. It is not a
comparison between unrelated carriers.

## Cofinal Cholesky selection law

> **In an indeterminate complete-moment constraint, the canonical inverse-Cholesky tower is a
> faithful carrier coordinate, but none of its finite prefixes is a selector: every finite prefix
> retains a positive Hilbert cube and an infinite-dimensional chart with residual maximal translation
> hypertranscendence at fixed spectral type. On the generic singular-continuous HT phase, the raw
> polynomial graph saturates the full product and the uniquely selecting tower diverges. The
> carrier survives only as coherently renormalized boundary data installed before closure.**

This is the positive form of the obstruction. It does not say merely that finite Toeplitz data
fail. It identifies what must replace them: the coherent, source-marked, generally nonuniform
frame tower.

## General HT consequence

For constrained Herglotz hypertranscendence, finite positive Hilbert geometry and global carrier
selection are different levels of structure. Strict positivity of all finite sections is
compatible with residual maximal HT and with complete loss of graph incidence at the limit.

A successful constraint must supply one of the following equivalent-strength data:

1. the complete compatible inverse-Cholesky/orthogonal-polynomial tower;
2. a graph norm or boundary relation recovering the same unitary incidence;
3. a global source condition that determines the full tower before the cofinal limit.

Any uniformly bounded finite-frame identification misses the generic singular phase because the
faithful coordinate itself obeys `(20)--(21)`.

## RH-facing consequence `[ROUTE CONSTRAINT; RH NOT PROVED]`

Under RH, the normalized Xi Herglotz carrier in the companion theorem is infinite pure point and
therefore purely singular. Its raw Toeplitz graph saturates, while its coherent Cholesky tower is
the unique canonical triangular coordinate that retains the carrier and necessarily diverges.

Consequently, an RH architecture passing through the normalized Xi Herglotz/Toeplitz carrier must
derive the complete frame tower, or an equivalent boundary marking, from prime--Gamma source data.
Matching any fixed number of Taylor coefficients, Toeplitz matrices, Schur defects, or finite
prime apertures cannot perform the selection: `(14)` leaves maximal-HT carrier freedom at every
finite level. Ordinary unmarked graph convergence cannot perform it either: `(19)` erases all
incidence.

This does not orient the Xi carrier and does not imply RH. It identifies the geometry that a
zero-preserving source weld must carry.

## Parent-theory and novelty attack

1. `[SEARCH]` Cholesky factorization, Verblunsky coordinates, Bernstein--Szego approximation,
   Toeplitz determinant identities, and the F. and M. Riesz theorem are classical.
2. `[SEARCH]` Verblunsky's map is classically a homeomorphism from circle probability measures to
   the compactified parameter product; Barry Simon's survey records this and the determinant
   formulas.
3. `[SEARCH]` Yafaev identifies absolute continuity as the closability boundary for semibounded
   Toeplitz forms.
4. `[SEARCH]` Hassi--Sebestyen--de Snoo--Szafraniec give the general regular/singular decomposition
   of linear relations, including Cartesian-product closures for singular relations.
5. `[BRIDGE]` The canonical Bauer simplex, exact spectral transport, finite-jet constrained
   transversality, and residual maximal translation HT are inherited from the parent carrier
   theorems.
6. `[PROVED HERE]` Equations `(8)--(12)` identify a finite inverse-Cholesky frame exactly with a
   finite regular Cauchy jet, so the HT aperture theorem applies to the canonical Hilbert frame
   rather than to an auxiliary analytic coordinate.
7. `[PROVED HERE]` Equations `(15)--(17)` prove the sharp selection threshold: every finite frame
   projection has infinite-dimensional maximal-HT fibers, whereas the coherent full tower is a
   faithful topological coordinate.
8. `[PROVED HERE VIA COMPANIONS]` On the residual singular-continuous maximal-HT phase, this
   selecting coordinate is precisely the divergent repair that converts a maximally multivalued
   raw relation into a unitary carrier.
9. `[CANDIDATE RESIDUE]` Targeted arXiv and OpenAlex searches found no work coupling finite
   Cholesky-prefix fibers, residual full-translation differential independence, exact moment
   constraints, graph saturation, and divergent unitary repair.
10. Absence from targeted searches is not a priority proof. Specialist audits in OPUC, moment
    theory, operator relations, and differential algebra remain required.

## Honest significance score

**72/100 current; plausible range 60--82.** The result is materially stronger than the retired
orientation-product paper: the same canonical matrices define exact Hilbert-cube fibers, the
complete selector, and the unique divergent unitary repair, so the interaction is real rather than
an independently engineered Cartesian product.

It is **not a true 90**. The residual HT theorem is inherited from the constrained-transversality
parent; complete-tower injectivity is adjacent to classical Verblunsky determinacy; graph
saturation and OPUC repair are classical separately; and the theorem is generic rather than an
explicit source-canonical construction. A field-level score would require a new intrinsic source
law that forces or orients the complete tower for a distinguished HT function, not only a sharp
description of the modulus that remains without such a law. Priority is also unverified, and the
theorem has not received an independent specialist proof audit or unconditional Lean
formalization.

## Lean status

Formalization is in progress; no Stage 3 claim is made. The unconditional modules
`GaloisForLFunctions.HTGeometry.CofinalCholeskyFiniteFrame`,
`GaloisForLFunctions.HTGeometry.CayleyMomentFrame`, and
`GaloisForLFunctions.HTGeometry.CauchyJetFrame` now prove:

1. the pointwise and measure-level Cayley triangular transform;
2. exact equivalence of every finite Cayley-moment and reciprocal-moment prefix;
3. the all-order dominated-differentiation formula
   `iteratedDeriv n (resolventTransform μ) (-i)=n! reciprocalMoment μ (n+1)`;
4. for probability measures, the exact equivalence
   `G_N(μ)=G_N(ν)` iff their regular Cauchy jets agree through order `N-1`;
5. the inverse Gram identity `G_N⁻¹=C_NᴴC_N`;
6. an explicit normalized Gram--Schmidt inverse-Cholesky construction for every positive-definite
   complex Gram matrix, including lower triangularity and real strictly positive diagonal; and
7. structural uniqueness among all lower-triangular positive-real-diagonal inverse-Cholesky
   frames, and equality of the explicit canonical frames iff equality of the Gram matrices iff
   equality of the corresponding finite Cauchy jets;
8. the exact determinant identities `det C * det G * star(det C)=1` and, for the canonical
   normalization, `det C=(det G)^(-1/2)` in positive-real form; and
9. leading-principal compatibility of the canonical frames, so the finite matrices form an actual
   coherent inverse-Cholesky tower rather than an unrelated family of normalizations.

The unconditional module `GaloisForLFunctions.HTGeometry.LabeledBoundarySimplex` additionally
proves the separated-kernel core of the boundary geometry: barycenter formation, exact label
pushforward `π_*(Beta η)=η`, injectivity, probability preservation, density transport, and mutual
absolute continuity under positive reweighting. It now also proves weak continuity of barycentring
through any weakly continuous measurable probability kernel, closed topological embedding under
exact label recovery, atomlessness transport, and singularity transport under the precise
reference-null preimage hypothesis used in the manuscript.

The unconditional module `GaloisForLFunctions.HTGeometry.CofinalCholeskySelection` now proves the
complete set-theoretic selector without assuming Fourier determinacy: Fourier characters determine
a finite measure on the additive circle, the real Cayley map is a measurable embedding, all
positive Cayley moments determine a real probability measure, and equality of every canonical
inverse-Cholesky section forces equality of the original carriers. Every fixed Cayley moment and
every finite Toeplitz Gram section are also proved weakly continuous.

The unconditional module `GaloisForLFunctions.HTGeometry.HamburgerBoundaryKernel` proves the
unbounded moment-preservation step used in the Nevanlinna construction. It derives a real-valued
bind-integral theorem from positive and negative `lintegral` parts, then proves that a measurable
probability kernel whose leaves share one complete Hamburger moment sequence has a barycenter with
exactly the same sequence. Odd-moment integrability is obtained from the common even moments, so no
unproved signed Fubini interchange is hidden in this step.

The unconditional module `GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryAlgebra` now proves the
determinant-one algebra underlying the concrete boundary label: the lower row has no common zero,
distinct finite denominator fibers are disjoint, every finite fiber is disjoint from the infinity
fiber, the explicit one-point label `[-D:C]` recovers each fiber exactly, and the resolvent
Möbius-difference formula follows from the determinant identity. For continuous lower-row entries,
the label is proved continuous into `OnePoint ℝ`; at zeros of `C`, the proof derives escape from
every compact real set rather than postulating projective continuity. With the projective line
equipped with its Borel sigma algebra, a probability leaf carried by a finite or infinite
denominator fiber is proved to push forward to exactly the corresponding Dirac label.

The unconditional module `GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryKernel` assembles these
results without assuming the simplex conclusion. From a classical N-extremal family carrying one
moment sequence, its exact denominator-fiber support, and weak continuity of its leaves, it derives
exact projective labeling, complete Hamburger-moment preservation for every barycenter, and the
closed topological embedding of projective parameter laws into real carrier laws. It also derives
exact density transport through the projective label and atomlessness of the carrier from
atomlessness of the parameter law. The still-open
classical construction core is to construct this family in Lean from every normalized
indeterminate Hamburger moment sequence; the assembled theorem does not discharge that existence.

All eight exact builds pass. `#print axioms` on the capstone declarations reports only `propext`,
`Classical.choice`, and `Quot.sound`. The touched modules contain no proof debt, and the
repository-wide formal lint passes. This validates only the declarations listed above, not the
still-unformalized claims in the paper.

The remaining formalization requires continuity of the triangular positive-diagonal factor,
construction and weak continuity of the actual N-extremal Nevanlinna
kernel and projective support label, the full Bauer-simplex/topological and spectral-type layer,
finite-frame Hilbert-cube fibers, constrained full-shift transversality, topological continuity of
the complete-tower coordinate, F. and M. Riesz, graph closure as a linear relation,
OPUC/Bernstein--Szegő repair and divergence, and the final residual-set capstone.

## Gates

- [x] complete compatible frame coordinate defined
- [x] finite Cholesky prefix identified with finite Cauchy jet
- [x] infinite-dimensional positive aperture in every finite prefix fiber proved
- [x] embedded Hilbert cube in every atomless finite prefix fiber proved
- [x] residual maximal full-translation HT in the exact prefix chart proved via parent
- [x] spectral type held fixed in the prefix chart
- [x] complete tower proved injective and topologically faithful
- [x] pure-singular graph saturation imported with exact scope
- [x] unique divergent unitary repair imported with exact scope
- [x] residual singular-continuous maximal-HT phase imported
- [x] RH consequence stated only as a carrier requirement
- [x] local repository collision search
- [x] targeted external collision search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] unconditional Lean formalization of the entire theorem

## Log

- 2026-07-12 -- Identified the inverse-Cholesky frame tower as the exact canonical coordinate
  joining finite-jet aperture to singular graph saturation. Proved the finite-prefix/full-tower
  selection threshold and its residual maximal-HT singular phase.
