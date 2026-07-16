# Finite Cholesky frames retain maximal HT; the complete divergent tower selects the carrier

- **ID:** `cofinal-cholesky-carrier-selection-threshold-law`
- **Stage:** 2-fully-proven / needs-audit
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

The classical Nevanlinna input is used in its source convention
`integral (z-x)^(-1)dnu=(A*tau-C)/(B*tau-D)`, `AD-BC=1`. The carrier convention
`integral (x-z)^(-1)dnu` is obtained by the exact determinant-preserving change
`(a,b,c,d)=(-A,C,B,-D)`. Thus the source support equation `B*tau-D=0` is literally the
carrier fiber equation `c*tau+d=0`. The formal interface assumes only the classical outputs:
weak continuity of the N-extremal leaves, concentration on these denominator fibers, and their
common Hamburger moments. Projective labels, kernel measurability, and all simplex consequences
are deductions, not literature hypotheses.

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
theorem has not received an independent specialist proof or priority audit; the exact classical
Riesz-brothers, Szegő, and Nevanlinna source interfaces remain cited inputs.

## Lean status

Formalization is complete relative to the exact classical source interfaces stated on this card.
In particular, `CofinalCholeskyResidualPhase.lean` now performs the formerly optional global
weak-topology gluing: on the complete Nevanlinna carrier range it intersects the transported
singular-continuous dense `G_delta` phase with the intrinsic maximal full-translation dense
`G_delta` phase, proves the intersection dense `G_delta` and residual, and derives atomlessness,
real-Lebesgue singularity, and maximal translation freeness for every point under the stated
real-analytic lower-row hypothesis. The supporting unconditional modules
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
atomlessness of the parameter law. Weak continuity now also proves the Giry measurability required
for barycentring through a general Portmanteau-to-Giry theorem, so measurability is no longer a
second external assumption.

The unconditional module `GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface` formalizes
the exact boundary with the classical theorem. It uses the source `A,C;B,D` convention and proves
that `(a,b,c,d)=(-A,C,B,-D)` preserves determinant one, converts the source Stieltjes fraction to
the negative carrier fraction, and identifies both finite and infinite denominator fibers and the
projective label literally. Its minimal `ClassicalNevanlinnaExtremalFamily` contains no barycenter,
label-recovery, simplex, density-transport, or atomlessness conclusion. The verified adapter builds
`NevanlinnaBoundaryFamily` and derives exact source-label recovery and the closed boundary-simplex
embedding. Existence of this classical input for a normalized indeterminate Hamburger moment
sequence is invoked from the established Nevanlinna parametrization and is intentionally not
reproved in Lean.

The unconditional module
`GaloisForLFunctions.HTGeometry.CholeskyDeterminantDivergence` now proves the repair-escape
implication used in `(20)--(21)`. For every positive-definite Gram tower with canonical
inverse-Cholesky frames, vanishing normalized Gram determinants force: normalized frame
determinants to tend to infinity, the least Gram eigenvalue to tend to zero, and the Euclidean
operator norms of the frames to tend to infinity. The norm proof uses a unit least-eigenvalue
eigenvector and the exact identity `G⁻¹=CᴴC`, so it introduces no dimension-dependent determinant
estimate. The same module proves the asserted exact finite identity
`||C_N||_2=sqrt(lambda_min(G_N)^(-1))` by diagonalizing `G_N⁻¹` in the Gram eigenbasis and combining
the matching lower eigenvector bound with `||C||_2^2=||C^*C||_2`. This does not yet formalize the
OPUC/Szegő theorem that supplies normalized determinant vanishing for a purely singular circle
measure.

The unconditional OPUC modules `FiniteOPUCRootLocation`, `FiniteOPUCReversal`,
`BernsteinSzegoDensity`, `BernsteinSzegoMeanValue`, `BernsteinSzegoMomentForm`, and
`BernsteinSzegoReconstruction` close the complete finite Bernstein--Szegő layer. They construct
the normalized terminal polynomial, prove strict open-disk root location, prove the exact
reversal identity and closed-disk zero-freeness, and construct the positive reciprocal-square
boundary density. Complex mean value gives exact normalization and lower-monomial
orthogonality. The terminal polynomial then defines a finite feedback operator whose eigenvalues
are roots of that polynomial. Gelfand's formula supplies a strictly contracting power. The
difference of any two compatible Toeplitz sesquilinear forms is invariant under simultaneous
feedback, so contraction forces the difference to vanish. Consequently the stable normalized
terminal vector determines the complete finite Toeplitz section, and the Bernstein--Szegő moment
law reproduces every positive and negative Fourier coefficient in that section exactly. This is
an unconditional finite reconstruction theorem; only the separate rational Carathéodory formula
remains outside this layer.

The unconditional modules `GaloisForLFunctions.HTGeometry.GraphSaturationCore` and
`GaloisForLFunctions.HTGeometry.ToeplitzPolynomialGraph` now formalize the Hilbert-product graph
as an actual submodule, identify its orthogonal complement exactly, and prove that triviality of
the joint annihilator forces full-product graph closure. For the circle-measure polynomial map,
the coefficient inclusion, monomial synthesis, the exact monomial inner-product integral, and the
reduction from all finitely supported polynomials to monomial tests are formalized. This isolates
the remaining analytic input precisely: a one-sided Fourier rigidity theorem strong enough to
deduce triviality of the monomial annihilator for a purely singular measure. Neither module
assumes graph saturation or F. and M. Riesz. One-sided Fourier rigidity is also proved to force
density of the analytic-monomial span in `L²(μ)`, the completeness statement needed for the
unitary repaired representation.

The unconditional module `GaloisForLFunctions.HTGeometry.RieszBrothersReduction` defines
normalized Lebesgue measure on `Circle` as transported Haar probability and reduces the entire
pure-singular graph theorem to one exact classical statement: square summability of the analytic
Fourier half-line of `y · μ` makes that complex density measure absolutely continuous with
respect to circle Lebesgue measure. It proves unconditionally that the density measure is also
absolutely continuous with respect to `μ`, that a vector measure absolutely continuous with
respect to two mutually singular positive measures is zero, that zero density measure forces
`y=0` in `L²(μ)`, and hence that the monomial annihilator vanishes and the raw graph saturates.
Thus F. and M. Riesz is now the sole unproved analytic implication in this chain, not an informal
umbrella for graph or measure-theoretic steps.

The unconditional module `GaloisForLFunctions.HTGeometry.CompleteGramTowerTopology` proves that
the complete Toeplitz Gram tower is continuous and injective on real probability measures, and
that its restriction to every compact carrier family is a closed topological embedding. This
formalizes the complete-tower topological selector in the equivalent Gram coordinate.

The unconditional module `GaloisForLFunctions.HTGeometry.CanonicalFrameClosedGraph` proves that
the strict positive-diagonal inverse-Cholesky normalization is equivalent, on its algebraic
inverse-frame locus, to the closed condition of real nonnegative diagonal. The determinant-one
identity rules out every zero diagonal entry. Consequently the graph of the literal canonical
inverse-Cholesky factor over the positive-definite cone is closed.

The unconditional module `GaloisForLFunctions.HTGeometry.CanonicalFrameContinuity` proves the
missing compact-range control and promotes that closed graph to actual continuity. Its key bound
is `|C i j|² ≤ (G⁻¹ j j).re`, hence `||C|| ≤ ||G⁻¹||+1` in the elementwise finite-matrix
norm. Local continuity of matrix inversion therefore traps all nearby canonical frames in one
compact ball; every cluster point lies in the closed canonical graph and uniqueness identifies it
with the limiting frame.

The unconditional module `GaloisForLFunctions.HTGeometry.CompleteFrameTowerTopology` applies this
fixed-level theorem to Cayley--Toeplitz probability measures with positive-definite sections at
every level. The literal complete positive-diagonal inverse-Cholesky tower is continuous and
injective in the weak/product topologies, and its restriction to every compact carrier family is
a closed topological embedding. Thus the paper's exact `C_N` topological selector, rather than
only its equivalent Gram coordinate, is now formalized.

The unconditional modules `GaloisForLFunctions.HTGeometry.PositiveHilbertCubeEmbedding`,
`FiniteConstraintBlockKernel`, and `CountableConstraintBlockAperture` prove the Banach-space core
of the finite-fiber aperture. A geometrically weighted biorthogonal kernel sequence gives a closed
embedded signed Hilbert cube, every point stays in the exact affine finite-constraint fiber, and
the total perturbation norm is at most its prescribed radius. Countably many separated
`(k+1)`-atom blocks produce such a sequence for every `k`-constraint operator.

The unconditional modules `GaloisForLFunctions.HTGeometry.LinftyFiniteConstraintAperture` and
`LinftyPositiveAperture` instantiate that geometry in real `L∞`. Normalized `L¹` indicator
pairings give exact biorthogonal coordinates on pairwise-disjoint positive measurable blocks.
Every aperture of radius below one about the constant density is strictly positive almost
everywhere, so it defines an injective family of positive density measures.

The unconditional module `GaloisForLFunctions.HTGeometry.AtomlessProjectivePositiveAperture`
derives the required countable positive block partition from the paper's actual atomlessness
hypothesis on `OnePoint ℝ`. It transports the law to the real chart, proves continuity of its CDF
from singleton-nullity, chooses strictly increasing quantile cuts, and pulls the resulting
pairwise-disjoint positive intervals back to the projective line. Thus no stronger unstated
nonatomic-divisibility axiom is used.

The unconditional modules
`GaloisForLFunctions.HTGeometry.ProjectiveFiniteConstraintCarrierAperture` and
`AtomlessProjectiveFrameFiber` connect the aperture to the literal carrier geometry. Finite real
`L¹` constraints, including normalization, produce a closed embedded Hilbert cube of positive
parameter probabilities; the Nevanlinna barycenter remains a closed embedding, preserves the
complete Hamburger moment sequence, and is injective by exact projective label recovery. Choosing
the real and imaginary parts of the leaf Cayley moments as the finite constraints proves that
every carrier in the cube has exactly the same level-`N` Cayley--Toeplitz Gram section and the same
regular Cauchy jet through order `N-1` as the base barycenter. This is the paper's literal
atomless Hilbert-cube frame-fiber proposition.

The unconditional module `GaloisForLFunctions.HTGeometry.InfiniteSupportPositiveAperture`
strengthens the measurable-block input: atomlessness is unnecessary. Any finite Borel measure
whose topological support is infinite and conull contains countably many pairwise-disjoint
positive measurable pieces, obtained from disjoint open subsets of its support. Consequently every
finite real `L¹` constraint fiber through density one contains a closed embedded positive Hilbert
cube. The projective carrier and exact Cayley-frame capstones are now proved under the paper's
weaker standing hypothesis that the parameter law has infinite support, while retaining mutual
absolute continuity, all Hamburger moments, the level-`N` Gram section, and the regular Cauchy jet
through order `N-1`.

The unconditional module `GaloisForLFunctions.HTGeometry.InfiniteSupportCayleyGram` proves the
paper's strict finite-section assertion rather than assuming it. The level-`N` Cayley--Toeplitz
matrix is the literal `L²` Gram matrix of the conjugate Cayley monomials. A linear dependence would
give a polynomial vanishing on the infinite injective Cayley image of the measure support, so every
coefficient vanishes and the Gram matrix is positive definite. Thus infinite support alone supplies
all finite inverse-Cholesky factors.

The unconditional modules `GaloisForLFunctions.HTGeometry.InfiniteSupportFrameTowerTopology` and
`InfiniteSupportBoundaryCarrier` propagate this fact through the complete selector. The complete
canonical frame tower is continuous and injective on infinite-support real probabilities and is a
closed topological embedding on each compact subfamily, with no separately supplied positivity
proof. Exact projective-label recovery also transports infinite support from a Nevanlinna parameter
law to its barycenter. Consequently the complete boundary-carrier tower directly selects every
infinite-support projective law and is a closed embedding on compact subfamilies of that boundary
domain.

The unconditional module
`GaloisForLFunctions.HTGeometry.ConstrainedCauchyJetControllability` now proves the exact finite
surjectivity core used by constrained translate transversality. For disjoint frozen and target
packets of distinct upper-half-plane Cauchy nodes, the target real-mass control map remains
surjective after restriction to the exact kernel of the frozen packet. The proof applies the
already-formalized controllability theorem to the combined packet with prescribed value
`(0,target)`. Surjectivity is proved invariant under arbitrary invertible linear coordinate changes
on the frozen and target packets, providing the exact interface for the Nevanlinna triangular
conversion. The same module proves positive algebraic escape inside the frozen kernel: every
nonzero polynomial relation on a disjoint finite target packet is broken by an arbitrarily small
finitely supported real perturbation that preserves positivity and annihilates the frozen packet
exactly. This closes the finite kernel-surjectivity and fixed-pattern escape statements.

The unconditional module `GaloisForLFunctions.HTGeometry.NevanlinnaJetTriangular` proves the
analytic conversion used in the manuscript rather than leaving it as a principal-part argument.
For `a(w)(tau-q(w))^{-1}`, it recursively expands every genuine iterated `w`-derivative into
parameter Cauchy powers, proves that the coefficient matrix is lower triangular with exact
diagonal `r! a(z) (q'(z))^r`, and constructs the resulting finite complex-linear equivalence when
`a(z)q'(z)` is nonzero. Products of these equivalences over arbitrary finite node packets identify
the genuine jet packet exactly. Restricting scalars to the reals and composing with the Cauchy
control map proves that a disjoint genuine target Nevanlinna-jet packet remains onto after a
genuine frozen packet is annihilated exactly.

The unconditional module `GaloisForLFunctions.HTGeometry.EvaluationCodimensionCore` proves the
root-counting core of the evaluation-codimension lemma. A nonzero tensor of coefficient
polynomials of degree at most `q`, evaluated at injectively indexed row parameters, can vanish
identically across all monomial labels on at most `q` rows. Equivalently, at least
`card(rows)-q` independent row variables carry a nonzero polynomial constraint. This validates
the precise algebraic count used before projectivizing the coefficient vector. It does not yet
formalize algebraic codimension, incidence projection, stratification, parametric transversality,
or the uncountable-shift Baire promotion.

The unconditional modules
`GaloisForLFunctions.HTGeometry.DisjointBlockPolynomialIndependence` and
`EvaluationIncidenceFiberIndependence` formalize the next fixed-coefficient layer without
mislabeling it as codimension. Every nonconstant complex multivariate polynomial admits an affine
line restriction of positive degree and hence a transcendental line restriction. Simultaneously
specializing disjoint row-variable blocks to those lines proves that any family of nonconstant
row polynomials becomes algebraically independent after disjoint-block embedding. Applied to a
nonzero bounded coefficient tensor, root counting supplies at least `card(rows)-q` active row
equations; either one is a nonzero constant, making the fixed incidence fiber empty, or all active
row equations have algebraically independent disjoint-block embeddings. This is an exact
fixed-coefficient independence certificate. It is not yet a regular-sequence, Krull-height,
projective-incidence, projection-dimension, stratification, or parametric-transversality theorem;
algebraic independence alone would not justify any of those stronger conclusions.

The unconditional modules `GaloisForLFunctions.HTGeometry.NonconstantMvPolynomialRoot`,
`ScalarExtendedPolynomialRegular`, `ScalarExtendedPolynomialProper`,
`ScalarExtendedHypersurfaceDimension`, `IteratedBlockHypersurfaceDimension`,
`FiniteFamilyBlockHypersurfaceDimension`, and `EvaluationIncidenceFiberDimension` now close the
genuine fixed-coefficient Krull-dimension step. Every nonconstant complex multivariate polynomial
has a zero. After scalar extension to any nontrivial complex coefficient algebra, it therefore
remains a nonunit; independently, its nonzero scalar leading coefficient makes it a
non-zero-divisor even if the coefficient algebra has zero divisors. Its principal hypersurface
ideal is proper and its quotient lowers Krull dimension by at least one. Iterating this argument
through fresh row-variable blocks proves that `r` nonconstant row equations lower the iterated
coordinate-ring dimension by at least `r`. Consequently every nonzero bounded coefficient tensor
has at least `card(rows)-q` active rows and its fixed incidence fiber is either empty or has this
exact additive Krull-dimension drop. The remaining algebraic gap begins only when the coefficient
tensor is allowed to vary projectively: affine/projective coefficient charts, total incidence
dimension, projection to packet space, and the resulting finite algebraic stratification are not
yet formalized.

The unconditional modules `GaloisForLFunctions.HTGeometry.MvPolynomialCoefficientRegular`,
`EvaluationCodimensionFieldCore`, `ProjectiveCoefficientPrimeActivity`, and
`PrimeLocalizedRowRegularity` enter the genuinely projective layer. A finite-variable
multivariate McCoy theorem is proved: one non-zero-divisor coefficient makes the entire
multivariate polynomial a non-zero-divisor. The bounded root count is extended from complex
coefficients to tensors over an arbitrary field. Applying it in the fraction field of every prime
coefficient specialization proves the uniform projective constraint: at any coefficient prime
where not all projective coordinates vanish, at least `card(rows)-q` universal row-coefficient
polynomials lie outside that prime. Localizing at such a coefficient prime turns any surviving
coefficient into a unit, and the associated row polynomial is formally a non-zero-divisor. Thus
the pointwise/projective-prime activity count and the local row-regularity mechanism are closed.
What remains is to assemble these locally regular active rows into the total incidence-ring height
bound, subtract the projective coefficient dimension, control projection to packet space, and
produce the finite algebraic stratification used by transversality.

The unconditional modules `GaloisForLFunctions.HTGeometry.IteratedUnitCoefficientBlockDimension`
and `ProjectivePrimeLocalIncidenceDimension` now perform that local assembly. Over an arbitrary
Noetherian coefficient ring, any finite list of fresh finite-variable equations with one unit
coefficient per equation defines an iterated quotient whose Krull dimension drops by at least the
length of the list. Instantiating the coefficient ring by the localization at a projectively
nonzero coefficient prime, the active rows are enumerated as a finite family; every surviving
coefficient is a localization unit, and the complete active local incidence ring loses one Krull
dimension per active row. Combined with the projective-prime root count, this proves the local
total-incidence height mechanism at every projectively relevant coefficient prime. The remaining
algebraic work is the comparison between these iterated local block rings and the single global
incidence coordinate ring, the global/projective dimension bound after subtracting coefficient
dimension, projection to packet space, and finite stratification.

The unconditional modules `GaloisForLFunctions.HTGeometry.FiniteDimensionalDensityControl` and
`GaloisForLFunctions.HTGeometry.LinftyDensityControl` close the abstract passage from atomic
finite-support control to the manuscript's bounded-density tangent. A continuous vector-valued
`L¹` kernel defines a continuous real `L∞` Bochner control. Normalized indicators of shrinking
positive-measure neighborhoods approximate every kernel column on the topological measure
support. Because a linear range in a finite-dimensional target is closed, surjectivity of finite
support combinations of support columns implies exact surjectivity of the `L∞` density control.
This theorem is unconditional and does not replace `L∞` densities by point masses.

The unconditional module `GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl`
instantiates that bridge on the paper's actual projective parameter line. Every nonreal-pole
Cauchy power extends continuously to `OnePoint ℝ` with value zero at infinity. Infinite
projective support remains infinite after removing the single infinity point, so its finite real
support parameters supply the spanning columns. Consequently every finite upper-half-plane
Cauchy packet is exactly controlled by real `L∞` densities, and every disjoint target packet stays
onto on the exact kernel of a frozen packet. Composing with the triangular Nevanlinna packet
equivalence proves the literal constrained genuine Nevanlinna-jet surjectivity asserted in the
first half of Proposition `prop:transversality`. At finite projective parameters the formal column
is proved equal to the actual iterated analytic jet; at infinity both perturbation columns vanish.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaPolynomialEscape` derives the literal positive
fixed-pattern consequence in that Banach chart. For every prescribed nonzero multivariate
polynomial on a disjoint finite target jet packet and every positive radius, there is a real
`L∞` perturbation in the exact frozen genuine-jet kernel whose norm is below the radius, whose
addition to density one is strictly positive almost everywhere, and whose target packet escapes
the polynomial zero set. Thus fixed finite algebraic-pattern density is now formalized with exact
frame preservation and positivity; only simultaneous parameter-family avoidance remains.

The unconditional module `GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaGenericity` upgrades
fixed escape to the full countable category layer. The projective Nevanlinna control is promoted
to a continuous real-linear map. Every fixed nonzero affine target-polynomial defect in the exact
frozen kernel is closed and nowhere dense. Since the kernel of a continuous frozen control is a
complete normed space, every countable family of certified surjective target patterns is
simultaneously avoided on a dense residual subset. Consequently ordinary Baire assembly is no
longer a gap; what remains is precisely the uncountable shift-configuration reduction that must
make each compact configuration patch one open dense condition by incidence codimension and
parametric transversality.

The unconditional module `GaloisForLFunctions.HTGeometry.CompactConfigurationBaire` closes the
topological half of that uncountable reduction. For a jointly continuous defect map, avoidance of
a closed bad locus uniformly over a compact configuration patch is proved open by the generalized
tube lemma; pointwise continuity is not substituted for uniform patch control. A countable compact
exhaustion then upgrades patchwise dense avoidance to global avoidance of every configuration on a
dense residual set. The dependent theorem handles countably many relation patterns with different
configuration and target spaces, and sigma-compactness supplies all compact exhaustions
automatically. Consequently the only remaining uncountable-configuration input is patchwise
density from the incidence-codimension/stratified parametric-transversality argument; compact-patch
openness and the subsequent Baire promotion are now unconditional Lean.

The unconditional module
`GaloisForLFunctions.HTGeometry.InjectiveShiftConfigurationTopology` verifies the exhaustion
hypothesis for the manuscript's literal configuration spaces. For every finite shift label type,
the collision-free locus is the finite intersection of the open inequalities `h_i != h_j`.
Therefore `InjectiveShiftConfiguration` is an open finite-dimensional complex configuration
space and is sigma-compact. The compact exhaustion used above is thus obtained without replacing
the uncountable complex shifts by a countable palette.

The unconditional modules
`GaloisForLFunctions.HTGeometry.EvaluationRankDefectTopology` and
`ExpandedEvaluationConfigurationBaire` close the concrete bad-locus side of this reduction. For
the literal rectangular matrix whose columns are the coefficient-degree/differential-monomial
labels, loss of coefficient-uniform rank is exactly `det(A^* A)=0`; hence the complete rank-defect
locus is closed without choosing a square minor. The expanded matrix depends continuously on the
finite row-jet packet. Combining this with the compact-configuration theorem proves, in Lean, that
compact-patch density for every countable relation pattern promotes to one dense residual
parameter set having full evaluation rank for every complex shift configuration. Thus neither
closedness of the rank defect, its semantic identification with failure of coefficient-uniform
rank, nor the countable/global Baire quantifiers remain in the transversality gap.

The unconditional module `GaloisForLFunctions.HTGeometry.CompactUniformFiniteProbe` closes the
finite-dimensional-parameter reduction that precedes Hirsch transversality. A surjective member
of a continuous family of controls with fixed finite-dimensional target has a linear right
inverse; nonvanishing of the determinant after composing nearby controls with that right inverse
produces an open neighborhood controlled by one finitely generated probe subspace. Compactness
then selects finitely many such neighborhoods, and the finite sum of their probe spaces is
surjective at every point of the compact family. Thus compact pointwise Cauchy-jet controllability
forces one common finite-dimensional perturbation manifold on the whole patch. In the carrier
application, the remaining analytic obligation for this theorem is continuity, in operator norm,
of the shift-dependent constrained Nevanlinna control family.

The unconditional module `GaloisForLFunctions.HTGeometry.LinftyKernelControlContinuity` reduces
that operator-topology obligation to the natural analytic statement. The map sending an `L^1`
vector kernel to its `L^infinity` density-control operator is itself continuous linear in operator
norm. Therefore any shift-dependent projective Cauchy-jet kernel that is continuous as an `L^1`
class automatically yields the continuous control family required by the compact uniform-probe
law. The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveCauchyKernelContinuity` closes the first concrete
analytic step. On every upper-half-plane collar `Im x >= eta > 0`, the projective resolvent obeys
the uniform bound `dist ((t-x)^-1) ((t-y)^-1) <= eta^-2 dist x y`, including the point at infinity.
Finite Cauchy-power packets therefore vary continuously in the projective sup norm, hence in
`L^1`, and their actual `L^infinity` density-control operators vary continuously in operator norm.
The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaKernelContinuity` closes the forward genuine-jet
conversion without introducing continuity of an inverse triangular matrix. The finite forward
Nevanlinna expansion remains continuous even where `a` or `q'` vanishes; those nonvanishing
hypotheses enter only when surjectivity is invoked. On the regular locus the direct expansion
control is proved equal to the existing triangular genuine-jet control. Finally,
`GaloisForLFunctions.HTGeometry.CompactNevanlinnaUniformProbe` restricts this continuous family to
the exact fixed frozen tangent and proves that every compact regular target-packet family has one
common finitely generated perturbation subspace which remains surjective at every packet. Thus
operator continuity, fixed-tangent restriction, and compact finite-dimensional uniformization no
longer belong to the transversality gap. What remains is the projectivized incidence projection,
finite algebraic/Whitney stratification, and the classical smooth parametric-transversality
instantiation producing compact-patch density.

The unconditional modules `GaloisForLFunctions.HTGeometry.MinimalTypeNoArithmeticProgression`,
`MinimalTypeNevanlinnaAperiodicity`, `MinimalTypeProjectiveSeparation`, and
`MinimalTypeProjectiveForbiddenSeparation` close the manuscript's translation-separation input.
The first proves quantitatively from Jensen's formula that an entire function of minimal
exponential type cannot vanish on a nonconstant complex arithmetic progression. The next three
upgrade this to the homogeneous geometry actually used by the Nevanlinna row: determinant/no-
common-zero data make the projective quotient aperiodic, every finite injective complex-shift
packet has arbitrarily high regular rows with pairwise distinct values of `-D/C`, and those rows
can simultaneously avoid an arbitrary finite frozen parameter packet. Thus neither the
real/nonreal period split nor an unproved row-selection step remains. This does not formalize the
subsequent algebraic-incidence codimension or perturbative parametric-transversality argument.

The unconditional modules `GaloisForLFunctions.HTGeometry.CompactProjectiveSeparationAtlas`,
`ProjectiveDerivativeNoncritical`, and `CompactNoncriticalProjectiveSeparationAtlas` close the
uniform compact-patch and noncriticality refinements that the manuscript's original paragraph
left implicit. For each fixed row the complete separation condition is open in the finite complex
shift configuration. Arbitrarily high good-row opens cover the injective configuration space, so
every compact shift patch has a finite row atlas. The Wronskian numerator
`D * deriv C - deriv D * C` is proved nonzero: if it vanished identically, `D/C` would be locally
constant on a regular ball and hence globally projectively constant, contradicting a zero of `C`
where `D` is nonzero. Multiplying its shifted values into the row certificate makes every atlas
row satisfy the missing `q' != 0` hypothesis of the triangular Nevanlinna jet conversion. Thus
compactness, finite row selection, openness, frozen-pole avoidance, and noncriticality are no
longer part of the transversality gap.

The unconditional modules `GaloisForLFunctions.HTGeometry.CoefficientPrimeActivityGeneral` and
`CoefficientPrimeLocalIncidenceDimensionGeneral` remove the special dependence on the universal
polynomial coefficient ring from the projective-prime argument. For an arbitrary finite complex
coefficient algebra and every coefficient prime at which some bounded-degree coordinate survives,
at least `card(rows)-q` row-coefficient polynomials survive. Localizing at that prime makes the
selected coefficient in each surviving row a unit, so the complete active block ring has the
corresponding additive Krull-dimension drop.

The unconditional module `GaloisForLFunctions.HTGeometry.ProjectiveAffineChartIncidenceDimension`
then dehomogenizes the projective coefficient tensor at an arbitrary nonzero coordinate. A chart
with `P` homogeneous coefficient coordinates has exactly `P-1` affine coefficient variables.
After adjoining the inactive row blocks freely and applying the localized active-row height bound,
the chart-local incidence ring satisfies the manuscript's exact numerical threshold

```text
dim(local incidence) + (card(rows) - P - q + 1) <= card(rows) * n
```

whenever `P + q < card(rows)`. This is an exact local incidence-ring theorem at every coefficient
prime of every affine projective chart. It does not identify these iterated local models with a
single global incidence scheme, assemble the finite chart cover or a finite algebraic
stratification, bound a projection to packet space, or prove smooth parametric transversality.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveAffineChartFullIncidenceDimension` removes one remaining
upper-model ambiguity. The active row equations are imposed in their disjoint blocks, every
inactive row is then assigned its own remaining packet block, and the ideal generated by all
inactive equations is quotiented out. This all-row coefficient-prime-localized incidence ring is
a quotient of the previous free inactive-row model, so it inherits the same exact threshold. The
dimension theorem therefore applies to a presentation containing every row equation, not merely
to a ring in which the inactive equations were discarded. What remains algebraically is the
comparison with a single global affine-chart incidence coordinate ring across its coefficient
primes and the finite chart/stratum assembly.

The unconditional module `GaloisForLFunctions.HTGeometry.ProjectiveCoefficientChartCover` proves
the set-theoretic chart assembly used by the incidence argument. Every nonzero coefficient tensor
has a nonzero coordinate, dehomogenizes in that coordinate's affine chart, and is reconstructed as
a nonzero scalar multiple of the chart-normalized tensor. Evaluation of the chart's universal
coefficient polynomials is proved equal to these literal normalized coordinates, and evaluation of
each universal row-coefficient polynomial is proved equal to the corresponding bounded row sum.
Thus the affine polynomial charts really cover the projective coefficient vectors and encode the
paper's row equations. The unresolved assembly is now scheme-theoretic/local-dimension comparison
and stratification, not the elementary projective cover or its equation semantics.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveAffineChartGlobalIncidenceRing` constructs the missing
global source object on each affine coefficient chart. It uses one packet-variable block per row,
places every universal row equation in its corresponding block, and quotients the single global
polynomial ring by the ideal generated by all rows. Coefficient evaluation is proved to produce
the literal fixed-coefficient row polynomial. A point of the global zero locus is therefore
equivalent, term for term, to the manuscript's projectivized null-vector incidence equations.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveAffineChartIncidenceBaseChange` then proves the genuine
coefficient-localization bridge. Mapping coefficients to `Localization.AtPrime p` carries every
global row generator to its explicit localized row polynomial and carries the entire global
incidence ideal to the ideal generated by those localized equations. The resulting quotient is
formally an `IsLocalization` of the global chart incidence quotient at the image of the
coefficient-prime complement. Thus the global scheme, its equations, and coefficient-prime base
change are now connected.

The unconditional module `GaloisForLFunctions.HTGeometry.IteratedBlockEvaluation` supplies the
universal map needed for that last comparison. A list of polynomial block equations, together with
target coordinates on which each equation vanishes, now induces an algebra homomorphism from the
successive fresh-block quotient. The homomorphism is proved to send the outer block variables to
their prescribed target coordinates and the embedded tail coefficient ring through the recursively
constructed tail map. This is the exact universal-property mechanism required to map the
active-row iterated quotient into the base-changed global incidence quotient. Its strengthened
coordinate theorem constructs a canonical preimage for every coordinate in every nested block.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveAffineChartActiveEvaluation` now constructs that
project-specific map. Every active row is turned into block-equation data by evaluating its packet
variables at their corresponding classes in the base-changed global quotient. Membership of the
localized row generator in the base-changed incidence ideal proves the required vanishing. The
universal iterated evaluator then yields an algebra homomorphism from the exact active block ring
to the base-changed global quotient. The evaluation and its exact active-coordinate witnesses are
constructed together, so no unproved dependent transport remains.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveAffineChartFullEvaluation` closes the local-presentation
comparison. It extends the active map across every inactive packet variable, proves that every
inactive row generator maps to zero, and therefore descends through the all-row local incidence
ideal. Every global packet coordinate then has an explicit preimage: active rows use their nested
block witness and inactive rows use their free packet variable. Polynomial induction proves that
the descended map onto the genuine base-changed global incidence quotient is surjective. Krull
dimension consequently transfers along this surjection, proving the manuscript's exact
evaluation-codimension threshold for the actual coefficient-prime localization of the single
global affine-chart incidence ring. The coefficient-prime bounds are assembled globally by the
next module.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveAffineChartGlobalIncidenceDimension` closes the
local-to-global algebraic step. Every prime of the genuine global chart incidence ring is
contracted to its coefficient-ring prime. Localization at the coefficient-prime complement keeps
that global prime alive, preserves its height under the localization prime correspondence, and
places it under the already formalized localized incidence bound. A generic prime-height supremum
lemma then assembles the uniform local inequalities into the manuscript's exact global
Krull-dimension threshold

```text
dim(global chart incidence) + (card(rows) - P - q + 1) <= card(rows) * n.
```

Thus the paper's global incidence-ring dimension estimate is now unconditional Lean. Finite
algebraic/Whitney stratification, projection control, and smooth parametric transversality remain
unformalized.

`GaloisForLFunctions.HTGeometry.RieszBrothersRieszFischer` formalizes the Riesz--Fischer reduction
in the graph-saturation proof. It transports the Fourier Hilbert basis from the additive circle to
the multiplicative circle, extends every square-summable analytic half-line by zero to an
`ℓ²(ℤ)` sequence, and constructs an `L²` circle function with exactly the prescribed analytic
monomial coefficients.

The unconditional module
`GaloisForLFunctions.HTGeometry.AnalyticPolynomialHardyFactorization` now closes the finite
factorization step in the F. and M. Riesz proof. For every nonzero complex polynomial it reflects
the open-disk zeros into a literal finite Blaschke factor, proves the complementary outerization
is zero-free on the open disk, and constructs holomorphic factors `p = g h`. With no unit-circle
zeros, the factors extend through the boundary and satisfy the exact identities
`|g|^2 = |h|^2 = |p|` there.

The unconditional modules
`GaloisForLFunctions.HTGeometry.HardyCoefficientBound`,
`AnalyticPolynomialHardyCoefficients`, `HardyTaylorCoefficient`, `CircleFejerKernel`, and
`FAndMRieszFejerPolynomial` now close the next finite-to-uniform layer. They prove that every
finite analytic polynomial has disk-analytic factors whose Taylor coefficients lie in `ℓ²`, whose
squared coefficient norms are bounded by the polynomial boundary `L¹` norm, and whose coefficient
convolution is exactly the original polynomial. For two integrable circle densities with equal
nonnegative analytic moments, Lean constructs the finite analytic Fejer polynomial of the
remaining moment half-line, identifies its boundary values with the exact nonnegative Fejer
convolution, and proves the uniform estimate

```text
boundaryL1(P_N) <= integral |f| dmu + integral |g| dnu.
```

`HardyCoefficientCompactness`, `FAndMRieszHardyCompactness`, `CircleRieszFischerFourier`, and
`HardyProductConvolution` close the sequential compactness and limiting-product layer.
`CircleFourierDensityUniqueness` proves Laurent-moment uniqueness for finite positive measures,
real signed density measures, and complex density-measure differences. Finally,
`FAndMRieszVanishing` proves the vanishing-half-line F. and M. Riesz conclusion for every finite
circle measure, with no classical-interface hypothesis. Thus the Riesz-brothers graph-saturation
input is now unconditional Lean. This closes the former Riesz analytic boundary; it does not close
the separate Nevanlinna-family and finite-dimensional transversality boundaries of this card.

The unconditional modules `GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws` and
`CircleAtomlessProbabilityLaws` formalize the first half of the paper's residual
singular-continuous premise. On every compact metric probability space, atomlessness is expressed
as a countable intersection of open finite-closed-cover mass conditions. On the additive unit
circle, normalized restrictions of Haar measure to shrinking balls form an explicit atomless
approximate identity; convolution by this family approximates every probability law. Hence
atomless circle laws are a dense `G_delta` in the weak topology.

The unconditional module `GaloisForLFunctions.HTGeometry.SingularProbabilityLaws` formalizes the
second half. Singularity to an outer-regular reference is equivalent to a countable family of open
two-sided concentration conditions with summable geometric errors. The reverse implication is
proved by the first Borel--Cantelli lemma. Density is proved by constructing arbitrarily fine
measurable countable-range quantizers on separable metric spaces, showing that their pushforwards
are singular to every atomless Borel reference, and bounding their Levy--Prokhorov distance by the
uniform point displacement.

The unconditional module
`GaloisForLFunctions.HTGeometry.CircleSingularContinuousResidual` intersects those two dense
`G_delta` constraints in the Baire probability space on the circle. It proves exactly that
atomless Haar-singular, hence singular-continuous, circle probability laws form a dense
`G_delta`.

The unconditional module
`GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual` constructs a concrete
homeomorphism from the real projective line `OnePoint ℝ` to the additive unit circle and lifts it
to a homeomorphism of weak probability-law spaces. It defines projective Lebesgue probability as
the standard Cauchy law in the finite chart, proves it atomless, and proves that atomless laws
singular to this reference form a dense `G_delta` on the actual Nevanlinna parameter line. The
closed Nevanlinna barycenter embedding transports this phase to a dense `G_delta` in its exact
carrier range, and every transported carrier is atomless unconditionally.

The unconditional module `GaloisForLFunctions.HTGeometry.AnalyticNullPreimage` proves the missing
one-dimensional analytic law: the zero set of a nonzero global real-analytic function is
countable, every nonconstant global real-analytic map pulls Lebesgue-null sets back to
Lebesgue-null sets, and the corresponding local-domain theorem holds when the derivative is
nowhere locally identically zero. The proof isolates the countable critical set and uses local
analytic inverses on its complement; no project-specific analytic axiom is introduced.

The unconditional module `GaloisForLFunctions.HTGeometry.ProjectiveLabelNullPreimage` applies this
law to the exact Nevanlinna label. Standard Cauchy probability and real Lebesgue measure are proved
to have the same null sets in the finite chart. For a determinant-one lower row, the finite and
infinite denominator fibers force the derivative numerator of `-D/C` to be nonzero; hence the
affine projective label is nowhere locally flat. Under the manuscript's stated real-analytic
lower-row hypothesis, every projective-reference-null Borel set therefore has a
real-Lebesgue-null label preimage. Consequently every carrier in the transported residual phase
is unconditionally atomless and real-Lebesgue singular, exactly the paper's
singular-continuous carrier conclusion. Only its intersection with the still-open maximal
full-translation HT residual set remains part of the final carrier capstone.

All listed exact modules pass. `#print axioms` on the new frame-fiber, selector,
constrained-control, triangular-jet, evaluation root-count, bounded-density, and projective
Nevanlinna-control/escape/genericity, compact-configuration Baire assembly,
sigma-compact injective-shift topology, rectangular evaluation-rank-defect topology, and expanded
evaluation configuration Baire assembly, compact uniform finite-probe reduction, and `L^1`-kernel
to `L^infinity`-control operator-norm continuity, projective Cauchy and forward genuine
Nevanlinna-kernel continuity, exact equality with the regular triangular control, fixed frozen-
tangent continuity, and compact regular-family uniform finite-probe control,
minimal-type projective-separation, compact-atlas, and
noncriticality, disjoint-block independence, scalar hypersurface, iterated Krull-dimension, and
fixed-incidence-fiber, coefficient-prime, projective affine-chart, and all-row local incidence
and projective-chart cover, global-incidence, incidence-base-change, and iterated-evaluation
active-block-evaluation, full-evaluation-surjectivity, genuine localized-incidence-dimension,
global-incidence-dimension, Riesz--Fischer reconstruction, atomless-law, singular-law,
countable-quantization, Levy--Prokhorov, circle and projective residual singular-continuous, and
exact carrier-range transport, analytic null-preimage, projective-label nonflatness, and
singular-continuous carrier, finite Toeplitz shift-isometry, normalized OPUC degree, strict
OPUC root-location, reversal, reciprocal-square density, mean-value orthogonality, moment-form,
stable-terminal reconstruction, exact Bernstein--Szegő prefix, ratio-to-root,
source-faithful Szegő-interface, pure-singular carrier-trichotomy, coherent finite-frame
polynomial, stable diagonal-row, exact coherent-span, and canonical Hilbert-basis/unitary
capstones reports only
`propext`, `Classical.choice`, and `Quot.sound`. The touched
modules contain no proof debt, and the
scoped carrier module builds pass, the repository-wide formal lint passes, and the generated
declaration indexes are current. The current aggregate build is independently blocked by the
unrelated sign-direction error in `RectangularKreinInertia`; no theorem in the carrier import
chain depends on that module. This validates only the declarations listed above and the relative
capstones named below.

The project-specific compact-patch density chain is now formalized. The global incidence-ring
bound is converted to a finite real-codimension stratification of the literal projected rank
defect through the general classical proper-projection/Whitney interface
`ClassicalComplexProjectiveIncidenceGeometry`. The actual Nevanlinna row-evaluation family is
smooth in operator norm; constrained pointwise surjectivity is promoted to one uniform finite
probe on each compact shift patch; the general classical parametric-transversality interface then
gives compact-patch density. Sigma-compact exhaustion and countable Baire intersection produce
one residual tangent locus simultaneously covering every finite differential pattern and every
tuple of distinct complex shifts. The analytic bridge identifies the abstract evaluation packet
with literal derivatives of the weighted-carrier Cauchy transform and promotes all finite pattern
rigidity to repository-level `Hypertranscendental`.

The frozen constraint is imposed in projective Cauchy-power coordinates while movable targets
remain genuine Nevanlinna jets. The everywhere-defined forward triangular map proves that frozen
actual jets are preserved without noncriticality at the frozen point. The upper source node `i`
supplies the controllability chart; conjugation of real-measure Cauchy jets proves that this
freezes the conventional frame at `-i`, and hence the exact finite Cayley Toeplitz/Cholesky prefix.
For every fixed infinite-support projective singular-continuous law, the positive mass-one part of
this exact frozen tangent consists entirely of atomless singular probability carriers with the
same Hamburger moments, while a dense residual subset has a literal hypertranscendental Cauchy
transform. Compact-patch density, actual Nevanlinna-image identification, the
singular-continuous/HT intersection in the positive chart, and the relative carrier capstone are
therefore closed in Lean.

The classical N-extremal source is matched convention-by-convention by
`NevanlinnaClassicalInterface`; its existence for an indeterminate Hamburger sequence remains an
unproved Lean obligation. The Riesz-brothers boundary is no longer external:
`FAndMRieszVanishing` proves the required one-sided density theorem, and
`RieszSingularSzegoCollapse` derives the singular Szegő limit internally from analytic-polynomial
completeness. Lean therefore proves graph saturation, analytic-polynomial completeness,
ratio-to-root collapse, least-eigenvalue collapse, and normalized-determinant and
Euclidean-operator-norm escape without a Riesz or singular-Szegő interface hypothesis.
The unitary carrier realization is now closed: Lean proves that the finite canonical frames
synthesize orthonormal polynomial families, leading-principal coherence stabilizes every row, the
stable diagonal rows have exactly the analytic-monomial span, and F. and M. Riesz upgrades them to
a Hilbert basis and unitary `ell^2 -> L^2(mu)`.

Formalization audit (needs-audit pass): the circle Fourier-density theorem, singular Szegő collapse,
graph saturation, frame escape, and coherent unitary construction are now unconditional and
axiom-clean. `PureSingularCarrierTrichotomy` and `PureSingularCarrierUnitary` contain the downstream
carrier deductions, and `FAndMRieszVanishing` discharges their former analytic input.
The indeterminate-Hamburger Nevanlinna-family construction remains a source-faithful interface, not
an unconditional theorem. The two general geometry inputs also remain packaged as
proper-projective-image/Whitney stratification and smooth finite-dimensional parametric avoidance.
All three must be constructed in Lean before this card can move to Stage 3 under the unconditional
proof rule. Bernstein--Szegő finite-prefix reproduction is already unconditional through
stable-terminal feedback reconstruction.

## Gates

- [x] complete compatible frame coordinate defined
- [x] finite Cholesky prefix identified with finite Cauchy jet
- [x] infinite-dimensional positive aperture in every finite prefix fiber proved
- [x] embedded Hilbert cube in every atomless finite prefix fiber proved
- [x] residual maximal full-translation HT in the exact prefix chart proved via parent
- [x] spectral type held fixed in the prefix chart
- [x] complete tower proved injective and topologically faithful
- [x] pure-singular graph saturation imported with exact scope
- [x] F. and M. Riesz and the singular Szegő collapse formalized unconditionally
- [x] unique divergent unitary repair assembled in Lean from exact classical scope
- [x] residual singular-continuous probability phase on `P(T)` formalized unconditionally
- [x] projective probability phase transported as dense `G_delta` to the exact carrier range
- [x] projective-label null-preimage theorem and unconditional carrier singularity
- [x] residual singular-continuous maximal-HT phase proved on paper via parents
- [x] compact-patch density and actual-carrier HT capstone formalized relative to exact classical inputs
- [x] upper-node Cauchy frozen tangent proved to preserve the conventional finite Cholesky frame
- [x] RH consequence stated only as a carrier requirement
- [x] local repository collision search
- [x] targeted external collision search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [ ] exact primary-source match for every literature theorem interface
- [ ] unconditional construction of the classical N-extremal Nevanlinna family
- [ ] unconditional proper-projective-image / Whitney-stratification theorem
- [ ] unconditional finite-dimensional stratified parametric-avoidance theorem
- [x] axiom-free Lean formalization of every original deduction in the relative paper capstone
- [x] single-declaration weak-topology gluing of the global carrier-range residual phase

## Log

- 2026-07-12 -- Identified the inverse-Cholesky frame tower as the exact canonical coordinate
  joining finite-jet aperture to singular graph saturation. Proved the finite-prefix/full-tower
  selection threshold and its residual maximal-HT singular phase.
- 2026-07-13 -- Formalized the general one-dimensional analytic null-preimage law and proved that
  the determinant-one Nevanlinna projective label is nowhere locally flat under the paper's
  real-analytic lower-row hypothesis. This closes the formerly conditional transfer from the
  residual projective singular-continuous phase to atomless real-Lebesgue-singular carriers.
