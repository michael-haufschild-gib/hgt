# Singular maximal-HT carriers saturate the canonical Toeplitz weld graph

- **ID:** `singular-maximal-ht-toeplitz-weld-graph-saturation`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM / COFINAL CARRIER-GRAPH PHASE LAW
- **Lane:** general hypertranscendence; singular Herglotz carriers; operator-relation geometry
- **Scientific status:** `[CIRCLE GRAPH/UNITARY LAW FORMALIZED UNCONDITIONALLY; REAL-LINE NEVANLINNA/TRANSVERSALITY INPUTS REMAIN] [NOVELTY UNVERIFIED]`
- **Parents:** `singular-maximal-ht-schur-defect-collapse-law.md`,
  `nevanlinna-boundary-bauer-retract-maximal-ht.md`
- **Statement:** For a purely singular infinite-support probability measure on the circle, the
  graph of the canonical analytic-polynomial identification from coefficient Hardy space to the carrier
  `L^2` space is dense in the full product. Its closure is therefore the maximally multivalued
  linear relation, not the graph of an operator. Nevertheless every canonical Bernstein--Szego
  truncation gives a bounded, bounded-below Toeplitz weld and reproduces the target Gram section
  through its truncation degree. There is a unique compatible positive-triangular repair: inverse
  Cholesky orthogonalization. It produces a unitary carrier frame but its norm diverges exactly as
  the inverse square root of the smallest Gram eigenvalue. On the canonical Bauer simplex of every
  indeterminate Hamburger moment constraint, this saturated-raw/divergent-unitary phase occurs on
  a residual set of singular-continuous maximal-translation-HT carriers.

## Goal

The strict-finite/cofinal-collapse theorem shows that the finite Toeplitz metrics lose coercivity.
That alone leaves open whether the source and carrier can still be joined by a closed unbounded
operator. The present theorem determines the graph geometry exactly.

The new carrier law is:

> **A singular maximal-HT carrier is not obtained by closing the canonical finite Toeplitz weld as
> an operator. The unrenormalized graph becomes dense in the whole source--carrier product, so its
> closure relates every source vector to every carrier vector. A successful constraint must retain
> the uniquely forced orthogonal-polynomial renormalization—or equally strong marked data—before
> taking the cofinal limit.**

## Canonical polynomial weld

Let `m` be normalized Lebesgue measure on the unit circle and let `mu` be a probability measure.
Write

```text
H=ell^2(Z_+) congruent H^2(m),
K_mu=L^2(mu),
D=c_00(Z_+).                                                (1)
```

For `a=(a_0,...,a_d,0,...)` define

```text
(A_mu a)(zeta)=sum_(n=0)^d a_n zeta^n.                     (2)
```

The domain `D` is dense in `H`. The Gram matrix of the first `N+1` coordinate vectors is exactly
the Toeplitz moment matrix

```text
G_N(mu)=(integral zeta^(j-k)d mu(zeta))_(0<=j,k<=N).       (3)
```

If `mu` has infinite support, every `G_N(mu)` is positive definite, so every finite restriction of
`A_mu` is injective. This finite strictness does not decide whether the infinite graph is closable.

## Classical closability boundary `[SEARCH]`

Yafaev's semibounded Toeplitz-form theorem states that the quadratic form

```text
q_mu[a]=||A_mu a||_(K_mu)^2                                (4)
```

is closable in `ell^2(Z_+)` exactly when `mu` is absolutely continuous with respect to `m`.
Equivalently, the densely defined operator `(2)` is closable exactly in the absolutely continuous
phase.

This already puts every singular measure beyond the operator-closure boundary. For a purely
singular measure the graph has a stronger exact description.

## Maximal graph saturation for pure singularity `[PROVED HERE]`

Assume

```text
mu perpendicular m.                                       (5)
```

Let `Graph(A_mu)` be the graph of `(2)` in `H direct_sum K_mu`. We prove

```text
closure(Graph(A_mu))=H direct_sum K_mu.                    (6)
```

It is enough to show that the graph has zero orthogonal complement. Suppose

```text
(x,g) in H direct_sum K_mu
```

is orthogonal to `Graph(A_mu)`. Testing against every monomial coefficient vector gives, up to the
fixed inner-product convention,

```text
x_n=-integral_(unit circle) conjugate(g(zeta)) zeta^n d mu(zeta),
n>=0.                                                       (7)
```

Because `x in ell^2`, one half of the Fourier coefficients of the finite complex measure

```text
d nu=conjugate(g)d mu                                      (8)
```

is square summable. The measure is finite because `g in L^2(mu)` and `mu` is a probability.
Choose `h in L^2(m)` with precisely those one-sided Fourier coefficients. Then
`nu-hm` has a vanishing Fourier half-line. The F. and M. Riesz theorem makes `nu-hm` absolutely
continuous; hence `nu` is absolutely continuous.

But `(8)` also gives `nu << mu`, and `(5)` makes `nu` singular with respect to `m`. Therefore

```text
nu=0,
g=0 mu-almost everywhere,
x=0 by (7).                                                (9)
```

Thus `Graph(A_mu)^perp={0}`, proving `(6)`.

In linear-relation language, the closure of the graph has

```text
domain=H,
multivalued part=K_mu,
closure(Graph(A_mu))=H times K_mu.                         (10)
```

This is maximal nonclosability. The cofinal closure retains no source--carrier incidence at all.

## Canonical finite welds lie in the opposite graph phase `[SEARCH + PROVED HERE]`

Let `mu^[N]` be the Bernstein--Szego approximation to an infinite-support `mu`:

```text
d mu^[N](theta)=rho_N(theta)d theta/(2 pi),
rho_N(theta)=1/|phi_N(e^(i theta))|^2.                     (11)
```

The density `rho_N` is positive and real analytic on the compact circle. Hence there are constants

```text
0<c_N<=rho_N<=C_N<infinity.                                (12)
```

The polynomial identification extends uniquely to a bounded, bounded-below map

```text
A_N:H^2(m)->L^2(mu^[N]),
c_N||f||_(H^2)^2<=||A_N f||^2<=C_N||f||_(H^2)^2.          (13)
```

Its range is the closed weighted Hardy subspace generated by analytic polynomials, and its graph
is closed. Thus every finite canonical carrier is an honest Hilbert-space weld.

The first `N` Verblunsky coefficients and first `N` circle moments of `mu^[N]` agree with those of
`mu`. Consequently

```text
G_N(mu^[N])=G_N(mu).                                      (14)
```

Equations `(13)--(14)` exhibit the phase transition:

```text
every finite stage:
  bounded and bounded-below operator graph,
  absolutely continuous carrier,
  rational differentially algebraic transform;

cofinal singular limit:
  graph dense in the full product,
  purely singular carrier,
  possibly maximal-translation HT transform.              (15)
```

The constants in `(12)` cannot remain uniformly controlled. The parent theorem already gives
`lambda_min(G_N)->0`, all superlinear density norms diverge, and every uniformly coercive source
factorization pinches. Equation `(6)` identifies the endpoint of that pinching: complete graph
saturation.

## The unique compatible triangular repair `[PROVED HERE + CLASSICAL OPUC]`

Graph saturation does not mean that the carrier has no Hilbert realization. It means that the raw
monomial identification has forgotten the required renormalization.

Let

```text
v_N=(1,z,...,z^N)^T                                       (16)
```

and let `C_N` be the unique lower-triangular matrix with positive diagonal for which

```text
Phi_N=C_N v_N=(phi_0,...,phi_N)^T,
C_N G_N(mu) C_N^*=I.                                     (17)
```

Thus `C_N` is the inverse Cholesky factor of the Toeplitz Gram matrix, and the `phi_n` are the
orthonormal polynomials of `mu`. Uniqueness is the ordinary uniqueness of positive-diagonal
Cholesky factorization. Since the first `N` moments determine `phi_0,...,phi_N`, the matrices are
compatible under leading-block restriction.

Equation `(17)` gives the exact norm law

```text
C_N^* C_N=G_N(mu)^(-1),
||C_N||=lambda_min(G_N(mu))^(-1/2).                       (18)
```

For a singular infinite-support carrier, the parent cofinal law therefore forces

```text
||C_N||->infinity.                                        (19)
```

The complete frame volume has the exact law

```text
det(C_N)=det(G_N(mu))^(-1/2),
det(C_N)^(1/(N+1))->infinity.                              (19a)
```

The second limit follows from the zero Szego determinant root of the singular carrier. Thus the
repair does not merely develop one bad coordinate: its geometric-mean expansion diverges.

This divergence is not a defect of a chosen basis: among compatible lower-triangular
positive-diagonal changes of the monomial frame, `(17)` determines `C_N` uniquely.

Define

```text
U_N:C^(N+1)->span{1,z,...,z^N} subset L^2(mu),
U_N(a_0,...,a_N)=sum_(n=0)^N a_n phi_n.                   (20)
```

Every `U_N` is unitary onto its range and the family is nested. It therefore defines an isometry

```text
U_mu:ell^2(Z_+)->L^2(mu),
U_mu e_n=phi_n.                                            (21)
```

For purely singular `mu`, analytic polynomials are dense in `L^2(mu)`. Indeed, if `g` is
orthogonal to every nonnegative monomial, the finite measure `conjugate(g)mu` has a vanishing
Fourier half-line; F. and M. Riesz makes it absolutely continuous, while it is also singular, so
it is zero. Hence `g=0`. Thus `(21)` is onto:

```text
U_mu:ell^2(Z_+)->L^2(mu) is unitary.                       (22)
```

The raw map `A_mu` has full-product graph closure `(6)`, while the uniquely normalized map `U_mu`
is unitary. The price of retaining incidence is exactly the divergent triangular frame `(19)`.

Because `mu^[N]` and `mu` have the same level-`N` Gram matrix, they also have the same matrix `C_N`
and the same first `N+1` orthonormal polynomials. Therefore the canonical Bernstein--Szego models
carry the exact finite repair, not merely the raw finite metric. What fails at the limit is uniform
control of the compatible repairs.

## Residual graph-saturated maximal HT in one exact constraint `[PROVED HERE VIA PARENTS]`

Fix an indeterminate normalized Hamburger moment sequence and its intrinsic Nevanlinna Bauer
simplex

```text
Beta:P(RP^1(R))->K_s subset M(s).                          (23)
```

The parent theorem proves that the following two subsets are residual in `K_s`:

1. singular-continuous representing measures;
2. measures whose real-line Cauchy transforms have differentially algebraically independent full
   complex translation families.

Their intersection is residual. Cayley transport preserves singular continuity and converts each
carrier to a purely singular circle measure `mu`. For every point in this residual intersection,
equation `(6)` applies to the circle carrier, while the original Cauchy transform is maximally
translation HT.

Therefore

```text
{nu in K_s :
  nu is singular continuous,
  m_nu has maximal full-translation HT,
  closure(Graph(A_(Cayley_*nu))) is the full product}
```

is residual in `K_s`.                                     (24)

All these carriers have exactly the same complete Hamburger moments and the same all-order formal
translated asymptotic germ at upper infinity. Maximal graph saturation is therefore a generic
internal phase of one exact complete constraint, not a pathology produced by changing moments.

## Universal carrier consequence

The usual prescription

```text
finite positive Gram matrices
  -> take a cofinal graph closure
  -> obtain the carrier operator                              (25)
```

fails maximally on the residual singular-HT phase. Every finite section is positive definite and
comes from a bounded canonical model, but the unweighted limiting graph closes to the whole
product. The compatible orthogonal-polynomial repair survives only through the divergent inverse
Cholesky tower `(17)--(22)`.

The positive necessity law is:

> **Any source realization of a singular maximal-HT carrier must alter the cofinal graph before
> closure. In the canonical triangular category, it must reconstruct the divergent inverse
> Cholesky/orthogonal-polynomial tower. Any alternative rigging, determinant-line marking, or
> boundary condition must carry at least the same incidence information.**

This is stronger than demanding an unbounded operator. Without extra structure, there is no
operator left to be unbounded.

## Consequences for proof architectures

These consequences concern routes that factor through the normalized Herglotz/Toeplitz carrier;
they do not claim that every imaginable RH formulation is Toeplitz.

1. **Finite Toeplitz or OPUC sections.** Strict positivity of every `G_N` is only the entrance
   condition. A successful construction must also produce the compatible matrices `C_N` and
   control their source meaning. Determinants or eigenvalue signs alone do not retain the carrier
   incidence in the limit.
2. **de Branges or Hilbert--Polya realizations.** A source-selected Hilbert norm cannot remain
   uniformly equivalent to the raw monomial Hardy norm. Its frame change must contain the same
   cofinal divergence as `(19)`, or a unitarily equivalent boundary marking. A uniformly bounded
   frame equivalence would leave the target form coercive and contradict the singular phase.
3. **Taylor or finite-prime zero transfer.** Locally uniform zero preservation and the formalized
   `1/log N` prime-clock pinning can locate a limiting divisor only after a source theorem couples
   them to the carrier. Ordinary convergence of the unrenormalized positive graphs cannot supply
   that coupling, because their target graph saturates. The missing theorem must transport the
   marked frame or graph norm as well as the scalar values.
4. **CCM/Weil finite-aperture graphs.** A proposed closed four-channel graph cannot be obtained by
   simply closing the unmarked moment-polynomial incidence. The source-selected boundary relation,
   determinant line, or channel rigging must be installed before the cofinal aperture limit; after
   unmarked closure the incidence information is gone.

The positive common requirement is not “avoid singularity.” The required Xi carrier is singular.
It is: **carry the divergent normalization coherently enough that singularity becomes a unitary
boundary representation instead of a maximally multivalued raw relation.**

## RH consequence `[PROVED HERE; RH NOT PROVED]`

The Xi companion proves that RH is equivalent to strict positivity of every finite Schur defect of
the normalized Xi germ. Under RH, its circle Herglotz measure is infinite pure point and hence
purely singular. Therefore the canonical Xi polynomial weld satisfies

```text
RH implies closure(Graph(A_(mu_Xi)))
  =H^2(m) times L^2(mu_Xi).                                (26)
```

Thus a source-faithful RH proof cannot obtain the Xi carrier by ordinary graph closure of its
finite Toeplitz sections, even though every section is strictly positive. The missing
prime--Gamma carrier must carry an additional cofinal marking before closure. A zero-preserving
source weld that is merely a convergent sequence of unrenormalized positive graphs cannot suffice.

Equation `(26)` is conditional and does not orient the source. Its role is to constrain the shape
of a successful construction.

## Parent-theory and novelty attack

1. `[SEARCH]` F. and M. Riesz one-sided Fourier rigidity is classical.
2. `[SEARCH]` Yafaev proves that a semibounded Toeplitz form is closable exactly for absolutely
   continuous representing measures:
   `https://arxiv.org/abs/1603.06229`.
3. `[SEARCH]` Hassi--Sebestyen--de Snoo--Szafraniec prove the general canonical decomposition of a
   relation into closable and singular parts, with the singular closure a Cartesian product:
   `https://arxiv.org/abs/math/0611045`.
4. `[SEARCH]` Bernstein--Szego approximation, Cholesky orthogonalization, and the OPUC frame are
   classical
   OPUC.
5. `[BRIDGE]` Residual maximal translation HT and the residual singular-continuous phase on the
   intrinsic Bauer simplex come from the parent carrier theorems.
6. `[SEARCH + SPECIALIZATION]` Pure singularity upgrades nonclosability to the graph-saturation
   identity `(6)`; the direct Fourier proof is included, but the general singular-relation
   phenomenon is known.
7. `[PROVED HERE]` Equations `(17)--(22)` identify the unique compatible triangular repair and its
   forced norm divergence, while `(13)--(15)` show that every canonical rational/AC approximant
   carries the exact finite repair.
8. `[PROVED HERE]` Combining saturation, divergent repair, and the residual Bauer phase gives the
   bounded-finite / maximally-multivalued-raw / unitary-after-divergent-renormalization trichotomy
   for a generic maximal-HT carrier inside one exact all-moment constraint.
9. `[CANDIDATE RESIDUE]` Preliminary exact searches found no theorem coupling residual maximal
   translation differential independence, indeterminate-moment Bauer geometry, canonical
   Bernstein--Szego finite welds, full graph saturation, and the uniquely forced divergent unitary
   repair.
10. The result remains `[NOVELTY UNVERIFIED]` pending operator-theory, moment-problem, and
   differential-algebra specialist audit.

## Honest significance score

**88/100 candidate; plausible range 77--94.** The graph-saturation phenomenon and the OPUC
orthogonalization are classical separately. The candidate new result is their exact interaction
with the residual maximal-translation-HT Bauer phase: canonical bounded rational/AC welds converge
to a carrier whose raw graph saturates, while the unique compatible unitary repair survives only
through a norm-divergent triangular tower. This gives a structural law for the carrier itself and
a sharp requirement on every source realization. It is not yet a verified true 90 because the
priority and specialist audits remain open.

## Lean status

The pure-singular circle graph and coherent-unitary conclusions are now unconditional:
`FAndMRieszVanishing` proves the one-sided density theorem, and `RieszSingularSzegoCollapse` derives
the singular Szego limit internally. The finite-dimensional stratified-avoidance theorem is now
unconditional. The residual real-line maximal-HT phase still consumes the packaged
Nevanlinna-family input. The projective-incidence stratification is now discharged by
`ProjectiveIncidenceHausdorffDimension`, but the complete card is not yet Stage 3.

The formal theorem surface is distributed as follows:

- `PureSingularCarrierTrichotomy.pureSingularCarrier_trichotomy_of_classical_inputs` proves full
  raw graph saturation, analytic-polynomial completeness, least-eigenvalue collapse, determinant
  escape, and inverse-Cholesky operator-norm escape.
- `PureSingularCarrierUnitary.exists_circleCanonicalCarrierUnitary_of_rieszBrothers` constructs the
  coherent onto unitary carrier frame from the finite canonical inverse-Cholesky tower.
- `BernsteinSzegoReconstruction.circleToeplitzGram_bernsteinSzegoMoment_eq` proves exact finite
  Toeplitz-section reconstruction by the canonical Bernstein--Szego carrier.
- `BernsteinSzegoWeldBounds.bernsteinSzego_polynomial_weld_quadratic_bounds` proves uniform positive
  lower and finite upper bounds for every finite Bernstein--Szego polynomial weld.
- `CofinalCholeskyResidualPhase.cofinalCholeskyResidualPhase_dense_gdelta_residual` proves the dense
  `G_delta`, hence residual, singular-continuous maximal-translation phase on the complete
  Nevanlinna carrier range.

The direct leaf builds and the formal lint gate pass. Axiom inspection of these endpoints reports
only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] canonical polynomial/Toeplitz weld defined
- [x] finite strict Gram positivity separated from infinite closability
- [x] pure-singular graph orthogonal complement proved zero
- [x] full-product graph closure proved
- [x] bounded and bounded-below Bernstein--Szego welds proved
- [x] exact level-`N` Gram agreement proved
- [x] unique compatible inverse-Cholesky repair identified
- [x] exact repair norm divergence proved
- [x] unitary singular-carrier OPUC frame proved onto
- [x] residual singular-continuous maximal-HT phase imported and intersected
- [x] positive carrier requirement stated
- [x] RH consequence scoped without claiming orientation
- [x] primary closability source checked
- [x] preliminary novelty search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [x] unconditional Lean formalization of the circle graph-saturation and coherent-unitary laws
- [x] unconditional projective-incidence stratification for the residual real-line phase
- [ ] unconditional Nevanlinna-family construction for the residual real-line phase

## Log

- 2026-07-12 -- Upgraded cofinal metric pinching to the exact graph endpoint. Proved that a pure
  singular carrier makes the analytic-polynomial graph dense in the full source--carrier product;
  combined this with canonical bounded Bernstein--Szego welds and the residual
  singular-continuous maximal-HT phase on the intrinsic moment Bauer simplex.
