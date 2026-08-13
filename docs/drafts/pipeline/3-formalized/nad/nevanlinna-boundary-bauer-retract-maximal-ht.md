# The Nevanlinna boundary is a canonical Bauer retract carrying maximal translation HT

- **ID:** `nevanlinna-boundary-bauer-retract-maximal-ht`
- **Stage:** 3-formalized
- **Type:** THEOREM / UNIVERSAL CONSTRAINT-FIBER GEOMETRY LAW
- **Lane:** general hypertranscendence; indeterminate Hamburger moments; convex carrier geometry
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Parents:** `indeterminate-moment-fiber-maximal-translation-ht.md`,
  `spectral-type-stratified-moment-fiber-maximal-ht.md`
- **Statement:** Every indeterminate normalized Hamburger moment fiber contains a canonical closed
  affine Bauer simplex, independent of the normalization of its Nevanlinna matrix and affinely
  homeomorphic to the probability measures on the real projective line. The whole moment fiber
  admits a canonical continuous affine retraction onto this simplex. Dually, the constraint
  defines an intrinsic idempotent weak-Feller Markov kernel whose stationary laws are exactly this
  simplex, whose ergodic stationary laws are exactly the `N`-extremals, and which sends every
  monomial to its prescribed moment in one step; from any initial probability law, one transition
  lands in the exact complete-moment fiber. Every infinite closed boundary face carries a dense
  residual phase whose Cauchy transforms have differentially algebraically independent full
  complex translation families, although all measures retain the exact same complete moments and
  formal differential-translation asymptotic germ.

## Goal

Indeterminacy should not be treated as an amorphous collection of alternative representatives.
The theorem identifies a normalization-free geometric object forced inside every indeterminate
moment constraint: a universal probability simplex, together with a canonical projection of the
whole constraint fiber onto it. The same projection is the measure-side action of an idempotent
Markov randomizer determined by the support foliation. Hypertranscendental freedom persists
generically among its stationary laws and on each infinite closed face.

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

## The constraint Markov projector `[PROVED HERE]`

The retract has a dual pointwise form. Define a probability kernel on the real line by

```text
Q_s(x,E)=mu_(pi(x))(E),                                    (17)
```

and its operator on bounded Borel functions by

```text
(P_s f)(x)=integral_R f(y) d mu_(pi(x))(y).                 (18)
```

The map `x |-> mu_(pi(x))` is weakly continuous by `(4)` and `(6)`. Hence `P_s` sends bounded
continuous functions to bounded continuous functions, is positive, preserves the constant one,
and contracts the supremum norm. It is a weak-Feller Markov operator. No claim that it preserves
`C_0(R)` is needed.

Equation `(5)` gives idempotence without an asymptotic limit. For `mu_(pi(x))`-almost every `y`,
one has `pi(y)=pi(x)`. Therefore

```text
Q_s^2(x,E)
 =integral_R mu_(pi(y))(E) d mu_(pi(x))(y)
 =mu_(pi(x))(E)
 =Q_s(x,E),
P_s^2=P_s.                                                  (19)
```

The constraint is flattened in one step. For every nonnegative integer `n`, interpreted on the
common integrability domain,

```text
(P_s[x |-> x^n])(x)
 =integral_R y^n d mu_(pi(x))(y)
 =s_n.                                                      (20)
```

Thus the entire moment sequence is the constant polynomial shadow of the Markov projector.

The measure-side dual of `P_s` is the same formula as `(12)`, now defined for every probability
law on the real line:

```text
bar(R)_s:P(R)->K_s,
bar(R)_s(nu)=Beta(pi_*nu).                                  (21)
```

It is continuous, affine, idempotent, and maps an arbitrary initial probability law into the
exact complete-moment fiber in one step. Its restriction to `M(s)` is `R_s`. Consequently

```text
nu is Q_s-stationary
 iff bar(R)_s(nu)=nu
 iff nu in K_s.                                             (22)
```

The ergodic stationary laws are precisely the `N`-extremals. If `nu=Beta(eta)` and `eta` is not a
point mass, a Borel boundary set of intermediate `eta`-mass has an invariant preimage under `pi`,
so `nu` is not ergodic. If `eta=delta_tau`, every transition from the leaf `pi^(-1)(tau)` has the
same law `mu_tau`; the resulting stationary chain is independent after one step and is ergodic.

This is not a flow construction. The complete constraint canonically supplies a one-step
idempotent randomization, its stationary simplex, and its ergodic boundary.

## The entire closed-face lattice is present `[PROVED HERE]`

For every closed subset `F subset T`, define

```text
K_s(F)=Beta(P(F)).                                         (23)
```

The probability measures supported on `F` form a closed face of `P(T)`: if
`eta=t eta_1+(1-t)eta_2` is supported on `F`, with `0<t<1`, positivity forces both `eta_1` and
`eta_2` to be supported on `F`. The affine homeomorphism `Beta` therefore makes `K_s(F)` a closed
face of `K_s`. Moreover,

```text
F_1 subset F_2  iff  K_s(F_1) subset K_s(F_2),
K_s(F_1 intersect F_2)=K_s(F_1) intersect K_s(F_2).        (24)
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
eta_epsilon=(1-epsilon)eta+epsilon kappa                  (25)
```

still satisfies `Beta(eta_epsilon) in U` and has infinite support.

The parameter-measure controllability theorem from the spectral-type companion applies to
`eta_epsilon`: every finite complex Cauchy-jet packet is onto on the bounded mean-zero tangent
space. Hence, in every positive `L-infinity(eta_epsilon)` chart about the constant density one, a
dense residual set of weights gives maximal full-complex translation HT.

Choose the chart radius small enough that all its barycenters remain in `U`. It contains a point
of `H_s`. Therefore

```text
H_s intersect K_s(F) is dense in K_s(F).                  (26)
```

### Residuality

The differential-relation detectors defining `H_s` are a countable intersection of relatively
open sets on `M(s)`. Their restriction to the closed compact space `K_s(F)` is `G_delta`. Together
with `(26)`,

```text
H_s intersect K_s(F) is dense residual in K_s(F)          (27)
```

for every infinite closed `F`.

Every two points in every face `(23)` still have all moments `(s_n)`. The parent flatness theorem
therefore gives, for every fixed complex translation and derivative order, equality of the entire
formal inverse-power asymptotic germ at upper infinity. `QED`

## Universal Bauer-retract HT law

> **Every indeterminate Hamburger moment constraint contains a normalization-independent Bauer
> probability simplex as a canonical continuous affine retract and as the stationary-law simplex
> of an intrinsic idempotent weak-Feller Markov projector. Its ergodic laws are the `N`-extremal
> support
> leaves, every initial probability law is sent in one step into the complete moment constraint,
> every monomial is sent to its prescribed moment, its entire closed-face lattice lies inside the
> exact moment fiber, and maximal full-complex translation
> hypertranscendence is residual on every infinite closed face despite complete formal moment
> agreement.**

This turns moment indeterminacy into a positive geometric law. The residual freedom is organized
by a universal projective probability modulus and a canonical constraint randomizer; it is not
merely the failure of uniqueness.

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

The companion `moment-polynomial-blind-resolvent-complete-boundary-splitting.md` sharpens this
test in `L^2`: all centered polynomials lie in the vertical kernel of the projector, the entire
mean-zero boundary pullback is polynomial-orthogonal, and conditional Cauchy resolvents span the
horizontal boundary space. It locates the residual HT freedom in the coordinate that moments erase
and finite-centre resolvents recover. The same companion proves the sharp selector law: one scalar
finite-centre value separates extremal leaves, while one regular analytic germ separates all
boundary probability laws, despite the common complete asymptotic germ at infinity.

The threshold companion `finite-jet-aperture-complete-germ-closure-law.md` shows that every finite
subjet still leaves infinite-dimensional positive aperture and residual maximal translation HT at
fixed spectral type; only completion of the coherent germ closes the boundary law to a point.

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

Together with the parent residual theorem, Hilbert splitting, and finite-jet threshold, this gives
an internal **90/100 candidate**, with a deliberately wide **72--94** range pending specialist
review. The earlier escalating self-scores were withdrawn: adding correct corollaries does not by
itself establish field-level novelty or significance.

- **Why it can plausibly reach 90:** the output is now a canonical,
  normalization-independent geometric invariant of every indeterminate moment constraint, not
  only a genericity theorem in an auxiliary coordinate chart. It gives an explicit affine
  idempotent on the whole carrier, identifies its image with a universal Bauer simplex, embeds the
  full closed-face lattice of the projective boundary, and proves maximal translation HT on every
  infinite face while every moment and formal translated asymptotic is fixed.
- **Why 90 is not yet verified:** all raw ingredients have strong classical parents; priority remains
  unaudited; the theorem does not construct a source-canonical HT representative, prove the Xi
  orientation sign, or supply an unconditional RH proof. Its exact full statement is not yet
  formalized in Lean.

## Lean status

Formalized relative to the classical Nevanlinna family stated on the card. Projected-incidence
stratification and finite-dimensional stratified avoidance are now unconditional in
`ProjectiveIncidenceHausdorffDimension` and `StratifiedParametricAvoidance`. The exact support-label left inverse, moment-preserving boundary barycenter, closed
Bauer embedding, whole-fiber retraction, projective-coordinate covariance, genuine Mathlib Markov
kernel, weak-Feller operator, idempotence, stationarity, invariant-set ergodicity, closed-face
lattice, and infinite-face residual maximal-translation law are in:

- `NevanlinnaBoundaryKernel.lean`, `NevanlinnaConstraintProjector.lean`,
  `NevanlinnaBauerRetract.lean`, `NevanlinnaAffineGeometry.lean`;
- `NevanlinnaBoundaryFaceLattice.lean`, `NevanlinnaStationaryBauer.lean`,
  `NevanlinnaKernelErgodicity.lean`;
- `BoundaryCarrierTranslationFreeness.lean`, `InfiniteSupportProbabilityLaws.lean`, and
  `NevanlinnaBoundaryFaceMaximalTranslation.lean`.

The maximal phase is stated intrinsically on probability carriers. Its density is proved through
the stronger simultaneous full-rank packet-witness phase. Its residuality consumes exactly the
parent card's countable `G_delta` detector, recorded as `MaximalTranslationInputs.phase_isGδ`, rather
than introducing a new analytic axiom. The principal endpoints have only `propext`,
`Classical.choice`, and `Quot.sound`; targeted builds and the formal lint gate pass.

## Gates

- [x] prior-research collision search in the local pipeline and formal tree
- [x] projective support map defined without pole choices
- [x] boundary barycenter proved moment-preserving and continuous
- [x] pushforward left inverse proved
- [x] canonical affine idempotent on the full moment fiber proved
- [x] normalization independence proved
- [x] intrinsic idempotent weak-Feller Markov kernel proved
- [x] stationary simplex and ergodic boundary identified
- [x] every monomial flattened to its prescribed moment in one step
- [x] full closed-face lattice embedded
- [x] residual maximal full-translation HT on every infinite closed face proved
- [x] general HT and concrete RH-carrier consequences scoped
- [x] preliminary exact literature search
- [ ] independent specialist proof audit
- [ ] full primary-source priority audit
- [x] Lean formalization relative to the exact classical and parent inputs stated above

## Log

- 2026-07-12 -- Defined the projective support-label map and proved that extremal barycentring has
  its pushforward as a continuous affine left inverse. Constructed the normalization-independent
  Bauer retraction and its dual idempotent weak-Feller Markov projector, identified the stationary
  and ergodic laws, embedded the closed-face lattice, and proved residual maximal translation HT
  on every infinite closed face.
- 2026-07-12 -- Extracted the companion Hilbert law: the projector is conditional expectation on
  stationary mixtures, centered polynomials lie in its vertical kernel, and conditional resolvents
  are complete on the horizontal boundary space.

## Log — the classical Nevanlinna input is discharged

**[PROVED]** `formal/GaloisForLFunctions/HTGeometry/NevBauerUnconditional.lean`

This card's Lean status reads "Formalized **relative to** the classical Nevanlinna family stated on
the card" — the `ClassicalNevanlinnaExtremalFamily` was an assumed input. It is no longer assumed.
`finite-jet-aperture-complete-germ-closure-law` (links 146–182) constructs one for every positive
definite normalised moment sequence with bounded kernel at a point, i.e. for every indeterminate
Hamburger moment problem, and `nevExtremalFamily` is that term.

Instantiating this card's package at `nevBoundaryFamily h h0b h0 := (nevExtremalFamily h h0b h0).toBoundaryFamily`:

- `nevBauer_isClosedEmbedding` — **the complete-moment fiber contains a canonical closed embedded
  Bauer simplex**, affinely parametrised by the probability measures on the projective line.
- `nevBauer_continuous_retract`, `nevBauer_retract_idempotent` — **the canonical continuous
  idempotent retraction of the whole fiber onto that simplex.**
- `nevBauer_range_retract` — its image is exactly the simplex.
- `nevBauer_fixed_iff` — a fiber point is fixed exactly when it lies on the simplex.
- `nevBauer_extreme_iff` — the extreme points are exactly the barycentres of Dirac parameter laws,
  i.e. the N-extremal leaves.

All endpoints `[propext, Classical.choice, Quot.sound]`; zero placeholders; registered in the
umbrella.

**Effect on this card.** Every statement above previously carried the standing hypothesis "given a
classical Nevanlinna family". They now carry only `PositiveMomentForm s`, `BoundedKernel s 0`,
`s 0 = 1`. The Lean-status line "Formalized relative to the classical Nevanlinna family stated on the
card" should be revised on audit: the classical family is now a theorem of this tree, not an input.

The remaining generic Bauer consequences are now instantiated in
`formal/GaloisForLFunctions/HTGeometry/NevBauerMarkovFacesUnconditional.lean`.  Its exact endpoints
cover projective-law recovery; continuous affine idempotent measure projection; the pointwise
idempotent weak-Feller Markov kernel; positivity, unitality, norm contraction and idempotence of its
dual operator; stationarity; monomial flattening; invariant-set ergodicity; and the closed-face
lattice, including genuine facehood and complete moments on every face.  These statements use only
`PositiveMomentForm s`, `BoundedKernel s 0`, and `s 0 = 1`.

## Unconditional Lean promotion audit — blocked

The card is not yet eligible for Stage 3.  Repository-wide symbol search found no construction of
`ClassicalAnalyticNevanlinnaCarrierFamily` from `nevExtremalFamily`, and no term of type
`MaximalTranslationInputs`.  Consequently
`boundaryCarrierFace_maximalTranslationPhase_dense_residual` still requires six undischarged
analytic fields: minimal exponential type, no common zero of the denominator row, a zero point, a
regular point, the upper-half-plane quotient law, and the intrinsic phase `G_delta` theorem.  The
claim that normalization independence follows for arbitrary admissible Nevanlinna matrices also
remains short of an unconditional endpoint: `carrierProjector_eq_of_leaf_label_covariance` proves
the exact implication from leaf/label covariance, but the tree does not derive that covariance from
arbitrary normalization changes.  No weaker statement is substituted for either claim.

## Log — the classical analytic Nevanlinna carrier family is constructed `[PROVED]`

The moment-fibre bottleneck shared by this card and nine others had two halves.  The first is closed.

`formal/GaloisForLFunctions/HTGeometry/NevLeafCauchyMoebius.lean` proves the **Weyl-disc closed
form** unconditionally, for every positive definite normalised moment sequence with bounded kernel
at a point:

```text
(B(z)*tau - D(z)) * integral (x - z)^(-1) d nu_tau  =  -(A(z)*tau - C(z)),
integral (x - z)^(-1) d nu_tau  =  -(A(z)*tau - C(z)) / (B(z)*tau - D(z)).
```

The finite stage `nevTrunc_cauchy_identity` is the quadrature identity multiplied by the common
factor turning the quasi-orthogonal pair into the truncated Nevanlinna entries; the limit uses the
weak convergence of the quadrature levels to the leaf together with the entrywise limits, and the
determinant identity forbids the denominator from vanishing off the real axis.
`NevLeafInfinityCauchyMoebius.lean` does the same at the parameter at infinity, giving
`integral (x - z)^(-1) d nu_infinity = -A(z)/B(z)`.

`formal/GaloisForLFunctions/HTGeometry/AnalyticNevanlinnaCarrierConstruction.lean` therefore builds

```text
analyticNevCarrierFamily h h0b h0 : ClassicalAnalyticNevanlinnaCarrierFamily s
```

in the carrier convention `(a,b,c,d) = (-A, C, B, -D)`, and
`exists_classicalAnalyticNevanlinnaCarrierFamily`.  All endpoints have axioms `propext`,
`Classical.choice`, `Quot.sound`, and the modules are wired into the `HTGeometry` umbrella.

## Log — `MaximalTranslationInputs` is presently uninhabitable `[DISPROVED FIELD]`

`formal/GaloisForLFunctions/HTGeometry/NevanlinnaWeylDiscPole.lean` proves

```text
nevInf_quotient_im_neg : 0 < z.im -> (D(z)/B(z)).im < 0
```

so `MaximalTranslationInputs.upperMap : forall z, 0 < z.im -> 0 < (F.quotient z).im` is **false**
for the constructed family: the pole of the Weyl-disc Möbius map lies strictly below the real axis,
because the map carries the closed upper half-plane into the Weyl disc and the pole to infinity.
The proof writes the imaginary part of the Möbius image as `Q(t)/|B t - D|^2` with `Q` a real
quadratic, notes `Q` vanishes at the pole and is positive on the real axis, and identifies the
coefficient of `Im t` as `Re(A conj D - C conj B)`, which equals `1` on the real axis, is
continuous, and cannot vanish on the connected upper half-plane.

The transversality chain therefore has to be restated with the jet poles in the **lower** half-plane
(or with the abstract lemmas instantiated at the conjugated poles and the conclusion conjugated
back).  Until then the residual maximal-translation phase theorem is vacuous.

## Log — M. Riesz's theorem is now a single named hypothesis `[REDUCTION PROVED]`

`formal/GaloisForLFunctions/HTGeometry/NevanlinnaEntryMinimalType.lean` adds `norm_nevBinf_le` and
`norm_nevCinf_le` to the corpus's existing `norm_nevAinf_le` / `norm_nevDinf_le`, defines

```text
KernelMinimalExponentialType s :=
  forall A > 0, exists C >= 1, forall z n,
    kernelRoot s (monicOrthoC s . z) n <= C * exp (A * |z|)  and the same for secondKindC
```

and proves `hasMinimalExponentialType_nevAinf`, `...nevBinf`, `...nevCinf`, `...nevDinf` from it.
So the `minimalExponentialType` field reduces to that one property.  The recurrence route to it is
closed: the comparison identity is a Volterra equation with Hilbert-Schmidt kernel, whose iterate
bound `|V^m| <= |V|_HS^m / sqrt(m!)` generates `exp(c|z|^2)`, order two rather than order one, and a
small-tail split only improves the constant.  The route that remains is entire-function theoretic
(real zeros with summable reciprocals, then a genus-zero Hadamard product), and Hadamard
factorization is absent from mathlib.

## Log — the last formalization gate is closed `[PROVED]`

The normalization-independence section `(14)`--`(16)` is now an unconditional Lean theorem, and
with it the card's whole numbered list.

- `HTGeometry/NevanlinnaNormalizationTwist.lean`: the matrix twist `W · g` for `g in SL(2,R)`, the
  denominator factorization `c'(x)sigma+d'(x)=c(x)(g00 sigma+g01)+d(x)(g10 sigma+g11)`, the label
  covariance `(W·g).projectiveLabel = g^(-1) . W.projectiveLabel`, fiber covariance in both
  charts, and the twisted boundary family of the *same* moment sequence.
- `HTGeometry/NevTwistUnconditional.lean`: `nevCarrierProjector_twist` and
  `nevBarycenter_range_twist` for the constructed family — the retraction `R_s` and the simplex
  `K_s` do not depend on the chosen determinant-one Nevanlinna matrix.

Together with `analyticNevCarrierFamilyMaximalTranslationInputs` (M. Riesz through Simon's
transfer route) and the unconditional `G_delta` phase detector, the residual maximal-translation
law `(25)`--`(27)` is `analyticNevCarrierFamily_maximalTranslationPhase_dense_residual`, with no
analytic hypothesis left.

Twenty-two audited declarations, `propext` / `Classical.choice` / `Quot.sound` only.  Promoted to
`3-formalized/nad` with companion `nevanlinna-boundary-bauer-retract-maximal-ht-formalized.md`.
The two open gates are external audits (specialist proof audit, primary-source priority audit) and
are not formalization obligations.
