# Active polarized constraint sheaves with transverse normalization horizons

- **ID:** `hypertranscendental-constraint-sheaf-reconstruction-duality`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CLASSIFICATION CONJECTURE / UNIFIED OBSTRUCTION FIELD
- **Scientific status:** `[CONJECTURE] [HOCHSTER KINEMATIC FIBRE PROVED]`
  `[BARE-SOURCE FULL FAITHFULNESS REFUTED] [NORMALIZATION-HORIZON CORRECTION]`
  `[FIELDS-MEDAL-SCALE OPEN CORE] [NOVELTY OPEN] [NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/hypertranscendental-hochster-source-coherence-duality.md`
  - `hypertranscendental-constraint-hodge-duality.md`
  - `hypertranscendental-polarization-transport-spectrum.md`
  - `pointed-polarized-constraint-coupling-correspondence.md`
  - `hypertranscendental-normalization-horizon-uniformization.md`
  - `../3-formalized/hypertranscendental-minimal-polarized-critical-completion-architecture.md`

## Founding displacement

There is no hidden finite law inside a one-generator hypertranscendental differential field.  Its
algebraic bulk is the universal free differential-rational field, and every finite simplicial
constraint topology together with its complete Hochster syzygy hierarchy is analytically
realizable.  Even that full derived topology is independent of residue orientation.

Therefore the object constrained by nature is not a function value, a finite equation, a chosen
topology, or an unpolarized derived category.  It is an **effective realization** of a universal
free bulk along a thin source boundary.

The proposed local-to-global object has the following irreducible layers.

```text
U       universal free differential-rational vertex bulk;
X       finite or pro-finite reduced source-constraint spectrum;
B       constructible derived boundary sheaf on X;
A       active representations of structural lattices on noncompact carrier quotients;
mu      affine pointing / source normalization;
P       self-duality and homotopy-coherent Hermitian polarization transport;
G       critical growth bornology on the full source-by-observable scale cone;
beta    comparison, continuation, and descent realization of B in analytic charts.
```

`B` contains the complete minimal source-presentation homotopy type, not merely the annihilator
ideal.  On a Stanley--Reisner chart its structural-identity fibre is fixed by the proved law

```text
pi_i(B)_W ~= H_tilde^(|W|-i-1)(X|W).                      (1)
```

The activity layer is independent: a faithful lattice trapped in a compact Abelian shadow has
unbounded aggregate capacity but no single observable of infinite capacity.  The polarization
layer is independent: every finite sign index occurs with the same field, topology, and derived
boundary.  The comparison layer is independent: identical local objects may fail to glue or may
glue noncanonically.

Two exact laws sharpen these independence statements.  First, the boundary-wedge family has
`htDim=2` and every projective source-coherence depth `m>=3`; hence neither `B` nor its polarization
descent can be uniformly Postnikov-truncated by analytic dimension.  Second, in the rank-one
boundary-wedge seed, imposing nondegenerate edge transport collapses the local sign product to one
sign per connected component.  Thus `P` cannot be a stalkwise sign decoration: it must be a
homotopy-coherent transport object coupled to `B`, `A`, and `beta`.

## Decisive correction: the bare source reconstructs a quotient stack, not a germ

The Gamma collision

```text
Gamma(z),       exp(2 pi i z) Gamma(z)
```

has the same source equation and one regular pointing.  Periodic gauges can also preserve every
prescribed finite jet.  Hence any package derived functorially only from that bare source has
nontrivial inertia and cannot be fully faithful on analytic germs.  Adding more topology,
polarization, completion, transport, or source-derived integral data cannot restore information
already forgotten.

The maximal source-observability theorem is

```text
Obs_R injective
  iff K^S intersect intersection_r ker R_r = {0}.           (1a)
```

Therefore `(U,X,B,A,mu,P,G,beta)` can at most reconstruct the source solution quotient stack and its
residual gauge groupoid.  Germ reconstruction requires a genuinely transverse normalization
horizon `N`; it is valid precisely on the stratum where the cofinal normalized inertia is trivial.

Gamma supplies the first exact positive model.  Every finite log-convexity horizon retains nonzero
radial gauge, while the cofinal intersection is a singleton and horizon-dependent radial scales do
not uniformize.  The reconstruction object must therefore include

```text
N = {N_lambda -> residual source gauge}_(lambda cofinal),   (1b)
```

not merely a richer invariant of the source.

## The Fields-scale conjecture

> **[CONJECTURE -- ACTIVE POLARIZED CONSTRAINT-SHEAF DUALITY]** There are categories
>
> ```text
> HT_reg^N    = regular source-minimal HT germs with a natural transverse normalization horizon,
> APCSH_eff   = effective pointed active polarized constraint sheaves with horizon inertia,
> ```
>
> and a functor
>
> ```text
> H^N : HT_reg^N -> APCSH_eff                             (2)
> ```
>
> with the following properties.
>
> 1. **Source quotient.** Forgetting `N` reconstructs the source solution quotient stack with
>    residual inertia, not a preferred germ.
> 2. **Normalized full faithfulness.** On the source-effectively normalized stratum where the
>    cofinal normalized inertia is trivial, every differential-analytic morphism is reconstructed
>    from its action on `(U,X,B,A,mu,P,G,beta,N)`.
> 3. **Essential image.** An abstract package is in the image exactly when it satisfies free-vertex
>    capacity, source-minimality, active concentration, derived face descent, critical growth,
>    polarized self-duality, horizon compatibility, and analytic effectivity.
> 4. **Noncircular reconstruction.** The package reconstructs the analytic germ without placing that
>    germ in `mu`, `beta`, or `N`; `N` must be transverse and target-free.
> 5. **Morita invariance.** Equivalent source presentations produce equivalent sheaves, including
>    their residual gauge, normalization-margin spectrum, and critical base-change defects.
> 6. **Universal kinematics.** On every finite Stanley--Reisner chart, `(1)` is recovered exactly;
>    arbitrary topology and arbitrary orientation remain possible before effectivity and coupling.
> 7. **Joint conservativity.** Analytic continuation, monodromy, spectral, boundary, Hermitian,
>    growth, and horizon realizations form a jointly conservative family on `APCSH_eff`.

This is deliberately stronger than assigning a stack, a derived category, or a Postnikov tower to
an HT source.  It is a classification of the quotient stack plus a noncircular transverse
normalization theorem.  Full faithfulness without `N` is refuted and is no longer a live claim.

## A precise constraint on hypertranscendence itself

The conjecture predicts a positive definition replacing the nineteenth-century negative one.

> **[CONJECTURE -- THIN-BOUNDARY CHARACTERIZATION]** An analytic germ is source-minimal
> hypertranscendental exactly when its vertex differential algebra is free at every finite order,
> while its complete nontrivial relation object is an effective active polarized constructible
> boundary sheaf in strictly positive source degree.

Thus hypertranscendence is not absence of structure.  It is a degree displacement:

```text
no vertical finite differential relation
        +
finite or controlled source relation object in positive descent degree
        +
one effective active polarized analytic realization.       (3)
```

The first summand is classical freeness.  The second has the exact Hochster model `(1)` in the
universal facet-sewn class.  The third is the new selection problem.

## Why a sheaf, not one obstruction class

A fixed `H^2` gerbe is already false in the additive pair-face class: there the complete sewing
law is degree one.  Normal-crossing restriction produces genuine exterior higher classes.  Bare
Stanley--Reisner systems realize arbitrary cohomological profiles.  Hence the obstruction degree
depends on the topology and categorical height of the local data.

One constructible derived sheaf accommodates all three facts:

```text
additive pair faces       -> a sheaf truncated at degree one;
normal crossings         -> an exterior higher-coherence fibre;
arbitrary constraint X   -> the induced-subcomplex Hochster profile (1).
```

The Postnikov tower is a filtration of `B`, not the fundamental object.  Different obstruction
chains can land in different homotopy sheaves or different realizations without being forced into
one scalar group.  This remains true on a fixed intrinsic analytic-dimension stratum: the exact
boundary-wedge sources have `htDim=2` and unbounded source-coherence projective dimension.

## Unified-obstruction conjecture

For an effective package `H(F)`, let `Real_r(B)` range over its admissible analytic, monodromic,
spectral, Hermitian, boundary, and growth realizations.

> **[CONJECTURE -- REPRESENTABILITY AND CONSERVATIVITY]** Every stable source-local excisive
> obstruction theory on `HT_reg` is represented by a module object over `B`, and the natural
> realization family is jointly conservative after retaining the comparison maps that pair its
> observations of the same boundary class.

This predicts literal meanings for the familiar failures:

```text
continuation failure     = failure of effectivity or extension of beta;
monodromy                = holonomy of beta on the source site;
spectral incompleteness  = nonzero homology of a stable realization of B;
positivity failure       = failure of P to reduce to the positive real cone;
boundary noncanonicity   = a noncontractible space of effective polarized extensions.
```

The dictionary is not evidence until two independently built realization functors are proved to
preserve the same class and their comparison is conservative.

## Self-dual degeneracy spectrum

For a reflected parameter family `F_s`, suppose the sheaf carries a source-canonical duality

```text
B_(s^vee) ~= D(B_s)                                      (4)
```

and a compatible polarization.  Each conservative realization gives a perfect comparison
complex `C_s`.

> **[CONJECTURE -- COMMON SELF-DUAL DEGENERACY]** The non-acyclicity support of `C_s` is independent
> of the conservative realization and equals the degeneracy support of the polarized sheaf.
> Duality pairs the support under `s -> s^vee`; positivity is the separate theorem that may force
> it onto the fixed locus.

Self-duality alone does not imply fixed-locus concentration.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` A completed-zeta package, if it exists, must be built from a
prime--archimedean source site before its zero divisor.  Different RH proof chains would be
representations of one interval only if they factor through the same `B_zeta`, preserve its
pointing and polarization, and are jointly conservative.  The critical zeros would then be the
common self-dual degeneracy spectrum of `(4)`.  RH would still require a separate positive
fixed-locus theorem.

No zero, zero-indexed operator, or RH-equivalent positivity criterion may define the package.

## Parent-theory collision boundary

The following are established languages, not discoveries:

- constructible and perverse sheaves, derived stacks, and factorization algebras;
- Stanley--Reisner rings, Hochster's formula, and moment-angle complexes;
- Tannakian reconstruction, Riemann--Hilbert correspondences, and parameterized difference Galois
  theory;
- shifted symplectic derived critical loci and excess-intersection theory;
- Krein polarizations, Gevrey bornologies, and controlled cohomology;
- Brown representability in stable categories.

The possible new mathematics is the exact HT functor `(2)`, its intrinsic essential image,
noncircular reconstruction, and joint conservativity across natural analytic obstruction
categories.  Merely placing known HT equations in these parent languages fails the novelty gate.

## First theorem-level attacks

1. Extend the Lean-formalized nonzero nodal Hochster class to the complete chain equivalence for
   a nontrivial finite constraint family.
2. Construct `B` functorially for the facet-sewn Stanley--Reisner class and prove relabeling,
   induced-face, and residue-surgery naturality.
3. Add the active carrier representation and prove the compact-shadow nonattainment theorem is
   exactly failure of active concentration in this sheaf model.
4. Construct one polarized analytic realization for two sources with the same `B` but different
   orientations, and prove the polarization separates them.
5. Construct the polarization-transport homotopy limit for the facet-sewn class and prove that it
   specializes to the Lean boundary-wedge component law.
6. Treat a genuinely nonlinear nonabelian source whose boundary sheaf is not truncated at degree
   one.
7. Construct natural target-free normalization horizons for the Barnes/multiple-sine and generic
   multiple-elliptic-gamma hierarchies, then prove normalized full faithfulness on the
   trivial-cofinal-inertia stratum.
8. Prove two independently constructed realization functors jointly conservative on that class.

## Anti-theatre gate

Retire or enlarge the package if:

1. equivalent source presentations yield inequivalent `B`;
2. `(1)` is not recovered exactly on the Stanley--Reisner class;
3. active capacity, pointing, orientation, or critical growth can be reconstructed from the other
   listed data, making a component redundant;
4. two inequivalent HT germs have equivalent complete noncircular packages;
5. the analytic essential image is all abstract packages, so effectivity imposes no restriction;
6. the realization functors are only verbal analogies or unpaired spectra;
7. an existing correspondence already supplies full faithfulness and the same essential image.

Every no-go must leave an exact positive result: either a smaller fully faithful class, a new
independent component forced by a counterexample, or a theorem that the boundary truncates on the
source class under attack.

## Gates

- [x] universal finite algebraic bulk proved
- [x] arbitrary finite constraint topology realized
- [x] complete Hochster kinematic fibre proved on paper
- [x] first nontrivial Hochster source-coherence class proved in Lean
- [x] arbitrary topology--orientation independence proved from formalized parents
- [x] active compact-shadow nonattainment theorem available
- [x] fixed-degree gerbe proposal falsified
- [x] fixed `htDim=2` shown to support unbounded source-coherence depth
- [x] first restriction-compatible polarization-transport collapse proved in Lean
- [x] bare-source full faithfulness refuted by the Gamma gauge collision
- [x] exact Gamma finite-horizon/cofinal normalization law proved in Lean
- [x] transverse normalization horizon identified as an irreducible package component
- [ ] construct the functorial derived boundary sheaf `B`
- [ ] prove Morita invariance
- [ ] construct one active polarized analytic realization
- [ ] prove a noncircular normalized reconstruction theorem
- [ ] prove a nontrivial essential-image theorem
- [ ] prove two realization functors jointly conservative
- [ ] establish the common self-dual degeneracy spectrum away from RH
- [ ] complete external specialist novelty audit
