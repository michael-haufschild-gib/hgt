# The hypertranscendental polarization-transport spectrum

- **ID:** `hypertranscendental-polarization-transport-spectrum`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / ORIENTATION-DESCENT FIELD / UNIFIED OBSTRUCTION RECEIVER
- **Scientific status:** `[CONJECTURE] [RANK-ONE FINITE SEED PROVED AND LEAN-FORMALIZED]`
  `[FIELDS-SCALE OPEN CORE] [NOVELTY OPEN] [NOT AN RH RESULT]`
- **Parents:**
  - `hypertranscendental-polarization-fibration.md`
  - `hypertranscendental-constraint-sheaf-reconstruction-duality.md`
  - `../2-fully-proven/not_new_scientific_knowledge/polarization-transport-component-collapse.md`
  - `../2-fully-proven/not_new_scientific_knowledge/03-ht-translation-projective-geometry/fixed-analytic-dimension-arbitrary-source-coherence.md`

## Medalist displacement

The universal orientation-surgery theorem proves that the complete unpolarized derived boundary
does not determine orientation.  The rank-one transport theorem proves the converse warning:
orientation is no longer arbitrary once it must be carried by the restriction maps of that
boundary.

Therefore the missing object is neither

```text
derived topology B,                  nor polarization P,
```

but the homotopy-coherent transport of `P` through `B` and its active analytic realizations.

The fixed-analytic-dimension theorem forces this transport object to be unbounded: already on the
stratum `htDim=2`, the source-coherence projective dimension takes every value at least three.
No fixed cohomology group, fixed gerbe degree, or finite Postnikov truncation can be universal.

## Candidate moves and attack

### A. Free topology--sign product `[KILLED]`

Taking `B x {sign chambers}` reproduces orientation surgery exactly and selects nothing.  It is
the local chamber atlas before compatibility, not the source object.

### B. One fixed obstruction class `[KILLED]`

A class in `H^1`, `H^2`, or any fixed degree cannot receive all constraint families.  Pair-face
systems truncate at degree one, normal crossings carry exterior classes of growing degree, and
boundary wedges have arbitrary source-coherence depth at `htDim=2`.

### C. Polarization transport as a sheaf of spaces and its Grothendieck--Witt spectrum `[SELECTED]`

Let `B` be an active self-dual derived constraint sheaf on a stratified source boundary `X`.  For
an active stratum `sigma`, let

```text
Pol_B(sigma)
```

be the groupoid of nondegenerate source-compatible real structures and Hermitian forms on the
analytic realization of `B_sigma`.  Restriction along an exit path pulls a form back only when the
active comparison map is nondegenerate and source-admissible.  This gives a constructible sheaf of
spaces, not a free sign assignment.

Define its transport space and group-completed self-dual receiver by

```text
PTr(B) = holim_(sigma in Exit(X)) Pol_B(sigma),              (1)
GWTr(B)= holim_(sigma in Exit(X)) GW(B_sigma).                (2)
```

The positivity subspace `PTr^+(B)` is retained before group completion.  A source pointing is a
specified point or boundary germ from which a section may be transported; it is forbidden to use
the target zero divisor or desired positivity conclusion.

## Polarization-transport conjecture

> **[CONJECTURE -- HT POLARIZATION-TRANSPORT COMPLETENESS]** For every regular source-minimal
> self-dual analytic HT germ `F`, the polarization layer of its minimal active constraint object
> is presentation-independently equivalent to `(PTr(B_F),GWTr(B_F))`.  Moreover:
>
> 1. `pi_0 PTr(B_F)` is the moduli of globally compatible Witt/Krein chambers;
> 2. `pi_1 PTr(B_F)` records polarization monodromy and isometry ambiguity;
> 3. higher homotopy groups record successive coherent extension obstructions;
> 4. the source pointing and analytic growth law define a canonical lift problem into
>    `PTr^+(B_F)`;
> 5. the full lift tower is functorial under source morphisms and Morita-invariant under changes
>    of source presentation;
> 6. together with the active boundary sheaf, the transport object is jointly conservative for
>    continuation, monodromy, spectral, positivity, and boundary-condition realizations.

This is not the assertion that Hermitian K-theory exists.  The open content is that an HT source
canonically constructs the diagram in `(1)`--`(2)`, that its admissible transport maps have an
intrinsic analytic essential image, and that the resulting coupled object reconstructs the
orientation-sensitive source data.

## Exact finite seed `[PROVED + LEAN]`

For rank-one Boolean forms, `Pol_B` is the locally constant sign sheaf.  Hence

```text
PTr(B) ~= {+,-}^(pi_0(X)).                                  (3)
```

For the deleted-centre boundary wedge, `pi_0=2`, so `(3)` is a four-point fibre.  Sewing through
the common vertex makes the boundary connected and collapses the fibre to two points.  A positive
pointing at the common vertex leaves one point.

Lean formalizes the two exact equivalences as

```text
boundaryWedgeDeletedCompatibleOrientationEquivBoolProd
boundaryWedgeCompatibleOrientationEquivBool.
```

This seed is deliberately elementary.  Its role is to prove that the proposed coupling is not an
empty decoration: transport strictly reduces the orientation-surgery fibre.

## Fixed-dimension nontruncation law `[PROVED BRIDGE]`

For every `m>=3`, there is a scalar meromorphic HT source with

```text
htDim=2,                 pd(source coherence)=m.            (4)
```

Therefore any universal construction of `(1)`--`(2)` must admit arbitrarily high obstruction
layers over one fixed analytic-dimension stratum.  Analytic thinness cannot mean bounded
cohomological amplitude.  It must instead mean bounded source rank, active carrier rank, or a
controlled comparison symbol while the compatibility tower remains unbounded.

## Unified obstruction dictionary `[CONJECTURE]`

For the canonical source lift problem into `PTr^+(B_F)`:

```text
continuation failure      = failure to extend the transport diagram to an analytic collar;
monodromy                 = nontrivial holonomy of the transported polarization;
positivity failure        = no global lift lands in PTr^+(B_F);
boundary noncanonicity    = a noncontractible space of positive lifts;
spectral incompleteness   = nonzero homology in a conservative linear realization of the
                            polarized transport cone.
```

These are not declared equal.  They are different invariants of one coupled lift problem.  The
claim is meaningful only after independent realization functors are constructed and proved to
preserve the same source class with comparison maps.

## Strong positive prediction

> **[CONJECTURE -- POINTED CONNECTED TRANSPORT RIGIDITY]** On an analytically connected active
> boundary with nondegenerate transport and trivial positive holonomy, one source-positive
> pointing extends to at most one global positive polarization.  Existence is the remaining
> descent obstruction.

The rank-one finite theorem proves this prediction when every active stalk is a real line and all
transport maps preserve its nonzero form.  In higher rank, the exact obstruction should live in
the positive component of `(1)` together with its Grothendieck--Witt class, not in unpolarized
cohomology.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` A zeta source object, if constructed independently of its zeros,
would need to supply a point of `PTr^+(B_zeta)`.  Derived topology could locate the common
self-dual degeneracy support, while the transported positive section would be the additional datum
capable of distinguishing fixed-locus degeneracy from an indefinite off-axis realization.

Any proposed RH proof that never changes under motion in the local chamber product before descent
has omitted `(1)` and cannot establish an orientation-sensitive conclusion.  Nothing here proves
that `B_zeta`, its positive transport point, or the fixed-locus theorem exists.

## Parent-theory and novelty gate

The following are established parent mathematics and are not novelty claims:

- constructible hypersheaves represented by exit-path functors;
- Grothendieck--Witt spaces and spectra of stable categories with duality;
- Hermitian K-theory, Witt groups, and descent of self-dual complexes;
- obstruction towers and homotopy limits;
- locally constant signature data on connected spaces.

Primary parent sources checked include:

1. D. Lejay, *Constructible hypersheaves via exit paths*,
   `https://arxiv.org/abs/2102.12325`;
2. M. Spitzweck, *A Grothendieck--Witt space for stable infinity categories with duality*,
   `https://arxiv.org/abs/1610.10044`;
3. M. Hoyois, J. Jelisiejew, D. Nardin, and M. Yakerson,
   *Hermitian K-theory via oriented Gorenstein algebras*,
   `https://arxiv.org/abs/2103.15474`.

Preliminary exact searches found these ingredients separately.  They did not locate an HT source
construction of `(1)`--`(2)`, an analytic essential-image theorem for its transport maps, or joint
conservativity across the five obstruction realizations.  Scientific novelty remains open until
those statements are proved and independently audited.

The conjecture fails the anti-theatre gate if `Pol_B` is defined as all forms with arbitrary maps,
if the source germ is hidden in a comparison field, if positivity is inserted after a target
spectrum is known, or if `(1)` reduces to a standard locally constant GW sheaf without an
HT-specific analytic essential image.

## Theorem program

1. Generalize the Lean rank-one component law from the boundary wedge to arbitrary finite
   constraint complexes.
2. Replace Boolean signs by one-dimensional nonzero real transport scalars and prove that metric
   existence is exactly trivial positive holonomy; pointing then gives uniqueness.
3. Construct `Pol_B` for the facet-sewn analytic Stanley--Reisner class and prove residue-surgery,
   restriction, and relabeling naturality.
4. Construct one higher-rank normal-crossing chart and identify its first nontrivial Witt
   obstruction.
5. Prove presentation invariance and one nontrivial analytic essential-image theorem.
6. Compare two genuinely inequivalent analytic realization functors and prove conservativity on a
   nontrivial source class.

## Gates

- [x] free orientation product killed
- [x] fixed-degree obstruction receiver killed
- [x] rank-one transport fibre proved on paper
- [x] rank-one boundary-wedge fibre formalized in Lean
- [x] fixed-analytic-dimension nontruncation proved
- [x] parent theories named explicitly
- [ ] arbitrary finite-complex rank-one transport theorem in Lean
- [ ] nonzero-scalar holonomy theorem
- [ ] analytic `Pol_B` construction for one HT class
- [ ] presentation invariance
- [ ] independent realization comparison
- [ ] scientific novelty and significance audit after a non-parent theorem is proved
