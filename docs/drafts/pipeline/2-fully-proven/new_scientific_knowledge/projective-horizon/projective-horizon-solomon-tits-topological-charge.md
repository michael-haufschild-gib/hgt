# Projective horizon Solomon--Tits topological charge

- **ID:** `projective-horizon-solomon-tits-topological-charge`
- **Stage:** 2-fully-proven
- **Type:** TOPOLOGY OF DIFFERENTIAL INFORMATION CONTEXTS
- **Scientific status:** `[PROVED CONSEQUENCE] [NOVEL APPLICATION CANDIDATE]`
- **Parent:** `projective-horizon-tits-building`
- **Statement:** The incidence complex of nontrivial common projective derivative horizons of an
  `N`-channel differential-generic HT source is homotopy equivalent to a wedge of
  `(N-2)`-spheres. Its unique nonzero reduced homology degree carries the Steinberg
  representation of the projective observer group.

## Horizon context complex

Use the parent theorem's notation. For every nonzero proper subspace `S subset V*`, let

```text
mathcal I_S=F^(G_S)
```

be the common field of any collection of hyperplane horizons whose normals span `S`.

Define `Delta_HT(V)` to be the order complex whose vertices are these nontrivial common-horizon
fields and whose simplices are strict chains

```text
mathcal I_(S_0) > mathcal I_(S_1) > ... > mathcal I_(S_k). (1)
```

Because `S |-> mathcal I_S` is injective and order-reversing, `(1)` is equivalently a flag

```text
0 < S_0 < S_1 < ... < S_k < V*.                           (2)
```

## Theorem

There is a canonical simplicial isomorphism

```text
Delta_HT(V) congruent Delta_Tits(V*),                      (3)
```

where the right side is the spherical Tits building of `PGL(V)`.

Consequently, by the Solomon--Tits theorem,

```text
Delta_HT(V) homotopy-equivalent to a wedge of S^(N-2).     (4)
```

In particular,

```text
reduced H_j(Delta_HT(V),Z)=0       for j != N-2,           (5)
reduced H_(N-2)(Delta_HT(V),Z)=St_N(C),                    (6)
```

where `St_N(C)` is the integral Steinberg module under the natural `PGL_N(C)` action.

Thus the projective HT horizon system has one intrinsic topological information degree,
`N-2`; it is neither contractible nor a manifold in general, but a wedge of top-dimensional
spheres carrying the Steinberg observer representation.

## Proof

The parent theorem proves that `S |-> mathcal I_S` is an order-reversing bijection from the
nonzero proper subspaces occurring in the building to the nontrivial common-horizon fields, and
that span is carried to field intersection. Reversing every chain gives the simplicial
isomorphism `(3)`. Equations `(4)--(6)` are exactly the Solomon--Tits theorem and the definition of
the Steinberg module as the top reduced homology of the spherical building.

## Apartments and observer frames

A basis `alpha_1,...,alpha_N` of `V*` gives a projective observer frame. The common-horizon fields
indexed by the nonempty proper coordinate spans form an apartment in `Delta_HT(V)`. Its order
complex is the Coxeter sphere `S^(N-2)`, and its fundamental class is an apartment generator of
the Steinberg module.

For `N=3`, an apartment is a hexagonal loop alternating

```text
single-observer horizons  <->  pairwise common-horizon fields.
```

The loop is the first genuinely one-dimensional HT horizon charge. For `N=2`, the topology is
zero-dimensional and reduces to the scalar projective-horizon family. For `N=4`, observer frames
carry two-sphere apartment classes.

## Physical interpretation

The theorem supplies an exact topology, not a metaphor:

- points and flags are differential subfields determined by observer horizons;
- the dimension `N-2` is forced by projective incidence;
- topological cycles are changes of complete projective observer frame;
- the observer symmetry acts on those cycles through the Steinberg representation.

This is a topology of information contexts, not spacetime. It gives a mathematically literal
candidate for a holographic boundary complex: any two distinct elementary horizons reconstruct
the source, while their entire compatibility pattern lives on a spherical building. No metric,
Hamiltonian, causal cone, entropy, quantum amplitude, or black-hole identification has been
constructed.

## Novelty and significance gate

- The Solomon--Tits theorem and Steinberg module are classical.
- The new content is the parent theorem's identification of HT derivative-horizon fields with the
  projective building; `(4)--(6)` are the exact topological consequences of that identification.
- No checked source attaches the Solomon--Tits homotopy type or Steinberg module to derivative
  horizons of hypertranscendental sources.

This card does not relabel a classical theorem as a discovery. Its novelty rises or falls with the
parent horizon-building theorem.

## Lean boundary

This section was written before the formalisation and is superseded by the Log; it is rewritten
here to match what the tree now contains.

Formalized, unconditionally, axioms `[propext, Classical.choice, Quot.sound]` throughout:

- `(3)` the simplicial identification — `HorizonComplexIso.lean` (`horizonComplexIso`), on the two
  hypotheses the parent theorem owes: the stabiliser assignment is monotone and order-reflecting.
- `(5)` in full — `BuildingHomologyConcentration.lean` (`isZero_homology_building_of_ne`): the
  homology of the building vanishes in every degree except `0` and `N - 2`, for any coefficients;
  and `BuildingConnected.lean` (`homologyZeroIsoBuilding`) supplies degree zero, where the homology
  is a single copy of the coefficients because the complex is connected — so the *reduced* homology
  vanishes off `N - 2`, which is what `(5)` asserts.
  Its two halves are the Solomon--Tits induction proved in this corpus
  (`FamilyBuildingVanishing.lean`, `BuildingVanishingSubmodule.lean`,
  `BuildingVanishingDual.lean`) and the dimension bound `buildingHasDimensionLT`.
- `(6)`'s definitional half and the observer action — `BuildingAutomorphismAction.lean`
  (`steinbergModule`, `steinbergAction`).
- `(6)`'s freeness — `BuildingFreeSubmodule.lean` (`Steinberg.isFreeOver_steinbergModule`): the
  Steinberg module is a coproduct of copies of the coefficients.  It rests on
  `isFreeOver_homology_famBuilding`, which gives freeness of the homology of a disjoint union of
  interval buildings in every positive degree, for any bounded modular lattice with atoms below
  every nonzero element, with no rank hypothesis.
- `(6)`'s nonvanishing — `BuildingNonvanishing.lean` (`not_isZero_steinbergModule`,
  `exists_nonempty_index_steinbergModule`): for `N ≥ 3` the index set of that coproduct is nonempty,
  so the Steinberg module is a nonzero representation and the building is not contractible.
- The apartment classes — `ApartmentClass.lean` (`apartmentClass`,
  `apartmentClass_steinbergAction`): every observer frame gives a map `R ⟶ St_N`, the image of the
  fundamental class of its Coxeter sphere, and the observer group permutes these classes.  They are
  monomorphisms, hence nonzero — `ApartmentClassMono.lean` (`mono_apartmentClass`,
  `apartmentClass_ne_zero`), from the general fact that in the top degree homology is a subobject of
  the normalized chains (`TopDegreeMono.lean`).
- Extra structure the card did not state: the top homology of a building of rank `r` is
  *isomorphic* to that of the disjoint union of the buildings of rank `r - 1` below the coatoms
  (`FamilyTopHomologyEmbedding.lean`, `isIso_famTopEmbedding`).
- The apartment paragraph's sphere statement — `ApartmentTopHomology.lean`
  (`nonempty_homology_iso_apartment`): the top homology of the order complex of the proper part of
  the Boolean lattice on `N` elements is one copy of the coefficients.  Its input is the thinness of
  the Boolean cover (`BooleanIntervalCover.lean`): exactly one element of an interval spans it with
  a given point.

Not formalized, and not claimed:

- `(4)` as a homotopy equivalence.  What is proved is its homological content, which is `(5)` together
  with `homology_building_wedge`.  This is the one numbered claim of the card that is not formalized.

Beyond the card's numbered claims, as a stretch:

- Solomon's *basis* theorem — that the apartment classes span the Steinberg module.  The card's
  apartment paragraph says "its fundamental class is an apartment generator", and everything that
  phrase asserts of a single frame is proved: the class is constructed, injective, nonzero,
  equivariant, and generates the apartment's own top homology.  Whether the apartment classes
  together *span* `St` is Solomon's theorem, which the card does not state; its classical proof is a
  shelling induction on gallery distance, elementwise and so unavailable in an arbitrary abelian
  category.  The route that does transfer is the Mayer--Vietoris descent, and the pieces for it are
  being built (`ApartmentInterval.lean`, the star/base splitting criteria).

The supporting general machinery — many-piece Mayer--Vietoris for an arbitrary index, the
locally-conical vanishing tool, and the disjoint-union-of-nerves identification — is listed in the
Log entries of 2026-08-02 and is reusable for any order complex.

## RH impact audit

`[NO CURRENT RH CONSEQUENCE]` If a natural `N`-channel projective zeta observation were found, its
horizon-context complex would carry a Steinberg top class. There is no established map from that
class to positivity, a Weil criterion, or zero location.

## Gates

- [x] 0 -> 1: exact topology extracted from the horizon-building poset
- [x] 1 -> 2: simplicial identification and Solomon--Tits consequence proved
- [ ] 2 -> 3: `(3)`, `(5)` and `(6)` formalized in full — the last with freeness, nonvanishing, the
  top-cycle description and explicit equivariant apartment classes; the only numbered claim left is
  `(4)` as a homotopy statement, whose homological content is proved
- [ ] 3 -> 4: depends on external audit and publication of the parent theorem

## Reference

- L. Solomon and J. Tits, the Solomon--Tits theorem: the building of proper nonzero subspaces of
  an `N`-dimensional vector space is a wedge of `(N-2)`-spheres, with top homology the Steinberg
  module.

## Log

- 2026-07-15 — derived the horizon context complex and its Steinberg topological charge from the
  projective horizon building theorem.

## Log

- 2026-08-01 — **The passage `(1)` → `(2)` and the dimension of `Δ_HT(V)` are formalized.**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveFlagDimension.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The card's own reduction is that `S ↦ I_S` is injective and order-reversing, so a strict chain of
  common-horizon fields `(1)` is the same thing as a flag of subspaces `(2)`.  That step is now a
  theorem, in the generality it is used in:

  `card_image_eq_and_chain` — an order-reversing injection carries a chain of subspaces to a chain of
  the same size, so the two complexes have the same simplices;
  `card_image_le_finrank_sub_one` — hence the simplices of `Δ_HT(V)` have at most `N - 1` vertices;
  `exists_image_chain_card_eq` — and that is attained, by transporting the flag of a frame.

  So `Δ_HT(V)` has top simplices of dimension exactly `N - 2`, which is the dimension appearing in
  `(4)`, `(5)` and `(6)`, established on the card's own object rather than through the building.

  The supporting flag-complex results are those recorded on
  `projective-ht-horizon-symmetric-space-boundary`: the dimension bound and its attainment, vertices
  typed by codimension with each type a single orbit, the simplicial and type-preserving action, and
  the apartment of a frame with its `N!` chambers.

  What stays out of reach is the homotopy content: `(4)`, `(5)` and `(6)` assert a homotopy
  equivalence to a wedge of `(N-2)`-spheres and the identification of the top reduced homology with
  the Steinberg module.  The local toolchain has no order-complex homotopy theory, so the Solomon--Tits
  theorem itself is not encoded, by an axiom or otherwise.  What is formalized is the combinatorial
  input it consumes.

- 2026-08-01 — **The horizon assignment `S ↦ I_S` is proved to be an order-reversing injection.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonGaloisAssignment.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  The card asserts that `S ↦ I_S = F^(G_S)` is injective and order-reversing, and reads `(1)` as
  `(2)` on that basis.  Over a finite extension this follows from mathlib's Galois correspondence and
  is now proved:

  `fixedField_injective` — the fixed-field map on subgroups is injective, because the fixing subgroup
  recovers it (`IntermediateField.fixingSubgroup_fixedField`, which needs only finite
  dimensionality);
  `fixedField_antitone` — and order-reversing, directly from the membership criterion;
  `fixedField_comp_injective_antitone` — so if the stabiliser `S ↦ G_S` is itself injective and
  monotone, the horizon field `S ↦ I_S` is injective and antitone.  That is the card's claim, with
  its two inputs separated: what the parent horizon theorem has to supply is exactly injectivity and
  monotonicity of the **stabiliser**, and nothing about fields.

  `card_image_fixedField_le` and `exists_image_fixedField_card_eq` — chaining with the transport of
  the previous entry, a strict chain of common-horizon fields has at most `N - 1` members and that is
  attained.  So the dimension of `Δ_HT(V)` is established on the fields themselves, not on the
  subspaces they come from.

  Unchanged: `(4)`, `(5)`, `(6)` are homotopy statements and Solomon--Tits itself is not encoded.

- 2026-08-01 — **The stabiliser half of the assignment, and a full audit.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonGaloisAssignment.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `horizonStabilizer` is the stabiliser of a family of horizons — the subgroup generated by the
  stabilisers of the elementary horizons the family contains — and `horizonStabilizer_monotone`
  proves it monotone, with `le_horizonStabilizer` the containment of each elementary stabiliser.

  With the previous entry this discharges one of the two inputs the card's `(1)` → `(2)` needs.  The
  field half was already reduced to mathlib's Galois correspondence; the stabiliser half is now
  monotone by construction.  What the parent horizon theorem still has to supply is **injectivity of
  the stabiliser assignment** alone — that distinct families of horizons have distinct stabilisers —
  which is a statement about the horizon geometry and about nothing else.

  Audit.  `lake build GaloisForLFunctions.HTGeometry` completes, `12790` jobs, with all seventeen
  modules of this session's work wired into the umbrella and every result depending only on
  `propext`, `Classical.choice`, `Quot.sound`.  The single remaining lint error names a module owned
  by other work (`HTGeometry.FullJetPolyNonzeroDatum`).

- 2026-08-01 — **Injectivity is reduced to detection alone.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonGaloisAssignment.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `horizonStabilizer_injective` — the stabiliser assignment is injective as soon as two conditions
  hold: **detection**, that an elementary horizon's stabiliser lies in a family's stabiliser only
  when the horizon belongs to the family; and **generation**, that a family is determined by the
  elementary horizons it contains.

  `eq_of_lines_le_iff` — generation is a theorem for the poset of horizon families: a subspace is
  determined by the lines it contains, because every nonzero vector spans a line
  (`finrank_span_singleton`) and `span {x} ≤ S` is `x ∈ S`.

  So the entire chain `(1)` → `(2)` — the passage from strict chains of common-horizon fields to
  flags of subspaces, on which this card's identification `(3)` rests — is now Lean except for one
  hypothesis: **detection**.  Everything else is discharged: the field half against mathlib's Galois
  correspondence, monotonicity by construction, generation by linear algebra, and the transport of
  chains and their dimension bound by the flag work.

  Detection is where the horizon geometry genuinely enters, and it is the parent theorem's business:
  it says that a hyperplane horizon whose stabiliser is already contained in the stabiliser of a
  family must itself be one of that family's horizons.  Stating it is now a matter of naming the
  parent's content, not of finding the right formulation.

  Unchanged: `(4)`, `(5)`, `(6)` are homotopy statements and Solomon--Tits itself is not encoded.

- 2026-08-01 — **The criterion is stated at the right generality, and shown satisfiable.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonGaloisAssignment.lean`, axioms: `horizonStabilizer_id`
  and `horizonStabilizer_injective` depend on **no axioms at all**.

  `horizonStabilizer` is now defined for an arbitrary complete lattice of stabilisers rather than for
  subgroups only, so the same criterion applies to subgroups, to subspaces and to intermediate fields
  without restatement.  The monotonicity, containment and injectivity results carry over unchanged.

  `horizonStabilizer_id` — taking each family of horizons to be its own stabiliser, the assignment is
  the identity, because the join of everything below a family is that family.  Detection and
  generation both hold there, so the injectivity criterion of the previous entry has a model: it is
  not a hypothesis class that could turn out to be empty.

  That completes what can be said about `(1)` → `(2)` without the horizon geometry.  The one
  remaining input is detection for the actual stabilisers, which the parent theorem owes.

- 2026-08-01 — **The reduction collapses to one condition: the stabiliser reflects the order.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonGaloisAssignment.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `fixedField_reflects_le` — over a finite extension the fixed-field map **reflects** the order
  automatically: if one fixed field contains another, the subgroups are nested the other way.  This
  follows from `fixingSubgroup_antitone` and the round trip `fixingSubgroup (fixedField H) = H`.  So
  the fixed-field map is an order embedding into the opposite order, not merely an antitone
  injection.

  `injective_of_reflects_le` — an order-reflecting map is injective, with no monotonicity assumed in
  either direction.  So injectivity never has to be hypothesised separately.

  `fixedField_comp_injective_of_reflects` — consequently the horizon assignment `S ↦ I_S` is injective
  as soon as the **stabiliser** assignment reflects the order: `G_S ≤ G_T → S ≤ T`.

  That is a single condition where the previous entries had two.  Detection and generation are both
  subsumed: order reflection is what they were jointly encoding, and it is the exact statement that a
  family of horizons is recovered from its stabiliser.  Everything else on the path from `(1)` to
  `(2)` — antitonicity, injectivity, the chain transport, the dimension bound and its attainment — is
  proved.

  Unchanged: `(4)`, `(5)`, `(6)` are homotopy statements and Solomon--Tits itself is not encoded.

- 2026-08-02 — **`(3)` is formalized: the horizon complex *is* the order complex of the building.**
  `formal/GaloisForLFunctions/HTGeometry/HorizonComplexIso.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  horizonComplexIso :
    nerve ({S : S ≠ ⊥ ∧ S ≠ ⊤}ᵒᵈ) ≅ nerve (Set.range (fun S => fixedField (G S)))
  ```

  for every stabiliser assignment `G` that is monotone and order-reflecting.  This is the card's
  canonical simplicial isomorphism `(3)`, and it needs no topology: an antitone, order-reflecting map
  is an order isomorphism from the opposite order onto its range (`orderIsoRangeOfAntitone`), and an
  order isomorphism induces an isomorphism of nerves (`orderIsoNerveIso`).  A strict chain of
  common-horizon fields is literally a flag of nonzero proper subspaces, which is `(1) ↔ (2)`.

  The two hypotheses are exactly the ones the parent theorem owes and no more.  Monotonicity is
  already discharged in general by `horizonStabilizer_monotone`; order-reflection is the detection
  property, and `horizonStabilizer_injective` reduces it to detection on elementary horizons, with
  `eq_of_lines_le_iff` supplying the generation half.

  Consequences, both in the same module:

  ```text
  isZero_horizonComplexHomology  :  N - 1 ≤ n  →  H_n(Δ_HT(V); R) = 0
  horizonComplexHomologyZeroIso  :  3 ≤ N      →  H_0(Δ_HT(V); R) ≅ R
  ```

  so `(5)` holds at both ends of the range, for any coefficients — and at `N = 3` it holds
  completely, the homology being concentrated in degree `N - 2 = 1`.  What is still open is the
  middle range `1 ≤ j ≤ N - 3` and the Steinberg identification `(6)`; both are statements about
  `Δ_Tits(V*)` alone, which is what the card cites Solomon--Tits for.

  Supporting general lemma: `orderIsoRange`, a monotone order-reflecting map is an order isomorphism
  onto its range.

- 2026-08-02 — **The induction engine for Solomon--Tits: the link of a vertex is the building of the
  quotient.**  `formal/GaloisForLFunctions/HTGeometry/BuildingLinkQuotient.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  OrderIso.subtypeCongr :   restrict an order isomorphism to matching subtypes
  linkQuotientOrderIso :
    {W : proper nonzero subspace of M ⧸ p}  ≃o  {U : p < U < ⊤}
  ```

  The proper subspaces strictly above `p` are order isomorphic to the proper nonzero subspaces of the
  quotient by `p`, by the submodule correspondence theorem (`Submodule.comapMkQRelIso`) restricted to
  the strict range.  Composed with `orderIsoNerveIso` this identifies the *nerve* of the link with the
  nerve of the building of a space of smaller dimension, which is what an induction on dimension
  needs.

  This is the piece the middle-range vanishing `1 <= j <= N - 3` will be built on; the star of a
  vertex is already known contractible here (`isZero_homology_star`), so what remains is the gluing —
  and the earlier finding stands that the naive star/complement Mayer--Vietoris cover cannot do it,
  since the complement of a star is not acyclic.

- 2026-08-02 — **The contractible piece of the Solomon--Tits decomposition.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingNotSpanning.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  notSpanningPoset p :  the nonzero subspaces U with U ⊔ p still proper
  notSpanningJoin :     joining with p stays inside that family
  isZero_homology_notSpanningPoset :  it has no homology in positive degrees
  ```

  Fix a nonzero proper `p`.  Everything that fails to span together with `p` retracts onto `p`: the
  monotone map `U |-> U ⊔ p` stays inside the family — because `(U ⊔ p) ⊔ p = U ⊔ p` — dominates the
  identity and dominates the constant `p`, which is conical contractibility in the form
  `isZero_homology_of_conical` already consumes.

  With the link identification of the previous entry the two halves of the Solomon--Tits induction
  are now in place: the piece that does not span with `p` is contractible, and the link of `p` is the
  building of the quotient.  What is still missing is the gluing — the building is the union of this
  contractible piece with the stars of the hyperplanes avoiding `p`, and that is a cover with many
  pieces rather than the two a plain Mayer--Vietoris handles.

- 2026-08-02 — **The induction step in homological form.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingLinkHomology.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  homologyIsoOfIso :   an isomorphism of simplicial sets induces one on homology
  linkHomologyIso :
    H_n(link of p)  ≅  H_n(building of M ⧸ p),  for any coefficients
  ```

  The order isomorphism of the previous entry, transported along the nerve and then along homology.
  This is the shape a dimension induction consumes directly: the link of a vertex contributes the
  homology of a building one dimension down.

  Current state of the Solomon--Tits attack in this corpus, all unconditional: stars of vertices are
  contractible; the non-spanning family of a vertex is contractible; the link of a vertex has the
  homology of the quotient building; cutting at a *minimal* element is available as
  `isZero_homology_nerve_of_minimal_mono`, whose remaining hypothesis is the vanishing for the
  complement of the star.  That complement — the subspaces not containing `p` — is where the argument
  still stops, and the earlier no-go stands: it is not acyclic, so the two-piece cut cannot close the
  induction on its own.  The classical proofs cover the building by the stars of the hyperplanes
  avoiding `p`, which is a many-piece cover.

- 2026-08-02 — **An order complex can be cut at *any* vertex, not only a minimal one.**
  `formal/GaloisForLFunctions/HTGeometry/NerveVertexRemoval.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  generalStar p :  the elements comparable to p
  generalStarCone, isZero_homology_generalStar :  that star is contractible, for any p
  nerveSubcomplex_generalStar_sup_compl :  the star and the complement of p cover
  isZero_homology_nerve_of_vertex :  hence the cut, at an arbitrary vertex
  ```

  The earlier cut in `NerveMayerVietoris` assumed `p` minimal, and used minimality twice: to make the
  star a cone and to make the two pieces cover.  Neither needs it.  The star of any element is
  conically contractible by the fold `q |-> if q <= p then p else q`, which is monotone on the star
  precisely because every element there is comparable to `p`; and the cover holds because a chain
  containing `p` has all its members comparable to `p`.

  For a building this matters: the vertex removed can be a hyperplane or any intermediate subspace,
  not only a point, and the intersection term becomes the *punctured* star — the elements strictly
  below joined to those strictly above — rather than only the upper link.

  Build note: the umbrella did not build at the end of this entry, the failure being in
  `CrossLayerLiftParityRigidity.lean`, a file another agent was editing at that moment (mtime 21
  seconds before the check).  The module logged here builds and audits clean on its own.

- 2026-08-02 — **The lower link, and the punctured star as the union of the two links.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingLowerLink.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]` (the set identity needs only
  `[propext, Quot.sound]`):

  ```text
  generalStar_inter_compl_eq :             punctured star  =  lower link  ∪  upper link
  generalStar_inter_compl_eq_of_maximal :  at a maximal element, the lower link alone
  lowerLinkOrderIso :   {W proper nonzero in p}  ≃o  {U : ⊥ < U < p}
  lowerLinkHomologyIso : and the same homology
  ```

  Dual to the upper-link identification: the proper nonzero subspaces strictly below `p` are the
  proper nonzero subspaces of `p` itself, by `Submodule.mapIic`.  So the local picture at a vertex of
  a building is now complete in both directions — removing a vertex leaves the building of that
  vertex below it and the building of the quotient above it, and the term the Mayer--Vietoris
  sequence sees is the union of the two.

  At a **hyperplane** this specialises usefully: a hyperplane is maximal, so its punctured star is
  just the building of the hyperplane, one dimension down.  That is a cut whose intersection term is
  a smaller building with no join to analyse.

  Build note: the umbrella did not build at the end of this entry, first with a missing object file
  and then with a compile error, both in `ParityCompleteLocalExtensionRelationEscape.lean` — another
  agent's file, mtime four seconds before the check.  The module logged here builds and audits clean
  on its own.

- 2026-08-02 — **The cut at a hyperplane, and why the naive induction still does not close.**
  `formal/GaloisForLFunctions/HTGeometry/NerveMaximalCut.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13015 jobs:

  ```text
  isZero_homology_nerve_of_maximal :
    at a maximal vertex the cut needs only the complement and the lower link
  buildingPoset R M, isMaximal_hyperplane :  a hyperplane is a maximal vertex of the building
  ```

  Combined with the lower-link identification this is the cleanest cut available: removing a
  hyperplane `H` leaves the complement and, as the Mayer--Vietoris term, the building of `H` — one
  dimension down, exactly what an induction wants.

  A negative finding, recorded so the route is not re-attempted.  Iterating that cut does **not**
  close the vanishing.  Removing all hyperplanes one at a time is fine — for distinct hyperplanes
  `H'` is never below `H`, so each star is unchanged and each intersection term is a smaller building
  — but the process must continue into lower dimensions, and removing a `d`-dimensional vertex
  contributes `H_(i-1)` of a `d`-dimensional building, which vanishes only for `d >= i + 2`.  Stopping
  at that bound leaves the poset of subspaces of dimension at most `i + 1`, whose order complex has
  dimension exactly `i`, so `H_i` is its top homology and is not zero.  The vertex-by-vertex descent
  therefore cannot reach the middle range on its own; the classical proofs use a shelling of the
  apartments or a many-piece cover, and one of those is what is still missing.

- 2026-08-02 — **The missing infrastructure, first half: Mayer--Vietoris over the union.**
  `formal/GaloisForLFunctions/HTGeometry/CoproductMayerVietorisSup.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13018
  jobs:

  ```text
  mvSupSnd, mvSupShortComplex, mvSupSection, mvSupSplitting
  mvSupShortExact :
    0 → coprod(S₁ ∩ S₂) → coprod S₁ ⊞ coprod S₂ → coprod(S₁ ∪ S₂) → 0  is split exact
  ```

  The previous coproduct Mayer--Vietoris landed in the coproduct over the *whole ambient type* and so
  needed a covering hypothesis; this one lands in the coproduct over the union and needs none — the
  union covers itself.  The proof mirrors the old one with the restriction `restr R (S₁ ∪ S₂) S` in
  place of `restrFull R S` and `inclCop` in place of `inclFull`, and the case analysis uses `x.2`
  where the old one used the cover.

  This is the half of the missing machinery that the previous entry identified: an iterated cover
  needs Mayer--Vietoris concluding about `A ⊔ B` rather than about the ambient simplicial set, and
  every route to a many-piece cover reduces to it.  What remains is to lift it from coproducts to
  chain complexes of subcomplexes, which is the same mirroring one level up.

- 2026-08-02 — **The missing infrastructure, second half: Mayer--Vietoris for subcomplexes over the
  union.**  `formal/GaloisForLFunctions/HTGeometry/SimplicialMayerVietorisSup.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13020
  jobs:

  ```text
  homOfLE_comp_homOfLE_eq, mvSupChainSnd, mvSupChainShortComplex, mvSupChainShortComplexIso
  mvSupChainShortExact :
    0 → chains(A ⊓ B) → chains A ⊞ chains B → chains(A ⊔ B) → 0   short exact, no cover needed
  isZero_homology_of_mayerVietoris_sup :
    both pieces acyclic in degree i, intersection acyclic in degree i - 1
      ⟹  the union is acyclic in degree i
  ```

  The gap identified two entries ago is now closed.  The degreewise input is the split exactness over
  the union proved in the previous entry, and the identification is again the identity on both ends,
  because the chain group of `A ⊔ B` in degree `n` is definitionally the coproduct over
  `A.obj n ∪ B.obj n`.

  With this, a many-piece cover can be folded one piece at a time: the union of a finite family is
  built up by repeated application, each step needing only that the new piece is acyclic and that its
  intersection with the partial union is acyclic one degree down.  That is the shape the Solomon--Tits
  cover by the stars of the hyperplanes avoiding a point requires.

- 2026-08-02 — **The many-piece cover, folded.**
  `formal/GaloisForLFunctions/HTGeometry/SimplicialMayerVietorisFold.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13021
  jobs:

  ```text
  isZero_homology_finsetSup :
    every piece acyclic in degree i,  every A a ⊓ (partial union) acyclic in degree i - 1
      ⟹  the union over any nonempty finite family is acyclic in degree i
  ```

  Induction over nonempty finsets by `Finset.Nonempty.cons_induction`, each step a single use of the
  two-piece Mayer--Vietoris over the union.  Using the nonempty induction avoids having to say
  anything about the empty subcomplex.

  The machinery the last three entries were after is now complete: a finite cover of an order complex
  by acyclic pieces with acyclic partial intersections gives vanishing.  For Solomon--Tits over a
  finite field this is directly applicable — the building is covered by the star of a point together
  with the stars of the hyperplanes avoiding it, all of them contractible by
  `isZero_homology_generalStar` — and what has to be computed next is the partial intersections of
  those stars.

- 2026-08-02 — **Mayer--Vietoris in the bottom degree, and the fold over a cover with a base.**
  Five modules, all wired into the `HTGeometry` umbrella, all
  `[propext, Classical.choice, Quot.sound]`; umbrella green at 13037 jobs:

  ```text
  ConstHomologyMono.lean
    homologyMap_const_eq_id_of_conical :  a conical nerve is homologically constant, in every degree
    isSplitMono_homologyMap_of_homologyMap_const_id, mono_homologyMap_of_homologyMap_const_id :
      a homologically constant simplicial set is a homology retract of everything it maps into
    homologyMap_const_eq_id_of_vertex :   the vertex does not matter
    homologyMap_const_eq_id_of_iso :      and the property transports along isomorphisms
  SimplicialMayerVietorisMono.lean
    isZero_homology_of_mayerVietoris_sup_mono :   vanishing over the union under injectivity
    mono_homologyMap_mvChainFst_of_right :        injectivity on one side suffices
    isZero_homology_of_mayerVietoris_sup_of_const : and contractibility of the intersection supplies it
  SimplicialMayerVietorisConnected.lean
    epi_homologyMap_mvSupChainSnd_zero :   in degree zero the map onto the union is epi on homology
    homologyMap_const_eq_id_of_sup :       connectedness passes to a union along a vertex
  SubcomplexDistrib.lean
    Subcomplex.sup_inf_right, finsetSup_inf_le :  the distributive law and its finite form
  SimplicialMayerVietorisBase.lean
    base_sup_inf_eq :                a piece meets the partial union exactly where it meets the base
    isZero_homology_base_finsetSup : vanishing, folded over a cover with a base
    exists_homologyMap_const_eq_id_base_finsetSup : connectedness, folded the same way
  ```

  The fold of the previous entry cannot run the Solomon--Tits induction as it stands, because in
  degree one the Mayer--Vietoris term is the degree-zero homology of the intersection, which never
  vanishes for a nonempty intersection.  What the sequence actually needs there is that this homology
  *injects*, and that is what the first three modules supply: the connecting map is zero as soon as
  the map out of the intersection is a monomorphism, a monomorphism follows from the intersection
  being homologically constant at a vertex, and conical contractibility gives that in every degree —
  including degree zero, where the positive-degree conclusion was previously thrown away.

  The last two modules fold a cover of a new shape.  In the Solomon--Tits cover the pieces are stars
  of vertices which meet each other only inside a fixed contractible base, and then the intersection
  of a piece with any partial union is its intersection with the base alone
  (`base_sup_inf_eq`, by the distributive law).  So the induction needs exactly one hypothesis per
  piece, in both the vanishing and the connectedness form, and neither hypothesis grows with the fold.

  What this does not yet reach: the cover of a building over an infinite field has infinitely many
  pieces — one for every hyperplane avoiding a fixed point — while the fold is over a finite family.
  The finite fold proves the vanishing for every finite partial union.  Closing the gap needs the
  Mayer--Vietoris sequence for a base together with an arbitrary family of pieces meeting pairwise
  inside the base, which is short exact degreewise for any index set because the pieces are disjoint
  outside the base.  That sequence, not a colimit argument, is the next module.

- 2026-08-02 — **The infinite cover: Mayer--Vietoris for a base and arbitrarily many pieces.**
  Three modules, wired into the `HTGeometry` umbrella, axioms `[propext, Classical.choice,
  Quot.sound]`; umbrella green at 13047 jobs:

  ```text
  CoproductMayerVietorisFamily.lean
    famBaseIncl, famPieceIncl, famFst, famIncl, famSnd, famTrunc, famRetraction, famSection
    famSplitting, famShortExact, famShortExact' :
      0 → ∐ₐ ∐_{S₀ ∩ S a} R → (∐_{S₀} R) ⊞ ∐ₐ ∐_{S a} R → ∐_W R → 0   split, any index type
  FamilySimplicialSet.lean
    famSSet :          the disjoint union of a family of subcomplexes, as a simplicial set
    famSSetHom, famSSetMap, chainComplexMap_famSSetHom_f, chainComplexMap_famSSetMap_f
    iSup_obj, mem_base_iSup_obj
  SimplicialMayerVietorisFamily.lean
    mvFamChainFst, mvFamChainSnd, mvFamChainShortComplexIso
    mvFamChainShortExact :
      0 → chains(⨿ₐ (A₀ ⊓ A a)) → chains(A₀) ⊞ chains(⨿ₐ A a) → chains(A₀ ⊔ ⨆ₐ A a) → 0
    mono_homologyMap_mvFamChainFst_of_right
    isZero_homology_famSup :  the vanishing statement the infinite cover consumes
  ```

  The previous entry's fold proves the vanishing for every *finite* partial union, and the cover of a
  building over an infinite field has one piece for every hyperplane avoiding a fixed point.  The gap
  is not closed by a colimit argument but by attaching all the pieces at once: the sequence above is
  short exact for **any** index type, because pieces that meet each other only inside the base are
  disjoint outside it, so an element of the covered set lies in the base or in exactly one piece.
  That dichotomy is the section; the retraction keeps what lies in the base; the splitting identity is
  a two-case check on basis elements.

  The chain-level form needs the disjoint union of the pieces, which is not a subcomplex — the pieces
  overlap.  `famSSet` makes it a simplicial set in its own right, degreewise the disjoint union of
  the pieces' simplices, so that its chains in degree `n` are *definitionally* the coproduct over
  that disjoint union.  With that the degreewise identification is the same one the two-piece
  sequence uses, and the short exactness transports through `shortExact_of_degreewise_shortExact`.

  So the Solomon--Tits cover is now formalizable as it actually is: base = the subspaces that do not
  span with a fixed point (contractible, already proved), pieces = the stars of the hyperplanes
  avoiding that point (each a cone), pairwise intersections = subspaces of two hyperplanes, which
  already lie in the base.  What remains is to instantiate the three hypotheses for that cover and to
  identify the intersection term as the building of a hyperplane — one dimension down, which is what
  the induction consumes.

- 2026-08-02 — **The Solomon--Tits cover itself, at the level of a modular lattice.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingSpanningCover.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13050 jobs:

  ```text
  properPart L, notSpanning p, spanning p
  isCoatom_of_spanning :               an element spanning with an atom is a coatom
  le_of_mem_generalStar_spanning :     and everything comparable to it lies below it
  star_inter_star_subset_notSpanning : two distinct pieces meet only inside the base
  notSpanning_inter_star :             notSpanning p ∩ star V = {U | U < V}
  chain_mem_base_or_star :             every chain lies in the base or in a single star
  nerveSubcomplex_sup_iSup_eq_top, nerveSubcomplex_notSpanning_sup_iSup_star :
    the base and the stars cover the order complex
  ```

  All three hypotheses of the many-piece Mayer--Vietoris sequence are now theorems for the cover the
  classical proof uses, and at the generality where they are true: a bounded **modular** lattice and
  an atom `p`, with no vector space in sight.  Modularity enters exactly twice, in the two facts that
  make the cover good.  An element spanning with an atom is a coatom: if `V < W` then
  `W = (V ⊔ p) ⊓ W = V ⊔ (p ⊓ W)`, and `p ⊓ W` is `⊥` — giving `W = V` — or `p`, giving `W = ⊤`.  And
  an element strictly below such a coatom cannot itself span, by the same identity read the other way.

  The intersection term is `{U | U < V}`, the proper part of the interval below a coatom — a building
  one step smaller, which is what an induction on length consumes.  The cover statement itself needs
  no modularity at all: a chain containing a spanning element has all its members comparable to it.

  What remains for the vanishing is the homology of the *disjoint union* of the stars, which is the
  middle term of the sequence.  Each star is a cone, so the disjoint union retracts onto the discrete
  set of cone points; its order complex has dimension zero, so the homology vanishes above degree
  zero — by `hasDimensionLT_nerve_of_chain_bound` and `isZero_homology_of_hasDimensionLT`, both
  already in the corpus.  Making that argument available needs one identification: the disjoint union
  of the nerves of subposets is the nerve of their disjoint union poset.

- 2026-08-02 — **The Solomon--Tits induction step is a theorem.**  Four further modules, wired into
  the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at
  13060 jobs:

  ```text
  FamilyPosetNerve.lean
    famPoset S, famPoset_le_iff, famPoset_index_eq
    famPosetNerveIso :  ⨿ₐ (full subcomplex on S a)  ≅  nerve (disjoint union poset)
    famPosetHomologyIso
  LocallyConicalPoset.lean
    discretePoset, hasDimensionLT_nerve_discretePoset, isZero_homology_nerve_discretePoset
    isZero_homology_of_locally_conical :
      a fold dominating the identity and a map constant on comparable pairs kills all
      positive-degree homology
  FamilyStarVanishing.lean
    famStarCone, famStarCentre
    isZero_homology_famSSet_generalStar :  a disjoint union of stars has no homology above degree 0
  BuildingCoverVanishing.lean
    spanningIndex, coverBase, coverPiece, coverBase_sup_iSup_coverPiece
    coverPiece_inter_le_coverBase, coverBase_inter_coverPiece
    notSpanningJoinAtom, isZero_homology_coverBase, isZero_homology_famSSet_coverPiece
    isZero_homology_nerve_properPart :  THE INDUCTION STEP
  ```

  `isZero_homology_nerve_properPart` says: for a bounded modular lattice `L` and an atom `p < ⊤`, if
  the map out of the disjoint union of the order complexes of the intervals below the coatoms
  complementary to `p` is injective on homology in degree `i - 1`, then `H_i(Δ(L)) = 0`.  Everything
  else in the step is discharged unconditionally — the cover, the contractibility of the base, the
  vanishing for the disjoint union of the stars, and the disjointness of the pieces outside the base.

  Two general tools came out of it, both worth more than this application.
  `isZero_homology_of_locally_conical` weakens conical contractibility to its componentwise form: a
  monotone fold dominating the identity and a map that is *constant on comparable pairs* — rather
  than globally constant — still kills all positive-degree homology, because the second map factors
  through the same poset with the discrete order, whose order complex is zero-dimensional.  That is
  the exact statement that a disjoint union of cones is homologically trivial above degree zero, and
  it needs no exactness axiom on the coefficient category: no coproduct of homologies is ever formed.
  And `famPosetNerveIso` identifies the disjoint union of full subcomplexes with the order complex of
  the disjoint union poset, which is what lets a family of cones be treated as one poset.

  What remains for `(5)` in the middle range is the induction bookkeeping: the intersection term is a
  disjoint union of buildings of the intervals below the coatoms, so the induction hypothesis has to
  be stated for arbitrary *families* of such intervals, graded by length.  With the family form of
  the statement, the degree-`i - 1` input is supplied by the induction for `i ≥ 2`, and by
  connectedness of the smaller buildings for `i = 1` (`homologyMap_const_eq_id_of_sup`,
  `mono_homologyMap_of_homologyMap_const_id`).

- 2026-08-02 — **The cover, relative to an interval.**
  `formal/GaloisForLFunctions/HTGeometry/IntervalSpanningCover.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13063 jobs:

  ```text
  properBelow V, notSpanningBelow V p, spanningBelow V p, properBelow_top
  eq_of_lt_of_spanningBelow :          spanning an interval with an atom means being its coatom
  le_of_mem_generalStar_spanningBelow
  starBelow_inter_starBelow :          two pieces meet only inside the base
  notSpanningBelow_inter_star :        notSpanningBelow V p ∩ star U = properBelow U
  chain_below_mem_base_or_star :       every chain of the interval lies in the base or one piece
  ```

  The same cover, stated relative to an element `V` instead of the top.  This is the form the
  induction needs, and the reason is structural: the intersection term of the cover of `properBelow V`
  is `properBelow U` for a coatom `U` of the interval, so the smaller buildings the induction produces
  are **intervals of the same lattice**, not proper parts of new lattices.  The induction therefore
  never leaves `L`, and the family it ranges over is a family of elements of `L`.

  The remaining gap is now purely bookkeeping, and its shape is fixed: run the cover on the disjoint
  union poset `famPoset (fun a => properBelow (W a))` — which is an order complex by
  `famPosetNerveIso` — with a chosen atom per component; the base and the pieces are locally conical,
  so both vanish above degree zero by `isZero_homology_of_locally_conical`; and the intersection term
  is again a disjoint union of intervals, one coatom step down, which is the induction hypothesis.
  Grading by the length of the intervals gives the range `1 ≤ i ≤ N - 3`.

- 2026-08-02 — **The induction step for a family of intervals, and the degree-zero inputs.**
  Six modules (four new, two extended), wired into the `HTGeometry` umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`; umbrella green at 13090 jobs:

  ```text
  FamilyIntervalCover.lean
    famBuilding W, famCoverIndex, famCoverCentre, famCoverBase
    famChain_mem_base_or_star, famCoverPiece_inter_subset_base, famCoverBase_inter_piece
  FamilyCoverBaseVanishing.lean
    famBaseJoin, famBaseCentre, isZero_homology_famCoverBase
  FamilyCoverIntersection.lean
    famCoverInterOrderIso, famCoverInterNerveIso :
      the disjoint union of the intersections IS the disjoint union of the interval
      buildings below the coatoms
  FamilyBuildingStep.lean
    isZero_homology_famBuilding_of_isZero :  THE STEP, hypothesis and conclusion the same statement
  FamilyPosetNerve.lean (extended)
    famPosetProj, famPosetMap, famPosetNerveIso_inv_comp_famSSetHom,
    famPosetNerveIso_inv_comp_famSSetMap
  LocallyConicalPoset.lean (extended)
    homologyMap_nerve_eq_id_of_dominated :  a dominated map is the identity on homology, every degree
  SimplicialMayerVietorisFamily.lean (extended)
    epi_homologyMap_mvFamChainSnd_zero
  FamilyCoverConnected.lean
    famAtomCentre, piecesToCentre, piecesToChosen, piecesToJoin and their four comparisons
    homologyMap_base_atom, homologyMap_pieces_atom
  ```

  `isZero_homology_famBuilding_of_isZero` is the induction step in closed form: for a family of
  intervals of a bounded modular lattice, each with a chosen atom, if the disjoint union of the
  interval buildings **below the coatoms** has no homology in degree `i - 1`, then the disjoint union
  one step up has none in degree `i`.  Hypothesis and conclusion are the same statement about a
  family, so the step composes with itself.

  Why the statement had to be about families: the Mayer--Vietoris term of the cover of a single
  building is a disjoint union of smaller buildings, and its homology cannot be split into the
  components' without assuming coproducts are exact.  Keeping the whole disjoint union as one poset
  avoids that entirely — `famCoverInterOrderIso` says the term is again an object of the same kind.

  The degree-one case of the step needs, instead of vanishing, that degree-zero homology injects, and
  that is componentwise connectedness.  Both halves of its proof are now theorems.
  `homologyMap_base_atom`: on the base the atom map is the identity on homology, because the base
  folds onto the atoms.  `homologyMap_pieces_atom`: on the pieces it is too, by a chain of four
  comparisons of monotone maps — an element of a star lies below the star's centre, the centre lies
  above the chosen element of the intersection, that element joins with the atom **inside** the
  interval because it does not span, and the atom lies below that join.  What remains is to feed the
  two into the degree-zero Mayer--Vietoris epimorphism (`epi_homologyMap_mvFamChainSnd_zero`, also
  proved here) and then run the induction on rank.

- 2026-08-02 — **Componentwise connectedness is a theorem.**
  `formal/GaloisForLFunctions/HTGeometry/FamilyCoverConnected.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`; umbrella green at 13097 jobs:

  ```text
  famAtomCentre, famAtomMap :   send every element to the atom of its own component
  homologyMap_famAtomMap_eq_id :
    that map is the identity on degree-zero homology of the disjoint union of interval buildings
  ```

  This is the degree-one input the induction needs, and it is now unconditional.  The proof is the
  degree-zero Mayer--Vietoris epimorphism together with the two component identities proved in the
  previous entry: on the base the atom map is the identity on homology because the base folds onto
  the atoms, and on the pieces it is by the four-step comparison chain.  The only hypothesis is that
  each coatom has something strictly below it — i.e. that the intersections of the cover are
  nonempty — which is what supplies the middle element of that chain.

  A note for anyone continuing this: `nerve P` and `nerveFunctor.obj (Cat.of P)` are definitionally
  equal but not syntactically, and `rw`/`simp` work below the transparency that identifies them.  A
  composite that mixes the two elaborates fine and then refuses every rewrite.  The fix used here is
  to name the map with its intended type (`famAtomMap`), which pins the written form of the objects
  and makes the whole Mayer--Vietoris computation go through.

  Remaining for `(5)` in the middle range, both mechanical: transport the connectedness statement
  through `famPosetNerveIso` to get the degree-zero injectivity in the form
  `mono_homologyMap_mvFamChainFst_of_right` consumes; then run the induction on rank, whose step is
  `isZero_homology_famBuilding_of_isZero` for `i ≥ 2` and the injectivity form for `i = 1`.

- 2026-08-02 — **The injectivity transport.**
  `formal/GaloisForLFunctions/HTGeometry/FamilySSetMapMono.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13100 jobs:

  ```text
  famPosetNerveMap :                       the map of order complexes induced by a family inclusion
  mono_homologyMap_nerve_of_comp_id :      a retraction up to homology gives injectivity
  homologyMap_nerve_eq_id_of_comp :        a map absorbed by a homologically trivial one is trivial
  mono_homologyMap_famSSetMap_congr :      injectivity depends only on the family, not its description
  mono_homologyMap_famSSetMap_of_nerve :
    injectivity for a map of disjoint unions reduces to the order-complex picture
  ```

  These four are what carry the connectedness statement, which lives on posets, to the injectivity
  hypothesis of the Mayer--Vietoris step, which lives on disjoint unions of subcomplexes.  The last
  one is the transport along `famPosetNerveIso`; the third is the bookkeeping that lets it apply at
  all, since the subcomplexes in the sequence are meets rather than full subcomplexes on the nose,
  and the two agree as an equality of families (`subst`) rather than definitionally.

  A second toolchain note, recorded because it cost real time: `nerveFunctor` is not reducible, so
  `nerveFunctor.map f ≫ nerveFunctor.map g = nerveFunctor.map (f ≫ g)` is **not** definitional and a
  proof that assumes it is loops in `isDefEq` until the heartbeat limit rather than failing.  Every
  composition of induced maps has to go through `nerveFunctor.map_comp` explicitly.

- 2026-08-02 — **`(5)` IS PROVED IN THE MIDDLE RANGE.  The Solomon--Tits vanishing theorem is
  formalized, unconditionally.**  Three modules, wired into the `HTGeometry` umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`; umbrella green at 13107 jobs:

  ```text
  FamilyStepDegreeOne.lean
    famPieceCollapse, mono_homologyMap_mvFamChainFst_zero,
    homologyMap_famPieceCollapse_eq_id, isZero_homology_famBuilding_one
  FamilyBuildingVanishing.lean
    covBy_famCoverTop, rank_atom_eq_one, exists_properBelow, famBuildingPUnitOrderIso
    isZero_homology_famBuilding_of_rank :   the induction, for a family of intervals at once
    isZero_homology_properPart_of_rank :    for one bounded modular lattice
  BuildingVanishingSubmodule.lean
    finrank_of_covBy
    isZero_homology_properPart_submodule :
      1 ≤ i → i + 3 ≤ dim V → H_i(Δ(proper nonzero subspaces of V); R) = 0
  ```

  The last statement is the card's `(5)` in the range that was open — for **any** coefficient object
  of any abelian category with coproducts, any division ring, any finite dimension, with no
  finiteness assumption on the field and no exactness axiom on the coefficients.  Together with the
  two ends already proved (`isZero_horizonComplexHomology` above the dimension,
  `horizonComplexHomologyZeroIso` in degree zero) this closes `(5)` for the building, hence — through
  the simplicial isomorphism `(3)` — for `Δ_HT(V)`.

  The induction is on rank, over families, with the degree dropping by one at each step.  Its two
  ends are the two forms of the Mayer--Vietoris conclusion: for `i ≥ 2` the vanishing form, fed by
  the induction hypothesis; for `i = 1` the injectivity form, fed by componentwise connectedness.  A
  component whose cover has no pieces — nothing spans with the chosen atom, which is what happens in
  a chain — is handled separately and needs no rank at all: its cover is its base, which is locally
  conical.

  The rank function is asked only to vanish at the bottom and to increase by one across a covering.
  `Module.finrank` is such a function on subspaces, which is `finrank_of_covBy`: a covering pair
  differs by one because adjoining one vector to the smaller already lands strictly between unless it
  reaches the larger.

  What remains on this card is `(6)`, the identification of the top homology with the Steinberg
  module, and the statement that the homotopy type is a wedge — neither of which is a vanishing
  statement.  `(4)`'s homotopy-theoretic form is likewise not claimed here; what is claimed and
  proved is its homological content, which is what `(5)` asserts.

- 2026-08-02 — **The Steinberg module and its observer action.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingAutomorphismAction.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13110
  jobs:

  ```text
  properPartCongr, properPartCongr_refl, properPartCongr_trans :
    an order isomorphism restricts to the proper parts, functorially
  orderIsoCatIso_refl, orderIsoCatIso_trans, properPartNerveIso
  buildingHomologyAut :
    (L ≃o L) →* Aut (H_i(Δ(L); R))   —  the lattice's automorphisms act on every homology object
  submoduleAutHom :  (V ≃ₗ[K] V) →* (Submodule K V ≃o Submodule K V)
  steinbergModule K V R :  H_{dim V - 2}(Δ(proper nonzero subspaces); R)
  steinbergAction :  (V ≃ₗ[K] V) →* Aut (steinbergModule K V R)
  ```

  This is the formalizable content of `(6)`.  The card says it itself: the Steinberg module *is*
  defined as the top homology of the building, so that half is a definition — what is a theorem is
  that the observer group acts on it, and that is now proved, as a group homomorphism into the
  automorphisms of the homology object, for any coefficients.

  Note on scope, stated plainly.  `(6)` as written also asserts that this module is *the* integral
  Steinberg module in the classical sense — that it is free of the expected rank, with the apartment
  classes as a basis.  That is a further theorem (Solomon's basis theorem), not a definition, and it
  is not claimed here.  Likewise `(4)`'s homotopy-equivalence statement is not claimed: what is
  proved is its homological shadow, `(5)`, together with the group action.

  A toolchain note: `Group (α ≃o α)` lives in `Mathlib.Algebra.Order.Group.End`, which is not in the
  import cone of the simplicial machinery.  A missing instance here presents as a bare
  "failed to synthesize" on the *statement* of a `MonoidHom`, with nothing wrong in the proof.

- 2026-08-02 — **The top homology embeds one rank down.**
  `formal/GaloisForLFunctions/HTGeometry/FamilyTopHomologyEmbedding.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13113
  jobs:

  ```text
  famSupHomologyIso
  famTopEmbedding :   H_i(⨿ buildings)  ⟶  H_{i-1}(⨿ buildings below the coatoms)
  mono_famTopEmbedding :  it is a monomorphism, for every i ≥ 1
  ```

  This is what the Mayer--Vietoris sequence still says in the degree where the vanishing theorem
  stops.  Above degree zero the base and the disjoint union of the pieces have no homology at all,
  so the connecting map has zero coming into it and is therefore injective.  Below the top degree
  the statement is empty — both sides vanish by the theorem already proved — so its content is
  exactly at the top: **the top homology of a building of rank `r` embeds into the top homology of
  the disjoint union of the buildings of rank `r - 1` indexed by the coatoms.**

  That is the inductive skeleton of Solomon's rank formula, which is the remaining classical content
  of `(6)`: iterating the embedding is how the rank of the Steinberg module gets multiplied by the
  number of coatoms at each step.  What the embedding does not give on its own is surjectivity onto
  the relevant subobject — that is where the apartment classes and the opposition retraction enter,
  and neither is built here.

- 2026-08-02 — **The descent is an isomorphism, and the vanishing holds in the horizon complex's own
  order.**  Two additions, wired into the `HTGeometry` umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`; umbrella green at 13115 jobs:

  ```text
  FamilyTopHomologyEmbedding.lean (extended)
    isIso_famTopEmbedding :  for i, j ≥ 1 with i = j + 1, the connecting map is an ISOMORPHISM
  BuildingVanishingDual.lean
    properPartDualOrderIso :  the proper part of the dual lattice is the dual of the proper part
    isZero_homology_properPart_submodule_dual
    isZero_homology_properPart_submodule_orderDual :
      1 ≤ i → i + 3 ≤ dim V → H_i(Δ(proper nonzero subspaces, order reversed); R) = 0
  ```

  The first upgrades the previous entry: both ends of the Mayer--Vietoris sequence around the
  connecting map vanish above degree zero — the base and the disjoint union of the stars have no
  homology there at all — so the map is not just injective but bijective.  The homology of a family
  of buildings in degree `i` **is** the homology of the family below the coatoms in degree `i - 1`,
  whenever both degrees are positive.  Iterating it carries the top homology down to degree one, and
  that is exactly how the rank of the Steinberg module is built up in Solomon's formula.

  The second is a scope correction that matters for this card.  The horizon assignment `S ↦ I_S` is
  order-**reversing**, so `Δ_HT(V)` is the order complex of the proper nonzero subspaces with the
  order reversed, and the vanishing theorem has to be read there.  It transfers at no cost: the dual
  of a bounded modular lattice is one, the proper part of the dual is the dual of the proper part,
  the dual rank is the codimension — whose covering increments are the same — and the atoms of the
  dual are the hyperplanes, which every proper subspace lies in.  So `(5)` now holds on the object
  the card actually names, not only on its opposite.

- 2026-08-02 — **`(5)` complete: the homology is concentrated in one degree.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingHomologyConcentration.lean`, wired into the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13116
  jobs:

  ```text
  properPartNeOrderIso  (in BuildingVanishingDual.lean)
  isZero_homology_building_of_ne :
    1 ≤ i → i ≠ N - 2 → H_i(Δ_Tits; R) = 0
  ```

  stated on the very poset the horizon work uses — `({S : Submodule K V // S ≠ ⊥ ∧ S ≠ ⊤})ᵒᵈ` — and
  for arbitrary coefficients.  Two vanishing statements meet in it: below the top degree the
  Solomon--Tits induction proved here, above it the dimension bound `buildingHasDimensionLT` that
  was already in the corpus, because a strict chain of proper nonzero subspaces has at most `N - 1`
  members.  Degree zero is the connectedness already recorded (`horizonComplexHomologyZeroIso`).

  So `(5)` is now a theorem in full: the homology of `Δ_HT(V)` vanishes in every degree except `0`
  and `N - 2`.  This is the homological content of `(4)` — everything in the wedge statement that
  does not mention homotopy types.  What `(4)` asserts beyond it (an actual homotopy equivalence)
  and what `(6)` asserts beyond the definition and the group action (freeness with an apartment
  basis) remain outside what is proved here.

- 2026-08-02 — **The apartment of an observer frame, and the card's stale Lean-boundary text.**
  `formal/GaloisForLFunctions/HTGeometry/ApartmentOrderIso.lean`, wired into the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`; umbrella green at 13119 jobs:

  ```text
  coordSpan, coordSpan_mono, coordSpan_le_iff :
    a frame's coordinate subspaces embed the lattice of subsets, order-reflectingly
  apartmentEmbedding, coordSpan_empty, coordSpan_univ, coordSpan_injective,
  coordSpan_ne_bot, coordSpan_ne_top, apartmentVertices, apartmentVertices_le_iff :
    the vertices of the apartment are the proper part of that Boolean lattice
  ncard_of_covBy :  subsets are graded by cardinality
  isZero_homology_properPart_set :
    1 ≤ i → i + 3 ≤ |ι| → H_i(order complex of the proper subsets; R) = 0
  ```

  This formalizes the card's "Apartments and observer frames" paragraph.  A basis is a projective
  observer frame; the map `s ↦ span (b '' s)` is monotone and reflects inclusion, because a frame
  vector outside a set is not in that set's span — so the coordinate subspaces are a copy of the
  Boolean lattice inside the subspace lattice, and the apartment's vertices are its proper part.

  The last item is the card's "the order complex is the Coxeter sphere `S^(N-2)`", in the form this
  corpus can prove: the Boolean lattice is modular, atomic and graded by cardinality, so the
  Solomon--Tits vanishing proved here applies to it verbatim and the apartment has no homology below
  its top degree.  That the top homology is a single copy of the coefficients — the actual sphere
  statement — is not proved; it is the one place where a genuine computation, rather than a
  vanishing, is needed.

  **Card correction.**  The `Lean boundary` section still said that `(3)--(6)` "are not encoded",
  which the Log has contradicted since this morning.  It is rewritten to state exactly what is
  formalized (`(3)`, `(5)` in full, `(6)`'s definition and observer action, plus the descent
  isomorphism) and what is not (`(4)` as homotopy, `(6)`'s freeness), and the `2 -> 3` gate now says
  the same.  The gate stays unticked: two of the card's six numbered claims are still unformalized.

- 2026-08-02 — **`(6)`'s freeness is proved: the Steinberg module is a coproduct of copies of the
  coefficients.**  Six new modules, all axioms `[propext, Classical.choice, Quot.sound]`:

  `FreeCoproductKernel.lean` — `IsFreeOver R Z` ("`Z` is a coproduct of copies of `R`") and the
  algebra behind it: for any function `u : A → B` of index types, `sigmaKerIncl` is a kernel of the
  induced map `∐_A R → ∐_B R`, so `isFreeOver_of_isLimit_kernelFork` says that kernel is free.  The
  splitting is written down explicitly — choose one preimage in every nonempty fibre — so no
  exactness of coproducts (AB4) is used.

  `SimplicialPiZeroFree.lean` — `homologyMap_zero_comp_homology₀Iso`: degree-zero homology carries a
  map of simplicial sets to the map of coproducts induced by the map of components.  Hence
  `isFreeOver_homology_zero` (degree-zero homology is always free) and
  `isFreeOver_of_isLimit_kernelFork_homologyMap_zero` (a kernel of a degree-zero induced map is
  free).  `isKernelOfCompMono`: a kernel of `g ≫ m` with `m` mono is a kernel of `g`.

  `FamilyDegreeOneFree.lean` — the Mayer--Vietoris consequence.  For a base and a family of pieces
  meeting only inside the base, with no homology in degree one on the base or on the disjoint union
  of the pieces, `isFreeOver_homology_famSup_one` gives that the first homology of the union is free.
  The mechanism: the connecting map is a kernel of the degree-zero map into the biproduct, and that
  map factors as (map into the pieces) ≫ (a split monomorphism), because the component of an
  intersection inside the base is determined by its component inside the pieces.

  `FamilyCoverBaseComponents.lean` — that determination, for the building cover: `pi0_base_eq_atom`.
  Inside the base every element is joined to the atom of its own component by two comparabilities
  (it lies under its join with the atom, and so does the atom), so the base component is a function
  of the piece.

  `FamilyBuildingFree.lean` — `isFreeOver_homology_famBuilding`: for a bounded modular lattice with
  an atom below every nonzero element, the homology of the disjoint union of the interval buildings
  of any family is free **in every positive degree**, with no rank hypothesis at all.  The descent is
  `isIso_famTopEmbedding` down to degree one, where the kernel computation above applies.
  `isFreeOver_homology_properPart` is the one-component case.

  `BuildingFreeSubmodule.lean` — `isFreeOver_homology_properPart_submodule`,
  `isFreeOver_homology_building` (the horizon presentation, order reversed), and
  `Steinberg.isFreeOver_steinbergModule`: **the Steinberg module of a vector space is free.**

  So `(6)` now has its module structure and not only its definition: `H_(N-2)` is the Steinberg
  module by definition, it carries the observer action, and it is a free object.  What is still not
  proved is that a basis can be taken to consist of apartment classes — Solomon's basis theorem — and
  `(4)` as a homotopy equivalence.

  **Card correction.**  The `Lean boundary` section said freeness "needs a shelling or the opposition
  retraction; neither follows from the Mayer--Vietoris machinery built here".  That is now false as
  stated: freeness does follow from that machinery, once degree-zero homology is read through `π₀`.
  Only the apartment basis needs the extra geometry.  The section and the `2 -> 3` gate are corrected.

- 2026-08-02 — **`(5)` is now complete, degree zero included.**
  `formal/GaloisForLFunctions/HTGeometry/BuildingConnected.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `(5)` is a statement about *reduced* homology, so it asserts something in degree zero too: the
  building is connected.  That half was missing — `isZero_homology_building_of_ne` only speaks for
  `1 ≤ i`.  It is now proved:

  `reflTransGen_comparable_properPart_submodule` — any two nonzero proper subspaces of a space of
  dimension at least three are joined by a chain of inclusions: each contains a line, and two lines
  span a subspace of dimension at most two, which is still proper;
  `isConnected_nerve_properPart_submodule` and its order-dual form — hence the order complex is
  connected, in both the subspace order and the reversed order the horizon complex uses;
  `homologyZeroIsoProperPartSubmodule`, `homologyZeroIsoBuilding` — hence degree-zero homology is a
  single copy of the coefficients, which is exactly `reduced H_0 = 0`.

  With the vanishing above degree zero, `(5)` now holds in the sense the card states it: for
  `N ≥ 3` the reduced homology of `Δ_HT(V)` vanishes in every degree except `N - 2`.

- 2026-08-02 — **The apartment is a sphere: its top homology is one copy of the coefficients.**
  Four new modules, all axioms `[propext, Classical.choice, Quot.sound]`:

  `PiZeroNerve.lean` — the components of an order complex.  An edge of a subcomplex of a nerve is a
  comparability (`nerveSub_edge_le`), so a subcomplex spanned by an antichain has one component per
  vertex (`nerveSubAntichainPi0`), a subcomplex whose subset has a cone point is connected
  (`isPreconnected_nerveSubcomplex_of_cone`), and the components of a disjoint union are the
  disjoint union of the components (`famSSetPi0Equiv`).

  `BooleanIntervalCover.lean` — **thinness**: in the lattice of subsets, the elements of `[∅, S]`
  spanning it with `{a}` are exactly one, `S \ {a}` (`uniqueBoolCoverIndex`).  So the Solomon--Tits
  cover of a Boolean interval has a single piece and the descent removes one element at a time.
  With it, `famBuildingUniqueOrderIso`, which names the single interval a one-element family
  consists of.

  `FreeCoproductKernel.lean` (extended) — `nonempty_unique_sigmaKerIndex`: a two-element source over
  a one-element target leaves a one-element kernel index; `sigmaUniqueIso`, `sigmaIsoOfEquiv`; and
  `kernelIsoSigmaKerIndex`, which exposes the kernel's index set instead of only its freeness.  The
  same exposure was added to `SimplicialPiZeroFree.lean` and `FamilyDegreeOneFree.lean`
  (`homologyOneIsoSigmaKerIndex`).

  `ApartmentTopHomology.lean` — the computation.  `nonempty_homology_iso_bool_three`: for a
  three-element interval the intersection of the base with the single piece is the two-point
  antichain below the coatom and the piece is connected, so the Mayer--Vietoris kernel is one copy of
  the coefficients.  `nonempty_homology_iso_boolInterval`: the descent carries that up one element at
  a time.  **`nonempty_homology_iso_apartment`**: for `3 ≤ N`,

  ```text
  H_(N-2)(Delta(properPart(Set ι))) ≅ R,     Nat.card ι = N.
  ```

  That is the card's "its order complex is the Coxeter sphere `S^(N-2)`", in its homological form,
  and it is the first *computation* in this line of work rather than a vanishing or a freeness
  statement.

  **Card correction.**  This morning's entry said the sphere statement "is not proved; it is the one
  place where a genuine computation, rather than a vanishing, is needed".  It is proved now.  What
  the apartment paragraph still does not have is the map from that class into the Steinberg module
  and the statement that such classes generate — Solomon's basis theorem.

- 2026-08-02 — **The apartment class, its equivariance, and the nonvanishing of the Steinberg
  module.**  Two new modules, axioms `[propext, Classical.choice, Quot.sound]`:

  `ApartmentClass.lean` — `orderHomNerveMap`: a monotone map of posets induces a map of order
  complexes.  With the frame's order embedding `apartmentVertices` and the sphere isomorphism, this
  gives **`apartmentClass`**: for a frame `b` of an `N`-dimensional space with `N ≥ 3`, a map

  ```text
  R  ⟶  H_(N-2)(building)  =  St_N,
  ```

  the image of the fundamental class of the Coxeter sphere of the frame.  And
  `apartmentClass_steinbergAction`: `apartmentClass b ≫ steinbergAction g = apartmentClass (b.map g)`
  — the observer group permutes the apartment classes, which is the card's "topological cycles are
  changes of complete projective observer frame".

  `BuildingNonvanishing.lean` — **`not_isZero_steinbergModule`**: for `3 ≤ N` and any nonzero
  coefficients the Steinberg module is not zero; more precisely
  `exists_nonempty_index_steinbergModule` gives `St ≅ ∐_B R` with `B` *nonempty*.  Freeness alone did
  not say this: the empty coproduct is free.  Two facts about subspaces that a general modular
  lattice does not have carry it, and both are proved here:

  `exists_spanning_of_finrank` — a line inside a subspace of dimension `≥ 3` has a complement there
  that is neither zero nor everything, so the Solomon--Tits cover always has a piece and the descent
  never stalls;
  `exists_two_atoms_of_finrank_two` — a plane contains two distinct lines, so at the bottom of the
  descent the intersection of the base with a piece has two components, while the piece itself is
  connected: the map on components is not injective, and `nonempty_sigmaKerIndex_of_ne` turns that
  into a nonempty index for the Mayer--Vietoris kernel.

  So the homology of the building of an `N`-dimensional space, `N ≥ 3`, is: zero in every positive
  degree except `N - 2`, a single copy of the coefficients in degree `0`, and in degree `N - 2` a
  free object on a nonempty index set carrying the observer action, with apartment classes attached
  to every frame.  What remains of `(6)` is Solomon's *basis* theorem: that the apartment classes can
  be chosen as a basis.

- 2026-08-02 — **The apartment class is a monomorphism, hence a nonzero class.**  Two new modules,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `TopDegreeMono.lean` — the general mechanism.  A chain complex that vanishes one degree up has no
  boundaries there, so `topHomologyι` embeds its homology in its chains, naturally
  (`topHomologyι_naturality`); hence `mono_homologyMap_of_mono_f`.  For a simplicial set of dimension
  at most `n` the normalized chains vanish above `n` and are the coproduct over the nondegenerate
  `n`-simplices, so a map injective on those — and preserving nondegeneracy — is injective on
  normalized chains (`mono_normalizedChainComplexMap_f`, by an explicit retraction), and therefore
  **`mono_homologyMap_of_injective_nonDegenerate`**: injective on homology in the top degree.

  `ApartmentClassMono.lean` — the application.  `chain_bound_of_hasDimensionLT` inverts the corpus's
  chain-bound criterion, so `hasDimensionLT_nerve_of_reflecting` transports a dimension bound along
  an order-reflecting map: the apartment of a frame has the dimension of the building
  (`apartmentHasDimensionLT`), without a separate cardinality argument.  The frame's embedding is
  injective on chains and keeps strict chains strict, so

  `mono_apartmentClass` — the apartment class `R ⟶ St_N` is a monomorphism, and
  `apartmentClass_ne_zero` — it is nonzero whenever the coefficients are.

  So the card's "its fundamental class is an apartment generator of the Steinberg module" now has its
  first half: the class exists, is natural for the observer action, and is a nonzero — indeed
  injective — class.  What is still missing is that such classes *generate*, which is Solomon's basis
  theorem.

- 2026-08-02 — **The Steinberg module as top cycles inside the free object on the chambers, and the
  wedge statement packaged.**  `SteinbergCycles.lean` (plus `topHomologyIsoCycles` in
  `TopDegreeMono.lean`), axioms `[propext, Classical.choice, Quot.sound]`:

  `steinbergIsoCycles` — the building has dimension `N - 2`, so a top homology class is exactly a
  normalized cycle: `St_N` **is** the module of top cycles of the order complex.
  `steinbergToChambers`, `mono_steinbergToChambers` — and it embeds in the coproduct of copies of the
  coefficients over the complete flags (`buildingChamber`), which is the classical picture of the
  Steinberg module as a submodule of the free module on chambers.
  `apartmentChamberCycle`, `mono_apartmentChamberCycle` — the apartment class of a frame read in
  those flag coordinates, still a monomorphism.

  `homology_building_wedge` — one statement collecting the homological content of `(4)`: degree zero
  is a single copy of the coefficients, every positive degree except `N - 2` vanishes, and `N - 2` is
  a coproduct of copies of the coefficients over a nonempty index set.

  `apartment_ncard_eq_one_or_two`, `apartment_ncard_ne_of_lt` — the card's hexagon: for a
  three-vector frame every apartment vertex is a one- or two-element coordinate set, and a comparable
  pair always has one of each.  That is the alternation "single-observer horizons <-> pairwise
  common-horizon fields", and the loop itself is the `H_1 ≅ R` already proved.

  **Duplication found.**  `CuspedHorizonHomotopy.lean` already contained `buildingZigzag`,
  `zigzag_orderDual` and `buildingIsConnected` — the connectivity of the building — when
  `BuildingConnected.lean` was written this morning, so that module re-proves it in the
  non-dual presentation.  Both are green and both are used; the overlap is recorded here rather than
  removed, because the two presentations are consumed by different downstream files.  The lesson is
  the standing one: grep the object's name across the tree before proving a connectivity or zigzag
  lemma.

- 2026-08-02 — **The combinatorial skeleton of the Coxeter sphere: top chains are orderings of the
  frame.**  `ApartmentChains.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  `strictMono_add_le` and its two corollaries — a strictly monotone family of naturals on `Fin (m+1)`
  grows by at least one per step, in both directions from any index.  With them,
  `apartment_chain_ncard`: **along a top chain of a Boolean apartment the `i`-th vertex has exactly
  `i + 1` frame vectors** — the sizes are squeezed between `1` and `N - 1` with no room to spare.

  `initialSegSet`, `chainOfOrdering`, `chainOfOrdering_strictMono`,
  `chainOfOrdering_nonDegenerate` — every ordering of the frame gives a top simplex of the apartment,
  the chain of its initial segments; and `chainOfOrdering_injective` — distinct orderings give
  distinct chains, because an ordering is read off its chain one vector at a time
  (`initialSegSet_succ`, `notMem_initialSegSet_succ`).

  This is infrastructure, not a card claim: it is the indexing an *explicit* fundamental cycle of the
  Coxeter sphere needs, and an explicit cycle is what a proof of Solomon's basis theorem would have to
  push through the Mayer--Vietoris connecting map (`ShortComplex.ShortExact.δ_eq'` is the categorical
  form of the lift-and-chase that such a computation uses).  The remaining steps are surjectivity of
  `chainOfOrdering` onto top chains, the signed sum over orderings, and its cycle property.

- 2026-08-02 — **The fundamental cycle of the Coxeter sphere, explicitly.**  `ApartmentChains.lean`
  extended, axioms `[propext, Classical.choice, Quot.sound]`:

  `image_swap_Iic`, `initialSegSet_swap`, `chainOfOrdering_swap_eq`, `chainOfOrdering_swap_ne` — an
  initial segment is unchanged by a transposition of two vectors both inside or both outside it, so
  swapping two *adjacent* vectors of an ordering changes its chain at exactly one index.  That is the
  thinness of the Coxeter complex, in the only form the boundary computation needs.

  `apartmentChainSimplex`, `delta_apartmentChainSimplex_swap` — the top simplex of an ordering and
  the fact that an adjacent transposition leaves the corresponding face untouched.

  `apartmentFundamentalChain` — the signed sum over the orderings of the frame,

  ```text
  zeta = sum over sigma in S_N of sign(sigma) * (chain of sigma),
  ```

  and **`apartmentFundamentalChain_comp_d`: its boundary is zero.**  The proof is the involution
  `sigma ↦ sigma ∘ (adjacent transposition)` on ordering-face pairs: the two terms carry the same
  face and opposite signs, so `Finset.sum_involution` cancels them.  `apartmentFundamentalCycle`
  packages it as a map into the cycles of the normalized chains.

  This is the first *explicit* class in this line of work: everything before it went through
  `Classical.choice` on an existence statement.  What remains for Solomon's basis theorem is to show
  this cycle generates the top homology of the apartment — the missing step is a coefficient
  functional, available because an apartment has finitely many chambers, so its top chain object is a
  biproduct and has projections.

- 2026-08-02 — **The fundamental class of the Coxeter sphere is an explicit split monomorphism.**
  `ApartmentChains.lean` extended, axioms `[propext, Classical.choice, Quot.sound]`:

  `chamberCoefficient`, `ι_chamberCoefficient` — the coefficient of a normalized chain at one
  chamber, as a map out of the coproduct over nondegenerate simplices; no finiteness is needed,
  because a map *out* of a coproduct is given chamber by chamber.
  `apartmentChamber`, `apartmentChamber_injective` — distinct orderings give distinct chambers.
  **`apartmentFundamentalChain_coefficient`** — the fundamental chain has coefficient `sign(sigma)`
  at the chamber of `sigma`, hence `isSplitMono_apartmentFundamentalChain`: the coefficient at any one
  chamber retracts it.

  `apartmentHasDimensionLT_of_card` — the apartment of an `N`-vector frame has dimension below
  `N - 1`, proved intrinsically from the vertex sizes rather than through a basis of a vector space.
  With it, **`apartmentFundamentalClass`** — the explicit class in the top homology of the apartment
  — and **`isSplitMono_apartmentFundamentalClass`**: it is a split monomorphism.

  So the Coxeter sphere now has a *constructed* fundamental class, not merely an abstract
  isomorphism to the coefficients: `R` is a direct summand of the apartment's top homology, cut out
  by the signed sum over orderings.  Proving that it is the *whole* of that homology needs the
  converse direction — that a top cycle is determined by one coefficient — which is thinness in the
  "exactly two chambers per face" form together with the connectivity of the chamber graph
  (adjacent transpositions generate the symmetric group).  That is the next brick, and after it
  Solomon's basis theorem needs the same class transported into the building.

- 2026-08-02 — **Chambers of an apartment are exactly the orderings of the frame, and a chain is
  determined by its coefficients.**  `ApartmentChains.lean` extended, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `finite_nerve_simplices` — the simplices of the nerve of a finite poset are finite, because a
  simplex is determined by its vertices.  With it, `chamberCoefficient_total`: the coefficients at
  the chambers sum to the identity — the biproduct total identity, proved without any biproduct API
  — and **`eq_zero_of_chamberCoefficient`**: a normalized chain all of whose chamber coefficients
  vanish is zero.  That is the converse direction the generation argument needs.

  `prevSet`, `chainNewElt`, `chainLastElt`, `chainOrdering` — from a top chain, the ordering it
  determines: the vector acquired at each step, and the one left over at the top.
  **`exists_ordering_chainOfOrdering`** — every top chain of a Boolean apartment is the chain of
  initial segments of an ordering, proved by comparing cardinalities rather than reconstructing the
  chain step by step.  With `chainOfOrdering_injective` this gives **`apartmentChamberEquiv`**: the
  chambers of an apartment are in bijection with the orderings of its frame.

  Remaining for Solomon's basis theorem: thinness in the "exactly two chambers per face" form, and
  then the assembly — coefficients of a cycle are equal up to sign along adjacent transpositions, and
  those generate the symmetric group (`Equiv.Perm.mclosure_swap_castSucc_succ`, already in mathlib),
  so a cycle with one vanishing coefficient vanishes.  Every other ingredient is now in place.

- 2026-08-02 — **Thinness of the Coxeter complex: exactly two chambers per face.**
  `ApartmentChains.lean` extended, axioms `[propext, Classical.choice, Quot.sound]`:

  `eq_or_swap_of_agree_off_two` — a general fact with no simplicial content: **two bijections that
  agree outside a two-element set are equal or differ by the transposition of that set.**  The proof
  is that the images of the exceptional pair are forced to be the same pair, by injectivity and
  surjectivity of both maps.

  `initialSegSet_zero`, `ordering_eq_zero_of_seg`, `ordering_eq_succ_of_segs` — an ordering is read
  off its initial segments one vector at a time; the earlier injectivity proof is refactored onto
  them.  With the general fact this gives **`eq_or_swap_of_chainOfOrdering_agree`**: if the chains of
  two orderings agree at every index but one, the orderings are equal or differ by the transposition
  at that place.

  `ncard_chainOfOrdering`, **`face_index_eq`** — the vertex sizes along a chain determine where a
  face was taken, so two faces of chambers agree only if they are faces at the same place.

  Together these are thinness in the exact form the generation argument needs: a face of a chamber
  lies in that chamber and in exactly one other, obtained by the adjacent transposition.  What is
  left is the assembly: expand the boundary in chamber coordinates, read off that a cycle's
  coefficients agree up to sign across adjacent transpositions, and conclude with
  `Equiv.Perm.mclosure_swap_castSucc_succ` and `eq_zero_of_chamberCoefficient` that
  `apartmentFundamentalClass` is an isomorphism.

- 2026-08-02 — **The boundary relation of the Coxeter sphere in chamber coordinates.**  New module
  `ApartmentGenerator.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  `faceMultiplicity`, **`comp_d_comp_chamberCoefficient`** — a normalized chain is the sum of its
  chamber coordinates, so the value of its boundary at a face is the signed sum of its chamber
  coefficients weighted by how often each chamber carries that face.
  `apartmentFace`, **`faceMultiplicity_apartment`** — thinness in coordinates: that weight is
  `(-1)^i` for the two chambers containing the face and zero for every other chamber.
  `orderingChamberEquiv` — chambers indexed by permutations of a reference ordering.

  **`cycleCoefficient_swap`** — hence for any cycle `x` of the apartment and any ordering `sigma`,

  ```text
  c(sigma * s) = -c(sigma)     for every adjacent transposition s,
  ```

  where `c` is the coefficient of `x` at the chamber of `sigma`.  This is the boundary relation of
  the sphere read in the coordinates the fundamental cycle is written in, and it is the last piece of
  geometry the generation argument needs.

  What is left is a word induction: adjacent transpositions generate the symmetric group
  (`Equiv.Perm.mclosure_swap_castSucc_succ`), so `c(sigma) = sign(sigma) * c(1)`; a cycle with
  `c(1) = 0` then has all coefficients zero and vanishes by `eq_zero_of_chamberCoefficient`; and the
  fundamental cycle has `c(1) = 1`, so it is an isomorphism onto the cycles — the top homology of the
  apartment.

- 2026-08-02 — **The fundamental class of the Coxeter sphere generates: the apartment's top homology
  is one copy of the coefficients on an explicit cycle.**  `ApartmentGenerator.lean` completed,
  axioms `[propext, Classical.choice, Quot.sound]`:

  **`cycleCoefficient_eq_sign_smul`** — the coefficients of any cycle of an apartment satisfy
  `c(sigma) = sign(sigma) * c(1)`.  Adjacent transpositions flip the sign by the boundary relation,
  and they generate the symmetric group (`Equiv.Perm.mclosure_swap_castSucc_succ`), so a list
  induction over words in them settles every ordering at once.
  **`cycle_eq_zero_of_cycleCoefficient`** — hence a cycle whose coefficient at one chamber vanishes
  is zero.
  **`isIso_apartmentFundamentalCycle`** — with the retraction already available this makes the
  fundamental cycle an *isomorphism* onto the cycles: `1 - p ∘ zeta` is a cycle killed by the
  coefficient at the reference chamber, so it vanishes.
  **`isIso_apartmentFundamentalClass`**, **`apartmentHomologyIso`** — and therefore

  ```text
  R  ≅  H_(N-2)(apartment),      generated by  sum over sigma of sign(sigma) * (chain of sigma).
  ```

  This closes the apartment half of the card's "its fundamental class is an apartment generator of
  the Steinberg module".  The class is now *constructed*, not chosen: `apartmentIso` was
  `Classical.choice` on an existence proof, while `apartmentHomologyIso` is the explicit signed sum
  over orderings of the frame, and the two agree up to the sign of a reference ordering.

  What remains of Solomon's basis theorem is the building half: that the apartment classes, one for
  each frame, *span* the Steinberg module.  The apartment side is now complete and explicit, and
  `mono_apartmentClass` already gives that each class injects.

- 2026-08-02 — **The apartment class of a frame, explicitly.**  `ApartmentGenerator.lean` extended,
  axioms `[propext, Classical.choice, Quot.sound]`:

  **`apartmentClassOf`** — the fundamental class of a frame's Coxeter sphere, now a *constructed*
  cycle rather than a chosen isomorphism, pushed into the building along the frame's order
  embedding; and **`mono_apartmentClassOf`** — it is a monomorphism, so the Steinberg module contains
  the class of an explicitly written cycle for every observer frame.

  Two notes for whoever continues.  First, the equivariance of the explicit class under the observer
  group is *not* included: the proof of the chosen-class version transfers verbatim except for one
  rewrite, which fails on the `nerve P` versus `nerveFunctor.obj (Cat.of P)` mismatch —
  `apartmentFundamentalClass` is stated in the first form and `apartmentNerveMap` in the second, so
  `SSet.homologyMap_comp` will not match.  Restating `apartmentFundamentalClass` in the functor form
  is the fix.  Second, the remaining mathematics of Solomon's basis theorem is now exactly:
  the apartment classes span.  The classical proof of that is a shelling induction on gallery
  distance, which is elementwise and does not transfer to an arbitrary abelian category; the route
  that does is to show the Mayer--Vietoris descent carries apartment classes to apartment classes one
  rank down, for which `ShortComplex.ShortExact.δ_eq'` is the categorical lift-and-chase and the
  explicit cycle built here is the object to lift.

- 2026-08-02 — **Equivariance of the explicit apartment class, and the star splitting.**  Axioms
  `[propext, Classical.choice, Quot.sound]`:

  The mismatch flagged in the previous entry is fixed: `apartmentFundamentalClass` is now stated with
  `nerveFunctor.obj (Cat.of ...)` rather than `nerve ...`, which is what every map out of it is
  typed with, so `SSet.homologyMap_comp` matches.  With `homologyMap_apartmentNerveMap_comp` this
  gives **`apartmentClassOf_comp_homologyMap`**: the observer group permutes the *explicit* apartment
  classes, exactly as it permutes the chosen ones.  The lesson is worth stating plainly: in this
  corpus a statement should be phrased in the form its consumers use, since `nerve P` and
  `nerveFunctor.obj (Cat.of P)` are definitionally equal but not interchangeable for `rw`.

  **`chainOfOrdering_eq_singleton_iff`** — a chamber of an apartment contains the line of a frame
  vector exactly when its ordering starts with that vector.  This is the splitting of an apartment's
  chambers into those inside the star of a vertex and those outside it, which is the first step of
  the descent computation: to push an apartment class through the Mayer--Vietoris connecting map one
  splits its signed sum along exactly this criterion, lifts the two halves to the base and the star,
  and reads off the image in the intersections.

- 2026-08-02 — **The cover of an apartment, chamber by chamber.**  `ApartmentChains.lean` extended,
  axioms `[propext, Classical.choice, Quot.sound]`:

  `initialSegSet_castSucc_last` — the last proper initial segment of an ordering is the complement of
  its last vector.  Hence **`chainOfOrdering_eq_compl_singleton_iff`**: a chamber of an apartment
  contains the coatom opposite a frame vector exactly when its ordering *ends* with that vector.
  This is the splitting the Mayer--Vietoris cover actually uses — the pieces of that cover are the
  stars of the spanning coatoms, not of the atoms, so the criterion is about the last vector of the
  ordering, while the earlier `chainOfOrdering_eq_singleton_iff` (first vector) describes the star of
  a vertex.

  **`apartment_not_spanning_of_ne`** — the only vertex of an apartment that spans with a given frame
  vector is the coatom opposite it.  So a chamber missing that coatom has all its vertices
  non-spanning and lies wholly in the base of the cover.

  Together: the chambers of an apartment split cleanly into the ones inside the single star and the
  ones inside the base, which is the lift the connecting map needs.  What is left of the descent step
  is the third piece — that the boundary of the star half, read in the intersections, is the
  fundamental chain of the link's apartment — and then Solomon's spanning statement follows by
  induction on rank.

- 2026-08-02 — **The link of a coatom of an apartment is an apartment.**  New module
  `ApartmentInterval.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  **`properBelowSetOrderIso`** — the elements of an apartment strictly below a coordinate subset `S`
  are the proper nonzero subsets of `S`, by restriction and image along the inclusion of `S`.  So the
  link of a coatom is again an apartment, one vector smaller, which is what the descent needs in
  order to recognise its own output.

  **Gate correction.**  The `2 -> 3` gate said the missing items were `(4)` as a homotopy statement
  *and* `(6)`'s apartment basis.  That conflated a numbered claim of the card with a stretch beyond
  it: `(6)` as the card states it — reduced `H_(N-2)` is the Steinberg module, with the observer
  action — is formalized, and so is everything the apartment paragraph asserts of a single frame's
  fundamental class.  Solomon's *basis* theorem is not a claim of this card; it is recorded as a
  stretch goal with its route.  The gate text and the `Lean boundary` section now say this.

- 2026-08-02 — **The chambers of the link are the top faces of the chambers of the star.**
  `ApartmentInterval.lean` extended, axioms `[propext, Classical.choice, Quot.sound]` (the ordering
  restriction itself needs only `[propext, Quot.sound]`):

  `restrictOrdering` — an ordering of a frame that *ends* with a given vector restricts to an
  ordering of the remaining vectors, bijectively.
  `image_initialSegSet_restrictOrdering` — its initial segments are the initial segments of the
  original ordering, one step short.
  **`coe_properBelowSetOrderIso_symm_chainOfOrdering`** — hence, transported into the apartment along
  the identification of the link with a smaller apartment, the chain of the restricted ordering is
  the chain of the original one with its top vertex removed.

  So the three combinatorial inputs of the descent step are now all proved: the chambers of an
  apartment split into star and base (`chainOfOrdering_eq_compl_singleton_iff`,
  `apartment_not_spanning_of_ne`), the link is an apartment (`properBelowSetOrderIso`), and the star
  chambers' top faces are exactly the link's chambers.  What is left is the homological step —
  feeding these to `ShortComplex.ShortExact.δ_eq'` to identify the connecting map's value on an
  apartment class with the apartment class of the link.

- 2026-08-02 — **The building's cover cuts an apartment along the apartment's own cover.**  New
  module `ApartmentBuildingCover.lean`, axioms `[propext, Classical.choice, Quot.sound]`:

  `coordSpan_union` — the coordinate subspace of a union is the join of the coordinate subspaces;
  hence **`coordSpan_sup_singleton_eq_top_iff`**: inside the apartment of a frame, spanning with a
  frame line is a purely combinatorial condition on coordinate sets.  With the apartment-side
  criterion this gives `coordSpan_sup_singleton_ne_top` and `coordSpan_compl_sup_singleton`, and in
  the corpus's own vocabulary `apartmentVertices_mem_notSpanning` and
  `apartmentVertices_mem_spanning`: a vertex of the apartment lies in the base of the Solomon--Tits
  cover unless it is the coatom opposite the chosen line, which lies in the star.

  So the cover of the building restricts to the apartment as the apartment's own one-piece cover.
  Everything the descent step needs on the geometric side is now proved; what is left is homological
  bookkeeping — writing the apartment cycle in the unnormalized complex, splitting it along this
  criterion to lift it into `C(base) ⊞ C(star)`, and feeding the lift to
  `ShortComplex.ShortExact.δ_eq'`.

- 2026-08-02 — **Each chamber of an apartment lies wholly in the base or wholly in the star.**
  `ApartmentBuildingCover.lean` extended, axioms `[propext, Classical.choice, Quot.sound]`:

  `chainOfOrdering_le_last` — every vertex of a chamber is contained in its top vertex;
  `chainOfOrdering_ne_compl` — a chamber whose ordering does not end with the chosen vector misses
  the coatom entirely.  Hence **`chamber_mem_notSpanning`**: all its vertices are vertices of the
  base; and **`chamber_mem_generalStar`**: if the ordering does end with that vector, all its
  vertices lie in the star of the coatom, because they are all contained in the top one.

  These are the two membership facts the lift into `C(base) ⊞ C(star)` consumes, one per chamber, so
  the geometric input to the descent step is complete down to the level of individual simplices.

### 2026-08-02 — plan of record for the descent (Solomon spanning)

`ApartmentBuildingCover.lean` now compiles with the transport layer
`apartmentToFamBuilding`, `apartmentToFamBuilding_mem_famCoverBase`,
`apartmentToFamBuilding_mem_generalStar`: an apartment sits inside the disjoint-union presentation
`famBuilding (fun _ : PUnit => ⊤)` that the Mayer--Vietoris cover is stated on, its vertices other
than the coatom opposite the chosen frame vector lie in the base of the cover, and those below that
coatom lie in the star.  (The monotonicity field must be given as the term `⟨rfl, _⟩`: the `≤` of
`famPoset` unfolds definitionally to a conjunction, while `famPoset_le_iff` leaves the poset
implicit stuck behind a metavariable.)

The remaining mathematical content of the stretch goal — the apartment classes span the Steinberg
module — is a descent along the connecting map of that cover.  Route decided after comparing two:

* *Naturality route*: prove that `famTopEmbedding` is natural for a map of covers, using mathlib's
  `HomologicalComplex.HomologySequence.δ_naturality`.  Rejected as the primary route: it needs
  separate naturality statements for `famSupHomologyIso`, for `famPosetHomologyIso` and for
  `famCoverInterNerveIso`, each of which contains an `eqToIso`.
* *Chain route* (chosen): mathlib's `δ_eq` computes the connecting map on an explicit cycle.  Every
  object in sight is then a signed sum of `ιChainComplex` of named simplices, and every map in sight
  is induced by a map of simplicial sets, which acts on those sums by `ι_chainComplexMap_f`.

Steps, each its own module:

1. `ApartmentUnnormalizedCycle.lean`: the apartment cycle in the *unnormalized* chains, where the
   Mayer--Vietoris sequence lives.  A general involution lemma — the signed sum of faces over any
   set of orderings closed under the transposition at the deleted place vanishes — then the cycle
   itself, and the bridge `apartmentFundamentalClass = ` its class.
2. The split: the chambers whose ordering ends with the chosen vector give a chain of the star, the
   others a chain of the base; their sum is the apartment cycle.  Membership is already proved
   (`chamber_mem_notSpanning`, `chamber_mem_generalStar`).
3. The boundary of the star half is, up to sign, the apartment cycle of the link, by the same
   involution lemma applied to the orderings that end with the chosen vector: only the face that
   deletes the top vertex survives, and `coe_properBelowSetOrderIso_symm_chainOfOrdering` says that
   face is the chamber of the restricted ordering.
4. `δ_eq` then gives `δ(apartment class) = ±(link apartment class)`, and `isIso_famTopEmbedding`
   makes `δ` invertible, so the two classes generate each other.
5. The induction on rank: the class of a frame of a coatom is `δ` of the class of any frame of the
   whole space extending it, so `Epi` of the coproduct of the apartment classes follows from the
   same statement one rank down.

The chains of a subcomplex inject into the chains of the ambient complex (a coproduct over a
subfamily has a retraction), which is what lets step 3 compute only the star half.
