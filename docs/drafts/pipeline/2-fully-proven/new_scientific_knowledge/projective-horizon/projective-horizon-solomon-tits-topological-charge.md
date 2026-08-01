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

The two-chart reconstruction supporting the building's complementary vertices is formalized in
`formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonBuilding.lean`. Mathlib currently provides
no local formal surface for the full Solomon--Tits theorem used here, so `(3)--(6)` are not encoded
as assumptions or placeholders.

## RH impact audit

`[NO CURRENT RH CONSEQUENCE]` If a natural `N`-channel projective zeta observation were found, its
horizon-context complex would carry a Steinberg top class. There is no established map from that
class to positivity, a Weil criterion, or zero location.

## Gates

- [x] 0 -> 1: exact topology extracted from the horizon-building poset
- [x] 1 -> 2: simplicial identification and Solomon--Tits consequence proved
- [ ] 2 -> 3: parent two-chart core formalized; full building topology unavailable in local Lean
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
