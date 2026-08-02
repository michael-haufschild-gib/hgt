# Projective HT horizons are a symmetric-space boundary at infinity

- **ID:** `projective-ht-horizon-symmetric-space-boundary`
- **Stage:** 2-fully-proven
- **Type:** NONPOSITIVELY CURVED OBSERVER GEOMETRY / TITS BOUNDARY
- **Scientific status:** `[PROVED CONSEQUENCE OVER C] [NOVEL INTERPRETATION CANDIDATE]`
- **Parents:** `projective-horizon-tits-building`,
  `projective-horizon-solomon-tits-topological-charge`
- **Statement:** Over the complex constants, the incidence geometry of common projective HT
  derivative horizons is equivariantly the Tits boundary at infinity of the symmetric space of
  unit-determinant Hermitian observer metrics.

## Complex specialization

Specialize the constant field to `C`. Let `V=C^N` and let

```text
X_N=SL_N(C)/SU(N).                                        (1)
```

The space `X_N` is equivalently the Riemannian symmetric space of positive-definite Hermitian
forms on `V` with determinant one. It is noncompact, nonpositively curved, and has real rank
`N-1`.

The projective HT horizon theorem supplies the spherical building

```text
Delta_HT(V)={nontrivial common-horizon fields mathcal I_S} (2)
```

with flags ordered by reverse field inclusion.

## Theorem

There is a `PGL_N(C)`-equivariant isomorphism of spherical buildings

```text
Delta_HT(V) congruent boundary_Tits X_N.                  (3)
```

Under `(3)`:

- an elementary hyperplane horizon is a vertex at infinity of the corresponding maximal
  parabolic type;
- a strict chain of common-horizon fields is a Weyl simplex at infinity;
- a complete projective observer frame gives an apartment, the Tits boundary of a maximal flat in
  `X_N`;
- the apartment sphere has dimension `N-2`;
- the Steinberg horizon class is the top homology class of the building at infinity.

## Proof

The parent horizon theorem identifies `Delta_HT(V)` with the flag complex of nonzero proper
subspaces of `V*`. The classical boundary theorem for noncompact symmetric spaces identifies
`boundary_Tits(SL_N(C)/SU(N))` with the spherical building of proper parabolic subgroups of
`SL_N(C)`. Using the dual defining representation, this is precisely the flag complex of nonzero
proper subspaces of `V*`, with the contragredient projective action. This direct identification is
`(3)`. Using Hermitian orthogonal complements instead gives the equivalent type-reversing model
through the standard diagram automorphism.

## Metric-degeneration description

Choose the identity Hermitian form as basepoint. A geodesic ray in `X_N` has the form

```text
H_A(t)=exp(tA),                                            (4)
```

where `A` is traceless Hermitian. Its endpoint in the Tits boundary is determined by the flag of
eigenspace sums ordered by the eigenvalues of `A`.

- distinct eigenvalues give a chamber, hence a complete chain of common-horizon fields;
- repeated eigenvalues give a face, hence a partial horizon chain;
- commuting choices of `A` lie in one maximal flat and give one apartment.

Thus every asymptotic degeneration pattern of an observer metric has a precise field label, and
every horizon flag arises from such a degeneration.

## Physical content and boundary discipline

Equation `(3)` is a literal boundary-at-infinity theorem. It gives the projective HT information
geometry a nonpositively curved bulk whose asymptotic directions are exactly horizon contexts.
The parameter `t` in `(4)` is the scale of observer-metric degeneration. It is not a time variable,
not a flow generating the HT source, and not evidence of source dynamics.

This is the strongest justified holographic statement currently available:

```text
HT horizon context geometry = Tits boundary of observer-metric space. (5)
```

It is not a black-hole horizon. No Lorentzian metric, causal structure, Einstein equation,
Hamiltonian, entropy-area law, temperature, or quantum state has been produced. The symmetric
space is attached to projective observer frames, not asserted to be physical spacetime.

## Relation to the nature of hypertranscendence

A jointly HT projective source has maximally free jets, so the full projective observer group acts
faithfully on its differential rational field and the generic-orbit dimension arguments recover
every building face without accidental field identifications. Its observer contexts therefore
have the complete type-`A_(N-1)` boundary geometry. Some specially projectively invariant
differential equations may retain part or all of this group action, so no converse characterization
of HT is asserted here.

The result reframes hypertranscendence as maximal projective boundary thickness: every parabolic
direction and every flag of observer degenerations survives as a distinct differential subfield.

## Novelty and significance gate

- The Tits-boundary description of `SL_N(C)/SU(N)` is classical.
- The horizon building and its realization by differential fixed fields are the new candidate
  content of the parent theorem.
- The new conclusion is their equivariant identification `(3)`, which turns the horizon topology
  into an actual boundary at infinity and supplies the observer-metric bulk interpretation.
- No checked source relates derivative horizons of HT sources to this symmetric-space boundary.

The physical terminology is subordinate to `(3)`; it adds no unsupported dynamics.

## Lean boundary

The arbitrary-dimensional two-chart complementarity feeding the vertices of `(2)` is formalized
in `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonBuilding.lean`. The local Lean
environment has no formal Tits-boundary/symmetric-space library, so `(3)` is not encoded by an
axiom or placeholder.

## RH impact audit

`[GEOMETRIC ORGANISING POSSIBILITY; NOT RH PROGRESS]` A canonical projective zeta observation
could place its horizon flags on the Tits boundary of an observer-metric symmetric space. No map
from that boundary to Weil positivity, the critical line, or zero exclusion is known.

## Gates

- [x] 0 -> 1: literal boundary candidate separated from spacetime and black-hole metaphors
- [x] 1 -> 2: equivariant building-at-infinity identification proved
- [ ] 2 -> 3: parent reconstruction core formalized; symmetric-space boundary unavailable in Lean
- [ ] 3 -> 4: external audit in symmetric spaces and projective differential invariants

## References

- The classical theorem that the Tits boundary of a symmetric space of noncompact type is its
  spherical building at infinity.
- J. Tits, *Buildings of Spherical Type and Finite BN-Pairs*.
- L. Ji, *Buildings and their applications in geometry and topology*.

## Log

- 2026-07-15 — identified the horizon building with the Tits boundary of
  `SL_N(C)/SU(N)` and separated observer-metric degeneration from source time evolution.

- 2026-08-01 — **The apartment dimension bullet of `(3)` is formalized.**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveFlagDimension.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `card_le_finrank_sub_one` — a chain of proper nonzero subspaces of an `N`-dimensional space has at
  most `N - 1` members, so the simplex it spans has dimension at most `N - 2`.  That is the card's
  clause "the apartment sphere has dimension `N-2`", on the flag-complex side of `(3)`.

  The proof is the dimension function.  `finrank_injOn_of_chain` — along a chain the dimension
  determines the member, since a strict inclusion strictly increases dimension in finite dimension.
  The dimensions of proper nonzero subspaces lie in `[1, N-1]`, a set of `N - 1` elements, so the
  chain injects into it.

  This is the combinatorial half of `(3)` and needs no building theory: an elementary horizon is a
  vertex, a strict chain of horizons is a simplex, and the bound above is what makes a complete frame
  give a top-dimensional simplex.  What `(3)` still needs is the other half — the identification of
  the Tits boundary of `SL_N(C)/SU(N)` with the building of parabolic subgroups — for which the local
  toolchain has no symmetric-space library, as the Lean boundary section already records.

- 2026-08-01 — **The apartment dimension is exact, not just bounded.**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveFlagDimension.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `exists_chain_card_eq_finrank_sub_one` — a complete frame gives a chain of **exactly** `N - 1`
  proper nonzero subspaces, and `isGreatest_chain_card` combines it with the previous entry's bound:

  ```text
  IsGreatest {card of a chain of proper nonzero subspaces} (N - 1).
  ```

  So the top simplices of the horizon complex have dimension exactly `N - 2`, which is the card's
  clause in full rather than as an inequality.

  The construction is mathlib's `Module.Basis.flag`, the flag of a basis, with its two trivial ends
  removed.  `flag_strictMono` gives distinctness of the members and, against `flag_zero = ⊥` and
  `flag_last = ⊤`, gives that each is a proper nonzero subspace; `flag_mono` gives comparability.  No
  dimension computation is needed for the construction — only for the matching upper bound, which is
  the previous entry.

  `(3)` still needs the symmetric-space side.  What is now formalized is that the flag complex it is
  to be identified with has the asserted top dimension.

- 2026-08-01 — **The type of a vertex, and the equivariance of `(3)` on the flag-complex side.**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveFlagDimension.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `exists_equiv_map_eq` — **vertices of the same type form a single orbit**: two subspaces of the
  same dimension are carried to one another by a linear automorphism.  So the dimension is a complete
  invariant of a vertex under the projective action, which is the card's clause that an elementary
  hyperplane horizon is a vertex of one maximal parabolic type — the type being the codimension.

  The construction is a complement on each side (`Submodule.exists_isCompl`), an isomorphism of the
  two subspaces and of the two complements (`LinearEquiv.ofFinrankEq`, using that the complements
  have equal dimension because each pair sums to the ambient dimension), and the two splittings
  glued by `Submodule.prodEquivOfIsCompl`.  Only the inclusion `W.map e ≤ W'` has to be checked by
  hand; equality then follows from `Submodule.eq_of_le_of_finrank_eq` since an automorphism preserves
  dimension.

  `finrank_map_of_equiv`, `map_equiv_injective`, `card_image_map_equiv` — the action preserves the
  type, is injective on vertices, and carries chains to chains of the same size.  So it acts
  simplicially on the horizon complex and preserves the type function: the "equivariant" in
  "equivariant isomorphism of spherical buildings", on the side of `(3)` that is available.

  Together with the two previous entries, the flag-complex side of `(3)` now has its vertices typed,
  its type-orbits identified, its simplices bounded and attained at dimension `N - 2`, and the action
  shown simplicial and type-preserving.  What is still missing is only the symmetric-space side.

- 2026-08-01 — **The apartment of a frame is the Coxeter complex of its orderings.**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveFlagDimension.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  `card_flags_of_frame` — a complete projective observer frame carries exactly `N!` complete flags:

  ```text
  Nat.card {(b.reindex σ).flag : σ a permutation of the frame} = N!.
  ```

  That is the card's clause "a complete projective observer frame gives an apartment", with the
  apartment's top-dimensional simplices identified as the orderings of the frame — the Coxeter
  complex of the symmetric group, which is what an apartment of a type `A` building is.

  `mem_flag_reindex_iff` is the mechanism: a frame vector lies in the flag of the reordered frame
  exactly below the position the ordering assigns it, which is mathlib's `self_mem_flag_iff` read
  through the reindexing.  `flag_reindex_injective` then recovers the ordering from the flag by
  testing membership at one index at a time, so distinct orderings give distinct flags.

  With the three previous entries the flag-complex side of `(3)` is now formalized in all four of the
  card's bullets that do not mention the symmetric space: vertices are typed by codimension, the types
  are single orbits, chains are simplices of dimension at most `N-2` with the bound attained, and a
  frame gives an apartment with `N!` chambers.  The remaining content of `(3)` is the identification
  of the Tits boundary of `SL_N(C)/SU(N)` with the building of parabolic subgroups, for which the
  toolchain still has no symmetric-space library.

- 2026-08-02 — **The metric-degeneration description `(4)` is formalized, in both directions.**
  Four new modules, all wired into the `HTGeometry` umbrella, all axioms
  `[propext, Classical.choice, Quot.sound]`:
  `HermitianDegenerationFlag.lean`, `HermitianFlagSimplex.lean`, `HermitianFlagRealization.lean`,
  `HermitianApartment.lean`.

  The card's section "Metric-degeneration description" says a traceless Hermitian direction `A`
  determines a flag of eigenspace sums, that distinct eigenvalues give a chamber and repeated ones a
  face, that commuting directions give one apartment, and that every horizon flag arises this way.
  All four are now theorems.

  The flag of a direction is `eigenSum A c = ⨆_{μ > c} eigenspace A μ`.  It is a chain
  (`eigenSum_antitone`, `isChain_range_eigenSum`) and it depends only on the *direction*: positive
  rescaling of `A` moves nothing (`eigenSum_smul`), and neither does adding a scalar
  (`eigenSum_add_smul_id`) — so the traceless, determinant-one normalization of the card costs
  nothing.  Through the eigenvector basis the flag is explicit (`eigenSum_eq_span`) and its members
  have the expected dimensions (`finrank_eigenSum`: the number of eigenvalues above the threshold).

  - **Simplex.** Every proper nonzero member is a vertex of the building
    (`eigenSum_mem_properPart`), and the flag is a nondegenerate simplex of the building's order
    complex of dimension two less than the number of distinct eigenvalues (`exists_flag_simplex`,
    `exists_nonDegenerate_flag`).
  - **Chamber.** With `N` distinct eigenvalues the flag is a complete flag — one subspace of every
    intermediate dimension — hence a chamber, a nondegenerate simplex in the top dimension `N - 2`
    (`exists_chamber_of_injective_eigenvalues`, `exists_nonDegenerate_chamber`).  Repeated
    eigenvalues drop the dimension, so they give a face, exactly as the card states.
  - **Apartment.** The eigenlines of a direction are a frame, and every member of its flag is the
    span of a subfamily (`exists_frame_eigenSum_span`): the flag lies in one apartment.  Two
    *commuting* directions have a joint eigenbasis (`exists_joint_eigenbasis` — the eigenspaces of
    one are invariant under the other, and diagonalizing inside each gives one frame), so their
    flags lie in a **single** apartment (`exists_frame_eigenSum_span_commuting`).  That is the
    card's "commuting choices of `A` lie in one maximal flat and give one apartment".
  - **Every horizon flag arises.**  The converse, `exists_isSymmetric_eigenSum_eq`: given any chain
    of proper nonzero subspaces there is a Hermitian operator whose degeneration flag is that chain.
    The construction is the orthogonal graded decomposition of the chain
    (`gradedPiece`, `iSup_gradedPiece_eq`) carrying the operator that is a distinct real scalar on
    each piece (`pieceOperator`), whose flag is computed unconditionally
    (`eigenSum_pieceOperator`, `eigenSum_pieceOperator_filtration`).

  So the degeneration flags of Hermitian directions are **exactly** the simplices of the building,
  with the chamber/face dichotomy of the card and the apartment structure of commuting directions.

  What is still missing for `(3)` is unchanged and is not asserted: the Tits boundary of
  `SL_N(C)/SU(N)` as a metric object — the symmetric-space metric, its geodesic rays, asymptote
  classes and the Tits distance — for which the toolchain has no library.  What is now formalized is
  the whole content of `(4)` that lives in linear algebra: the map from Hermitian directions to
  simplices of the building, its surjectivity, and the two structural facts (chamber criterion,
  common apartment for commuting directions) that make it a boundary-at-infinity dictionary.
