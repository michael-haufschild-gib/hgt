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
- [x] the degeneration dictionary `(4)`: Hermitian directions ↔ simplices of the building, with the
  chamber/face criterion, the common apartment of commuting directions, surjectivity onto all
  flags, and the exponential growth law of the ray `exp (t A)` along the flag
- [x] equation `(1)`: the space of observer metrics is one orbit of the observer group with the
  isometries as stabilizer, and the rays of traceless directions stay inside it
- [x] the equivariance of the dictionary: conjugating a direction moves its flag by the
  conjugating symmetry, and scalars act trivially
- [x] the boundary parametrization is faithful: a direction is determined by its flag family, so
  distinct directions give distinct boundary data
- [x] real rank `N - 1`: a maximal flat is a Euclidean space of dimension `N - 1`, all of whose
  directions commute and share one apartment
- [x] the Cartan parametrization: the exponential is a bijection from traceless Hermitian
  directions onto the determinant-one observer metrics, with the spectral logarithm as inverse
- [x] the tangent norm and the radial distance: the Hilbert–Schmidt norm of a direction is the
  Euclidean norm of its eigenvalues, and a ray leaves the reference metric at constant rate
- [x] maximal flats are Euclidean: in the logarithmic chart the distance between two points of a
  flat is the Euclidean distance of their weights
- [x] inversion is the geodesic symmetry: `log (P⁻¹) = − log P`, so an observer metric and its
  inverse are at the same distance from the reference metric
- [x] the distance between two observer metrics is defined and separates them
- [x] the triangle inequality for that distance — the nonpositive-curvature theorem for the
  observer-metric space — proved unconditionally in Lean
- [x] symmetry of that distance, and the packaged `MetricSpace` instance on the observer metrics:
  the symmetric-space distance of `X_N` now exists in Lean as a metric object
- [x] for that metric: a maximal flat is an isometric Euclidean space, and the rays `(4)` are
  geodesic lines with `d (exp (s T)) (exp (t T)) = |t - s| ‖T‖`
- [x] the boundary is faithful as a *metric* statement: rays with distinct traceless directions
  diverge linearly, by the exponential metric increasing property (Golden--Thompson, Cordes and
  the Lie--Trotter product formula, all built here)
- [x] geodesic asymptote classes: the asymptote relation is defined and computed — the asymptote
  class of a ray is its degeneration flag — and every flag is realized by a traceless direction, so
  boundary points and simplices of the building correspond bijectively
- [x] the Tits metric inside an apartment: the divergence rate of two rays of a flat is the chordal
  distance `2 sin (θ/2)` of their unit directions, so an apartment's boundary is the round sphere
- [x] the equivariance of that correspondence: the congruence action of the observer group on rays
  induces the conjugation action on flags.  A moved ray is asymptotic to a ray from the reference
  metric, and the direction of that ray is the one carrying the transported flag — so the boundary
  is basepoint-independent and the group acts on it through flags
- [ ] 2 -> 3: what remains for `(3)` is the Tits metric between boundary points of *different*
  apartments
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

- 2026-08-02 — **The ray `exp(tA)` itself is now in the formalization, with its growth law.**
  `formal/GaloisForLFunctions/HTGeometry/HermitianGeodesicRay.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  Equation `(4)` names the ray `H_A(t) = exp(tA)`, not just its direction.  `metricRay T t` is that
  exponential — mathlib's `NormedSpace.exp` of `t • T` — and it dilates each eigenvector by the
  exponential of its eigenvalue (`metricRay_apply_of_eigenvector`, proved from the exponential
  series through the corpus's own `pow_apply_of_eigenvector'`).

  The flag is then exactly the record of expansion rates along the ray:

  ```text
  v ∈ eigenSum T c        →  exp (c t) ‖v‖ ≤ ‖exp (t T) v‖        (t ≥ 0)
  v ∈ (eigenSum T c)ᗮ     →  ‖exp (t T) v‖ ≤ exp (c t) ‖v‖        (t ≥ 0)
  ```

  (`norm_metricRay_ge`, `norm_metricRay_le`).  So the flag member at threshold `c` is precisely the
  subspace on which the observer metric expands at least at rate `c`, and its orthogonal complement
  is where it expands at most at that rate: the two-sided statement that the flag *is* the
  asymptotic degeneration pattern of the ray.  Together with the scaling and translation invariance
  already proved (`eigenSum_smul`, `eigenSum_add_smul_id`) this says the pattern depends only on the
  direction of the ray, which is what makes it a point of the boundary at infinity rather than of
  the space.

  The gap to `(3)` is unchanged and now sharply localized: what is missing is not the dictionary but
  the *metric* — the symmetric-space distance on `SL_N(C)/SU(N)`, its geodesics, and the Tits
  metric on asymptote classes.  Every statement of `(4)` that does not mention that metric is now a
  theorem.

- 2026-08-02 — **Equation `(1)` and the equivariance of `(3)`, formalized.**  Three modules, in the
  `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:
  `HermitianFlagEquivariance.lean`, `HermitianObserverMetric.lean`, `ObserverMetricSpace.lean`.

  **The observer metric.**  The value of a ray is a genuine observer metric: `exp (t T)` is a
  Hermitian form (`isSymmetric_metricRay`), positive definite (`inner_metricRay_pos`), and its
  determinant is `exp (t · tr T)` (`det_metricRay`), proved from the spectral decomposition — this
  is the identity `det (exp A) = exp (tr A)`, which mathlib still lists as a TODO, in the case the
  card needs.  With `trace_eq_sum_eigenvalues` it follows that the ray lies in the
  determinant-**one** space exactly when the direction is traceless
  (`det_metricRay_eq_one_iff`, `metricRay_mem_observerMetric`) — the normalization the card's
  `X_N = SL_N(C)/SU(N)` imposes.  The flag reads the degeneration of the *form* as well as of the
  norm: `exp (c t) ‖v‖² ≤ ⟪v, exp (t T) v⟫` on the flag member at threshold `c`, and `≤` the other
  way on its orthogonal complement (`re_inner_metricRay_ge`, `re_inner_metricRay_le`).

  **Equation `(1)`.**  `exists_congruence_of_observerMetric`: every positive-definite Hermitian form
  of determinant one is the pullback of the reference form by a determinant-one symmetry — its
  positive square root, constructed here from the spectral decomposition (`sqrtOp`,
  `sqrtOp_comp_sqrtOp`, `det_sqrtOp`).  `congruence_eq_refl_iff`: the symmetries fixing the
  reference form are exactly the isometries.  Together: the space of observer metrics is a single
  orbit of the observer group with the unitary group as stabilizer, which is the card's description
  of `X_N` as `SL_N(C)/SU(N)`.

  **Equivariance.**  `eigenSum_conj`: conjugating a direction by an observer symmetry moves its
  degeneration flag by that symmetry, `eigenSum (g T g⁻¹) c = map g (eigenSum T c)`; and
  `conj_smul_eq`: scalars act trivially, so the action is that of the *projective* observer group.
  That is the equivariance clause of `(3)` at the level of the dictionary.

  Still not asserted, and now the only missing piece: the *metric geometry* of `X_N` — its
  distance, geodesics as metric objects, asymptote classes and the Tits metric.  The algebraic
  description of the space, the rays, the flags, their equivariance and the two-sided degeneration
  law are all theorems.

- 2026-08-02 — **Faithfulness of the boundary data, and the real rank.**  Two modules, in the
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:
  `HermitianFlagUniqueness.lean`, `HermitianFlat.lean`.

  **A direction is its flag.**  `eq_of_eigenSum_eq`: two Hermitian directions whose degeneration
  flags agree at every threshold are *equal*.  The proof is the reconstruction of the spectral data
  from the flag: the dimensions of the flag members count the eigenvalues above each threshold, and
  two antitone families with the same upper counts coincide (`eigenvalues_eq_of_eigenSum_eq`); then
  each eigenspace is cut out of the flag by a threshold in the gap below its eigenvalue
  (`exists_gap`, `eigenspace_eq_inf_orthogonal`), so the eigenspaces agree too.  This is the
  statement that the boundary parametrization is faithful — distinct rays of observer metrics have
  distinct degeneration data — which is what makes "the flag *is* the point at infinity" an honest
  reading rather than a lossy one.

  The reconstruction needed three general facts about spans of parts of an orthonormal basis, now
  proved once and reused: coordinates vanish off the index set of a span, a vector whose coordinates
  vanish off a set lies in the corresponding span, and `span (b '' t) ⊓ (span (b '' s))ᗮ
  = span (b '' (t \ s))`.

  **The real rank.**  `HermitianFlat.lean` builds the flat of a frame: the directions diagonal in an
  orthonormal frame, parametrized linearly and faithfully by their weights (`diagOpₗ`,
  `diagOpₗ_injective`), with trace the sum of the weights (`trace_diagOp`).  The traceless ones —
  exactly those whose rays stay in the determinant-one space — form a subspace of dimension `N - 1`
  (`finrank_flat`).  That is the card's "real rank `N - 1`": a maximal flat is a Euclidean space of
  that dimension, so its sphere at infinity has dimension `N - 2`, the dimension of an apartment.
  All directions of one flat commute (`commute_of_mem_flat`) and hence, by the apartment theorem,
  have all their flags inside a single apartment (`exists_frame_flat`) — the card's "commuting
  choices of `A` lie in one maximal flat and give one apartment", now with the flat itself
  constructed.

  What remains for `(3)` is unchanged: the *metric* on the space of observer metrics and the Tits
  metric on its boundary.  Everything the card says about the space, its flats, its rank, its rays
  and their degeneration data is now proved.

- 2026-08-02 — **Every observer metric lies on exactly one ray: the Cartan parametrization.**
  `formal/GaloisForLFunctions/HTGeometry/HermitianLog.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  The card's geodesic rays `H_A(t) = exp (t A)` only describe the space if they *fill* it, one ray
  per point.  They do, and both halves are now theorems.

  `logOp` is the Hermitian logarithm of a positive-definite form, built from its spectral
  decomposition like the square root before it.  The two inversion identities are proved through the
  flag, using the uniqueness theorem of the previous entry:

  ```text
  eigenSum (exp (t T)) c = eigenSum T (log c / t)        (t > 0, c > 0)
  eigenSum (log P) c     = eigenSum P (exp c)
  ```

  (`eigenSum_metricRay`, `eigenSum_logOp`), so `log (exp T)` and `T` have the same flag at every
  threshold and are therefore equal (`logOp_metricRay`), and symmetrically `exp (log P) = P`
  (`metricRay_logOp`).  The exponential is therefore a bijection from Hermitian directions onto
  positive-definite Hermitian forms (`exists_unique_isSymmetric_metricRay`).

  Under the determinant-one normalization the correspondence is with *traceless* directions:
  `trace_logOp_eq_zero` — the trace of the logarithm is `log (det P)`, hence zero exactly when the
  determinant is one — and `exists_unique_traceless_metricRay` states the bijection in the form the
  card uses: every observer metric of determinant one lies on exactly one ray of a traceless
  direction, and every such ray stays inside the space.

  Combined with the earlier entries, the geodesic picture of `X_N` is complete except for its
  metric: the space is one orbit `SL_N(C)/SU(N)`, its points are the exponentials of the traceless
  Hermitian directions bijectively, its maximal flats are Euclidean of dimension `N - 1`, and each
  direction carries a faithful degeneration flag which is a simplex of the building, with the
  chamber/face dichotomy and the apartment structure of commuting directions.

- 2026-08-02 — **The tangent norm and the radial distance.**
  `formal/GaloisForLFunctions/HTGeometry/ObserverDistance.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  The metric layer starts at the tangent space.  The norm of a Hermitian direction is its
  Hilbert–Schmidt norm — and this corpus already owns the Hilbert–Schmidt theory
  (`HilbertSchmidtOperator.lean`, `HilbertSchmidtRankOne.lean`), so nothing about it had to be
  rebuilt: the triangle inequality (`hsNorm_add_le`), definiteness and homogeneity come from there.
  What is new here is the bridge to the spectral picture, `hsNorm_toCLM_eq_sqrt`:

  ```text
  ‖T‖_HS = √(∑ᵢ λᵢ²)
  ```

  for a Hermitian direction with eigenvalues `λᵢ` (through `isHilbertSchmidt_toCLM`: in finite
  dimension every operator is Hilbert–Schmidt).  So the directions at the reference metric form a
  normed space whose norm is the Euclidean norm of the eigenvalues — the flat metric of a maximal
  flat, matching the rank computation of the previous entry.

  Transported by the exponential this gives the radial distance `distId P = ‖log P‖`, and:

  - `logOp_metricRay_smul` — the logarithm of the point of a ray at parameter `t` is `t · T`;
  - `distId_metricRay` — that point is at distance `t · ‖T‖` from the reference metric, so the rays
    of `(4)` are radial geodesics parametrized proportionally to arclength;
  - `distId_eq_zero_iff` — only the reference metric is at distance zero.

  What is still not formalized, and is the last item of `(3)`: the distance between two *arbitrary*
  observer metrics — whose triangle inequality is the nonpositive-curvature statement — and the Tits
  metric on the boundary.  The radial case, which is what the card's rays use, is done.

- 2026-08-02 — **Maximal flats are Euclidean.**
  `formal/GaloisForLFunctions/HTGeometry/FlatEuclidean.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  The tangent-norm formula of the previous entry was generalized from an eigenbasis to *any*
  orthonormal basis (`hsNorm_toCLM_diagonal`: an operator diagonal in an orthonormal basis has
  tangent norm the Euclidean norm of its diagonal), which is what a flat needs, since the directions
  of a flat are diagonal in a common frame but their eigenvalue *ordering* is not the frame's.

  Consequently, for the flat of a frame:

  ```text
  ‖diag w‖              = √(∑ᵢ wᵢ²)                       (hsNorm_diagOp)
  ‖diag w − diag w'‖    = √(∑ᵢ (wᵢ − w'ᵢ)²)               (hsNorm_diagOp_sub)
  ```

  and, transported to the points of the flat by the logarithm (`logOp_metricRay_diagOp`),
  `flat_dist_eq`: the distance between two points of a flat, measured by the tangent norm of the
  difference of their logarithms, is the **Euclidean distance of their weights**.  It vanishes only
  on the diagonal (`flat_dist_eq_zero_iff`) and the parametrization is faithful
  (`metricRay_diagOp_injective`).

  With `finrank_flat = N - 1` this is the card's "real rank `N - 1`" in metric form: a maximal flat
  is a Euclidean space of dimension `N - 1`, so its sphere at infinity is a genuine `S^(N-2)`, the
  dimension of an apartment.

  Still open, and now the only gap: the distance between observer metrics in *different* flats —
  whose triangle inequality is the nonpositive-curvature theorem — and the Tits metric on the
  boundary.

- 2026-08-02 — **Inversion, and a general handle on the logarithm.**
  `formal/GaloisForLFunctions/HTGeometry/ObserverInverse.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  The reusable piece is `logOp_eq_of_diagonal`: an operator diagonal in **any** orthonormal frame
  with positive weights has as logarithm the operator diagonal in the *same* frame with the
  logarithms of those weights.  Proved through the flag and the uniqueness theorem, so no
  eigenbasis bookkeeping is needed — mathlib's chosen eigenbasis of the operator never has to be
  compared with the frame one actually holds.  Two supporting general facts came with it: the
  quadratic form of a frame-diagonal operator is the weighted sum of squared coordinates
  (`inner_self_of_diagonal`), so positive weights give a positive-definite form
  (`inner_self_pos_of_diagonal`).

  With that, `invOp` — the spectral inverse of a positive-definite Hermitian form — is immediate:
  it is Hermitian (`isSymmetric_invOp`), positive definite (`inner_invOp_pos`), inverts
  (`invOp_comp`), and

  ```text
  log (P⁻¹) = − log P            (logOp_invOp)
  dist (P⁻¹) = dist P            (distId_invOp)
  ```

  so inversion fixes the distance from the reference metric: it is the geodesic symmetry through the
  reference point, the involution that makes the observer-metric space *symmetric* in the sense of
  the card's phrase "Riemannian symmetric space".

  Two earlier eigenbasis-specific lemmas (`inner_eq_sum_repr`, `repr_metricRay`) were rewritten as
  corollaries of the new frame-general ones, so the corpus keeps one proof of each fact.

  Still open: the distance between observer metrics in different flats — the triangle inequality
  there is the nonpositive-curvature theorem — and the Tits metric on the boundary.

- 2026-08-02 — **The distance between two observer metrics.**
  `formal/GaloisForLFunctions/HTGeometry/ObserverPairDistance.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  `observerDist P Q = ‖log (√P⁻¹ Q √P⁻¹)‖`: the second metric measured in the frame of the first,
  then read by the radial distance of the earlier modules.  The relative form `relOp` is Hermitian
  (`isSymmetric_relOp`) and positive definite (`inner_relOp_pos`), so it *is* an observer metric and
  the definition is legitimate; and

  ```text
  observerDist P P = 0                       (observerDist_self)
  observerDist P Q = 0 ↔ Q = P               (observerDist_eq_zero_iff)
  relOp id Q = Q                             (relOp_id)
  ```

  — the distance vanishes exactly on the diagonal, and measured from the reference metric it is the
  radial distance already studied.  Supporting facts proved on the way: the spectral inverse inverts
  on both sides (`comp_invOp`) and is injective, and the square root is positive definite
  (`inner_sqrtOp_pos`).

  So the observer-metric space now carries a genuine point-separating distance function.  What is
  still missing — and it is now the *only* missing analytic input for `(3)` — is its **triangle
  inequality**, which for this distance is precisely the nonpositive-curvature (CAT(0)) theorem for
  the symmetric space, together with the Tits metric that is built from it on the boundary.

- 2026-08-06 — **The triangle inequality is proved: the observer-metric distance is a metric.**
  Four new modules under `formal/GaloisForLFunctions/HTGeometry/`, all in the `HTGeometry`
  umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  MatrixCompound.lean            compound k A, Cauchy-Binet, star, unit, diagonal, unitary
  CompoundKyFan.lean             prod_le_mul_of_compound  (multiplicative Ky Fan for a pencil)
  TopSumMajorization.lean        topSum, Karamata for the square, sqrt_sum_sq_le_of_topSum_le
  ObserverTriangleInequality.lean  observerDist_triangle
  ```

  ```text
  observerDist hP hn hR ≤ observerDist hP hn hQ + observerDist hQ hn hR
  ```

  for arbitrary positive-definite Hermitian `P`, `Q`, `R`, with no further hypotheses.  This was
  the last missing analytic input of `(3)`, and it is the nonpositive-curvature statement for
  `X_N`: with `observerDist_eq_zero_iff` the space of observer metrics now carries a genuine
  point-separating distance obeying the triangle inequality.

  **The proof is elementary and calculus-free**, which is the part worth recording.  The classical
  route (Bhatia) is Riemannian: the exponential-metric-increasing property, proved from the
  Daleckii--Krein derivative of `exp`, plus the identification of the distance with an infimum of
  path lengths.  Mathlib has no Fréchet derivative of the operator exponential, so that route was
  rejected.  The Golden--Thompson / Araki log-majorization route was rejected too, and for a
  mathematical reason rather than a formalisation one: it runs the *other* way, giving
  `‖H + K‖ ≤ ‖log (e^(H/2) e^K e^(H/2))‖`, which is the exponential-metric-increasing inequality,
  not the triangle inequality; the reverse comparison `‖log (e^(H/2)e^Ke^(H/2))‖ ≤ ‖H+K‖` is false.

  What works instead is the multiplicative Ky Fan inequality.  Write `λ(P,Q)` for the spectrum of
  the pencil, that is the eigenvalues of `√P⁻¹ Q √P⁻¹`, so that
  `observerDist P Q = ‖log λ(P,Q)‖₂` (`distId_eq_sqrt`).  Then:

  1. for positive-definite forms, `x* Q x ≤ a · x* P x` and `x* R x ≤ b · x* Q x` compose to
     `x* R x ≤ ab · x* P x` — a chain of quadratic-form inequalities and nothing else;
  2. run that chain on the `k`-th compound, where a product of `k` eigenvalues becomes a single
     one: `∏_(i<k) λ↓(P,R) ≤ ∏_(i<k) λ↓(P,Q) · ∏_(i<k) λ↓(Q,R)`;
  3. at `k = N` the inequality is an equality, by multiplicativity of the determinant;
  4. so `log λ(P,R)` is *majorized* by `log λ(P,Q)↓ + log λ(Q,R)↓`, and Karamata's inequality for
     the square — one summation by parts, with the antitone weights `a i + v i` — gives the
     Euclidean comparison, which is the triangle inequality.

  Mathlib has none of Cauchy--Binet, an inner product on exterior powers, or majorization theory.
  The compound is therefore defined as the matrix of `exteriorPower.map`, which makes
  **Cauchy--Binet a corollary of functoriality**; the minor formula
  `exteriorPower.ιMultiDual_apply_ιMulti` then gives `C_k (Aᴴ) = C_k(A)ᴴ`, which is what makes the
  compound of a unitary unitary and the compound of a Hermitian form Hermitian.  The pencil
  statements are all phrased through *explicit* unitary diagonalisations supplied as hypotheses,
  so no eigenvalue-multiset uniqueness is ever needed and the operator-to-matrix bridge
  (`obsMat`, `invSqrtMat`) is mechanical.

- 2026-08-06 — **The observer metrics are a metric space, in mathlib's sense.**
  Two further modules, in the `HTGeometry` umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  ObserverDistanceSymmetry.lean       observerDist_comm, distId_swap, distId_eq_sqrt_of_diagonal
  ObserverMetricSpaceStructure.lean   ObserverMetric, instance : MetricSpace (ObserverMetric E)
  ```

  Symmetry was the one axiom of a metric that the card had not recorded as needed, and it is not
  formal: `observerDist P Q` and `observerDist Q P` are read off *different* frames.  What
  identifies them is that the relative form of the reversed pair is the inverse of the relative
  form up to a change of frame:

  ```text
  √P (√Q⁻¹ √Q⁻¹ √P)  =  (√P⁻¹ Q √P⁻¹)⁻¹                (relOp_swap_eq_invOp)
  ```

  and that the two orders `X* X` and `X X*` of a product of two Hermitian operators carry the same
  weights (`distId_swap`): if `X* X` has orthonormal eigenframe `u` with weights `g`, the
  normalised images `g i ^ (-1/2) • X (u i)` are an orthonormal eigenframe of `X X*` with the same
  weights.  This is the polar-decomposition fact, proved here without a polar decomposition —
  the frame is written down and its orthonormality is the polarisation identity.  Since inversion
  negates the logarithm (`distId_invOp`, already in the corpus), the two distances agree.

  The capstone packages the three facts as an instance: the positive-definite Hermitian forms with
  `observerDist` are a `MetricSpace`.  `X_N` is the determinant-one slice of that space, so the
  symmetric-space distance of `(3)` now exists as a metric object in Lean.  What `(3)` still needs
  is the *asymptotic* layer on top of it: geodesic asymptote classes and the Tits metric on the
  set of classes.

- 2026-08-06 — **Flats are isometrically Euclidean and rays are geodesic lines, for the metric
  itself.**  `formal/GaloisForLFunctions/HTGeometry/FlatGeodesicIsometry.lean`, in the umbrella,
  axioms `[propext, Classical.choice, Quot.sound]`.

  The earlier flat module measured a flat in the logarithmic chart — the tangent norm of the
  difference of the logarithms.  With `observerDist` now a metric, the same computation can be run
  for the distance itself:

  ```text
  observerDist (diagOp b p) (diagOp b q) = ‖log q - log p‖₂          (observerDist_diagOp)
  observerDist (exp (s T)) (exp (t T))   = |t - s| · ‖T‖             (observerDist_metricRay)
  ```

  So a maximal flat is an isometric copy of Euclidean space — the real-rank statement is now
  metric, not only linear-algebraic — and the card's rays `(4)` are genuine geodesic lines, not
  merely curves leaving the reference metric at constant rate.

  The enabling lemmas are of independent use: a form diagonal in a frame has its **square root**
  and its **inverse** diagonal in the same frame (`sqrtOp_eq_diagOp`, `invOp_eq_diagOp`), hence so
  does the relative form of two forms in one frame.  The square-root statement is the uniqueness of
  the positive square root, proved through the flag: at a nonnegative threshold the flag of a square
  root is the flag of the form at the squared threshold, so `eq_of_eigenSum_eq` applies with no
  eigenbasis bookkeeping.  The inverse statement needs no flag at all — the diagonal candidate is a
  left inverse, and `comp_invOp` makes it the inverse.

  Added in the same module: `observerDist_metricRay_diagOp` and
  `exists_pos_observerDist_metricRay_diagOp` — two rays of one flat separate at exactly `|t|` times
  the Euclidean distance of their weight vectors, and that rate is positive as soon as the
  directions differ.  So inside an apartment the boundary is faithfully parametrised by directions,
  and the asymptotic separation rate is the Euclidean one, which is the comparison quantity the
  Tits angle is built from.  The corresponding statement for directions **not** in a common flat
  needs the exponential-metric-increasing inequality `‖H - K‖ ≤ d (exp H) (exp K)`, whose analytic
  input is the operator-norm Golden--Thompson inequality; note that mathlib does carry
  Löwner--Heinz (`CFC.rpow_le_rpow`), which is the usual entry point to it.

- 2026-08-06 — **The analytic core of the asymptotic layer is built: Lie–Trotter and
  Golden–Thompson.**  Two modules, in the `HTGeometry` umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`:

  ```text
  LieTrotterProduct.lean    tendsto_pow_exp_smul_inv, norm_exp_le_exp_norm, norm_pow_sub_pow_le
  GoldenThompsonNorm.lean   norm_exp_half_mul_exp_half_sq_le, norm_exp_add_le
  ```

  ```text
  (exp (A/n) * exp (B/n)) ^ n → exp (A + B)                     in any Banach algebra
  ‖exp (x/2) * exp (y/2)‖ ^ 2 ≤ ‖exp x * exp y‖                 Cordes at exponent 1/2
  ‖exp (x + y)‖ ≤ ‖exp x * exp y‖                               Golden–Thompson for the norm
  ```

  Mathlib has neither the product formula nor Golden–Thompson.  What it does have, and what makes
  the second line cheap, is **Löwner–Heinz** (`CFC.rpow_le_rpow`, `CFC.sqrt_le_sqrt`): the norm
  bound on `exp y exp (2x) exp y` is transported by conjugation with `exp (-y)` into
  `exp (2x) ≤ (c exp (-y)) ^ 2`, the square root turns that into `exp x ≤ c exp (-y)`, and a
  second conjugation with `exp (y/2)` returns Cordes.  Iterating Cordes makes the dyadic sequence
  `‖exp (2⁻ᵐ x) exp (2⁻ᵐ y)‖ ^ 2 ^ m` non-increasing, and the product formula identifies
  `‖exp (x + y)‖` as a limit of terms below it.

  The product formula is proved by the quantitative two-line estimate: the defect
  `exp (tA) exp (tB) − exp (t(A+B))` has vanishing derivative at `t = 0`, hence is `o(t)`, and
  `‖x ^ n − y ^ n‖ ≤ n M ^ n ‖x − y‖` for `‖x‖, ‖y‖ ≤ M`, `1 ≤ M`; taking
  `M = exp ((‖A‖+‖B‖)/n)`, whose `n`-th power is constant, turns `o(1/n)` into `o(1)`.

  This is the missing input for the exponential-metric-increasing inequality
  `‖H − K‖ ≤ d (exp H) (exp K)`, which is what makes rays with distinct directions non-asymptotic
  outside a common flat, and hence what the boundary-at-infinity layer of `(3)` needs.

- 2026-08-06 — **The exponential metric increasing property, and the boundary is faithful.**
  `formal/GaloisForLFunctions/HTGeometry/ExponentialMetricIncreasing.lean`, in the umbrella,
  axioms `[propext, Classical.choice, Quot.sound]`.

  ```text
  eigenvector_le_observerDist :
    (S - T) v = μ • v,  v ≠ 0   →   μ ≤ observerDist (exp T) (exp S)

  exists_pos_le_observerDist_metricRay :
    tr (S - T) = 0,  S ≠ T      →   ∃ c > 0, ∀ t ≥ 0,
      c * t ≤ observerDist (exp (t T)) (exp (t S))
  ```

  The second is the card's boundary-faithfulness statement in full generality: **two rays with
  distinct traceless directions diverge linearly**, with no assumption that the directions commute.
  The flat case was the Euclidean computation of `observerDist_diagOp`; that argument is blind to
  the case of two directions with the *same spectrum in different frames*, which is exactly where
  the curvature lives, and there the elementary test-vector estimates all return zero.  What
  supplies it is the exponential metric increasing property, whose analytic input is the
  Golden–Thompson inequality of the previous entry.

  The chain, all of it now formal: `observerDist` dominates `log` of the operator norm of the
  relative form (the ℓ² norm of the log-spectrum dominates its ℓ^∞ norm, and the operator norm of a
  positive form is one of its eigenvalues); the relative form of two rays is
  `exp (-T/2) exp S exp (-T/2)`, whose norm is `‖exp (S/2) exp (-T/2)‖ ^ 2` by the C⋆-identity;
  Golden–Thompson bounds that below by `‖exp ((S-T)/2)‖ ^ 2 = ‖exp (S - T)‖`; and that is at least
  `exp μ` for any eigenvalue `μ` of `S - T`.  Finally a nonzero traceless Hermitian direction has a
  positive eigenvalue, and the scaling `t ↦ t (S - T)` gives the linear rate.

  Supporting lemmas of independent use: the operator norm of a form diagonal in a frame is bounded
  by the sup of `|w i|` (`norm_toCLM_diagOp_le`), the inverse square root of a ray is the ray at
  parameter `-1/2` (`invSqrtOp_metricRay`), and `exp` of a direction dominates `exp` of each of its
  eigenvalues (`exp_le_norm_metricRay_of_eigenvector`).

- 2026-08-06 — **The boundary at infinity is constructed, and its points are the flags.**
  Two modules, in the `HTGeometry` umbrella, axioms `[propext, Classical.choice, Quot.sound]`:

  ```text
  ObserverBoundaryAtInfinity.lean   observerRay, Asymptotic, not_asymptotic_observerRay,
                                    asymptotic_iff_eigenSum_eq, eq_of_asymptotic,
                                    observerDist_metricRay_diagOp_unit
  ObserverBoundaryBuilding.lean     exists_traceless_isSymmetric_eigenSum_eq,
                                    exists_observerRay_eigenSum_eq
  ```

  The asymptote relation on rays is defined (`Asymptotic γ δ ↔ the distance stays bounded`), shown
  reflexive, symmetric and transitive, and then computed:

  ```text
  Asymptotic (ray T) (ray S)  ↔  ∀ c, eigenSum T c = eigenSum S c      (traceless T, S)
  ```

  **The asymptote class of a ray is exactly its degeneration flag** — the card's
  metric-degeneration description upgraded from a dictionary to an equivalence.  The forward
  direction is the exponential metric increasing property of the previous entry; the backward
  direction is that a direction is determined by its flag.

  The correspondence is onto: `exists_traceless_isSymmetric_eigenSum_eq` realizes **every** flag of
  the building by a *traceless* direction, hence by a ray that stays inside the determinant-one
  space `X_N`.  Tracelessness is free because adding a scalar shifts the flag thresholds without
  moving the flag.  So asymptote classes of rays based at the reference metric and simplices of the
  horizon building correspond bijectively, which is `(3)` at the level of points.

  Inside an apartment the Tits metric is computed:

  ```text
  observerDist (exp (t · diagOp b w)) (exp (t · diagOp b w')) = |t| · √(2 - 2 ⟪w, w'⟫)
  ```

  for unit weight vectors, so the divergence rate is `2 sin (θ/2)` for the Euclidean angle `θ`
  between the directions: the boundary of a maximal flat carries the spherical metric, which is
  the Tits metric of an apartment.

  What `(3)` still lacks is the *equivariance* at boundary level — that the congruence action of
  the observer group on rays induces the conjugation action on flags.  The two halves of that are
  already present separately (`eigenSum_conj` on the flag side, and the congruence-invariance of
  the distance on the metric side); only their combination is unwritten.

- 2026-08-06 — **The correspondence is equivariant for the stabiliser of the reference metric.**
  `formal/GaloisForLFunctions/HTGeometry/ObserverBoundaryEquivariance.lean`, in the umbrella,
  axioms `[propext, Classical.choice, Quot.sound]`.

  ```text
  isSymmetric_conjOp, trace_conjOp   conjugation by an isometry preserves Hermiticity and trace
  eigenSum_conjOp                    eigenSum (g T g⁻¹) c = (eigenSum T c).map g
  asymptotic_conjOp_iff              Asymptotic (ray (gTg⁻¹)) (ray (gSg⁻¹)) ↔ Asymptotic (ray T) (ray S)
  conjOp_smul_eq                     scalars act trivially, so the action is projective
  ```

  With the previous entry this is `(3)` for the stabiliser `SU(N)` of the reference metric: the
  boundary point of a conjugated ray is the conjugated flag, and the correspondence between
  asymptote classes and simplices of the horizon building intertwines the two actions.  Note that
  the equivariance needs no metric input at all once the asymptote class has been identified with
  the flag — it is inherited from the flag side.

  Two items remain before `(3)` is encoded in full: equivariance for the whole observer group
  rather than the stabiliser, which needs the basepoint-change theorem (every ray is asymptotic to
  exactly one ray from any prescribed point — the CAT(0) statement), and the Tits metric between
  boundary points of *different* apartments.

- 2026-08-06 — **The observer group acts by isometries.**
  `formal/GaloisForLFunctions/HTGeometry/ObserverCongruenceIsometry.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  ```text
  congrOp g P = g* P g                                    the congruence action
  observerDist (g* P g) (g* Q g) = observerDist P Q       (observerDist_congrOp)
  ```

  for an arbitrary symmetry `g` of the observer space — not only for the isometries fixing the
  reference metric.  With the orbit description of `(1)` this is the statement that the observer
  group acts on `X_N` by isometries, which is the missing metric half of the `PGL`-equivariance of
  `(3)`: the boundary at infinity is now an object on which the whole group acts, not only its
  basepoint stabiliser.

  The mechanism avoids any eigenvalue-uniqueness theory.  The operator

  ```text
  X = (g* P g)^(-1/2) g* P^(1/2)
  ```

  preserves inner products (`inner_congrIntertwine`) — the computation uses only that the inverse
  square root squares to the inverse and that `g* P g` inverts `g⁻¹ P^(-1/2)` — and it carries the
  eigenframe of the relative form of `(P, Q)` onto an eigenframe of the relative form of the
  congruated pair with the *same* weights.  Since the distance is the Euclidean norm of the
  logarithms of those weights, it is unchanged.

  Supporting facts of independent use: `invSqrtOp_comp_invSqrtOp` (the inverse square root squares
  to the inverse), `apply_invSqrtOp` (`P P^(-1/2) = P^(1/2)`), and the symmetry and positive
  definiteness of the congruate.

- 2026-08-06 — **The distance is bounded by the pencil norms** — the converse of the exponential
  metric increasing property.  `formal/GaloisForLFunctions/HTGeometry/ObserverDistNormBound.lean`,
  in the umbrella, axioms `[propext, Classical.choice, Quot.sound]`.

  ```text
  ‖P⁻¹ Q‖ ≤ C,  ‖Q⁻¹ P‖ ≤ C,  1 ≤ C   →   observerDist P Q ≤ √n · log C
  ```

  EMI turns a spectral gap into a lower bound on the distance; this turns operator estimates into
  an *upper* bound, which is what any boundedness statement about two rays needs — in particular
  the basepoint change, the last open item of `(3)`.

  The mechanism is short: `P^(-1/2)` carries an eigenvector of the relative form to an eigenvector
  of `P⁻¹ Q` with the same eigenvalue, and the same vector is an eigenvector of `Q⁻¹ P` with the
  reciprocal eigenvalue, so every `|log λ|` is at most `log C` and the Euclidean norm of the
  logarithms is at most `√n log C`.

  With this the remaining mathematics of the basepoint change is an operator estimate rather than a
  metric one.  The shape of that estimate, worked out on paper: writing `g = u p` in polar form, the
  ray `t ↦ g* exp (t T) g` is `t ↦ p exp (t u* T u) p`, and its candidate limit direction is the one
  whose flag is `p (eigenSum T c)` with the *same* thresholds.  Expanding
  `p⁻¹ exp (-t T) p⁻¹ exp (t S)` in the two spectral resolutions, the coefficient of
  `exp (t (σ_j - τ_i))` vanishes whenever `σ_j > τ_i`, precisely because
  `p⁻¹ (S-eigenspace σ_j) ⊆ eigenSum T (σ_j - ε)`; so the sum is bounded for `t ≥ 0`, and
  symmetrically for the inverse.

- 2026-08-06 — **Eigenframes in decreasing order, and the flag as an initial segment.**
  `formal/GaloisForLFunctions/HTGeometry/AntitoneEigenframe.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  ```text
  exists_antitone_eigenframe    every direction has an orthonormal eigenframe with antitone weights
  gt_set_eq_empty_or_Iic        above a threshold the indices form an initial segment
  eigenSum_eq_span_initial      eigenSum T c is ⊥ or the span of b '' Set.Iic k
  ```

  This is the shape in which the flag is transported by a symmetry.  The basepoint change needs a
  direction `S` with `eigenSum S c = (eigenSum T c).map g*` **at the same thresholds**; realizing it
  by the corpus's graded-piece construction would require enumerating the distinct eigenvalues,
  whereas an antitone frame makes every flag member the span of an initial segment — and initial
  segments are exactly what Gram–Schmidt preserves (`span_gramSchmidt_Iic`).  So `S` will be the
  frame obtained by orthonormalising `g* b` in decreasing order, weighted by the same eigenvalues.

- 2026-08-06 — **Flag transport: the limit direction of a moved ray exists.**
  `formal/GaloisForLFunctions/HTGeometry/FlagTransport.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  ```text
  exists_isSymmetric_eigenSum_map :
    ∀ g T, ∃ S, S.IsSymmetric ∧ ∀ c, eigenSum S c = (eigenSum T c).map g*
  ```

  The thresholds are the *same*, which is what the basepoint change needs and what the corpus's
  graded-piece realization does not give: it realizes a flag with thresholds of its own choosing.
  The construction is Gram–Schmidt in an eigenframe ordered by decreasing eigenvalue.  There every
  flag member is the span of an initial segment (previous entry), initial spans are exactly what
  Gram–Schmidt preserves (`span_gramSchmidt_Iic`), and normalisation does not move a span
  (`span_image_of_smul`), so orthonormalising `g* b` in that order and weighting by the same
  eigenvalues gives the required direction.

  This is the direction the basepoint change assigns to the ray `t ↦ g* exp (t T) g`.  What remains
  of `(3)` is the estimate that the two rays stay a bounded distance apart, whose paper proof is in
  the entry above and whose metric half — turning the two operator bounds into a bounded distance —
  is `observerDist_le_of_norm_le`.

  By-products: `adjoint_equiv_injective` (the adjoint of a symmetry is injective) and
  `span_gramSchmidtOrthonormalBasis_Iic` (the Gram–Schmidt *orthonormal basis*, not only the
  unnormalised family, preserves initial spans — mathlib states this only for the unnormalised
  one).

- 2026-08-06 — **Triangularity of the transported frame.**
  `formal/GaloisForLFunctions/HTGeometry/TriangularFrames.lean`, in the umbrella, axioms
  `[propext, Classical.choice, Quot.sound]`.

  ```text
  (g*)⁻¹ (gs j) ∈ span (b '' Set.Iic j)        adjoint_symm_gramSchmidt_mem_span
  g* (b i)      ∈ span (gs '' Set.Iic i)       mem_span_gramSchmidtOrthonormalBasis
  ```

  These are the two facts that make the estimate work, and the reason the argument needs no
  spectral projections at all.  Expanding the pencil `P⁻¹Q = g⁻¹ e^(-tT) (g*)⁻¹ e^(tS)` on the
  transported frame gives

  ```text
  (P⁻¹Q) (gs j) = ∑_i ⟪b i, (g*)⁻¹ (gs j)⟫ · e^(t (w j - w i)) · g⁻¹ (b i),
  ```

  where triangularity kills every term with `i > j`, and antitonicity of the weights makes
  `w j - w i ≤ 0` on the surviving terms — so the exponentials are bounded by `1` for `t ≥ 0` and
  the whole expression is bounded uniformly.  The mirror expansion, using the second inclusion,
  bounds `Q⁻¹P`.

  Also recorded here, both elementary and reusable: `norm_toCLM_le_sum_norm_apply` (an operator's
  norm is at most the sum of the norms of its values on an orthonormal frame) and
  `inner_eq_zero_of_mem_span_Iic` (a vector spanned by an initial segment of a frame has vanishing
  coordinates beyond it).

- 2026-08-06 — **Basepoint change: the boundary is independent of the basepoint, and the
  observer group acts on it through flags.**  This closes the equivariance half of `2 -> 3`.
  `formal/GaloisForLFunctions/HTGeometry/BasepointChange.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  - `exists_asymptotic_observerRay` — for every symmetry `g` and every Hermitian direction `T`
    there is a direction `S` with `Asymptotic (movedRay g hT) (observerRay hS)` and
    `eigenSum S c = (eigenSum T c).map g*` at every threshold.  So a ray that has been moved off
    the reference metric still has a boundary point, that point is the ray of a reference
    direction, and the direction is the one carrying the transported flag.
  - `asymptotic_movedRay` — the estimate itself, from a pair of frames.
  - `movedRay`, `dist_movedRay` — the moved ray as a curve of observer metrics.

  The mechanism is a pair of uniform pencil bounds, in
  `formal/GaloisForLFunctions/HTGeometry/MovedRayPencil.lean`:

  - `pencil_apply` — with `P = g* exp (t T) g` and `Q = exp (t S)`,
    `(P⁻¹ Q) (gs j) = ∑ i, exp (t (w j - w i)) ⟪b i, (g*)⁻¹ (gs j)⟫ · g⁻¹ (b i)`.
  - `mirror_pencil_apply` — the same expansion in the other direction, on both frames.
  - `norm_pencil_le`, `norm_mirror_pencil_le` — both pencils are bounded uniformly in `t ≥ 0`.
  - `invOp_congrOp_metricRay` — the inverse of a moved ray is the moved inverse; proved from
    `invOp_eq_of_left_inverse`, that the spectral inverse is *any* left inverse.
  - `metricRay_expand`, `invOp_metricRay_expand` — a ray and its inverse in an eigenframe.

  Why the estimate closes: the exponent `t (w j - w i)` appears only for `i ≤ j`, because the
  Gram–Schmidt frame of the images is triangular against the original frame; and there
  antitonicity of the weights makes the exponent nonpositive.  So no exponential survives, the
  bound is a fixed sum of frame coordinates, and `observerDist_le_of_norm_le` turns the two
  operator bounds into a bounded distance.  The same construction supplies the flag identity, via
  the extracted `eigenSum_diagOp_eq_map` in `FlagTransport.lean` — the flag computation of
  transport, now stated from a pair of frames rather than only existentially.

  Note that no curvature, no polar decomposition and no operator-exponential derivative enters:
  the whole equivariance statement rests on triangularity plus the order of the weights.

  Audit: `lake build GaloisForLFunctions.HTGeometry` green, 15118 jobs.

- 2026-08-06 — **Cordes' inequality at a general exponent**, the analytic input for the one
  remaining item.  `formal/GaloisForLFunctions/HTGeometry/CordesGeneralExponent.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  - `norm_exp_smul_mul_exp_smul_le` — for self-adjoint `x, y` in a C⋆-algebra and `s ∈ [0,1]`,
    `‖exp (s x) * exp (s y)‖ ≤ ‖exp x * exp y‖ ^ s`.
  - `exp_rpow` — `(exp x) ^ s = exp (s x)`, the functional-calculus power of an exponential.
  - `exp_smul_one`, `exp_smul_sub` — exponentials with a scalar absorbed into the exponent.

  The corpus already had this at `s = 1/2` only.  The general exponent is the same proof —
  conjugate, take the root, conjugate back — with operator monotonicity of the square root
  replaced by operator monotonicity of the `s`-th power.  What makes the middle step available is
  writing the normalising scalar as part of the exponent, `z = (log c) 1 - y`: the functional
  calculus is then applied only to exponentials, where `(exp x) ^ s = exp (s x)`, and no
  scalar-versus-power algebra is needed.

  Its purpose: the remaining card item, the Tits metric across apartments, is the divergence rate
  `lim_{t→∞} d (exp (t T), exp (t S)) / t`.  Boundedness of `d / t` by `2` is already available
  from the triangle inequality; monotonicity is the geodesic homothety contraction
  `d (exp (λ X), exp (λ Y)) ≤ λ d (exp X, exp Y)`, which is Araki–Lieb–Thirring, which is this
  inequality applied on the `k`-th compound.  Monotone and bounded gives the limit.

  Audit: `lake build GaloisForLFunctions.HTGeometry` green, 15122 jobs.

- 2026-08-06 — **The homothety contraction in the operator order.**
  `formal/GaloisForLFunctions/HTGeometry/CordesGeneralExponent.lean`, axioms
  `[propext, Classical.choice, Quot.sound]`:

  - `exp_smul_le_of_exp_le` — for self-adjoint `x, y`, `0 < c` and `s ∈ [0,1]`,

    ```text
    exp y ≤ c exp x   →   exp (s y) ≤ c ^ s exp (s x).
    ```

  This is the order form of the contraction the last card item needs, and it turns out to need
  *no norms at all*: operator monotonicity of the `s`-th power applied to the hypothesis gives it
  directly, once the scalar is carried inside the exponent as `z = (log c) 1 + x`, where the power
  acts on it as an ordinary real power.  Cordes' inequality is the norm form of the same fact and
  remains the tool for the compound step.

  What this reduces the remaining item to: with `Π_k` the largest `k`-fold subset product of the
  pencil spectrum, applying this on the `k`-th compound gives `Π_k (A_λ) ≤ (Π_k (A_1)) ^ λ`, which
  is the log-majorization; Karamata then gives the homothety contraction of the distance itself,
  hence monotonicity of the divergence rate.

  Audit: `lake build GaloisForLFunctions.HTGeometry` green, 15124 jobs.
