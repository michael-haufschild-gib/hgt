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
- [ ] 2 -> 3: parent reconstruction core formalized; the Tits boundary of `SL_N(C)/SU(N)` as a
  metric object (symmetric-space distance, geodesic asymptote classes, Tits metric) is still
  unavailable in Lean, so `(3)` itself is not encoded
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
