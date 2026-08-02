# Adelic Kummer nuclear test scale

- **ID:** `deninger-adelic-kummer-nuclear-test-scale`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE`
- **Parent:** `deninger-adelic-kummer-gelfand-triple`
- **Statement:** logarithmic Kummer functions admit a canonical nuclear
  locally constant test-space closure densely embedded in the mixed
  Banach and adelic Hilbert completions.

## Setup

Let \(Y\) be the Allcock--Vaaler space.  It is a second-countable,
zero-dimensional, locally compact space, decomposed into compact-open
place components.  Let
\[
 \mathcal D(Y)=C_c^{\mathrm{lc}}(Y,\mathbb R)
\]
with its usual locally constant test-function topology.

Choose an increasing cofinal tower of finite Galois extensions of
\(\mathbb Q\) and an increasing exhaustion of rational places.  Let
\(\mathcal D_m\) be the finite-dimensional space of functions supported
on the first \(m\) place components and constant on the clopen
partitions induced by the \(m\)-th field.  Then
\[
 \mathcal D(Y)=\underset{m}{\operatorname{ind\,lim}}\mathcal D_m.   \tag{1}
\]
The topology is independent of the chosen cofinal exhaustion.

Let \(\mathcal F_{\mathbb R}\) be the real span of logarithmic Kummer
functions and define
\[
 \mathcal S_{\mathrm{Kum}}
 =\overline{\mathcal F_{\mathbb R}}^{\,\mathcal D(Y)}.              \tag{2}
\]

## Theorem

`[PROVED HERE] [DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE]`

The space \(\mathcal D(Y)\) is a complete nuclear LF space and
\(\mathcal S_{\mathrm{Kum}}\) is a closed nuclear subspace.  There is a
dense continuous scale
\[
 \mathcal S_{\mathrm{Kum}}
 \longhookrightarrow
 E_{\mathrm{Kum}}
 \longhookrightarrow
 H_{\mathrm{Kum}}=L^2(Y,\lambda),                                  \tag{3}
\]
and hence continuous dual injections
\[
 H_{\mathrm{Kum}}
 \longhookrightarrow
 E_{\mathrm{Kum}}'
 \longhookrightarrow
 \mathcal S_{\mathrm{Kum}}'.                                      \tag{4}
\]
Together `(3)`--`(4)` form a source-native nuclear
test/Banach/Hilbert/distribution scale.

The integral
\[
 I(f)=\int_Yf\,d\lambda
\]
is continuous on \(\mathcal D(Y)\), and
\[
 \mathcal S_{\mathrm{Kum}}\subseteq\ker I.                          \tag{5}
\]
Galois maps, normalized field-norm projections, and Tate-twisted power
maps act continuously on the entire scale and preserve `(5)`.

For the logarithmic suspension coordinate \(t=\log u\), the completed
projective tensor product
\[
 \mathcal S_{\mathrm{susp}}
 =
 \mathcal S_{\mathrm{Kum}}
   \widehat\otimes_\pi C_c^\infty(\mathbb R)                         \tag{6}
\]
is nuclear.  Translation in \(t\), the rational shifts
\(t\mapsto t-\log q\), and convolution by a compactly supported smooth
test function act continuously on `(6)`.

## Proof

Each \(\mathcal D_m\) is finite-dimensional and nuclear.  The
inclusions in `(1)` have closed image, so `(1)` is a strict countable
inductive limit of finite-dimensional spaces.  Standard LF-space
theory makes \(\mathcal D(Y)\) complete and nuclear.  Closed subspaces
of nuclear locally convex spaces are nuclear, proving the first claim
for `(2)`.

The inclusions
\[
 \mathcal D(Y)\longrightarrow L^1(Y,\lambda)\cap L^2(Y,\lambda)
\]
are continuous: on each finite-dimensional stage every norm is
continuous, and the LF topology is final.  They restrict to
\(\mathcal S_{\mathrm{Kum}}\) and factor through the mixed completion
\(E_{\mathrm{Kum}}\).  Their images contain
\(\mathcal F_{\mathbb R}\).  By definition this span is dense in
\(E_{\mathrm{Kum}}\), and by Allcock--Vaaler it is dense in \(L^2\);
therefore the arrows in `(3)` have dense image.  The dual arrows in
`(4)` follow from the \(L^2\) pairing and restriction of continuous
functionals.

The integral is continuous on every finite-dimensional stage and hence
on the LF limit.  It vanishes on logarithmic Kummer functions by the
product formula, so it vanishes on their closure, proving `(5)`.
Galois and power maps permute/refine finite clopen stages.  Fili--Miner
field-norm projections are conditional expectations onto such stages.
Thus all stated operations are continuous and preserve the Kummer
span and its closure.

The standard test-function space \(C_c^\infty(\mathbb R)\) is nuclear,
and completed projective tensor products of nuclear locally convex
spaces are nuclear.  Translation and convolution are continuous on the
second factor, proving the suspension corollary `(6)`.

## Consequence for Deninger's program

The source coefficient now has separate canonical layers:

- nuclear locally constant test topology for distributions;
- its nuclear tensor with the smooth suspension test topology;
- mixed \(L^1/L^2\) topology for product formula and residue closure;
- \(L^2\) Hilbert topology for positive Kummer energy.

This is enough to type Deninger's desired distributional trace on a
source test space.  It is not enough to prove that a
test-function-smoothed flow operator is nuclear or trace class.  That
requires the uniform finite-stage estimates in
`DAC_PRO_NUCLEAR_KAHLER_TRACE_TOWER`.

## Gates

- [x] complete paper proof
- [ ] Lean formalization of strict LF nuclearity and dense embeddings
- [ ] sheafwise extension from Kummer functions to the full
  Steinberg-corrected Milnor coefficient and real orientation

## References

- Daniel Allcock and Jeffrey D. Vaaler, *A Banach space determined by
  the Weil height*: https://arxiv.org/abs/0808.1038
- Paul Fili and Zachary Miner, *Orthogonal decomposition of the space
  of algebraic numbers and Lehmer's problem*:
  https://arxiv.org/abs/0911.1975

## Log

- 2026-07-26 — Extracted the canonical nuclear test layer from the
  locally constant place-space geometry.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerNuclearTestScale.lean`, 15 declarations, axiom audit
for every one of them: `propext, Classical.choice, Quot.sound`.

**`(1)`, the inductive-limit test topology.**

- `deningerIndLimitTopology` — the finest topology on the limit for which every stage map is
  continuous, with `deningerIndLimit_continuous_stage`.
- `deningerIndLimit_continuous_iff` — **continuity out of the limit is stagewise**.  This is the
  proof's recurring move: the integral, and the inclusions into `L¹ ∩ L²`, are continuous on every
  finite-dimensional stage and therefore on the limit, because the limit topology is final.
- `deningerIndLimit_le_of_refines`, `deningerIndLimit_eq_of_refines` — **the topology is
  independent of the chosen cofinal exhaustion**, the sentence stated right after `(1)`.  Two
  exhaustions each of whose stages factors continuously through a stage of the other give the same
  topology.

**`(2)` and `(5)`, the Kummer test space and the vanishing of the integral.**

- `deningerKummerClosure` — the closure of the span of the Kummer functions, with
  `deningerKummerClosure_isClosed`: it is a closed subspace, which is `(2)`.
- `deningerKummerClosure_le_ker`, `_apply_eq_zero` — **`(5)`**: a continuous functional vanishing
  on the Kummer functions vanishes on the whole closed span, because its kernel is a closed
  subspace containing the span.  Combined with the product formula, which is what makes the
  integral vanish on the Kummer functions, this is exactly `𝒮_Kum ⊆ ker I`.
- `deningerKummerClosure_map_le`, `_map_ker` — **the operations preserve `(5)`**: a continuous
  operator preserving the span preserves the closed span, so Galois maps, normalized field-norm
  projections and Tate-twisted power maps act on the Kummer test space and keep the integral zero.

**`(3)`--`(4)`, the density and duality of the scale.**

- `deningerDenseRange_of_comp` — density propagates along the scale: once the Kummer span is dense
  in the last space, every arrow of the scale has dense image.
- `deningerDual_comp_injective` — **a dense continuous injection gives an injection of duals**,
  which is precisely how `(4)` is deduced from `(3)`.

### What cannot be stated in Lean, and why

Nuclearity itself cannot be stated.  mathlib has no locally convex spaces beyond normed spaces: no
seminorm-family topologies as a structure, no nuclear spaces, no LF spaces, no strict inductive
limits of locally convex spaces, and no completed projective tensor product.  So:

- "complete nuclear LF space", "closed nuclear subspace", and the nuclearity of the finite stages
  cannot be written down;
- `(6)`, the nuclearity of `𝒮_Kum ⊗̂_π C_c^∞(ℝ)`, cannot be written down, since the completed
  projective tensor product is absent;
- `E_Kum` and `H_Kum = L²(Y,λ)` exist in mathlib, but `𝒟(Y) = C_c^lc(Y,ℝ)` with its locally
  constant test topology does not, so the scale `(3)` cannot be instantiated on the actual spaces.

What is formalized is every step of the proof that is not about nuclearity: the inductive-limit
topology and its independence of the exhaustion, stagewise continuity, closedness of the Kummer
span, the vanishing of a continuous functional on it, its stability under the stated operations,
and the passage from a dense scale to a dual scale.  The card's second gate therefore splits: the
inductive-limit and dense-embedding half is done, and the nuclearity half is blocked on locally
convex space theory being absent from mathlib.

### Gates

- [x] Lean formalization of the inductive-limit test topology, its independence of the exhaustion,
  and the dense/dual scale arguments
- [ ] Lean formalization of nuclearity: blocked on mathlib having no locally convex, LF or nuclear
  space theory and no completed projective tensor product

### Log

- 2026-08-02 — Formalized the inductive-limit topology of `(1)`, the closed Kummer span and the
  vanishing `(5)` with its stability under the source operations, and the density/duality
  arguments of `(3)`--`(4)`.

### Nuclear operators, built

The blocker recorded above says nuclearity cannot be stated because mathlib has no nuclear space
theory.  The first missing piece is now built:
`formal/GaloisForLFunctions/RHTower/DeningerNuclearOperator.lean` (11 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout) defines nuclear *operators* between normed
spaces, which mathlib does not have in any form.

- `DeningerIsNuclear T` — `T` is a sum of rank-one maps `x ↦ φ_i(x) • y_i` with `∑ ‖φ_i‖‖y_i‖`
  summable.  The index type is arbitrary, which is equivalent to the usual sequential definition
  because a summable family has countable support, and makes the ideal proofs direct.
- `deningerIsNuclear_zero`, `deningerIsNuclear_smulRight`, `DeningerIsNuclear.add`, `.smul` — the
  nuclear maps form a submodule containing the rank-one maps.
- `DeningerIsNuclear.compL`, `.compR` — **nuclear maps are a two-sided ideal**: composing with any
  bounded map on either side preserves nuclearity.
- `DeningerIsNuclear.hasSum_smulRight` — **a nuclear map is the sum of its rank-one terms in the
  operator norm**, not merely pointwise; and `.norm_le` bounds the operator norm by the nuclear
  sum `∑ ‖φ_i‖‖y_i‖`.
- `deningerSmulRight_isCompactOperator`, `DeningerIsNuclear.isCompactOperator` — **a nuclear map
  is compact**, obtained by exhibiting it as an operator-norm limit of finite sums of rank-one
  maps, each compact because the image of a ball lies in the image of a compact ball of scalars
  under scaling by a fixed vector.

This is the operator-level half of nuclearity.  What still does not exist is the space-level
notion: a locally convex space is nuclear when for every continuous seminorm there is a dominating
one whose induced map between the associated normed quotients is nuclear.  mathlib has
`LocallyConvexSpace` and `WithSeminorms` but no seminormed quotients and no completed projective
tensor product, so the LF and Fréchet claims of this card remain out of reach; the operator input
they rest on is now available.

- 2026-08-02 — Built nuclear operators between normed spaces, the operator-level half of the
  nuclearity gate.

### Nuclear spaces, defined

The space-level half is now built too:
`formal/GaloisForLFunctions/RHTower/DeningerSeminormQuotient.lean` (19 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout).  mathlib has `Seminorm`, `WithSeminorms` and
`LocallyConvexSpace`, but it has no normed space attached to a seminorm, so the definition of a
nuclear space could not even be written; that gap is closed.

- `deningerSeminormKer` — the kernel of a seminorm as a submodule, and
  `deningerSeminorm_eq_of_sub_mem`: a seminorm is constant on its cosets.
- `DeningerSeminormSpace p` — **the normed space attached to a seminorm**, the quotient by the
  kernel, with its `NormedAddCommGroup` and `NormedSpace` instances built from an `AddGroupNorm`
  so that no competing norm is introduced.  `deningerSeminormMk_norm` says the norm of a class is
  the seminorm of a representative, by definition.
- `deningerSeminormComparison` — **the comparison map** induced by a domination `p ≤ C q`, with
  `_norm_le` bounding its operator norm by `C`.
- `DeningerIsNuclearSpace P` — **a nuclear locally convex space**: every defining seminorm is
  dominated by one whose comparison map is a nuclear operator, in the sense of
  `DeningerNuclearOperator`.
- `deningerIsNuclear_of_finiteDimensional` — **a map out of a finite-dimensional space is
  nuclear**, expanded over `Module.finBasis` as a finite sum of rank-one maps; hence
  `deningerIsNuclearSpace_of_finiteDimensional`: a space whose seminorm quotients are finite
  dimensional is nuclear.  That is exactly the card's "each finite stage is finite-dimensional and
  nuclear".

What remains between this and the card's claims is the permanence theory — closed subspaces,
countable products and projective limits of nuclear spaces are nuclear — and the completed
projective tensor product, neither of which exists yet.

- 2026-08-02 — Built the normed space attached to a seminorm and the definition of a nuclear
  space, with the finite-dimensional case proved.

### Nuclearity is independent of the defining family

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSpaceInvariance.lean` (7 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) makes the definition usable by proving
it is an invariant of the topology rather than of the chosen seminorms.

- `deningerSeminormComparison_ext` — a map out of a seminorm quotient is determined by its effect
  on classes of vectors; `_congr` — the comparison map does not depend on the domination constant;
  `_trans` — a chain of dominations gives the composite of the comparison maps.
- `deningerIsNuclearSpace_of_dominating` — **if two seminorm families dominate each other, one is
  nuclear exactly when the other is.**  A comparison map of the second family factors as
  `bounded ∘ nuclear ∘ bounded` through a comparison map of the first, and the ideal property of
  nuclear operators finishes it.
- `deningerIsNuclearSpace_comp` — **nuclearity may be tested on a cofinal subfamily**, the
  nuclearity counterpart of the statement that the test topology does not depend on the chosen
  cofinal exhaustion.

- 2026-08-02 — Proved that nuclearity does not depend on the defining seminorm family and may
  be tested on a cofinal subfamily.

### Bridge to the corpus trace-class theory

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSchattenBridge.lean` (2 declarations, axiom
audit `propext, Classical.choice, Quot.sound`) connects the new general notion to the Schatten
machinery the corpus already owns.

- `deningerSmulRight_hasRankLE_one` — a rank-one map has rank at most one in the
  approximation-number sense, its image lying in the line spanned by its vector.
- `DeningerIsNuclear.memSchattenClass_one` — **a nuclear operator on a Hilbert space is trace
  class**.  The operator-norm expansion `DeningerIsNuclear.hasSum_smulRight` is exactly the
  hypothesis of the corpus criterion `memSchattenClass_one_tsum_rankOneTerms_of_summable_norm`,
  which takes an arbitrary index type and needs no enumeration.

So on Hilbert spaces the general definition agrees with the corpus trace class, and the trace
norm, the ideal bounds and the additivity of the Schatten 1-class are available to it.

- 2026-08-02 — Bridged nuclear operators to the corpus Schatten 1-class on Hilbert spaces.

### Products of nuclear spaces

`formal/GaloisForLFunctions/RHTower/DeningerNuclearProduct.lean` (12 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout) proves the first permanence property.

- `deningerSeminormInduced` — **the map of normed spaces induced by a bounded linear map**, a
  linear map carrying one seminorm into a multiple of another.  The comparison map of two
  seminorms on one space is the case of the identity; the coordinate projections and the
  coordinate inclusions of a product are the other cases.
- `DeningerIsNuclear.sum` — a finite sum of nuclear maps is nuclear.
- `deningerPiSeminorm`, `deningerPiFamily` — the product presented by the seminorms that add
  finitely many coordinate seminorms, with `_proj_le` and `_single_eq_of_mem` relating it to the
  coordinates.
- `deningerIsNuclearSpace_pi` — **an arbitrary product of nuclear spaces is nuclear**, in
  particular a countable product.  The comparison map of two product seminorms is shown to be the
  finite sum, over the coordinates involved, of the coordinate comparison maps conjugated by the
  projection and the inclusion; each summand is nuclear by the ideal property and the sum by
  `DeningerIsNuclear.sum`.  The identification of that sum with the honest comparison map is the
  observation that a vector and the sum of its coordinate components differ by something the
  product seminorm does not see.

What is still missing for the cards is the other permanence property, closed subspaces.  That one
is not a formal consequence of the ideal property: the vectors of a nuclear representation of a
comparison map need not lie in the subspace, and the classical proof goes through the
Hilbert--Schmidt characterization, where subspaces are complemented.

- 2026-08-02 — Proved that products of nuclear spaces are nuclear.

### Hilbert--Schmidt composites are nuclear

`formal/GaloisForLFunctions/RHTower/DeningerHilbertSchmidtNuclear.lean` (4 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) supplies the bridge on which the
remaining permanence theory rests.

- `DeningerIsHilbertSchmidtOn` — the Hilbert--Schmidt condition relative to a Hilbert basis: the
  images of the basis vectors are square-summable.
- `deningerSummable_mul_of_sq` — a product of square-summable nonnegative families is summable, by
  the arithmetic-geometric mean inequality.  Only summability is needed, so no Cauchy--Schwarz.
- `deningerIsNuclear_comp_of_hilbertSchmidt` — **a composite of Hilbert--Schmidt maps is
  nuclear**.  Expanding a vector in a Hilbert basis `c` of the middle space writes
  `B (A x) = ∑ⱼ ⟨A* cⱼ, x⟩ · B cⱼ`, so the rank-one data is the adjoint of the first factor against
  the images of the second, and the norms `‖A* cⱼ‖ ‖B cⱼ‖` are summable by the previous lemma.
- `deningerMemSchattenClass_one_comp_of_hilbertSchmidt` — the same statement in the corpus
  Schatten language: a composite of Hilbert--Schmidt operators is trace class.

This is the classical route to the permanence properties that remain: subspaces of nuclear spaces
are nuclear because a nuclear map factors through Hilbert spaces, where subspaces are complemented
by orthogonal projection.  Still to build for that: the Hilbertian-seminorm refinement of a
nuclear space, and the converse factorization of a nuclear map through Hilbert--Schmidt maps.

- 2026-08-02 — Proved that a composite of Hilbert--Schmidt maps is nuclear.

### Parseval, and the Hilbert--Schmidt condition is intrinsic

`formal/GaloisForLFunctions/RHTower/DeningerHilbertSchmidtAdjoint.lean` (7 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) removes the basis from the previous
module's hypothesis.

- `deningerParseval_summable`, `deningerParseval` — **Parseval for a Hilbert basis**: the
  coefficients of a vector are square-summable with sum the squared norm.  mathlib has the
  Hilbert-basis isometry onto `ℓ²` but not this identity; it is read off from
  `lp.norm_rpow_eq_tsum` and `Memℓp.summable`.
- `deningerHilbertSchmidt_tsum_eq_adjoint` — **the Hilbert--Schmidt sum of a map equals that of
  its adjoint**.  Both are the sum of the squared absolute values of the matrix coefficients, in
  the two possible orders; the exchange is `ENNReal.tsum_comm`, which needs no summability
  hypothesis, so the statement is unconditional and holds with both sides infinite.
- `deningerIsHilbertSchmidtOn_adjoint_iff`, `deningerIsHilbertSchmidtOn_basis_independent` — the
  Hilbert--Schmidt condition transfers to the adjoint and **does not depend on the chosen basis**,
  so it is a property of the map alone.

Together with the previous module this gives the classical statement "a composite of
Hilbert--Schmidt maps is nuclear" with Hilbert--Schmidt in its usual, intrinsic sense.

- 2026-08-02 — Proved Parseval and the basis-independence of the Hilbert--Schmidt condition.

### Nuclear implies Hilbert--Schmidt

`formal/GaloisForLFunctions/RHTower/DeningerNuclearHilbertSchmidt.lean` (2 declarations, axiom
audit `propext, Classical.choice, Quot.sound`) closes the converse direction on Hilbert spaces.

- `deningerInner_adjoint_comp` — pairing `T* T` against a vector gives the squared norm of its
  image.
- `DeningerIsNuclear.isHilbertSchmidtOn` — **a nuclear operator on a Hilbert space is
  Hilbert--Schmidt**.  If `T` is nuclear so is `T* T`, by the ideal property, hence it is trace
  class and compact; the corpus's Horn-type majorization `sum_norm_inner_le_traceNorm` then bounds
  every finite partial sum of `‖T bₙ‖²` by the trace norm of `T* T`, which is summability.

With the previous two modules this places the nuclear operators inside the Hilbert--Schmidt ones
on Hilbert spaces, in both directions of the classical comparison.

- 2026-08-02 — Proved that a nuclear operator on a Hilbert space is Hilbert--Schmidt.

### Finite-rank maps and the usable nuclearity criterion

`formal/GaloisForLFunctions/RHTower/DeningerNuclearFiniteRank.lean` (2 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerIsNuclear_of_finiteRank` — **a map with finite-dimensional range is nuclear**.  The
  corestriction to the range, expanded over a basis of the range, is a finite sum of rank-one
  maps.  This is the complement of the earlier finite-dimensional-source case: there the basis is
  taken upstairs, here downstairs.
- `deningerIsNuclearSpace_of_finiteRank` — **a space whose comparison maps have finite rank is
  nuclear**.  This is the criterion one actually applies: no nuclear representation need be
  exhibited, only a dominating seminorm whose comparison map has finite-dimensional range.  It
  covers the finite stages of a test space directly, without passing through finite
  dimensionality of the whole stage.

- 2026-08-02 — Proved that finite-rank maps are nuclear, giving the finite-rank criterion for
  nuclear spaces.

### Nuclearity passes to the completions

`formal/GaloisForLFunctions/RHTower/DeningerNuclearCompletion.lean` (4 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout).

- `deningerCompletionFunctional`, `_coe`, `_norm_le` — **the extension of a continuous functional
  to the completion**, agreeing with the original on the image and with no larger norm.
- `DeningerIsNuclear.exists_completion` — **a nuclear map extends to a nuclear map of the
  completions**, agreeing with the original on the image of the source.

The extension is built rather than characterized: the functionals of a nuclear representation are
extended, the vectors are pushed into the completion of the target, and the resulting rank-one
family — whose norms are still summable, since extension does not increase functional norms — is
summed in the operator norm.  The extension is therefore nuclear by construction, which avoids
having to re-prove nuclearity for a map obtained by an abstract extension theorem.

This is the step that makes nuclearity of a locally convex space a statement about the *completed*
seminorm quotients, which is the classical definition and the one the permanence theory for closed
subspaces is formulated against.

- 2026-08-02 — Proved that a nuclear map extends to a nuclear map of completions.

### Subspaces, and the exact point where they are not formal

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSubspace.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout).

- `DeningerIsNuclear.of_comp_left_inverse` — if the left factor of a nuclear composite has a
  bounded left inverse, the right factor is nuclear.
- `deningerRestrictSeminorm`, `deningerSubspaceEmbedding` — the restriction of a seminorm to a
  subspace, and the induced embedding of quotients, which is isometric because the subspace
  seminorm *is* the restriction.
- `deningerIsNuclearSpace_subspace_of_leftInverse` — **a subspace whose quotient embeddings admit
  bounded left inverses is nuclear**.  The subspace comparison map followed by the embedding equals
  the ambient comparison map preceded by the embedding, which is nuclear by the ideal property;
  the left inverse brings it back.

This isolates the remaining analytic input precisely.  Everything about subspaces is now formal
*except* the complementation of the embedded quotient, and that is genuinely not formal: a nuclear
representation of the composite has its vectors in the ambient quotient, not in the subspace one.
Classically it is supplied by refining the presenting seminorms to Hilbertian ones, where a closed
subspace is complemented by orthogonal projection; that refinement is Grothendieck's factorization
of a nuclear map through a Hilbert space, and is what remains to be built.

- 2026-08-02 — Proved subspace permanence modulo complementation of the quotient embeddings,
  isolating the one remaining analytic input.

### Balancing a nuclear representation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearBalanced.lean` (2 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `DeningerIsNuclear.exists_balanced` — **a nuclear map has a representation in which every
  functional has the same norm as its vector**.  Each rank-one term is rescaled by a real scalar
  and its reciprocal, which changes neither the term nor the product of the two norms; terms where
  one factor vanishes are replaced by zero.
- `DeningerIsNuclear.exists_balanced_summable_sq` — in such a representation the *squares* of the
  functional norms are summable, since they are the terms of the original convergent series.

This is the normalization step of the factorization of a nuclear map through a Hilbert space: with
a balanced representation the coefficient map `x ↦ (φₐ x)ₐ` lands in `ℓ²` with norm at most
`(∑ ‖φₐ‖²)^{1/2} ‖x‖`, and the map is dominated by the resulting Hilbertian seminorm.

The rescaling needs real scalars to act, so it is stated over `RCLike` fields.  That is not an
artefact: over a field whose value group is discrete the norms of scalars cannot be adjusted
continuously, and exact balancing genuinely fails.

- 2026-08-02 — Proved that a nuclear representation can be balanced, with square-summable
  functional norms.

### The Hilbertian domination of a nuclear map

`formal/GaloisForLFunctions/RHTower/DeningerNuclearHilbertFactor.lean` (2 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `deningerTsum_mul_le_sqrt` — **Cauchy--Schwarz for sums**: for nonnegative square-summable
  families, `∑ f g ≤ (∑ f²)^{1/2} (∑ g²)^{1/2}`.  mathlib has the finite version
  `Finset.sum_mul_sq_le_sq_mul_sq` but not the summable one; it is obtained by bounding every
  partial sum.
- `DeningerIsNuclear.exists_hilbert_factor` — **a nuclear map is dominated by a Hilbertian
  seminorm**.  From a balanced representation the coefficient map `x ↦ (φₐ x)ₐ` lands in `ℓ²`, is
  bounded by `(∑ ‖φₐ‖²)^{1/2} ‖x‖`, and dominates the map: `‖T x‖ ≤ (∑ ‖φₐ‖²)^{1/2} ‖A x‖`.

Both inequalities are what the permanence theory needs.  The first says the Hilbertian seminorm
`x ↦ ‖A x‖` is continuous, so it may be inserted into a presenting family; the second says the
original comparison map factors through it.  Iterating this refinement makes a presenting family
Hilbertian, at which point the quotients are pre-Hilbert spaces and the embedding of a subspace
quotient is complemented — the hypothesis of
`deningerIsNuclearSpace_subspace_of_leftInverse`.

- 2026-08-02 — Proved that a nuclear map is dominated by a Hilbertian seminorm, with
  Cauchy--Schwarz for summable families.

### A nuclear space is presented by Hilbertian seminorms

`formal/GaloisForLFunctions/RHTower/DeningerHilbertianRefinement.lean` (3 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `DeningerIsHilbertianSeminorm` — a seminorm given by the norm of a linear map into an `ℓ²`
  space.
- `deningerNuclear_hilbertian_refinement` — **every seminorm of a nuclear space is squeezed by a
  Hilbertian one**: the comparison map is dominated by the norm of its `ℓ²` coefficient map, which
  is in turn dominated by the dominating seminorm.
- `deningerNuclear_exists_hilbertian_family` — **a nuclear space has a nuclear Hilbertian
  presentation**.  Choosing one squeeze per index gives a family that mutually dominates the
  original, and nuclearity transfers by the invariance theorem.

What remains for closed subspaces is a formulation issue rather than a missing theorem.  With a
Hilbertian presentation the seminorm quotients are pre-Hilbert, and the image of a subspace
quotient inside `ℓ²` is complemented by orthogonal projection onto its *closure* — so the left
inverse required by `deningerIsNuclearSpace_subspace_of_leftInverse` exists into the completion of
the subspace quotient, not into the quotient itself.  Closing the argument therefore means
restating nuclearity against the completed quotients, for which
`DeningerIsNuclear.exists_completion` already provides the transfer of nuclear maps.

- 2026-08-02 — Proved that a nuclear space has a nuclear Hilbertian presentation.

### The completed formulation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSpaceCompleted.lean` (9 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout).

- `DeningerSeminormCompletion`, `deningerSeminormMkC`, `_norm` — the Banach space attached to a
  seminorm, and the canonical map into it, whose norm is the seminorm.
- `deningerSeminormComparisonC`, `_coe` — **the completed comparison map**, defined as the
  extension of the composite `E_q → E_p → Ê_p` along the dense isometric embedding of `E_q`, and
  agreeing with the uncompleted comparison map on the image.
- `DeningerIsNuclearSpaceC` — **nuclearity in the classical, completed sense**.
- `DeningerIsNuclearSpace.toC` — **it follows from the uncompleted notion**.  The extension of the
  nuclear comparison map provided by `DeningerIsNuclear.exists_completion` agrees with the
  canonical completed comparison map on a dense set, hence equals it, so the canonical map is
  nuclear.

This is the formulation the closed-subspace argument is stated against: with the Hilbertian
presentation of the previous module, the completed quotients are Hilbert spaces, and the image of a
completed subspace quotient is a *closed* subspace of one, hence complemented by orthogonal
projection.

- 2026-08-02 — Built the completed formulation of nuclearity and derived it from the
  uncompleted one.

### Subspaces in the completed formulation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSubspaceCompleted.lean` (5 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout).

- `deningerSubspaceEmbedding_square` — the comparison square of a subspace before completion.
- `deningerSubspaceEmbeddingC`, `_coe`, `_square` — **the completed embedding of a subspace
  quotient and the completed comparison square**.  Commutativity after completion is inherited:
  both composites are continuous and agree on the dense image of the uncompleted quotient.
- `deningerIsNuclearSpaceC_subspace_of_leftInverse` — **a subspace whose completed quotient
  embeddings admit bounded left inverses is nuclear in the completed sense.**

At the completed level the left-inverse hypothesis is the honest one.  With the Hilbertian
presentation the completed quotients are Hilbert spaces and the image of a completed subspace
quotient is a *closed* subspace, hence complemented by orthogonal projection — whereas before
completion only the closure of the image is complemented, which is exactly why the uncompleted
version of this theorem could not be discharged.

- 2026-08-02 — Proved completed subspace permanence modulo the complementation hypothesis,
  now stated where it is actually satisfiable.

### The `ℓ²` embedding of a Hilbertian quotient

`formal/GaloisForLFunctions/RHTower/DeningerHilbertianEmbedding.lean` (10 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout).

- `deningerHilbertianEmbedding`, `_norm`, `_isometry` — a Hilbertian seminorm's defining map kills
  the kernel of the seminorm, so it induces an **isometric embedding of the seminorm quotient into
  `ℓ²`**.
- `deningerHilbertianEmbeddingC`, `_coe`, `_norm`, `_isometry` — the extension to the completion,
  still isometric: the two continuous functions `‖J w‖` and `‖w‖` agree on the dense image.
- `deningerHilbertianEmbeddingC_isClosed_range` — **the extended embedding has closed range**,
  since an isometry out of a complete space has complete, hence closed, range.

A closed subspace of `ℓ²` is complemented by orthogonal projection, so this is the last structural
ingredient of the bounded left inverse that
`deningerIsNuclearSpaceC_subspace_of_leftInverse` requires.

- 2026-08-02 — Built the isometric `ℓ²` embedding of a Hilbertian seminorm quotient and its
  completion, with closed range.

### Subspaces of a Hilbertian nuclear space are nuclear

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSubspaceHilbertian.lean` (16 declarations,
axiom audit `propext, Classical.choice, Quot.sound` throughout).

The complementation hypothesis of the previous step is now **discharged**, so permanence under
subspaces is unconditional for a Hilbertian presentation.

- `deningerSubspaceEmbedding_norm`, `deningerSubspaceEmbeddingC_norm`, `_isometry`,
  `_isClosed_range`, `_injective` — the seminorm of a subspace being the restriction of the
  ambient one, the induced map of quotients **preserves norms**, and so does its extension to the
  completions; an isometry out of a complete space therefore has closed image.
- `deningerRestrict_hilbertian` — the restriction of a Hilbertian seminorm is Hilbertian, with
  defining map `A ∘ₗ F.subtype`.
- `deningerHilbertianEmbeddingC_subspace` — the ambient and the subspace `ℓ²` embeddings are
  **compatible**: `J_E ∘ emb = J_F`, proved by density on the image of the uncompleted quotient.
- `deningerSubspaceRange`, `_coe`, `_completeSpace` — the image of the completed subspace quotient
  is a closed, hence complete, subspace of `ℓ²`.
- `deningerSubspaceRangeEquiv`, `_coe` — the completed subspace quotient is **isometrically
  isomorphic to that image**, the corestricted embedding being a surjective linear isometry.
- `deningerSubspaceLeftInverse`, `deningerSubspaceLeftInverse_comp` — **the bounded left inverse**:
  send the ambient class into `ℓ²`, project orthogonally onto the closed image, undo the isometry.
  The compatibility puts `J_E (emb v)` inside the image, where the projection is the identity, so
  the composite returns `v`.
- `deningerIsNuclearSpaceC_subspace_of_hilbertian`,
  `deningerIsNuclearSpace_subspace_of_hilbertian` — **a subspace of a nuclear space presented by
  Hilbertian seminorms is nuclear**, in the completed sense, from either form of the hypothesis.

Combined with `deningerNuclear_exists_hilbertian_family` — every nuclear space *has* a Hilbertian
presentation — this is the substance of permanence under subspaces.  What is still missing to
state it for an arbitrary presentation is the completed analogue of
`deningerIsNuclearSpace_of_dominating`: transporting completed nuclearity along two mutually
dominating families, which needs a composition law for the completed comparison maps.

- 2026-08-02 — Discharged the complementation hypothesis; subspaces of a Hilbertian nuclear space
  are unconditionally nuclear.

### Permanence under subspaces, for any presentation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearCompletedInvariance.lean` (6 declarations,
axiom audit `propext, Classical.choice, Quot.sound` throughout).

The restriction to a Hilbertian presentation is now removed.

- `deningerSeminormComparisonC_ext` — a map out of a completed seminorm quotient is determined by
  its values on the classes of vectors, these being dense in the completion.
- `deningerSeminormComparisonC_congr`, `_trans` — the completed comparison maps obey the same
  calculus as the uncompleted ones: the constant is irrelevant, and a chain of dominations
  composes.
- `deningerIsNuclearSpaceC_of_dominating`, `deningerIsNuclearSpaceC_comp` — **completed nuclearity
  is an invariant of the topology**, not of the chosen family: it transfers between mutually
  dominating families and may be tested on any cofinal subfamily.
- `deningerIsNuclearSpaceC_subspace` — **every subspace of a nuclear space is nuclear.**  Take the
  Hilbertian presentation supplied by `deningerNuclear_exists_hilbertian_family`, apply subspace
  permanence there, and transfer back along the two dominations, which restrict to the subspace.

This is the permanence theorem in the form the nuclear test scale of this card uses: the steps of
the strict inductive limit are subspaces of the ambient test space, and their nuclearity is now a
theorem rather than an assumption, for whatever family the ambient space is presented by.

- 2026-08-02 — Subspace permanence proved unconditionally for an arbitrary nuclear presentation.

### A nuclear test scale that is not finite dimensional

`formal/GaloisForLFunctions/RHTower/DeningerRapidSequenceSpace.lean` (14 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerRapidSequenceNuclear.lean` (11 declarations), axiom
audit `propext, Classical.choice, Quot.sound` throughout.

Until now the only spaces known to be nuclear in the corpus were the finite dimensional ones, so
every permanence theorem above was formally true but carried no infinite dimensional content.  It
does now.

- `DeningerRapidCarrier`, `deningerRapidSeminorm` — the **rapidly decreasing sequences**: those
  whose polynomial multiples are all square-summable, graded by the weighted `ℓ²` seminorms
  `‖(n+1)^k a n‖`.  `deningerRapidSeminorm_hilbertian` — each is Hilbertian by construction;
  `deningerRapidSeminorm_le` — they increase with the weight;
  `deningerRapidWeight_norm_mul_le` — each controls every weighted coordinate;
  `deningerRapidSeminorm_basis` — the basis vector `e_n` has `k`-th seminorm exactly `(n+1)^k`.
- `deningerHasSum_of_hilbertian` — a series converges in a Hilbertian seminorm quotient as soon
  as its image in `ℓ²` converges, the embedding being an isometry.
- `deningerRapid_hasSum_basis` — **a rapidly decreasing sequence is the sum of its coordinates**,
  in every weighted quotient; obtained from `lp.hasSum_single` through that transfer.
- `deningerRapidCoeff`, `_norm_le` — the coordinate functionals of the quotients, of norm at most
  `(n+1)^{-k}`, constructed by lifting `a ↦ a n` across the kernel of the seminorm.
- `deningerRapid_isNuclearSpace`, `deningerRapid_isNuclearSpaceC` — **the rapidly decreasing
  sequences form a nuclear space.**  The comparison map from the `(k+2)`-nd to the `k`-th
  quotient is the series of rank one maps `φ_n ⊗ [e_n]`, and `‖φ_n‖ ‖[e_n]‖ ≤ (n+1)^{-2}` is
  summable.
- `deningerRapidBasis_linearIndependent`, `deningerRapid_not_finiteDimensional` — the space is
  **not finite dimensional**, so the nuclearity theory is not exhausted by the trivial case.
- `deningerRapid_subspace_isNuclearSpaceC` — every subspace of it is nuclear, the permanence
  theorem applied to a space that actually inhabits the hypothesis.

- 2026-08-02 — Built the model nuclear space; the nuclearity theory of this card is no longer
  vacuous in infinite dimensions.

### The test space of the card is nuclear, and so is its Kummer subspace

`formal/GaloisForLFunctions/RHTower/DeningerFinestNuclear.lean` (16 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerLocallyConstantTestSpace.lean` (12 declarations),
axiom audit `propext, Classical.choice, Quot.sound` throughout.

This is the first half of the proof of `[DAC_ADELIC_KUMMER_NUCLEAR_TEST_SCALE]` — the statement
that `𝒟(Y)` is nuclear and `𝒮_Kum ⊆ 𝒟(Y)` is a nuclear subspace — formalized without the
inductive-limit machinery, by going directly to the property that makes `(1)` work.

**The finest locally convex topology.**

- `deningerBasisSeminorm`, `deningerBasisSeminorm_coord_le`, `deningerSeminorm_le_basisSeminorm` —
  a basis and a positive weight sequence define a weighted `ℓ¹` seminorm; it dominates any
  seminorm whose values on the basis are dominated by the weights, and it controls every
  coordinate.
- `deningerBasisCoeff`, `_norm_le` — the coordinate functionals of its quotient, of norm at most
  the inverse weight.
- `deningerIsNuclearSpace_finest` — **the family of *all* seminorms on a space with a basis
  indexed by `ℕ` is nuclear.**  For a given `p`, the weights `2^n (p (b n) + 1)` give a dominating
  seminorm whose comparison map is `∑ φ_n ⊗ [b n]` with `‖φ_n‖ ‖[b n]‖ ≤ 2^{-n}`.
- `deningerIsNuclearSpace_finest_of_countable`, `deningerIsNuclearSpaceC_finest_subspace` — the
  same for any countable index (a finite basis gives finite dimensional quotients), and hence
  **every subspace of a countable-dimensional space is nuclear**.

**The test space.**  `Y` second countable and Hausdorff — the properties of the Allcock–Vaaler
space that the argument actually uses.

- `deningerCompactOpens_countable` — **a second countable space has only countably many compact
  open sets**: each is a finite union of basic opens, and the finite subsets of a countable basis
  are countable.
- `DeningerTestSpace` — the locally constant compactly supported real functions, a submodule of
  all functions; `deningerSupport_isClosed` — the support of a locally constant function is
  clopen, which is what makes the support of a sum compact.
- `deningerIndicator_isLocallyConstant`, `deningerIndicator_mem`, `deningerTestIndicators` — the
  indicators of compact open sets are test functions, and there are countably many of them.
- `deningerTestSpace_range_finite`, `deningerTestIndicators_span` — **a test function takes
  finitely many values and is the sum, over its nonzero values, of the value times the indicator
  of its level set**, which is compact open; so those indicators span the test space.
- `deningerTestSpace_isNuclearSpace` — **the test space `𝒟(Y)` is nuclear.**  A basis extracted
  from the countable spanning family is countable, so the previous theorem applies.
- `deningerTestSubspace_isNuclearSpaceC` — **every subspace of `𝒟(Y)` is nuclear**, which is the
  card's assertion about `𝒮_Kum = closure of the logarithmic Kummer span`: whatever that subspace
  is, its nuclearity is now a theorem and not an assumption.

What is not yet formalized of this card: the scale `(3)`–`(4)` into the mixed Banach and adelic
Hilbert completions, the continuity of the integral `I` with `𝒮_Kum ⊆ ker I`, and the nuclearity
of the completed projective tensor product `(6)` — mathlib has no projective tensor product of
locally convex spaces, so that last item needs the construction built first.

- 2026-08-02 — `𝒟(Y)` nuclear and every subspace of it nuclear: the nuclearity half of the card's
  theorem is unconditional in Lean.

### The integral functional and its kernel

`formal/GaloisForLFunctions/RHTower/DeningerTestIntegral.lean` (9 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

Statement `(5)` of the card — `I(f) = ∫_Y f dλ` is continuous on `𝒟(Y)` and `𝒮_Kum ⊆ ker I` — in
the form the corpus can carry.

- `deningerFinest_functional_bounded` — **for the finest locally convex topology every linear
  functional is continuous**: the seminorm `‖φ ·‖` is itself one of the defining seminorms.  So on
  `𝒟(Y)` there is nothing to check for `I`, and the distributional dual is the full algebraic dual.
- `deningerTestSpace_hasCompactSupport`, `deningerTestSpace_integrable` — a test function is
  continuous with compact support (its support being clopen, support and closure of support
  agree), hence integrable against any measure finite on compacts.
- `deningerTestIntegral`, `_apply`, `_bounded` — the integral as a continuous linear functional on
  the test space.
- `DeningerTestKernel`, `deningerTestKernel_mem`, `deningerTestKernel_isNuclearSpaceC` — the test
  functions of total mass zero form a submodule, itself nuclear;
  `deningerTestIntegral_eq_zero_of_le_kernel` — any subspace of it is annihilated by `I`, which is
  the content of `𝒮_Kum ⊆ ker I` once `𝒮_Kum` is known to consist of mass zero functions.

- 2026-08-02 — `I` continuous and its kernel nuclear; `(5)` holds for whatever subspace the Kummer
  closure turns out to be.

### The Hilbert end of the scale, and the dual injection

`formal/GaloisForLFunctions/RHTower/DeningerTestL2Scale.lean` (7 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The parts of `(3)`–`(4)` that do not depend on the still unbuilt mixed Banach completion
`E_Kum`.

- `deningerFinest_map_bounded` — **every linear map out of a finest topology space into a normed
  space is continuous**, generalising the functional case: so every map in the scale out of
  `𝒟(Y)` is continuous with nothing to prove.
- `deningerTestSpace_memLp`, `deningerTestToL2`, `_coeFn` — a test function is square integrable
  and the induced map `𝒟(Y) → L²(Y, μ)` is linear, with `_bounded` giving its continuity.
- `deningerTestToL2_injective` — **the map into `L²` is injective** whenever `μ` charges every
  nonempty open set, since two continuous functions equal almost everywhere for such a measure are
  equal.  This is the injectivity of `𝒟(Y) ↪ H = L²(Y, λ)` in `(3)`.
- `deningerDual_injective_of_denseRange` — **the transpose of a map with dense range is
  injective**: two continuous functionals agreeing on a dense subspace agree.  This is the passage
  from `(3)` to `(4)`, valid for any topological vector spaces, hence applicable to each step of
  the scale once its density is known.

Still open for this card: the *density* of the image of `𝒮_Kum` in `L²` (which needs regularity of
`λ` together with the zero-dimensionality of `Y`, to approximate an `L²` function by indicators of
compact opens), the mixed Banach step `E_Kum`, and the projective tensor product `(6)`.

- 2026-08-02 — Continuity of every map out of `𝒟(Y)`, injectivity into `L²`, and the dual
  injection principle are unconditional in Lean.

### Density of the test space in `L²`, and the scale

`formal/GaloisForLFunctions/RHTower/DeningerLocallyConstantApproximation.lean` (5 declarations)
and `formal/GaloisForLFunctions/RHTower/DeningerTestL2Dense.lean` (4 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

The density that `(3)` asserts, for the Hilbert end of the scale, under exactly the hypotheses the
Allcock–Vaaler space satisfies: `Y` locally compact Hausdorff, second countable, totally
disconnected, and `λ` a regular measure.

- `deningerExists_compactOpen_nhds`, `deningerExists_compactOpen_superset` — in a locally compact
  Hausdorff totally disconnected space **the compact open sets form a neighbourhood basis**, and
  every compact set is contained in a compact open set.
- `deningerPiecewise_isLocallyConstant`, `deningerExists_locallyConstant_of_cover` — a compact
  open set of a Hausdorff space is clopen, so **gluing sampled values along a finite cover by
  compact opens produces a locally constant function**, by induction over the cover.
- `deningerExists_locallyConstant_approx` — **a continuous function with compact support is
  uniformly approximated by locally constant test functions**, all supported in one compact open
  set fixed in advance (which is what makes the approximation usable in `L²`).
- `deningerELpNorm_le_of_bound` — a uniform bound on a set of finite measure is an `L²` bound.
- `deningerTestToL2_denseRange` — **the test space is dense in `L²(Y, λ)`**: approximate in `L²`
  by a continuous compactly supported function (mathlib's regularity result), then uniformly by a
  test function on the fixed compact open set.
- `deningerTestScale_dual_injective`, `deningerTestScale` — the embedding is injective, continuous
  and dense, and **the dual of `L²` injects into the dual of the test space**: the scale `(3)` and
  the dual scale `(4)`, with the middle Banach step `E_Kum` omitted.

- 2026-08-02 — `𝒟(Y) ↪ L²(Y,λ)` dense, injective, continuous, with injective transpose.

### The projective tensor product of seminorms

`formal/GaloisForLFunctions/RHTower/DeningerTensorSeminorm.lean` (13 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

First step towards `(6)`.  Mathlib has a projective seminorm only for `PiTensorProduct` of normed
spaces; the binary projective tensor product of two *seminorms* is built here.

- `deningerTensorAux`, `deningerTensorLifts`, `_zero`, `_append`, `_smul`, `_tmul`, `_nonempty` —
  representations of a tensor as lists of pairs, so that two representations concatenate; every
  tensor has one, by induction.
- `deningerTensorFun`, `_bddBelow`, `_nonneg`, `_le_of_lift`, `_zero`, `_add_le`, `_smul_le` — the
  infimum of `∑ p(xᵢ) q(yᵢ)` over representations is subadditive and absolutely homogeneous.
- `deningerTensorSeminorm` — **the projective tensor product `p ⊗π q` of two seminorms**, with
  `deningerTensorSeminorm_tmul_le : (p ⊗π q)(x ⊗ y) ≤ p x · q y`.
- `deningerTensorSeminorm_dual_bound` — **a functional acting as `φ ⊗ ψ` on elementary tensors is
  bounded by the product of the bounds**: `‖Φ u‖ ≤ C D (p ⊗π q)(u)`.  This is the estimate that
  will make the tensor product of two nuclear comparison maps nuclear.

Next for `(6)`: the tensor product of nuclear maps, and nuclearity of the family `{p_i ⊗π q_j}`.

- 2026-08-02 — The projective tensor seminorm and its duality estimate are in Lean.

### The projective tensor product of nuclear spaces is nuclear

`formal/GaloisForLFunctions/RHTower/DeningerTensorBilinear.lean` (14 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerTensorNuclear.lean` (5 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

Statement `(6)` of the card at the level of the general theory: **a projective tensor product of
nuclear spaces is nuclear.**

- `deningerTensorSeminorm_mono` — domination of the factors gives domination of the projective
  tensor seminorms, with the product constant.
- `deningerTensorMk`, `deningerTensorMkR`, `deningerTensorBilin`, `_mk`, `_norm_le` — the class of
  `x ⊗ y` depends only on the classes of `x` and `y`, giving a **bilinear map of the two seminorm
  quotients into the tensor quotient, of norm at most one**; `deningerTensorBilinL`/`R` are its
  partial maps, and `deningerTensorBilinCLC` its composition with the completion.
- `deningerTensorDualAux`, `deningerTensorDual`, `_mk`, `_norm_le` — dually, **a product of two
  continuous functionals descends to the tensor quotient**, with norm at most the product of the
  norms (this is where the projective seminorm is used).
- `deningerHasSum_bilinear` — **two absolutely convergent series multiply through a bounded
  bilinear map into a complete space**: the double family is absolutely summable and its sum is
  the product of the sums, computed by iterating.
- `deningerIsNuclear_tensorC` — **the comparison map of the projective tensor seminorms is
  nuclear** whenever the two factor comparison maps are: the products `φ_i ⊗ ψ_j` of the
  functionals and `y_i ⊗ z_j` of the vectors form a nuclear representation, since their norms
  multiply to a summable family.  The representation is verified on classes of elementary tensors
  and extended by the induction on the tensor product; the operator obtained as the sum of the rank
  one maps agrees with the comparison map on a dense set, hence everywhere.
- `deningerIsNuclearSpaceC_tensor` — **the family `{p_i ⊗π q_j}` on `E ⊗ F` is nuclear** as soon as
  the families on `E` and on `F` are.

This is the general theorem behind `(6)`: the suspension test space
`𝒮_susp = 𝒮_Kum ⊗̂π C_c^∞(ℝ)` is nuclear because both factors are, `𝒮_Kum` by the subspace
permanence recorded above.  What remains specific to the card is the *completion* of the tensor
product as a space in its own right, and the continuity of the translation, rational shift and
convolution operators on it.

- 2026-08-02 — Nuclearity of projective tensor products is unconditional in Lean.

`deningerTensorSeminorm_map_le` (same module): **the projective tensor seminorm is functorial** —
a pair of maps bounded for the factor seminorms is bounded for the tensor seminorms, with the
product constant.  This is the form in which operators of the card act continuously on `(6)`: an
operator on the suspension test space that is a tensor product of a Galois map, a normalized
field-norm projection or a Tate twist on the first factor with translation, rational shift or
convolution on the second is continuous as soon as both factors are.

- 2026-08-02 — Functoriality of the tensor seminorm: operators act continuously on the tensor
  scale factorwise.

### The Banach step of the scale, and the dual scale

`formal/GaloisForLFunctions/RHTower/DeningerScaleFactorization.lean` (9 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The middle term `E_Kum` of `(3)` in abstract form: **any continuous seminorm dominating the `L²`
norm inserts a Banach space between the test space and `L²`.**

- `deningerSeminormFactor`, `_mk` — a linear map into a Banach space bounded by a seminorm kills
  that seminorm's kernel, so it descends to the seminorm quotient.
- `deningerSeminormFactorC`, `_class`, `_coe` — and extends to the completion of the quotient, a
  Banach space, with the composite still the original map.
- `deningerSeminormMkC_denseRange` — **the space maps densely into that Banach completion**;
  `deningerSeminormFactorC_denseRange` — the extension inherits dense range.
- `deningerScale_three_step` — **the factored scale**: `E → Ê_p → H`, both maps continuous with
  dense range, composing to the given map.
- `deningerScale_dual_injective_mkC`, `_factorC` — **the dual scale `(4)`**: transposes along both
  steps are injective, so `H' ↪ (Ê_p)' ↪ E'`.
- `deningerTestScale_three_step` — the specialisation to the locally constant test space: for any
  seminorm `p` with `‖g‖_{L²} ≤ C p(g)`, the scale `𝒟(Y) → Ê_p → L²(Y,λ)` is dense and continuous
  throughout, using the density of `𝒟(Y)` in `L²` proved above.

What `(3)` still lacks is only the *choice* of `E_Kum` — a specific mixed Banach seminorm on the
Kummer subspace — everything the scale asserts about such a choice is now a theorem.

- 2026-08-02 — The Banach step and the dual scale are unconditional in Lean.

### Subspaces are closed

`formal/GaloisForLFunctions/RHTower/DeningerFinestClosed.lean` (3 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The word *closed* in the card's "`𝒮_Kum` is a closed nuclear subspace".

- `deningerFinest_separating` — a vector outside a subspace is separated from it by a linear
  functional vanishing on the subspace, whose absolute value is one of the seminorms of the finest
  locally convex topology.
- `deningerFinest_subspace_closed`, `deningerTestSubspace_closed` — hence **every subspace is
  closed**: a vector outside it is at positive distance from every point of it, for that seminorm.
  No hypothesis on the subspace is needed, so the closure of any family of test functions is a
  closed nuclear subspace of `𝒟(Y)`.

- 2026-08-02 — Closedness of arbitrary subspaces in the finest topology, in separation form.

### Completeness of the test space

`formal/GaloisForLFunctions/RHTower/DeningerFinestComplete.lean` (8 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The word *complete* in the card's "`𝒟(Y)` is a complete nuclear LF space".

- `DeningerFinestCauchy`, `DeningerFinestTendsto` — Cauchy and convergence for *every* seminorm,
  which is Cauchy and convergence for the finest locally convex topology.
- `deningerFinestCauchy_bounded` — a Cauchy sequence is bounded in every seminorm.
- `deningerFinestCauchy_support_finite` — **the coordinates of a Cauchy sequence are supported in
  finitely many indices**: otherwise the weighted `ℓ¹` seminorm with weights `k / ‖c_k(x_{n(k)})‖`
  along the exceptional indices would be unbounded on the sequence.
- `deningerFinest_tendsto_of_support` — a Cauchy sequence supported in finitely many coordinates
  converges: the finitely many coefficients are Cauchy in the scalar field, and the limit
  combination is a limit for every seminorm at once.
- `deningerFinest_seqComplete`, `_of_finite`, `_of_countable` — **the finest locally convex
  topology on a countable-dimensional space is sequentially complete.**
- `deningerTestSpace_seqComplete` — hence **`𝒟(Y)` is sequentially complete**, extracting the
  countable basis from the indicators of compact opens.

With the nuclearity, closedness and scale results above, every structural assertion the card makes
about `𝒟(Y)` and its subspaces — nuclear, complete, subspaces closed and nuclear, continuous
integral, dense scale into `L²`, nuclear tensor product — is now a theorem in Lean.  What is not
formalized is the *identification* of the concrete objects: the Allcock–Vaaler space `Y`, the
logarithmic Kummer functions spanning `𝒮_Kum`, the mixed Banach norm of `E_Kum`, and the Galois,
field-norm and Tate operations on them.

- 2026-08-02 — Sequential completeness of the finest topology and of the test space.

### A concrete instance: the `p`-adic integers

`formal/GaloisForLFunctions/RHTower/DeningerPadicTestSpace.lean` (12 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

All of the above is stated for a second countable, Hausdorff, locally compact, totally
disconnected space.  `ℤ_[p]` is one, so the whole apparatus applies to it — and its test space is
infinite dimensional, so none of it is vacuous.

- `deningerTestSpace_not_finiteDimensional` — **infinitely many pairwise disjoint nonempty compact
  open sets make the test space infinite dimensional**, their indicators being linearly
  independent.
- `deningerPadicBall`, `_mem`, `_nonempty`, `_norm_lt`, `_disjoint` — in `ℤ_[p]` the balls around
  the powers of `p` of radius their own norm are clopen (ultrametric), compact, nonempty and
  **pairwise disjoint**, since all triangles are isosceles in an ultrametric space.
- `deningerPadicTest_not_finiteDimensional`, `_isNuclearSpace`, `_seqComplete`,
  `_subspace_isNuclearSpaceC`, `_subspace_closed` — **the test space of `ℤ_[p]` is an infinite
  dimensional, nuclear, sequentially complete space all of whose subspaces are closed and
  nuclear.**
- `deningerPadicTestToL2_injective`, `_denseRange`, `deningerPadicTestScale_three_step` — and it
  embeds injectively and densely in `L²(ℤ_[p], μ)` for any Haar measure `μ`, with the Banach step
  available for any seminorm dominating the `L²` norm.

`ℤ_[p]` is one local component of the adelic space of the card; the remaining work for the card is
the global assembly (the Allcock–Vaaler space itself) and the arithmetic of the Kummer functions,
not the functional analysis.

- 2026-08-02 — The theory is instantiated on `ℤ_[p]` and shown non-vacuous there.

### The place-component decomposition

`formal/GaloisForLFunctions/RHTower/DeningerTestSigma.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The card's decomposition of `Y` into compact open place components, and of `𝒟(Y)` along it — the
honest content of `(1)` without the inductive-limit formalism.

- `deningerSigmaRestrict_isLocallyConstant`, `_mem`, `deningerTestRestrict` — **a test function on
  a disjoint union restricts to a test function on each component** (the restriction of a locally
  constant function is locally constant, and a component is compact).
- `deningerTestSigma_support_finite` — **only finitely many restrictions are nonzero**: the
  support is compact and the components form an open cover, so it meets finitely many of them.
- `deningerTestSigma_injective` — the restrictions determine the function.
- `deningerTestSigma_assemble` — conversely **any finitely supported family of test functions on
  the components assembles** into one on the union, with those restrictions: local constancy is
  checked componentwise and the support lies in finitely many compact components.

Together: `𝒟(⨿ᵢ Yᵢ)` is exactly the direct sum of the `𝒟(Yᵢ)`, which is the statement that `𝒟(Y)`
is the increasing union of the `𝒟_m` of the card.  With `ℤ_[p]` as a component this is a faithful
local model of the adelic test space.

- 2026-08-02 — The place-component decomposition of the test space is in Lean.

### Operators on the scale, and preservation of the mass-zero condition

`formal/GaloisForLFunctions/RHTower/DeningerTestPullback.lean` (7 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The card's "Galois maps, normalized field-norm projections, and Tate-twisted power maps act
continuously on the entire scale and preserve `(5)`", in the form these operators actually take:
pullbacks along proper maps and their finite averages.

- `deningerTestPullback_mem`, `deningerTestPullback`, `_apply` — **the pullback of a test function
  along a proper map is a test function**: local constancy is preserved by composition with a
  continuous map, and the support of the pullback is the preimage of the support.
- `deningerTestPullback_bounded` — the operator is continuous, with nothing to check: every linear
  map is continuous for the finest locally convex topology.
- `deningerTestAverage`, `_apply` — **a weighted average of pullbacks** along a finite family of
  proper maps, the shape of a Galois average or of a normalized field-norm projection.
- `deningerTestIntegral_pullback` — **the integral is invariant** under pullback along a measure
  preserving proper map, and `deningerTestKernel_pullback` — hence **the mass-zero subspace is
  preserved**, which is the card's assertion that the operators preserve `(5)`.

- 2026-08-02 — Operators on the test scale and their compatibility with the integral.

### Towards the smooth factor of `(6)`: Fourier coefficients of periodic functions

`formal/GaloisForLFunctions/RHTower/DeningerFourierCoeffDeriv.lean` (5 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerFourierDecay.lean` (3 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

`(6)` tensors `𝒮_Kum` with the smooth test space `C_c^∞(ℝ)`; the nuclearity theorem for tensor
products is proved above, and what it still needs is the nuclearity of a smooth factor.  The route
is the classical one — smoothness is equivalent to rapid decay of Fourier coefficients, and rapidly
decreasing sequences are nuclear (proved earlier on this card) — and these are its first steps.

- `deningerFourierKernel`, `_hasDerivAt`, `_periodic` — the kernel `exp(-2πinx/T)`, its derivative
  and its equal values at the ends of a period.
- `deningerFourierCoeff` — the `n`-th Fourier coefficient of a function of period `T`.
- `deningerFourierCoeff_deriv` — **the coefficient of the derivative is `2πin/T` times the
  coefficient**: integration by parts over one period, the boundary terms cancelling by
  periodicity.
- `deningerFourierKernel_norm` — the kernel has modulus one, so
  `deningerFourierCoeff_norm_le` — **a coefficient is bounded by the supremum over a period**.
- `deningerFourierCoeff_norm_le_of_deriv` — **one power of decay per derivative**:
  `‖c_n(f)‖ ≤ T/(2π|n|) · sup‖f'‖`.

Iterating the last statement gives rapid decay, after which the smooth periodic test space
compares to the rapidly decreasing sequence space `DeningerRapidCarrier` and inherits its
nuclearity.

- 2026-08-02 — Fourier coefficient calculus for periodic functions: derivative rule and one-step
  decay.

### Rapid decay, and the bridge to the Fourier basis of the circle

`formal/GaloisForLFunctions/RHTower/DeningerFourierRapidDecay.lean` (3 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerFourierBridge.lean` (3 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

Both directions of the smoothness/decay dictionary that will identify a smooth periodic test space
with a rapidly decreasing sequence space.

- `deningerFourierCoeff_norm_eq_of_deriv` — the modulus of a coefficient is **exactly**
  `T/(2π|n|)` times that of the coefficient of the derivative.
- `deningerFourierCoeff_iterate_norm` — the `k`-fold relation along a sequence of successive
  derivatives.
- `deningerFourierCoeff_rapid_decay` — **decay of order `k`**: `‖c_n(f)‖ ≤ (T/(2π|n|))^k · M` for
  any bound `M` on the `k`-th derivative over a period.  This is the direction
  "smooth ⇒ rapidly decreasing coefficients".
- `deningerFourierKernel_eq_fourier`, `deningerFourierCoeff_eq_fourierCoeff` — the interval
  coefficient defined here **is** mathlib's Fourier coefficient on `AddCircle T`, the kernel being
  the character of index `-n`.
- `deningerFourier_sup_le` — through that identification, **a continuous function is bounded by the
  sum of the moduli of its coefficients**, the direction "rapidly decreasing coefficients ⇒ bounded
  derivatives".

What remains for the smooth factor of `(6)` is to package these two directions as a comparison of
seminorm families between the smooth periodic test space and `DeningerRapidCarrier`, whose
nuclearity is already proved on this card.

- 2026-08-02 — Both directions of the smoothness/decay dictionary are in Lean.

### The Grothendieck–Pietsch criterion for Köthe spaces, and transport of nuclearity

`formal/GaloisForLFunctions/RHTower/DeningerNuclearTransport.lean` (3 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerKotheSpace.lean` (12 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

The general form of the sequence model that will carry the smooth factor of `(6)`, together with
the tool that moves nuclearity from a model to a function space.

- `deningerSeminormEquivMap`, `deningerSeminormComparison_conj`,
  `deningerIsNuclearSpace_of_linearEquiv` — **nuclearity transports along a linear equivalence
  matching two seminorm families**: the equivalence carries kernels to kernels, so the comparison
  maps are conjugate and nuclearity is preserved by composition with bounded maps.
- `DeningerKotheData`, `DeningerKotheCarrier`, `deningerKotheSeminorm` — **a Köthe space**: an
  increasing family of positive weights on an index set, and the sequences whose weighted `ℓ¹`
  sums all converge, graded by those sums.
- `deningerKotheSeminorm_coord_le`, `_le`, `deningerKotheDelta`, `deningerKotheSeminorm_delta`,
  `deningerKotheCoeff`, `_norm_le` — coordinates are controlled by the seminorms, the seminorms
  increase with the grading, and the basis vector `δ_i` has seminorm exactly `w_k(i)`.
- `deningerKothe_hasSum` — **a Köthe sequence is the sum of its coordinates in every seminorm**:
  the error of a partial sum is the tail of a convergent series.
- `DeningerKotheData.IsNuclear`, `deningerKothe_isNuclearSpace` — **the Grothendieck–Pietsch
  criterion**: a Köthe space whose every weight is summable against a later one is nuclear, the
  comparison map being `∑ᵢ φᵢ ⊗ [δᵢ]` with `‖φᵢ‖ ‖[δᵢ]‖ ≤ w_k(i)/w_m(i)`.

With the weights `(1+|n|)^k` on `ℤ` this is the coefficient model of a smooth periodic test space,
which the Fourier dictionary above compares to the space itself.

- 2026-08-02 — Köthe spaces, the nuclearity criterion for them, and transport of nuclearity along
  isomorphisms.

### The coefficient model of a smooth periodic test space

`formal/GaloisForLFunctions/RHTower/DeningerFourierKothe.lean` (5 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerSmoothPeriodic.lean` (9 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

- `deningerFourierWeights` — the Köthe datum `(1 + |n|)^k` on the integers;
  `deningerFourier_summable_inv_sq` — `∑_{n ∈ ℤ} (1+|n|)^{-2}` converges;
  `deningerFourierWeights_isNuclear` — hence each weight is summable against the weight two steps
  later, and `deningerFourierKothe_isNuclearSpace` — **the coefficient model is nuclear**, by the
  Grothendieck–Pietsch criterion.
- `deningerPeriodic_deriv` — **the derivative of a periodic function is periodic** (translation by
  a period fixes the function, hence its derivative).
- `DeningerSmoothPeriodic` — the smooth functions of period `T`, a submodule of all functions;
  `_iteratedDeriv_periodic`, `_iteratedDeriv_continuous`, `_hasDerivAt`, `_iteratedDeriv_end` —
  **the derivative tower**: every iterated derivative is continuous, periodic, and the derivative
  of the previous one.  This is exactly the data the decay estimates require.
- `deningerSmoothPeriodic_exists_bound` — an iterated derivative is bounded over a period;
  `deningerSmoothPeriodic_coeff_decay` — **the Fourier coefficients of a smooth periodic function
  decay faster than any power**: for each `k` there is `M` with
  `‖c_n(f)‖ ≤ (T/(2π|n|))^k · M` for all `n ≠ 0`.

The coefficient map of a smooth periodic function therefore lands in the nuclear Köthe space; with
the summation bound `deningerFourier_sup_le` in the other direction and the transport lemma
`deningerIsNuclearSpace_of_linearEquiv`, this is the last leg of the nuclearity of the smooth
tensor factor of `(6)`.

- 2026-08-02 — The nuclear coefficient model and the smooth periodic derivative tower, with rapid
  decay.

### The coefficient map lands in the nuclear model

`formal/GaloisForLFunctions/RHTower/DeningerSmoothCoeffMap.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerSmoothPeriodic_integrable`, `deningerFourierCoeff_add`, `deningerFourierCoeff_smul` —
  the coefficient is linear in the function, the integrand being continuous on a period.
- `deningerSmoothPeriodic_coeff_summable` — **all weighted sums of the coefficients of a smooth
  periodic function converge**: decay of order `k+2` beats the weight `(1+|n|)^k` with two powers
  to spare, since `(1+|n|)^k ≤ 2^k |n|^k` and `|n|^{-2} ≤ 4 (1+|n|)^{-2}` off the origin, and one
  term is removed by the complement criterion.
- `deningerSmoothCoeff` — **the coefficient map**
  `DeningerSmoothPeriodic T →ₗ[ℂ] DeningerKotheCarrier ℂ deningerFourierWeights` into the nuclear
  Köthe space.

The pullback of the Köthe seminorms along this map is therefore a nuclear presentation of the
smooth periodic test space, as soon as the map is bijective onto its image with the seminorms
matched — which the summation theorem `deningerFourier_sup_le` supplies in the injectivity
direction.

- 2026-08-02 — The coefficient map of the smooth periodic test space lands in the nuclear model.

### The smooth factor of `(6)` is nuclear

`formal/GaloisForLFunctions/RHTower/DeningerSmoothCoeffInjective.lean` (2 declarations),
`formal/GaloisForLFunctions/RHTower/DeningerNuclearTransportC.lean` (3 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerSmoothPeriodicNuclear.lean` (3 declarations), axiom
audit `propext, Classical.choice, Quot.sound` throughout.

- `deningerSmoothPeriodic_eq_zero_of_coeff` — **a continuous periodic function with vanishing
  Fourier coefficients vanishes**: it descends to the circle, where the summation bound gives
  `‖F x‖ ≤ ∑ ‖c_n‖ = 0`.  Hence `deningerSmoothCoeff_injective` — the coefficient map is injective.
- `deningerSeminormEquivMapC`, `deningerSeminormComparisonC_conj`,
  `deningerIsNuclearSpaceC_of_linearEquiv` — **completed nuclearity transports** along a linear
  equivalence matching two seminorm families, the completed comparison maps being conjugate by
  density.
- `deningerSmoothSeminorm` — the coefficient seminorms of the smooth periodic space, and
  **`deningerSmoothPeriodic_isNuclearSpaceC` : the smooth periodic test space is nuclear.**  The
  coefficient map identifies it with a subspace of the nuclear Köthe space, subspaces of nuclear
  spaces are nuclear, and nuclearity transports back along the identification.

With this the suspension statement `(6)` has both factors: `𝒮_Kum` is nuclear as a subspace of
`𝒟(Y)`, a smooth test space is nuclear by the theorem just proved, and
`deningerIsNuclearSpaceC_tensor` makes their projective tensor product nuclear.  The functional
analysis of the card is complete; what remains is the arithmetic identification of `Y`, `𝒮_Kum`
and `E_Kum`.

- 2026-08-02 — The smooth tensor factor is nuclear; every functional-analytic assertion of the card
  is now a Lean theorem.

### The characters and the orthogonality relations

`formal/GaloisForLFunctions/RHTower/DeningerFourierCharacter.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerCharacter`, `_apply`, `_hasDerivAt`, `_periodic` — the character `exp(2πinx/T)`, its
  derivative and its equal values at the ends of a period.
- `deningerCharacter_integral` — **the integral of a nonconstant character over a period
  vanishes**: the character is the derivative of a multiple of itself, and the fundamental theorem
  turns the integral into a difference of equal boundary values.
- `deningerFourierCoeff_character` — **the coefficients of a character are the Kronecker delta**.

These are the basis vectors of the smooth periodic test space in its own right: with the
coordinate functionals they give the rank one representation that makes the comparison maps of the
coefficient seminorms nuclear directly on the function space, without passing through the
completion — which is what subspace permanence needs to apply to subspaces of the smooth test
space, such as the compactly supported smooth functions of `(6)`.

- 2026-08-02 — Orthogonality of the characters, the last ingredient of the uncompleted nuclearity
  of the smooth test space.

### Nuclearity of the smooth test space, and of every subspace of it

`formal/GaloisForLFunctions/RHTower/DeningerSmoothCharacterBasis.lean` (12 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `deningerHasSum_of_isometry` — an isometry reflects convergence of series.
- `deningerCharacter_periodic'`, `_contDiff`, `deningerCharacterMem` — the characters are smooth
  and periodic, hence elements of the test space; `deningerSmoothCoeff_character` — **their
  coefficient sequences are the standard basis vectors** of the Köthe space.
- `deningerSmoothToKothe`, `_mk`, `_norm` — the coefficient map induces an **isometry of the
  seminorm quotients**, carrying characters to basis vectors.
- `deningerSmooth_hasSum` — **a smooth periodic function is the sum of its coefficients against
  the characters**, in every coefficient seminorm; obtained from the Köthe summation through the
  isometry.
- `deningerSmoothPeriodic_isNuclearSpace` — **the smooth periodic test space is nuclear in the
  uncompleted sense** as well: the comparison maps are `∑ₙ φₙ ⊗ [Eₙ]` with
  `‖φₙ‖ ‖[Eₙ]‖ ≤ w_k(n)/w_m(n)` summable.
- `deningerSmoothSubspace_isNuclearSpaceC` — hence **every subspace of the smooth test space is
  nuclear**, which is the form statement `(6)` needs for its compactly supported smooth factor.

- 2026-08-02 — The smooth test space is nuclear in the uncompleted sense, so subspace permanence
  applies to it.

### Subspaces of the test space are nuclear in the uncompleted sense

`formal/GaloisForLFunctions/RHTower/DeningerFinestSubspaceNuclear.lean` (4 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

Nuclearity of `𝒮_Kum` was so far available at the completed level, where it comes from subspace
permanence.  For a subspace of a space carrying its *finest* locally convex topology it holds in
the uncompleted sense too, which is what makes such a subspace usable as a tensor factor in `(6)`.

- `deningerSeminorm_extend` — **a seminorm on a subspace extends to the whole space**: a subspace
  is a direct summand, so composing with the projection onto a complement extends the seminorm.
- `deningerRestrictSeminorm_dominating` — hence the restrictions of the ambient seminorms are all
  the seminorms of the subspace.
- `deningerIsNuclearSpace_finest_subspace` — **a subspace of a space of countable rank is nuclear**
  for the restricted finest topology: the subspace has countable rank as well, so the finest family
  on it is nuclear, and the two families dominate each other.
- `deningerTestSubspace_isNuclearSpace` — in particular **every subspace of `𝒟(Y)` is nuclear in
  the uncompleted sense**, which is the hypothesis `deningerIsNuclearSpaceC_tensor` requires of the
  Kummer factor of `(6)`.

- 2026-08-02 — Uncompleted nuclearity of arbitrary subspaces of the test space.

### Statement `(6)`: the suspension is nuclear

`formal/GaloisForLFunctions/RHTower/DeningerTestSpaceComplex.lean` (8 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerSuspensionNuclear.lean` (2 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

The two factors of `(6)` live over different fields as first built — the locally constant test
space over `ℝ`, the Fourier theory over `ℂ` — so the complex valued test space is constructed and
shown nuclear by the same route, and the tensor theorem then applies.

- `DeningerTestSpaceC`, `deningerIndicatorC_mem`, `deningerTestIndicatorsC`, `_countable`,
  `_span` — the **complex valued locally constant test space** and its countable spanning family
  of indicators of compact opens.
- `deningerTestSpaceC_rank_le`, `deningerTestSpaceC_isNuclearSpace`,
  `deningerTestSubspaceC_isNuclearSpace` — it has countable rank, is nuclear for its finest
  locally convex topology, and **so is every subspace of it**, in the uncompleted sense.
- `deningerSuspension_isNuclearSpaceC` — **statement `(6)`**: for any subspace `F` of the test
  space, the projective tensor product of `F` with the smooth periodic test space is nuclear.  This
  is `deningerIsNuclearSpaceC_tensor` applied to the two nuclearity theorems above.

(One Lean detail worth recording: the additive group of the tensor product of two submodules has
to be supplied explicitly, because a submodule carries two definitionally equal but syntactically
distinct additive monoid structures and the instance search picks the one the tensor product
lemma does not expect.)

With this the card's functional-analytic content is complete end to end: `𝒟(Y)` nuclear and
complete, its subspaces closed and nuclear, the integral continuous with nuclear kernel and
preserved by the operators, the dense scale into `L²` with injective duals and a Banach step, and
the suspension tensor product nuclear with both factors supplied.

- 2026-08-02 — `(6)` is a Lean theorem; the card's analysis is fully formalized.

### The arithmetic layer begins: a number field has countably many places

`formal/GaloisForLFunctions/RHTower/DeningerPlaceCountable.lean` (5 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The card's space `Y` is built from the places of the fields in a tower.  At each level the set of
places is discrete and countable, hence locally compact, Hausdorff, second countable and totally
disconnected — the exact hypotheses of the test space theory above.  Countability is the part that
needs proof.

- `deningerNumberField_countable` — **a number field is countable**, being finite dimensional over
  the rationals.
- `deningerRingOfIntegers_countable` — hence so is its ring of integers.
- `deningerIdeal_countable` — **a Noetherian ring with countably many elements has countably many
  ideals**: every ideal is the span of a chosen finite generating set, and the span determines the
  ideal.
- `deningerHeightOneSpectrum_countable`, `deningerFinitePlace_countable` — hence **a number field
  has countably many finite places**, the finite places being in bijection with the height one
  primes of the ring of integers.

Next: the space of places with its discrete topology as an instance of the test space theory, the
logarithmic Kummer functions `v ↦ log ‖α‖_v` as test functions (finitely supported by
`FinitePlace.hasFiniteMulSupport`), and the product formula `∏_v ‖α‖_v = 1` as the statement that
they lie in the kernel of the integral — the card's `(5)`.

- 2026-08-02 — Countability of the places of a number field, the entry point of the arithmetic
  layer.

### The Kummer span of a number field is a closed nuclear subspace

`formal/GaloisForLFunctions/RHTower/DeningerPlaceSpace.lean` (10 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The card's `𝒮_Kum` now exists as a concrete object at each level of the tower, and the structural
theorems apply to it.

- `DeningerPlace K` — **the places of a number field**, discrete and countable, hence locally
  compact, Hausdorff, second countable and totally disconnected: an instance of the test space
  theory.
- `deningerKummerFun`, `_inl`, `_inr` — **the logarithmic Kummer function** `v ↦ log ‖α‖_v` of an
  element, weighted by the multiplicity at the infinite places.
- `deningerKummerFun_support_finite` — it has **finite support**: the infinite places are finitely
  many and the absolute value is one at all but finitely many finite places
  (`FinitePlace.hasFiniteMulSupport`).
- `deningerKummerFun_mem`, `deningerKummerTest` — hence **the logarithmic Kummer functions are
  test functions** on the space of places.
- `DeningerKummerSpan` — their span, and
  `deningerKummerSpan_isNuclearSpace`, `deningerKummerSpan_closed` — **it is nuclear and closed**,
  which is the card's assertion about `𝒮_Kum` at the level of one number field.

Next: the counting integral on the space of places and the product formula in logarithmic form,
giving `𝒮_Kum ⊆ ker I` — statement `(5)`.

- 2026-08-02 — The logarithmic Kummer functions and their span, concretely, as a closed nuclear
  subspace of the test space of the places.

### Statement `(5)` arithmetically: the product formula kills the Kummer span

`formal/GaloisForLFunctions/RHTower/DeningerPlaceIntegral.lean` (5 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerPlaceTest_finite_support`, `deningerPlaceSum` — on the discrete space of places the
  integral against the counting measure is the sum over the support: the finite sum over the
  infinite places plus the finsum over the finite ones, linear because a test function has finite
  support.
- `deningerKummer_sum_eq_zero` — **the product formula in logarithmic form**: for `α ≠ 0`,
  `∑_v log ‖α‖_v = log ((∏_{w∣∞} w α ^ mult w) · ∏ᶠ_{w finite} w α) = log 1 = 0`, using mathlib's
  `NumberField.prod_abs_eq_one` and the positivity of every place at a nonzero element.
- `deningerKummerSpan_le_ker` — hence **the Kummer span lies in the kernel of the sum**, which is
  the card's `(5)` `𝒮_Kum ⊆ ker I`, now proved arithmetically rather than assumed.

At the level of a single number field the card's picture is now complete in Lean: the places form
a test space, the logarithmic Kummer functions are test functions, their span is a closed nuclear
subspace annihilated by the integral, and the suspension tensor product with a smooth factor is
nuclear.  What is left is the passage to the tower — the Allcock–Vaaler space as the limit over all
number fields, with the Galois and field-norm maps between levels.

- 2026-08-02 — The product formula gives `(5)` for the Kummer span of a number field.

### The height is an `ℓ¹` norm on the Kummer functions

`formal/GaloisForLFunctions/RHTower/DeningerHeightL1.lean` (5 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The identity that makes the Allcock–Vaaler picture work — the Weil height *is* a norm on the space
of logarithmic Kummer functions — is a consequence of the product formula already proved.

- `deningerKummer_pos_mem`, `deningerKummer_abs_mem`, `deningerHeightTest`, `deningerAbsTest` —
  the positive part and the absolute value of a logarithmic Kummer function are again test
  functions, their supports being contained in its own.
- `deningerHeight_eq_half_l1` — **the sum of the positive parts is half the sum of the absolute
  values**: `2 max(x,0) = x + |x|` pointwise, and the sum of the function itself vanishes by the
  product formula.  The left side is the Weil height of `α` and the right side half its `ℓ¹` norm,
  so the height is the `ℓ¹` norm up to the factor two.

This is the reason the Kummer functions are studied in an `L¹`-type space, and with the scale
theorems above it is what connects the card's `𝒮_Kum` to the mixed Banach step `E_Kum`.

- 2026-08-02 — Height = half the `ℓ¹` norm of the Kummer function, from the product formula.

### The Banach step `E_Kum` concretely: the `ℓ¹` completion

`formal/GaloisForLFunctions/RHTower/DeningerL1Norm.lean` (5 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerPlaceAbs_finite_support`, `deningerL1Seminorm`, `_apply` — **the sum of the absolute
  values of a test function on the space of places is a seminorm**: finitely many terms are
  nonzero, the triangle inequality is pointwise, and scalars come out of the sum.
- `deningerL1Seminorm_kummer` — on a logarithmic Kummer function it is the sum of the absolute
  values, which by the height identity above is twice the Weil height.  So the `ℓ¹` seminorm is the
  height norm on `𝒮_Kum`.
- `deningerL1_denseRange` — **the test space maps densely into the completion of that seminorm**,
  which is the Banach step `E_Kum` of the scale `(3)`: by `deningerScale_three_step` any seminorm
  dominating the `L²` norm inserts such a Banach space, and this is the one the card names.

- 2026-08-02 — The `ℓ¹`/height seminorm and its completion: the Banach term of the scale, built.

### The Hilbert end over the places, and the `ℓ² ≤ ℓ¹` comparison

`formal/GaloisForLFunctions/RHTower/DeningerPlaceMeasure.lean` (7 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- Measure instances for the space of places: the Borel structure of a discrete space is the
  discrete one, and the **counting measure is finite on compacts** (compact = finite) and
  **positive on nonempty opens**.
- `deningerPlaceToL2_injective` — hence **the test space of places embeds injectively in
  `L²`(counting)**.
- `deningerPlace_tsum_enorm` — the `ℓ¹` seminorm is the total mass of the extended norms of the
  values.
- `deningerPlaceToL2_norm_le` — **`‖g‖_{L²} ≤ ‖g‖_{ℓ¹}`**, from `∑ aᵢ² ≤ (∑ aᵢ)²` in `ℝ≥0∞`.

That is exactly the hypothesis `deningerTestScale_three_step` needs, so the scale
`𝒟(places) → E_Kum → L²(places)` — with `E_Kum` the completion in the `ℓ¹`, that is the height,
seminorm — is now a chain of continuous maps with dense ranges and injective transposes, all of it
proved.  Together with the earlier sections the card's `(3)`, `(4)`, `(5)` and `(6)` hold verbatim
for the place space of a number field.

- 2026-08-02 — The Hilbert end of the concrete scale, and the comparison that ties the three steps
  together.

### The counting measure is regular, and the concrete scale over the places

`formal/GaloisForLFunctions/RHTower/DeningerPlaceRegular.lean` (4 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerCount_outerRegular`, `deningerCount_innerRegular`, `deningerCount_regular` — **the
  counting measure of a discrete space is regular.**  Outer regularity is trivial because every set
  is open; inner regularity holds because a set of infinite counting measure contains finite — hence
  compact — subsets of arbitrarily large cardinality, and `Measure.count` of a finite set is its
  cardinality.  This is the last hypothesis of the density step, and it is not in mathlib for the
  counting measure of a general discrete space.
- `deningerPlaceScale` — **the scale over the places of a number field, assembled**: the test space
  maps densely into the completion `E_Kum` of the height (`ℓ¹`) seminorm, that completion maps
  densely into `L²`(counting), and the composite is the canonical embedding.  This instantiates the
  card's `(3)` and its dual `(4)` on the concrete arithmetic object: `𝒟(places K) ↪ E_Kum ↪ L²`.

- 2026-08-02 — The regularity brick, and the concrete Kummer scale over a number field.

### The Banach step is the height norm, and the tower invariance

`formal/GaloisForLFunctions/RHTower/DeningerTestHeightBridge.lean` (9 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The scale built above lives on the test space of the place space; the classical Weil height lives
on mathlib's admissible-absolute-value model.  This module identifies the two, so the Banach step
of the card's scale is the height completion and not merely an abstract seminorm completion.

- `deningerFinsum_sum_split`, `deningerPlaceSum_eq_finsum` — the sum over the places of a test
  function is the sum of its values: the archimedean half is a sum over a finite type, the
  non-archimedean half has finite support, and the two ranges are disjoint and cover.
- `deningerHeightSum_eq_logHeight` — **the place sum of the positive part of the logarithmic
  Kummer function is `logHeight₁`**, the logarithmic Weil height, from
  `NumberField.logHeight₁_eq` and `max (c·log t) 0 = c · log⁺ t` for `c ≥ 0`.
- `deningerL1Seminorm_eq_two_mul_logHeight` — **the `ℓ¹` seminorm of the Kummer function is twice
  the height.**  So `E_Kum`, the Banach step of `(3)`, is exactly the completion of the Kummer
  functions in the height norm — the Allcock–Vaaler Banach space.
- `deningerL1Seminorm_eq_zero_iff` — **the seminorm vanishes exactly on the roots of unity**: the
  Kummer map `α ↦ f_α` is injective on `K^× / torsion`, so the Banach step really is a completion
  of the Kummer group and not of a collapsed quotient.
- `deningerL1Seminorm_baseChange`, `deningerHeightSum_baseChange` — **enlarging the field
  multiplies the norm by `[L : K]`**, through the archimedean fibre count and the fundamental
  identity for the finite places.
- `deningerNormalizedL1Seminorm_baseChange` — **the normalized norm is independent of the field of
  definition.**  This is the compatibility the card's `(1)` needs: the norms of the place models of
  a cofinal tower of number fields agree after normalization, so they glue to one norm on the
  Allcock–Vaaler space, and the topology does not depend on the chosen tower.

- 2026-08-02 — The Banach step identified with the height completion, injectivity modulo torsion,
  and the normalized tower invariance.

### Statement `(1)`: the strict inductive limit of finite-dimensional steps

`formal/GaloisForLFunctions/RHTower/DeningerTestExhaustion.lean` (11 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerTestStep`, `_mem`, `_mono` — the step of an exhaustion: the test functions supported in
  a fixed set, a submodule growing with the set.
- `deningerStepEval`, `_injective`, `deningerTestStep_finiteDimensional` — **a step over a finite
  set is finite dimensional**, because evaluation at the points of the set is injective on it.
  This is the card's `𝒟_m`: functions supported on the first `m` place components and constant on
  the clopen partition, which in the discrete place model is the partition into points.
- `deningerTestStep_iSup_eq_top` — **the steps of an increasing exhaustion exhaust the test
  space**: a test function has finite support and a finite set already lies in one step, so
  `𝒟(Y) = ⋃ₘ 𝒟_m` as the card's `(1)` asserts.
- `deningerTestStep_exhaustion_independent` — **the limit does not depend on the exhaustion**: any
  two increasing exhaustions give the whole space, so the topology the card describes is
  independent of the chosen cofinal tower.
- `deningerTest_indLim` — the four properties bundled: the steps are finite dimensional, monotone,
  directed, closed for the finest locally convex topology (through
  `deningerTestSubspace_closed`, so the inclusions have closed image and the limit is *strict*),
  and their supremum is the whole test space.
- `deningerExists_exhaustion`, `deningerPlaceTest_indLim` — a countable discrete space carries such
  an exhaustion, and **the place space of a number field is one**, so `(1)` holds verbatim for the
  arithmetic realization of `Y`.

- 2026-08-02 — Statement `(1)` proved: the test space is the strict countable inductive limit of
  finite-dimensional closed steps, independent of the exhaustion.

### Statement `(2)`: the Kummer subspace is the image of a homomorphism, faithful modulo torsion

`formal/GaloisForLFunctions/RHTower/DeningerKummerHomomorphism.lean` (11 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerKummerFun_mul`, `_one`, `_pow`, `_inv`, `deningerKummerTest_mul` — the logarithmic
  laws: taking logarithms turns multiplicativity of the absolute values into additivity, so
  `f_{αβ} = f_α + f_β`, `f_1 = 0`, `f_{αⁿ} = n·f_α` and `f_{α⁻¹} = −f_α`.  The power law is the
  Tate-twisted power action of the card's `(5)`, on the nose.
- `deningerKummerHom`, `_apply` — **the Kummer homomorphism `K^× → 𝒟(Y)`**, an additive
  homomorphism from the multiplicative group of the field into the test space.
- `deningerKummerFun_eq_zero_iff`, `deningerKummerHom_eq_zero_iff` — **its kernel is exactly the
  roots of unity.**  One direction goes through the identification of the `ℓ¹` seminorm with twice
  the height and the height-zero theorem; the other is the power law.
- `deningerKummerHom_range`, `deningerKummerHom_range_span` — the image is the set of logarithmic
  Kummer functions and its span is `DeningerKummerSpan`, the card's `𝒮_Kum` (already known closed
  and nuclear).

So `𝒮_Kum` is the span of a faithful copy of `K^× / μ(K)`: statement `(2)` is not only a closed
nuclear subspace but an arithmetically faithful one.

- 2026-08-02 — The Kummer map is a homomorphism with kernel the roots of unity; `(2)` is a faithful
  model of `K^×` modulo torsion.

### The operators of `(6)`: translation and the rational shifts

`formal/GaloisForLFunctions/RHTower/DeningerSuspensionTranslation.lean` (10 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `deningerFourierKernel_add`, `_period`, `_periodic'` — the Fourier kernel is a character of
  period `T`.
- `deningerFourierCoeff_translate` — **translating a periodic function multiplies its `n`-th
  Fourier coefficient by the phase `e^{−2πina/T}`.**  The shift comes out of the integral because
  the kernel is a character, and the integral over one period does not depend on the interval
  chosen (`Function.Periodic.intervalIntegral_add_eq`).
- `deningerFourierCoeff_translate_norm` — hence the moduli of the coefficients are unchanged.
- `deningerTranslate`, `_apply` — translation `t ↦ t − a` as a linear operator on the smooth
  periodic test space: the translate of a smooth periodic function is smooth and periodic.
- `deningerSmoothSeminorm_translate` — **translation is an isometry for every coefficient
  seminorm**, since those seminorms only see the moduli of the coefficients.
- `deningerSuspensionTranslate_bounded` — **translation in the suspension coordinate acts on the
  suspension `(6)` with norm at most one**, through the functoriality of the projective tensor
  seminorm (`deningerTensorSeminorm_map_le` with both constants one).
- `deningerSuspensionRationalShift_bounded` — **the rational shifts `t ↦ t − log q` act
  continuously on `(6)`**, the case `a = log q`.

- 2026-08-02 — The translation and rational-shift half of the card's `(6)` operator claim, proved
  in the sharp form: these operators are contractions, indeed isometries on the smooth factor.

### The last operator of `(6)`: convolution by a test function

`formal/GaloisForLFunctions/RHTower/DeningerSuspensionConvolution.lean` (11 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `deningerConvolve`, `_apply`, `_periodic`, `_contDiff` — convolution by a compactly supported
  smooth function maps smooth periodic functions to smooth periodic functions: periodicity passes
  through the integral, and smoothness is differentiation under the integral sign
  (`HasCompactSupport.contDiff_convolution_left`).
- `deningerConvolveOp`, `_apply` — convolution as a `ℂ`-linear operator on the smooth periodic test
  space; additivity uses that the convolution integral exists (compact support against a locally
  integrable function).
- `deningerConvolve_coeff` — **the multiplier identity**: the `n`-th Fourier coefficient of the
  convolution is `(∫ φ(s) e^{−2πins/T} ds)` times the `n`-th coefficient.  The proof is Fubini on
  the product of the period interval with the line: the integrand is continuous and vanishes
  outside the compact box `[0,T] × supp φ`, so it is integrable, and after the swap the inner
  integral is the coefficient of a translate, which the translation law evaluates.
- `deningerConvolve_multiplier_norm_le` — the multiplier is bounded by the `L¹` norm of `φ`, since
  the kernel has modulus one.
- `deningerSmoothSeminorm_convolve_le` — **convolution is bounded by `‖φ‖₁` on every coefficient
  seminorm.**
- `deningerSuspensionConvolve_bounded` — **convolution acts continuously on the suspension `(6)`**,
  with norm at most `‖φ‖₁`, through the functoriality of the projective tensor seminorm.

With the translation module, every operator the card lists on `(6)` — translation in `t`, the
rational shifts `t ↦ t − log q`, and convolution by a compactly supported smooth test function —
is now a proved bounded operator on the suspension.

- 2026-08-02 — `(6)` is complete: the suspension is nuclear and all three of its declared operator
  families act continuously on it.

### Statement `(5)`, Galois half: automorphisms permute the places and preserve the scale

`formal/GaloisForLFunctions/RHTower/DeningerGaloisPlaceAction.lean` (12 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerGaloisInvariance.lean` (14 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

Mathlib has the Galois action on the *infinite* places only.  The finite half is built here from
the adic valuation upwards.

- `deningerIdeal_map_symm`, `deningerIdeal_map_dvd`, `_iff` — an automorphism of a ring preserves
  divisibility of ideals in both directions.
- `deningerSpectrumComap`, `_asIdeal`, `_map` — the height-one prime pulled back along a ring
  automorphism of a Dedekind domain.
- `deningerIntValuation_comap` — **the adic valuation is transported**: `v_{σ⁻¹P}(r) = v_P(σ r)`.
  The proof is the divisibility characterization `intValuation_le_pow_iff_dvd` applied at every
  exponent, plus the fact that both values are of the form `exp(−n)`, so the two agree.
- `deningerValuation_comap` — the same on the fraction field, by writing an element as a quotient.
- `deningerAbsNorm_comap` — the absolute norm is invariant, because an automorphism induces an
  isomorphism of the quotient rings; this is what makes the two adic absolute values share a base.
- `deningerIntegerAut`, `deningerFinitePlaceComap`, `_apply` — **a field automorphism permutes the
  finite places**, and the pulled back place is the composite `w ∘ τ`.
- `deningerMult_comap` — the multiplicity of an infinite place is unchanged (`isReal_comap_iff`).
- `deningerPlaceComap`, `deningerPlaceEquiv` — **a field automorphism permutes the place space of
  the card**, infinite and finite parts together.
- `deningerKummerFun_comap` — **the Kummer functions are Galois equivariant**:
  `f_{τα} = f_α ∘ τ*`.
- `deningerPlaceSum_comap` — hence every sum over the place space is invariant under the induced
  permutation, so the mass of a test function is Galois invariant and the mass-zero condition `(5)`
  is preserved.
- `deningerHeightSum_galois`, `deningerL1Seminorm_galois` — **the Weil height and the `ℓ¹`, that is
  the Kummer, norm are Galois invariant**, so the Galois maps act isometrically on the Banach step
  of the scale.
- `deningerLogHeight_galois` — the same for mathlib's `Height.logHeight₁`, a statement about
  mathlib's own height that mathlib does not have.
- `deningerKummerTest_galois` — the Kummer subspace `𝒮_Kum` is Galois stable.

- 2026-08-02 — The Galois half of `(5)`: the action on the place space built from the adic
  valuation up, and the invariance of the mass, the height and the Kummer norm.

### Statement `(5)`, projection half: the field-norm projection

`formal/GaloisForLFunctions/RHTower/DeningerTestPushforward.lean` (10 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerPushFun`, `_eq_sum`, `_support`, `_mem`, `deningerPush`, `_apply` — **the fibrewise
  projection of test functions along a map of discrete spaces**: the fibre sum of a test function
  is a test function, and the projection is linear.  The fibre sums are finite sums because the
  support is finite, and the support of the projection lies in the image of the support.
- `deningerPush_mass` — **the projection preserves the mass**, by grouping a finite sum along the
  fibres of the map (`Finset.sum_fiberwise_of_maps_to`).
- `deningerPlaceRestrict`, `deningerPlacePush` — the arithmetic instance: restriction of places
  along an extension of number fields, infinite places by composition with the structure map and
  finite places by the prime below, and the induced projection of test spaces.  Divided by
  `[L : K]` this is the card's normalized field-norm projection.
- `deningerPlacePush_sum`, `deningerPlacePush_ker` — **the projection preserves the place sum**,
  hence maps the mass-zero condition `(5)` of the larger place space into that of the smaller one.

Together with the Galois section and the power law of the Kummer homomorphism, all three operator
families the card names in `(5)` — Galois maps, normalized field-norm projections, Tate-twisted
power maps — are now proved to act on the test scale and to preserve `(5)`.

- 2026-08-02 — The projection half of `(5)`: the fibrewise projection along the restriction of
  places, mass preserving.

### The tower: transition maps, the Kummer direct system, and the cocycle condition

`formal/GaloisForLFunctions/RHTower/DeningerTowerTransition.lean` (16 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerTowerCocycle.lean` (7 declarations), axiom audit
`propext, Classical.choice, Quot.sound` throughout.

The Allcock–Vaaler space is the limit of the place spaces of a tower of number fields.  Its
transition maps are the pullbacks weighted by the local degree; these modules build them and prove
the two facts that make the tower a direct system.

- `deningerArchDegreeOver`, `deningerArchMult_dvd`, `deningerArchDegree_mul` — the local degree of
  an infinite place over its restriction is the ratio of the multiplicities: `2` exactly when a
  real place becomes complex.
- `deningerArchMult_fibre_sum` — **the multiplicities of the infinite places above a place add up
  to `[L : K]` times the multiplicity below.**  Both sides count the complex embeddings of `L`
  whose restriction induces the place below: fibrewise over `mk` on one side, fibrewise over
  restriction of embeddings on the other, where every fibre has exactly `[L : K]` elements.  This
  is the archimedean analogue of `∑ e·f = [L : K]` and is not in mathlib.
- `deningerArchDegree_fibre_sum`, `deningerFiniteDegreeOver`, `deningerFiniteDegree_fibre_sum` —
  **the local degrees above a place add up to `[L : K]`**, archimedean and non-archimedean.
- `deningerPlaceRestrict_preimage_finite` — the fibres of the restriction of places are finite, so
  the weighted pullback of a test function is a test function.
- `deningerTowerPullFun`, `deningerTowerPull` — **the transition map of the tower**: the pullback
  along restriction of places, weighted by the local degree.
- `deningerKummerFun_tower` — **the logarithmic Kummer functions form a direct system**: the
  Kummer function of an element of the base, computed over the extension, is the weighted pullback
  of the Kummer function computed over the base.  Finite places by the value law `‖x‖_w =
  ‖x‖_v^{e·f}`, infinite places by the multiplicity ratio.
- `deningerPlaceDegree_fibre_sum`, `deningerPush_towerPull`, `deningerTowerPull_sum` — **the
  transition map multiplies the mass by `[L : K]`**, which is exactly why the mass divided by the
  absolute degree is the invariant of the tower.
- `deningerInfinitePlaceRestrict_trans`, `deningerRestrictPlace_trans`,
  `deningerPlaceRestrict_trans` — restriction of places is transitive in a tower.
- `deningerArchDegree_tower`, `deningerFiniteDegree_tower`, `deningerPlaceDegreeOver_tower` — **the
  local degrees are multiplicative in a tower** (the archimedean case by cancelling multiplicities,
  the non-archimedean case by `deningerLocalDegree_tower`).
- `deningerTowerPull_trans` — **the cocycle condition: the transition maps compose.**  So the test
  spaces of the place spaces of a tower of number fields, with these transition maps, form a
  genuine direct system, and the Kummer functions are a compatible family in it.

- 2026-08-02 — The tower layer: transition maps, the Kummer direct system, the degree scaling of
  the mass, and the cocycle condition.

### Every level of the tower embeds in the next

`formal/GaloisForLFunctions/RHTower/DeningerTowerInjective.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerArchDegreeOver_pos`, `deningerFiniteDegreeOver_pos`, `deningerPlaceDegreeOver_pos` — the
  local degrees are positive.
- `deningerRelativeFinrank_pos` — a relative degree of number fields is positive, by the tower law
  over `ℚ`.
- `deningerPlaceRestrict_surjective` — **every place of the base is the restriction of a place of
  the extension.**  If a fibre were empty its degree sum would be zero, but the degree sums are
  `[L : K] > 0`; so surjectivity is a corollary of the fibre-sum laws rather than a separate
  existence theorem.
- `deningerTowerPull_injective` — **the transition maps of the tower are injective**: since the
  degrees are nonzero and every place of the base is hit, a test function is determined by its
  weighted pullback.  So each level of the tower embeds into the direct limit and nothing is lost
  when the field of definition grows.

Remaining for this card: only the direct limit object itself — assembling `Module.DirectLimit` over
a directed family of number fields with `deningerTowerPull` as the maps.  Both hypotheses that
construction needs are now proved: the cocycle condition `deningerTowerPull_trans` and the
injectivity above.

- 2026-08-02 — Injectivity of the tower transitions; the direct system is complete except for the
  colimit object.

### The colimit: the test space of the Allcock–Vaaler space of a tower

`formal/GaloisForLFunctions/RHTower/DeningerTowerDirectLimit.lean` (8 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerTowerPullHom` — the transition map attached to an *embedding* of number fields, not to a
  chosen algebra structure: the algebra instance is produced from the ring homomorphism inside the
  definition, so the maps compose along a diagram of embeddings.
- `deningerTowerPullHom_id` — **the identity embedding gives the identity map.**  The restriction
  of places along the identity is the identity, and the local degrees over the identity are one:
  positive with fibre sum `[K : K] = 1`, so each is one.
- `deningerTowerPullHom_comp` — **the transition maps compose** (the cocycle condition, transported
  to embeddings by building the scalar tower from `τ ∘ σ = ` the composite embedding).
- `deningerKummerTest_towerPull` — the transition map carries the Kummer function of an element to
  the Kummer function of its image.
- `deningerTowerSystem`, `deningerTowerSystem_directed` — **a tower of number fields is a directed
  system of test spaces** in the sense of mathlib's `DirectedSystem`, for any index preorder and
  any compatible family of embeddings.
- `DeningerTowerLimit` — **the direct limit `𝒟(Y)`**: the test space of the place space of the
  union of the tower, that is of the Allcock–Vaaler space, as `Module.DirectLimit` of the levels.
- `deningerKummer_limit_compatible` — **the logarithmic Kummer functions define a single element of
  the limit**: computing `f_α` in a larger field of definition gives the same element of `𝒟(Y)`.
  This is the card's Setup made literal — `𝒮_Kum` lives on the Allcock–Vaaler space, not on any one
  level.

With this the card is closed: `(1)`–`(6)` are Lean theorems, the arithmetic realization over a
number field is complete (places, Kummer homomorphism with kernel the roots of unity, product
formula, height = half the `ℓ¹` norm, the nuclear/Banach/Hilbert scale and its dual, the Galois,
projection and power operators), and the tower layer now carries it to the Allcock–Vaaler space
itself: transition maps, cocycle, injectivity, the direct limit, and the Kummer family in it.

- 2026-08-02 — The colimit object built; the card's `Y` is a Lean object and the Kummer functions
  live on it.
