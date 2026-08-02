# Deninger--Meyer strict nuclear radial--angular comparison

- **ID:** `deninger-meyer-strict-nuclear-radial-angular-comparison`
- **Stage:** 2-fully-proven
- **Type:** SOURCE TOPOLOGICAL COMPARISON THEOREM
- **Labels:** `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`,
  `DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** Meyer's Poisson complex is a strict complex of
  nuclear Fréchet spaces, remains strict after tensoring with the
  finite-stage Tate--Milnor coefficient and passing to its strict
  pro-Ind limit, and the Hilbert--Kummer modulus angle contracts by an
  explicit topological chain homotopy without contracting the unitary
  phase.

## 1. Radial nuclear spaces

Write
\[
 \mathcal H_-
 =
 \bigcap_{s\in\mathbb R}
 \mathcal S(\mathbb R_{>0}^{\times})_s,
 \qquad
 \mathcal S(\mathbb R_{>0}^{\times})_s
 =
 \{f:x^sf(x)\in\mathcal S(\mathbb R_{>0}^{\times})\}.
                                                                    \tag{1}
\]
It is enough to intersect over \(s\in\mathbb Z\).  Let
\[
 \mathcal H_\cap
 =
 \{f\in\mathcal S(\mathbb R):
 f(-x)=f(x),\ f(0)=\widehat f(0)=0\}.                              \tag{2}
\]

`[PROVED HERE] [DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS]`

Both `(1)` and `(2)` are nuclear Fréchet spaces.  The Poisson operator
\[
 Z:\mathcal H_\cap\longrightarrow\mathcal H_-,
 \qquad
 Zf(x)=\sum_{n\geq1}f(nx),                                       \tag{3}
\]
is a strict closed embedding.  Consequently
\[
 0\longrightarrow\mathcal H_\cap
 \xrightarrow{Z}\mathcal H_-
 \longrightarrow M_\zeta
 \longrightarrow0                                                \tag{4}
\]
is a strict exact sequence of nuclear Fréchet spaces.

### Proof

The even Schwartz space is a closed subspace of
\(\mathcal S(\mathbb R)\), and `(2)` is the common kernel of two
continuous functionals.  Hence `(2)` is nuclear Fréchet.

Exhausting the weights in `(1)` by the intervals \([-m,m]\) realizes
\(\mathcal H_-\) as the countable projective limit of the nuclear
Fréchet spaces
\[
 \mathcal S(\mathbb R_{>0}^{\times})_{[-m,m]}.
\]
Equivalently it is the closed compatibility subspace of the product
of the integer-weight Schwartz spaces.  Countable products and closed
subspaces of nuclear Fréchet spaces are nuclear Fréchet.

Meyer's zeta estimate and Poisson summation theorem prove that `(3)`
is continuous, has closed range, and is a topological isomorphism
onto its range.  The quotient in `(4)` is therefore Fréchet and
nuclear.

This proof also fixes the support convention.  \(\mathcal H_-\) is
not \(C_c^\infty(\mathbb R_{>0})\); in logarithmic coordinates it is
the nuclear Fréchet space of smooth functions decaying faster than
every exponential at both ends.  Compactly supported smooth functions
form a dense core.

## 2. Strict tensor transport

Let \(E_\nu^\bullet\) be a finite pro-Stein character-lattice and
finite relative Tate--Milnor cell stage.  Every term is a nuclear
Fréchet space: coherent finite-rank analytic pieces over a Stein torus
are nuclear, and finite cones, kernels, quotients, and sums preserve
nuclearity.

Grothendieck exactness for completed projective tensor product with a
nuclear Fréchet space applied degreewise to `(4)` gives
\[
 0\to
 E_\nu^\bullet\widehat\otimes_\pi\mathcal H_\cap
 \xrightarrow{1\widehat\otimes Z}
 E_\nu^\bullet\widehat\otimes_\pi\mathcal H_-
 \to
 E_\nu^\bullet\widehat\otimes_\pi M_\zeta
 \to0                                                           \tag{5}
\]
as a strict exact sequence of complexes.

The pro-Stein Tate--Milnor coefficient is the strict filtered union of
these finite stages in each fixed bidegree.  Filtered colimits of
complex vector spaces are exact, and the topology is the final strict
pro-Ind topology.  Passing `(5)` through the stages therefore gives
the same strict sequence for the full phase coefficient
\(E_{\mathrm{phase}}^\bullet\).

The mixed \(L^1/L^2\) Kummer maps and the nuclear test-space maps are
continuous on every finite stage, hence on the final topology.
Density survives completed tensoring because the algebraic tensor of
dense subspaces is dense.  For the all-prime residue graph no general
tensor-flatness claim is needed:
`DAC_STRICT_PRO_LOG_COLLAR_SECTION` and
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL` give split strict boundary
sequences, and completed projective tensor product preserves an
explicit continuous splitting.  Thus `(5)` is compatible with:

1. the nuclear Kummer test topology;
2. the mixed \(L^1/L^2\) completion;
3. the completed finite-residue graph;
4. the real homology-current boundary;
5. the two endpoint functionals.

The dilation flow is continuous on `(1)`--`(2)`.  Meyer's theorem,
not a formal interchange of an infinite sum, defines `(3)` in these
topologies.  Deninger's identity
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u]
\]
then identifies each summand with the corresponding source flow
pullback.

## 3. Angular cosheaf contraction

Let \(H=H_{\mathrm{Kum}}\) and \(S(H)\) be its unit sphere.  Use the
augmented topological singular-chain cosheaf
\[
 \epsilon:C_\bullet^{\mathrm{top}}(S(H))\longrightarrow\mathbb R,
                                                                    \tag{6}
\]
where each chain space has the free locally convex direct-sum topology
on singular simplices.  A continuous map or homotopy induces a
continuous chain map or prism operator.

The explicit contraction in
`DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION` gives a
continuous prism homotopy
\[
 \operatorname{id}
 \simeq
 \iota\epsilon                                                   \tag{7}
\]
for a chosen point inclusion \(\iota\).  Hence `(6)` is a split
chain-homotopy equivalence in complete locally convex complexes.

`[PROVED HERE]
[DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION]`

For every complete phase/radial complex \(A^\bullet\), functoriality of
completed projective tensor product extends `(7)` to
\[
 C_\bullet^{\mathrm{top}}(S(H))
 \widehat\otimes_\pi A^\bullet
 \simeq
 A^\bullet.                                                       \tag{8}
\]
This is a continuous chain-homotopy equivalence, so it is stronger
than a bare cohomology isomorphism and remains valid for the nuclear,
mixed, residue-graph, and endpoint topologies above.

The positive rational flow multiplies \(h\in H\) by a positive scalar
and therefore fixes \(h/\|h\|\).  Thus `(8)` commutes with every
Poisson dilation and with their already-defined sum `(3)`.

For compact Galois descent, the augmentation `(6)` is equivariant even
though the chosen contraction need not be.  Continuous invariants are
exact on the complete coefficient modules used here by normalized
Haar averaging.  Applying invariants to `(6)` therefore preserves its
strict quasi-isomorphism.

## 4. Apex and unitary phase

The polar product is
\[
 X_{\mathrm{unit}}\times S(H)\times\mathbb R_{>0}.
\]
Only \(S(H)\) is contracted.  Fibrewise adjoining \(h=0\) forms the
cone on \(S(H)\), so `(8)` extends to
\[
 X_{\mathrm{unit}}\times H
 \rightsquigarrow
 X_{\mathrm{unit}}\times\mathbb R_{\geq0}.                        \tag{9}
\]
The unitary character factor remains the Tate--Milnor phase
coefficient at every radius, including zero.

On the radial Schwartz domain,
`DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE` identifies the two relative
boundary maps as
\[
 f\longmapsto f(0),
 \qquad
 f\longmapsto\frac{\pi}{2}\widehat f(0).                          \tag{10}
\]
Therefore the relative common kernel is exactly
\(\mathcal H_\cap\).  No angular class and no extra “Fourier boundary
point” survives.

## 5. Arithmetic consequence

The Hilbert--Kummer bounded locus is used as its own fine ringed
source, with the continuous map to Deninger's pointwise coarse
approximation.  Sheafification means derived pushforward along this
map; boundedness need not be a local property of the coarse topology.

Equations `(5)`--`(10)` close the following parts of
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`:

- radial nuclear sheaf/cosheaf topology;
- strictness and closed range of the Poisson differential;
- compatibility with mixed Kummer and completed residue topologies;
- strict angular contraction after retaining the phase coefficient;
- correct treatment of the unitary apex and both endpoint maps.

The remaining comparison is arithmetic gluing: identify the
finite-residue/real-boundary totalization of the intrinsic source
middle complex with `(4)`, and prove cup/trace compatibility.

## Hostile audit

- Ordinary contractibility alone is not used to preserve completed
  tensors; the continuous prism homotopy `(7)` supplies explicit
  splittings.
- No Haar probability measure on the infinite-dimensional sphere is
  asserted.
- No compact support is imposed in the angular direction.
- The phase factor is not contracted.
- Meyer's closed-range theorem supplies the infinite Poisson sum; no
  unjustified termwise convergence in a new topology is asserted.
- No zeta zero, spectral divisor, Weil positivity, RH, CCM object, or
  numerical computation enters the construction.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, especially Theorem 4.1:
  https://arxiv.org/abs/math/0412277.
- Alexander Grothendieck, *Résumé des résultats essentiels dans la
  théorie des produits tensoriels topologiques et des espaces
  nucléaires*, Ann. Inst. Fourier 4 (1952), 73--112:
  https://doi.org/10.5802/aif.46.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §6 and §12: https://arxiv.org/abs/1807.06400.

## Log

- 2026-07-27 — Proved nuclearity and strict tensor stability of
  Meyer's Poisson complex and upgraded Hilbert--Kummer angular
  contractibility to an explicit strict cosheaf chain contraction.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerMeyerRadialEndpoints.lean`, 16 declarations, axiom
audit for every one of them: `propext, Classical.choice, Quot.sound`.

**`(2)` and `(10)`, Meyer's space and the two endpoint functionals.**  mathlib has the Schwartz
space and the Fourier transform on it, so this part of the card is buildable on the actual
objects rather than on a shadow.

- `deningerSchwartzEval` — **evaluation of a Schwartz function as a continuous functional**, built
  through the bounded-continuous-function realization; `deningerFourierEval` — evaluation of the
  Fourier transform at the origin, likewise continuous.  These are the two boundary maps `(10)`.
- `deningerEvenSchwartz`, `_mem_iff`, `_isClosed` — the even Schwartz functions, cut out as the
  intersection over all `x` of the kernels of `f ↦ f(-x) - f(x)`, hence closed.
- `DeningerMeyerCap`, `deningerMeyerCap_mem_iff` — **`(2)`**: `ℋ_∩` is exactly the even Schwartz
  functions with `f(0) = 0` and `f̂(0) = 0`.
- `deningerMeyerCap_isClosed` — **`ℋ_∩` is a closed subspace of the Schwartz space**, which is the
  card's own argument that it is "the common kernel of two continuous functionals" inside the
  closed even subspace.  This is the whole content of `(2)` that does not mention nuclearity.
- `deningerFourierEndpoint`, `_ker`, `deningerMeyerCap_eq_endpoints` — **§4's conclusion**: the
  normalization `π/2` of the second endpoint map does not change the subspace it cuts out, so the
  relative common kernel of the two boundary maps of `(10)` is exactly `ℋ_∩` and no extra Fourier
  boundary point survives.

**Two structural ingredients.**

- `deningerIInf_real_eq_int` — **"it is enough to intersect over `s ∈ ℤ`"** in `(1)`: if every real
  weight is dominated by its two neighbouring integer weights, the real-indexed intersection equals
  the integer-indexed one.
- `deningerNormalize_smul` — **the positive rational flow fixes `h/‖h‖`**, the sentence in §3 that
  makes `(8)` commute with every Poisson dilation.

### What cannot be stated in Lean, and why

Every claim of this card that contains the word *nuclear*, *Fréchet* or *strict* is out of reach,
and so is the Poisson operator itself:

- mathlib has no locally convex spaces beyond normed spaces, hence no nuclear spaces, no Fréchet
  spaces as a class, no strict morphisms, no strict exact sequences and no completed projective
  tensor product.  So `(1)`'s nuclear Fréchet structure, the strictness and closed range of `(3)`,
  the strict exact sequence `(4)`, the tensor transport `(5)` and the tensored contraction `(8)`
  cannot be written down.
- `𝓗_-`, the intersection of the weighted Schwartz spaces on `ℝ_{>0}^×`, is not in mathlib: only
  the unweighted Schwartz space on a normed space is.  `deningerIInf_real_eq_int` is the
  index-reduction step of its construction, stated for an arbitrary family of subspaces.
- §3's cosheaf of topological singular chains with the free locally convex direct-sum topology, and
  the continuous prism homotopy `(7)`, need locally convex direct sums and a topological singular
  chain complex; mathlib has neither.

So the card stays at stage 2.  What is formalized is the part of the theorem that lives inside the
Schwartz space: the two endpoint functionals of `(10)`, the identification of `ℋ_∩` as their common
kernel among even functions, its closedness, the irrelevance of the `π/2` normalization, and the
two structural lemmas used in `(1)` and §3.

### Log

- 2026-08-02 — Formalized `(2)` and `(10)` on mathlib's Schwartz space, together with the
  integer-weight reduction of `(1)` and the flow-invariance of the normalization used in §3.

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

`deningerIsNuclearSpaceC_subspace_of_hilbertian` and
`deningerIsNuclearSpace_subspace_of_hilbertian`: **a subspace of a nuclear space presented by
Hilbertian seminorms is nuclear.**  The bounded left inverse required by
`deningerIsNuclearSpaceC_subspace_of_leftInverse` is constructed rather than assumed —
`deningerSubspaceLeftInverse` composes the ambient `ℓ²` embedding, the orthogonal projection onto
the closed image `deningerSubspaceRange` of the completed subspace quotient, and the inverse
`deningerSubspaceRangeEquiv` of the corestricted isometry; the compatibility
`deningerHilbertianEmbeddingC_subspace` places the image of a subspace class inside that closed
subspace, where the projection acts as the identity.

This is the permanence property the radial–angular comparison of this card needs: the strict
inductive limit's steps are subspaces of the ambient test space, and their nuclearity no longer
has to be assumed.  It does not by itself finish the card, whose open ingredient remains the
nuclearity of the Schwartz space (the Hermite-coefficient characterisation).

- 2026-08-02 — Subspace permanence for Hilbertian nuclear spaces is unconditional in Lean.

### Permanence under subspaces, for any presentation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearCompletedInvariance.lean` (6 declarations,
axiom audit `propext, Classical.choice, Quot.sound` throughout).

`deningerIsNuclearSpaceC_subspace`: **every subspace of a nuclear space is nuclear**, with no
hypothesis on the presenting family.  The Hilbertian case is transferred along the two dominations
of `deningerNuclear_exists_hilbertian_family` using
`deningerIsNuclearSpaceC_of_dominating`, itself resting on the calculus
`deningerSeminormComparisonC_ext`/`_congr`/`_trans` of completed comparison maps — proved by
density on the classes of vectors.

- 2026-08-02 — Subspace permanence holds for an arbitrary nuclear presentation.

### A nuclear space that is not finite dimensional

`formal/GaloisForLFunctions/RHTower/DeningerRapidSequenceSpace.lean` and
`.../DeningerRapidSequenceNuclear.lean` (25 declarations together, axiom audit `propext,
Classical.choice, Quot.sound`).

`deningerRapid_isNuclearSpace`: **the rapidly decreasing sequences form a nuclear space**, and
`deningerRapid_not_finiteDimensional`: it is not finite dimensional.  The comparison map between
consecutive weighted `ℓ²` seminorms is written as the series of rank one maps given by the
coordinate functionals `deningerRapidCoeff` and the basis classes, with
`‖φ_n‖ ‖[e_n]‖ ≤ (n+1)^{-2}`; the convergence statement `deningerRapid_hasSum_basis` comes from
`lp.hasSum_single` through the isometric `ℓ²` embedding of a Hilbertian quotient.

This supplies the model against which the radial–angular comparison of this card is to be
calibrated, and it makes the permanence theorems of the nuclear test scale non-vacuous: they now
have an infinite dimensional space to act on.

- 2026-08-02 — The nuclear test scale has an infinite dimensional model in Lean.

## Lean: corpus survey before starting (2026-08-02)

Survey of what the formal tree already provides for this card, so the work starts at the real gap.

Already built and usable (`formal/GaloisForLFunctions/RHTower/`):

- `DeningerNuclearOperator` — `DeningerIsNuclear` (rank-one series), sums of nuclear maps.
- `DeningerSeminormQuotient`, `DeningerNuclearSpaceCompleted` — `DeningerIsNuclearSpace`,
  `DeningerIsNuclearSpaceC` and the comparison-map presentation of nuclearity for a seminorm
  family.
- `DeningerNuclearProduct` — **`deningerIsNuclearSpace_pi`: a product of nuclear spaces is
  nuclear**, exactly the permanence the card's proof of `(1)` invokes.
- `DeningerNuclearSubspaceHilbertian`, `DeningerNuclearCompletedInvariance`,
  `DeningerFinestSubspaceNuclear` — **subspaces of nuclear spaces are nuclear**, the other
  permanence the card invokes.
- `DeningerKotheSpace` — Köthe spaces and the Grothendieck–Pietsch criterion
  (`deningerKothe_isNuclearSpace`).
- `DeningerRapidSequenceNuclear` — the space of rapidly decreasing sequences is nuclear.
- `DeningerNuclearTransport(C)` — nuclearity transports along a linear equivalence matching the
  seminorms; `DeningerTensorNuclear` — projective tensor products of nuclear spaces are nuclear.

The real gap for this card: **nuclearity of the Schwartz space itself**, which mathlib does not
have.  The route through the existing toolkit is the classical one: the Hermite coefficient map
identifies `𝒮(ℝ)` with a subspace of the rapidly decreasing sequences, matching the seminorms, so
`deningerRapid_isNuclearSpace` plus subspace permanence plus `deningerIsNuclearSpace_of_linearEquiv`
give it.  What must be built is the Hermite expansion with its two-sided seminorm estimates.

After that, `(2)` is a closed subspace (two continuous functionals) and `(1)` is a countable
product-and-subspace, both by the permanence lemmas above; then the Poisson operator `Z`, its
strictness, and the exact sequence `(4)`.

### Lean: the oscillator number operator and the decay of Hermite coefficients

`formal/GaloisForLFunctions/HTGeometry/HermiteNumberOperator.lean` (7 declarations) and
`formal/GaloisForLFunctions/HTGeometry/HermiteCoefficientDecay.lean` (3 declarations), axiom audit
`propext, Classical.choice, Quot.sound`.

The corpus already owned the oscillator algebra on `𝓢(ℝ,ℂ)` — creation and annihilation operators,
their commutator, the raising and lowering relations on the Hermite functions, the adjointness of
`A` and `B` for the bilinear pairing, and the orthonormality of the Hermite family in `L²`.  These
two modules add the piece the nuclearity argument runs on.

- `numberCLM` — the number operator `N = A B`.
- `numberCLM_hermiteSchwartz` — **the Hermite functions are its eigenfunctions with eigenvalue
  `4πn`**: `B` lowers with factor `2n`, `A` raises back with factor `2π`.
- `schwartzPair_numberCLM` — **`N` is symmetric for the bilinear pairing**, since `A` and `B` are
  adjoint to each other; hence `⟨Nᵏf, g⟩ = ⟨f, Nᵏg⟩`.
- `numberCLM_iterate_hermiteSchwartz`, `schwartzPair_hermiteSchwartz_numberCLM_iterate` — **the
  `n`-th Hermite coefficient of `Nᵏf` is `(4πn)ᵏ` times that of `f`.**
- `schwartzPair_eq_inner_toLp`, `norm_schwartzPair_hermiteSchwartz_le` — the pairing against a
  Hermite function is an `L²` inner product (the Hermite functions are real valued), so
  Cauchy–Schwarz applies.
- `schwartzPair_hermiteSchwartz_decay` — **`(4πn)ᵏ ‖⟨f, hₙ⟩‖ ≤ ‖hₙ‖₂ ‖Nᵏf‖₂`**: the Hermite
  coefficients of a Schwartz function decay faster than any power, with an explicit constant at
  every order.

Remaining chain to `𝒮(ℝ)` nuclear, in order: completeness of the Hermite system in `L²`; the
two-sided comparison between the Schwartz seminorms and the number-operator seminorms
`qₖ(f) = ‖Nᵏf‖₂` (the easy direction is a temperate-growth estimate, the other is the
one-dimensional Sobolev bound `‖g‖∞² ≤ 2‖g‖₂‖g'‖₂` plus the oscillator algebra); then transport
onto the rapidly decreasing sequence space, which the corpus already knows is nuclear, by
`deningerIsNuclearSpace_of_linearEquiv` and subspace permanence.

- 2026-08-02 — Number operator, its eigenrelation and symmetry, and the rapid decay of Hermite
  coefficients: the engine of the Schwartz nuclearity proof.

### Lean: the Hamiltonian, its seminorms, and the easy comparison

`formal/GaloisForLFunctions/HTGeometry/HermiteHamiltonian.lean` (13 declarations) and
`formal/GaloisForLFunctions/HTGeometry/HermiteOscillatorContinuity.lean` (4 declarations), axiom
audit `propext, Classical.choice, Quot.sound`.

- `schwartzPair_add_right`, `_add_left` — additivity of the bilinear pairing in each slot.
- `hamiltonianCLM`, `hamiltonianCLM_two_smul` — the **oscillator Hamiltonian** `H = A B + 2π`,
  shown to be the symmetric combination `(A B + B A)/2` by the commutation relation.
- `hamiltonianCLM_hermiteSchwartz` — **eigenvalue `2π(2n+1)`**, which never vanishes; unlike the
  number operator, the Hamiltonian gives an estimate that is meaningful at the ground state too.
- `schwartzPair_hamiltonianCLM`, `schwartzPair_hamiltonianCLM_iterate` — the Hamiltonian and all
  its powers are symmetric for the bilinear pairing.
- `hamiltonianCLM_iterate_hermiteSchwartz`, `schwartzPair_hermiteSchwartz_hamiltonian_iterate`,
  `schwartzPair_hermiteSchwartz_hamiltonian_decay` — **`(2π(2n+1))ᵏ ‖⟨f, hₙ⟩‖ ≤ ‖hₙ‖₂ ‖Hᵏf‖₂`.**
- `hamiltonianPowCLM`, `oscillatorSeminorm`, `_apply` — **the oscillator seminorms**
  `qₖ(f) = ‖Hᵏf‖₂` as `Seminorm` objects on the Schwartz space, the Hilbertian family in which the
  nuclear structure will be visible; the Hermite functions diagonalize every one of them.
- `oscillatorSeminormFamily`, `oscillatorSeminorm_continuous`,
  `oscillatorSeminorm_le_schwartzSeminorm` — **each oscillator seminorm is continuous, hence
  bounded by finitely many Schwartz seminorms** (`Seminorm.bound_of_continuous` against
  `schwartz_withSeminorms`).  That is one of the two comparisons needed to identify the oscillator
  presentation of the Schwartz topology with the standard one.

Next: the reverse comparison (a Schwartz seminorm bounded by an oscillator seminorm) and
completeness of the Hermite system in `L²`, after which the nuclearity of `𝒮(ℝ)` follows from the
corpus's Köthe/rapid-sequence nuclearity by transport.

- 2026-08-02 — Hamiltonian, its spectrum on the Hermite functions, the oscillator seminorms, and
  the easy half of the seminorm comparison.

### Lean: the Hermite polynomials span, and the vanishing of Gaussian moments

`formal/GaloisForLFunctions/HTGeometry/HermitePolynomialSpan.lean` (11 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `hermitePoly_degree_leadingCoeff`, `_degree`, `_leadingCoeff`, `_coeff_self`,
  `_coeff_eq_zero` — **the `n`-th Hermite polynomial has degree `n` and leading coefficient `2ⁿ`.**
  Each recursion step multiplies by `2X` and subtracts a multiple of the derivative, whose degree
  is strictly smaller, so the top term is untouched.
- `mem_span_hermitePoly_of_degree_lt`, `hermitePoly_span_eq_top` — **the Hermite polynomials span
  the polynomial ring**, by the triangular argument: subtracting the right multiple of the `n`-th
  Hermite polynomial lowers the degree, and one descends on the degree.
- `polyGaussSchwartz_add`, `_smul`, `polyGaussLM` — the Gaussian multiples of polynomials as an
  `ℝ`-linear map into the Schwartz space.
- `schwartzPair_polyGauss_eq_zero` — **a Schwartz function orthogonal to every Hermite function is
  orthogonal to every polynomial multiple of the Gaussian**: all of its Gaussian moments vanish.
  Proved by span induction, so it needs no coordinates.

This is the first step of the completeness of the Hermite system.  What remains for completeness:
the vanishing of all moments of the integrable function `f·e^{−πx²}` forces its Fourier transform
to vanish (its power series at the origin is identically zero and it is entire, since the Gaussian
weight makes every moment bound factorially small), and a function with vanishing Fourier transform
is zero.

- 2026-08-02 — The Hermite polynomials span; orthogonality to the Hermite family kills every
  Gaussian moment.

### Lean: vanishing moments kill every exponential integral

`formal/GaloisForLFunctions/HTGeometry/HermiteGaussianExponential.lean` (5 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `complex_hasSum_exp`, `real_hasSum_exp` — the exponential series in `HasSum` form, over `ℂ` and
  over `ℝ`.
- `gauss_mul_exp_abs_le` — **the Gaussian dominates every exponential**:
  `e^{−πx²}e^{|a||x|} ≤ e^{a²/π} e^{−3πx²/4}`, from `4π|a||x| ≤ 4a² + π²x²`, that is from
  `(2|a| − π|x|)² ≥ 0`.
- `integrable_gauss_mul_exp_abs` — hence the dominating function is integrable.
- `integral_gaussMul_exp_eq_zero` — **a Schwartz function orthogonal to every Hermite function
  integrates to zero against the Gaussian times any complex exponential**:
  `∫ f(x) e^{−πx²} e^{cx} dx = 0` for every `c ∈ ℂ`.  The exponential is expanded into its power
  series and integrated term by term — legitimate by dominated convergence with the bound above —
  and every term is a Gaussian moment, which vanishes by the span step.

Taking `c = −2πit` this says the Fourier transform of `f·e^{−πx²}` vanishes identically.  What
remains for completeness of the Hermite system is the Fourier uniqueness step: an integrable
continuous function whose Fourier transform vanishes is zero, whence `f = 0`.

- 2026-08-02 — Every exponential integral of a Hermite-orthogonal Schwartz function vanishes; only
  Fourier uniqueness is left before completeness.

### Lean: completeness of the Hermite system on the Schwartz space

`formal/GaloisForLFunctions/HTGeometry/HermiteCompleteness.lean` (4 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `gaussMul`, `gaussMul_apply` — the Gaussian multiple of a Schwartz function, itself Schwartz.
- `fourier_gaussMul_eq_zero` — **the Fourier transform of `f·e^{−πx²}` vanishes identically** for a
  Schwartz `f` orthogonal to every Hermite function: it is the exponential integral of the previous
  module at the imaginary exponent `c = −2πit`.
- `hermiteSchwartz_complete` — **a Schwartz function orthogonal to every Hermite function is
  zero.**  Fourier inversion (`Continuous.fourierInv_fourier_eq`) turns the vanishing transform
  into the vanishing of `f·e^{−πx²}`, and the Gaussian never vanishes.

So the Hermite coefficient map is injective on `𝒮(ℝ)`: the Hermite system is complete there.  This
was the remaining blocker; it is the injectivity the nuclearity transport consumes.

What is left for `𝒮(ℝ)` nuclear: the reverse seminorm comparison — a Schwartz seminorm bounded by
an oscillator seminorm `qₖ(f) = ‖Hᵏf‖₂` — after which the coefficient map identifies `𝒮(ℝ)` with a
subspace of the rapidly decreasing sequence space, matching the seminorms, and the corpus's
`deningerRapid_isNuclearSpace` plus subspace permanence and
`deningerIsNuclearSpace_of_linearEquiv` finish it.

- 2026-08-02 — Hermite completeness on the Schwartz space: the coefficient map is injective.

### Lean: `L²` bounds for the oscillator operators

`formal/GaloisForLFunctions/HTGeometry/SchwartzOscillatorL2Bound.lean` (12 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

The reverse seminorm comparison needs the creation and annihilation operators to be controlled in
`L²` by the number operator.  That is what this module proves, working with the corpus's
conjugation operator `SchwartzMap.conjSLM`.

- `conjSLM_conjSLM`, `schwartzPair_eq_inner`, `norm_toLp_conjSLM`, `norm_schwartzPair_le` — **the
  bilinear pairing is the `L²` inner product against the conjugate**, conjugation is an `L²`
  isometry, and hence **Cauchy–Schwarz holds for the pairing**:
  `‖⟨u, v⟩‖ ≤ ‖u‖₂‖v‖₂`.
- `norm_schwartzPair_conj_self` — the pairing of the conjugate against the function is the square
  of the `L²` norm.
- `conjSLM_derivSCLM`, `conjSLM_mulXCLM`, `conjSLM_creationCLM`, `conjSLM_annihilationCLM` —
  **conjugation commutes with all four operators** (their coefficients are real); the derivative
  case is the chain rule through the `ℝ`-linear conjugation.
- `norm_toLp_creationCLM_sq_le` — **`‖Ag‖₂² ≤ ‖g‖₂‖(N + 4π)g‖₂`**, from adjointness `⟨Ag,h⟩ =
  ⟨g,Bh⟩` and the commutation relation `B A = N + 4π`.
- `norm_toLp_annihilationCLM_sq_le` — **`‖Bg‖₂² ≤ ‖g‖₂‖Ng‖₂`**, likewise with `A B = N`.

Since `x = (A+B)/4π` and `d/dx = (B−A)/2`, iterating these two bounds controls every
`‖x^k ∂^n f‖₂` by oscillator seminorms; combined with the one-dimensional Sobolev estimate
`‖g‖∞² ≤ 2‖g‖₂‖g′‖₂` this will give the reverse comparison and finish the nuclearity of `𝒮(ℝ)`.

- 2026-08-02 — Cauchy–Schwarz for the pairing, conjugation compatibility, and the `L²` bounds for
  the creation and annihilation operators.
